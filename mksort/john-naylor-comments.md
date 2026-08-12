# John Naylor 的 mksort comments

## 状态

本文记录 John Naylor 对 mksort compare abstraction、presort semantics 和
comparator hot path 的意见，以及相应的设计分析。各节保留重构前的问题背景，
已经采用的修改在对应的“当前实现”小节中说明。

## 问题背景

standard sort 对 btree index tuple 的特殊语义集中在
**comparetup_index_btree()** 和 **comparetup_index_btree_tiebreak()** 中：

1. 比较第一个显式 index key。
2. 比较剩余显式 index keys。
3. 所有显式键相等时处理 unique index 约束和 NULL 语义。
4. 最后比较隐式 heap TID，保证 index tuple 的物理顺序唯一。

generic tuplesort 只调用 btree comparator，不需要知道 duplicate、unique
constraint、NULL 或 TID 的存在。

重构前的 mksort 将这些职责拆散到了多个层次：

- **mkqs_get_datum()** 和 **MkqsGetDatumFunc** 按 depth 提取 datum。
- generic **mk_qsort_tuple()** 识别最后一键的 equal partition。
- generic recursion 维护并向下传递 **seenNull**。
- **MkqsHandleDupFunc** 处理最后的 duplicate group。
- btree 的 **mkqs_handle_dup_index_btree()** 检查 uniqueness，并对 duplicate
  group 再按 heap TID 排序。

因此当时的 generic mksort 开始了解原本应由 btree comparator 封装的知识。John
所说的 “new single-use abstraction for the btree tid tiebreak” 主要指
**MkqsHandleDupFunc / mkqs_handle_dup_index_btree()** 这一套 abstraction，
而不是 **mkqs_compare_datum_tiebreak()**。

后者虽然名称中包含 tiebreak，但实际负责当前显式排序键的 datum
extraction、abbreviation full comparison 和 SortSupport comparison，并不是
btree heap TID comparator。

当前实现已经删除 **seenNull** 和 duplicate handler 中不可达的 unique-check
分支。Unique btree tuplesort 仍使用 standard sort；non-unique btree mksort
保留 **MkqsHandleDupFunc**，仅在所有显式键相等后按 heap TID 排序。将 TID
表示为隐式最后 depth 的方案没有采用。

## 设计目标

1. 让 heap 和 btree 各自拥有 tuple representation、datum accessor 和最终
   ordering semantics。
2. generic mksort 只处理 quicksort/radix-style partition 和 depth recursion。
3. 从 generic mksort 中删除 duplicate handler、btree TID 和 unique/NULL
   相关知识。
4. 使用同一个 comparator contract 支持 single-depth 和 depth-range
   comparison。
5. 不在比较热路径中重新引入不可接受的动态 accessor 开销。
6. 不改变 planner、统计信息或 mksort applicability policy。

## 建议接口

概念接口如下：

~~~c
typedef int (*SortTupleMkComparator) (const SortTuple *a,
                                      const SortTuple *b,
                                      int start_depth,
                                      int max_depth,
                                      Tuplesortstate *state);
~~~

也可以表示成：

~~~c
comparetup_mk(state, a, b, start_depth, max_depth)
~~~

这里 **max_depth** 是 inclusive：

- **start_depth == max_depth**：只比较一个 depth。
- **start_depth < max_depth**：从 start_depth 连续比较到 max_depth，遇到
  第一个不相等的键立即返回。

接口名称和参数顺序可以调整，关键是 comparator 同时支持单键和键范围。

## Depth 语义

### Heap tuple

对于包含 nKeys 个排序键的 heap tuple：

~~~text
0 ... nKeys - 1    显式排序键
~~~

heap comparator 不接受超过 nKeys - 1 的 depth。

### Btree index tuple

对于包含 nKeys 个显式 index keys 的 btree index tuple：

~~~text
0 ... nKeys - 1    显式 index keys
nKeys              隐式 heap TID
~~~

btree comparator 看到 **depth == nKeys** 时，不再调用 index_getattr()，而是
比较两个 IndexTuple 的 t_tid。

generic mksort 只看到一个额外 depth，不需要知道它代表 heap TID。tuple
variant 初始化阶段可以提供该 sort variant 的最大 depth。

## mksort 中的调用方式

当前 partition 在指定 depth 比较 tuple：

~~~c
ret = mkqs_compare_datum(a, b, depth, state);
~~~

建议改成 single-depth comparison：

~~~c
ret = comparetup_mk(a, b, depth, depth, state);
~~~

需要判断 tuple 在剩余 keys 上的完整顺序时，可以使用：

~~~c
ret = comparetup_mk(a, b, depth, max_depth, state);
~~~

对于 non-unique btree，当最后一个显式 key 的 equal partition 仍包含多个
tuples 时，generic algorithm 可以像进入普通下一键一样进入
**depth == nKeys**。该 depth 的 comparator 自动比较 TID，不再调用
duplicate handler。

## 可以取代的现有组件

该方案完整实现后，预计可以删除或合并：

- **mkqs_compare_datum()**
- **mkqs_compare_datum_tiebreak()**
- **mkqs_get_datum()**
- **MkqsGetDatumFunc**
- **mkqs_get_datum_index_btree()**
- **MkqsHandleDupFunc**
- **mkqs_handle_dup_index_btree()**
- **TuplesortPublic.mkqsGetDatumFunc**
- **TuplesortPublic.mkqsHandleDupFunc**
- generic mksort 的 terminal duplicate-handler dispatch
- 仅为 duplicate handling 服务的 seenNull recursion
- 如果 seenNull 完全删除，则包括 **check_datum_null()**

这里的“取代”不一定意味着把所有逻辑放进一个很大的 C 函数。heap 和
btree 可以各自使用 inline helpers，但 generic API 不再暴露独立 accessor
和 duplicate handler。

## 保留在 mk_qsort_tuple() 中的逻辑

以下内容属于排序算法本身，不应移入 tuple comparator：

- pivot 和 median selection
- presort detection
- insertion sort / qsort threshold
- less/equal/greater partition
- tuple swap 和 vector swap
- equal partition 进入下一 depth
- less/greater partition recursion
- interruption checks

因此该方案重构的是 comparison boundary，不是替换 multi-key quicksort
算法。

## Btree TID 处理的变化

当前流程：

~~~text
最后一个显式键形成 equal group
  -> generic mksort 判断 duplicate
  -> 调用 mkqs_handle_dup_index_btree()
  -> 对整个 group 使用 TID qsort
~~~

建议流程：

~~~text
最后一个显式键形成 equal group
  -> generic mksort 进入下一个 depth
  -> btree comparetup_mk(depth == nKeys) 比较 TID
~~~

这样 TID 是 btree ordering model 中的隐式最后一键，而不是 generic
mksort 中的一种特殊 duplicate action。

## Unique index 和 NULL

当前代码不允许 unique btree build 进入 mksort：

~~~c
if (base->nKeys > 1 && !enforceUnique)
    base->mkqsTupleType = MKQS_TUPLE_TYPE_INDEX_BTREE;
~~~

因此当时建议第一阶段只支持可达的 non-unique btree 路径：

- 删除 mksort duplicate handler 中不可达的 unique-check 分支。
- 删除仅为该分支传递的 seenNull。
- 将 TID 作为 btree 隐式最后 depth。

当前实现采用了前两项，但没有采用第三项：TID 仍由 terminal duplicate
handler 排序，不作为 mksort depth。

未来若允许 unique btree 进入 mksort，必须单独设计：

- 何时确认所有显式 keys 完全相等。
- 如何获得所有显式 keys 的 NULL 信息。
- uniqueNullsNotDistinct 的语义。
- 在比较 TID 前何时抛出 unique violation。

不能为了删除 seenNull 而遗漏这些语义，也不应把它们重新放回 generic
mk_qsort_tuple()。

## Abbreviation

第一个 key 可能在 SortTuple.datum1 中保存 abbreviated value。新的
comparator 必须保持 standard sort 的行为：

1. 先比较 abbreviated leading key。
2. abbreviated values 相等时，提取完整 datum。
3. 调用 ApplySortAbbrevFullComparator()。
4. 后续 depths 使用普通 SortSupport comparator。

**start_depth == max_depth == 0** 仍然必须完成 abbreviation fallback，不能
只比较 abbreviated proxy。

## 性能约束

John 的建议改善 abstraction boundary，但朴素实现可能引入性能回退。
尤其不能在每次 hot comparison 中通过新的动态函数指针完成 tuple dispatch
和 datum access。

建议保留以下优化原则：

- 在 mksort 入口只进行一次 heap/btree dispatch。
- 使用 template/macro 从同一算法源码生成 heap 和 btree 专用路径。
- comparator 内部使用 tuple-type-specific static inline helper。
- single-depth comparison 应允许 compiler inline datum accessor。
- first-key integer shortcut 和 abbreviation shortcut 不能无意丢失。
- range comparator 不应在只比较一个 depth 时循环所有剩余 keys。

因此 depth-range comparator 与 accessor template 方案并不冲突：

- depth-range comparator 定义职责边界和语义。
- template/inline specialization 保证执行层性能。

## Presort 语义

John 的第二个问题是：

> I don't understand why the pre-ordered check sometimes tolerates
> duplicates and sometimes doesn't.

重构前代码中确实存在多种 pre-ordered check。表面上的差异是有时使用
**ret > 0** 判定未排序，允许 equality；有时使用 **ret >= 0**，要求严格
递增。真正决定 equality 是否安全的因素不是 comparator type，而是该检查
覆盖的 key range，以及发现 equality 后是否继续处理后续 depths。

### 完整 tuple comparator

depth 0 的 specialized path 使用 standard sort 的完整 comparator：

~~~c
if (COMPARETUP(state, x + i, x + i + 1) > 0)
    preOrdered = false;
~~~

COMPARETUP 按完整 ordering semantics 比较所有显式 keys；btree comparator
还会比较隐式 TID。返回 0 表示两个 tuples 在完整排序语义下相等，它们保持
当前相对位置仍然是合法排序结果。因此这里可以接受 equality。

重构前的 generic comparator path 在进入 mk_qsort_tuple() 之前也通过
**tuplesort_memtuples_presorted()** 做同样的 full-key check。standard
radix/qsort 的 presorted check 也采用 full comparator 和 nondecreasing
判定。

### 只比较当前 depth

重构前 mk_qsort_tuple() 的另一条路径只调用：

~~~c
mkqs_compare_datum(a, b, depth, state)
~~~

这个函数只比较当前 depth，因此 presort check 要求：

~~~c
ret < 0
~~~

如果 ret == 0，只能证明当前 keys 相等，不能证明后续 keys 已排序。例如：

~~~text
(1, 9)
(1, 2)
~~~

在 depth 0 上两个 tuples 相等，但 depth 1 明显逆序。此时必须继续
partition，并让 equal group 进入下一 depth。因此 single-depth check 不能
把 equality 当成“整个 range 已排序”。

### Leading-key optimization

重构前的 **mkqs_try_presorted_leading_key()** 也允许第一键 equality：

~~~c
if (ret > 0)
    return false;
~~~

但它不会因为 leading key nondecreasing 就直接认为完整 tuple array 已排序。
它识别每个 equal-key group，并对 group 从 depth 1 递归调用
mk_qsort_tuple()。因此这里 tolerates leading-key duplicates 的准确含义是：

> 保留现有第一键顺序，但显式地递归处理所有 ties。

这与 full-key check 接受 equality 后直接返回，是两种不同的安全条件。

### 重构前的 mkqsTopPresortChecked

generic top-level full-key check 失败时，会记录：

~~~c
mkqsTopPresortChecked =
    mkqs_compare_datum(st - 1, st, 0, state) >= 0;
~~~

它表示本次 full-key inversion 同时已经证明第一键不可能严格递增：

- ret > 0：第一键本身逆序。
- ret == 0：第一键相等，但后续 key 逆序。

mk_qsort_tuple() 随后可以跳过一次必然失败的 single-depth strict-order
扫描。这个 flag 是为了避免重复检查，但名称没有表达“full-key check 已经
证明 leading key strict order 不成立”的完整语义。

### 为什么 John 的疑问合理

重构前行为在算法上可以解释，但 abstraction 和命名不够清楚：

- COMPARETUP 隐含 full-key range。
- mkqs_compare_datum 隐含 single-depth range。
- mkqs_try_presorted_leading_key 接受 equality，但会递归处理 ties。
- 分支选择依赖 depth、mkqsCompFuncType 和 mkqsTopPresortChecked。
- duplicate 有时表示当前 key 相等，有时表示所有显式 keys 相等。

因此 reviewer 只看到 **> 0** 和 **>= 0** 的差异时，很难确认这是有意的
range semantics，还是不一致的 duplicate handling。

### depth-range comparator 如何改善

start_depth / max_depth 可以把每次检查的范围直接写在调用点：

~~~c
/* 完整剩余 ordering；full-range equality 是合法结果。 */
comparetup_mk(a, b, depth, max_depth, state) > 0

/* 只检查当前 key；equality 表示还需要处理下一 depth。 */
comparetup_mk(a, b, depth, depth, state) >= 0
~~~

leading-key optimization 则应明确写成“single-depth nondecreasing scan +
recursive handling of equal groups”，而不是泛称 presorted check。

重构时还需要明确：

- 最终 qsort fallback 是否比较所有剩余 depths。
- btree full-order check 是否包含隐式 TID。
- abbreviation fallback 是否属于 depth 0 的完整单键比较。
- 哪一层负责处理 equal groups，而不是仅通过 duplicate 一词暗示。

这不会自动减少所有 presort scans，但会让每次 scan 的正确性条件可见，也
能避免 generic/specialized comparator 对“已排序”的定义继续漂移。

### 当前实现

当前代码已经通过命名和 depth-range 调用把三种语义分开：

1. **mkqs_full_order_presorted()** 只用于 top-level complete ordering scan。
   heap 明确比较 depth 0 到 nKeys - 1；btree 在隐式 TID depth 尚未纳入
   **comparetup_mk()** 前，继续使用其 standard full comparator。该检查允许
   full-order equality，并可以直接结束排序。
2. **mkqs_depth_strictly_increasing()** 只比较当前 depth。它要求严格递增；
   equality 表示后续 depths 尚未检查，必须继续 partition 和 depth recursion。

曾实现 leading-key nondecreasing scan，并从下一 depth 单独排序每个 equal
group。该优化只适用于少于 **QSORT_THRESHOLD** 个 tuple、第一键非严格有序且
后续键尚未有序的窄场景，因此已移除。

原来的 **mkqsTopPresortChecked** 已改为 **mkqsTopPresortFailed**。generic
top-level full-order scan 失败后直接设置该状态，不再额外执行一次必然得到
大于或等于零的 single-depth comparison。这样 state 表达的是“相同的完整
top scan 已执行且失败”，而不是隐含的 strict-order 推论。

曾尝试在每个 mksort recursive depth 都执行完整 remaining-range scan，并允许
equality。该方案功能正确，但在 3 到 5 键 duplicate-heavy case 中造成约
3% 到 4% 稳定回退，因为 mksort 的 equal-key depth recursion 会重复扫描后续
键；standard qsort 没有对应的逐键递归层级。因此最终只在 top level 使用
full-order scan，递归 depth 保留语义明确且成本较低的 single-depth strict
scan。

## 3A：将 shortcut 和 abbreviation 表示为负 depth

John 的想法是：

> I wonder if the shortcut (and abbreviated?) comparisons could be thought
> of as having their own depth < 0. If it's worth it to postpone later keys,
> maybe it's worth it to postpone the full comparison for the first key as
> well?

这里的 postpone 不是省略 full comparison，而是延迟到便宜的比较无法确定
顺序时再执行。

multikey sort 已经这样处理后续 keys。depth 0 只比较 first key；只有 first
key 相等的 equal partition 才进入 depth 1。John 想把 first key 内部的
abbreviated comparison 和 full comparison 也表示成两个 depth：

~~~text
depth -1    abbreviated first key
depth  0    full first key
depth  1    second explicit key
depth  2    third explicit key
~~~

在 depth -1 上 abbreviated values 不同就能确定顺序；只有 abbreviated
equal group 才进入 depth 0 提取完整 datum。完整 first keys 仍相等时，才
进入 depth 1。

### 当前实现已经有局部 postpone

当前 mkqs_compare_datum() 在一次 comparator 调用中执行：

~~~text
compare abbreviated key
  -> unequal: return
  -> equal: immediately compare full first key
~~~

因此当前实现已经通过 short-circuit 避免不必要的 full comparison。负
depth 方案的新增部分，是把 immediate fallback 提升为独立 partition 和
下一层 recursion：

~~~text
当前：一次 comparator 内 abbrev -> full
建议：按 abbrev partition，equal group 下一 depth 按 full partition
~~~

如果负 depth 只是接口中的概念编号，而 comparator 内部仍立即 fallback，
运行成本接近零，但也不会产生新的性能收益。真正需要评估的是建立独立
partition 的版本。

### Exact shortcut 和 abbreviation 不能等同

abbreviated value 是可能 collision 的 proxy。abbreviated equality 不代表
完整 first key 相等，因此可以自然地分成 proxy depth 和 full-key depth。

int/bigint shortcut 通常直接比较 SortTuple 中缓存的精确 datum1。它已经是
完整 first key，不存在另一轮 full comparison。如果定义：

~~~text
depth -1    exact integer shortcut
depth  0    full integer first key
~~~

就会重复比较同一个值。exact shortcut 要么继续作为 first-key depth，要么
在 equality 后直接跳到第二个显式 key。对它引入负 depth 最多只是编号重排，
不应增加真实 recursion。

### 独立负 depth 的成本

真正增加一层 abbreviated partition 会带来：

- 一层 mk_qsort_tuple() recursion 和 depth checks。
- abbreviated equal group 的额外 partition traversal。
- 额外 pivot/median selection。
- 额外 tuple swaps 和 equal-group boundary handling。
- hot path 中的负 depth 判断或 depth mapping。

单个可预测的 depth branch 成本通常很小，主要成本是 equal group 被再次
完整遍历和交换。

### 不同分布下的预期

#### Abbreviated values 基本唯一

当前 comparator 和负 depth 都主要依靠 abbreviated comparison 确定顺序。
负 depth 没有可节省的 full comparisons，只增加少量 depth 管理成本，预期
持平或轻微回退。

#### Abbreviated values 和 full first keys 都相同

这是 mksort 的重要目标场景：first key 大量真实重复。

当前一次 partition comparison 完成 abbreviated equality 和 full-key
equality，然后直接形成 first-key equal partition。负 depth 会先形成
abbreviated equal partition，再对同一 group 做 full-key partition，之后才
进入第二个显式 key。

primitive abbrev/full comparison 数量未必显著增加，但 partition loop、
pivot 和 swaps 会执行两层。这个场景更可能回退。

#### Abbreviated values 相同，但 full first keys 不同

这是负 depth 唯一比较明确的潜在收益场景。设 collision group 大小为 m：

~~~text
当前：
  O(m log m) abbreviated comparisons
  O(m log m) full comparisons

独立负 depth：
  O(m) abbreviated comparisons，用于形成 equal group
  O(m log m) full comparisons，用于排序 group
~~~

它可以避免 full-key sorting 阶段重复执行便宜的 abbreviated comparison。
但不会减少昂贵的 full comparisons，并且增加一次 partition。只有 collision
group 很大、其中 full values 又大多不相等时，才可能获得净收益。

### 总体判断

PostgreSQL abbreviation 本身倾向于减少 collision；mksort 的主要收益场景
又是 first key 真实重复，而不只是 abbreviated collision。因此独立负 depth
在总体 workload 上获得稳定收益的可能性不高：

- abbreviation 基本唯一：无收益，可能轻微回退。
- first key 真实重复：额外 partition，较可能回退。
- 大型 abbreviation collision group 且 full values 不同：可能收益。
- exact int/bigint shortcut：没有算法收益。

这与 John 使用 “Random thought” 和 “I could be wrong” 一致：该建议首先是
对统一 depth model 的探索，而不是已经证明的性能优化。

### 实施前需要的证据

在编写 prototype 前应加入轻量计数，至少收集：

- depth-0 comparison 总数。
- abbreviated equality 次数。
- full first-key comparison 次数。
- full comparison 返回 0 的次数。
- full comparison 返回非 0 的次数。
- equal-abbrev group size 分布。

如果 abbreviated equality 主要来自 full-key duplicate，独立负 depth 不值得
实现。如果主要来自大型 abbreviation collision group，才值得进行 focused
prototype，并与当前 immediate fallback 比较 instructions、cycles、swaps
和总时间。

## 3B：分离 first-key NULL tuples

John 的 side note 是：

> I've long wanted to try separating all NULL first keys to a separate array,
> so we can remove all those branches for NULL ordering and reduce SortTuple
> to 16 bytes. That might be easier to code if we could simply specify
> "start_depth = 1" at the top level for that.

该想法不是为 NULL group 编写一套特殊排序算法，而是从数据入口开始维护
两个 tuple arrays：

~~~text
first key is NULL
  -> null_memtuples[]
  -> sort(start_depth = 1)

first key is NOT NULL
  -> nonnull_memtuples[]
  -> sort(start_depth = 0)
~~~

NULL array 中所有 tuples 在 depth 0 上必然相等，因此直接从第二个显式 key
开始排序。只有一个排序键时，NULL array 内部不需要排序。两个 arrays 完成
排序后，根据 NULLS FIRST/LAST 决定拼接顺序。

### 它不能删除后续 depths 的 NULL handling

即使 first-key NULL tuples 已经分离，第二键及后续 keys 仍然可能为 NULL。
这些 depths 的 datum extraction、NULL ordering 和 comparator branches 都
必须保留。

该方案只消除最热 first-key path 中的 NULL handling：

- non-NULL array 的 depth-0 comparator 可以假定双方都非 NULL。
- NULL array 完全跳过 depth 0。
- NULLS FIRST/LAST 在最终拼接时决定，而不是每次 first-key comparison
  都判断。

因此不能把它描述成“消除 tuplesort 的 NULL handling”，准确说法是“消除
first-key hot comparison 的 NULL handling”。

### 为什么 first key 仍然可能重要

standard lexicographic comparator 的每次 tuple comparison 都从 first key
开始。对于 comparison sort，first-key NULL checks 可能执行 O(N log N)
次，而输入阶段分离两个 arrays 只需要 O(N)。

后续 keys 只在所有前置 keys 相等时访问，所以第一键的执行频率通常最高。
收益取决于 branch predictability：

- first key 从不为 NULL：分支高度可预测，单纯移除 branch 的收益很小。
- NULL 很少：通常仍然较容易预测。
- NULL/non-NULL 随机混合：更可能产生 branch misprediction。
- int/bigint 等便宜 comparison：NULL branch 的相对占比更高。
- text/collation 等昂贵 comparison：NULL branch 的相对占比更低。

### 对 mksort 的收益可能更小

mksort 已经按 depth 分层。first key 大量重复时，depth 0 做一次 three-way
partition 后，equal group 进入 depth 1，不会在后续 depths 反复检查 first
key。

因此在 mksort 的典型收益场景中：

~~~text
提前分离 NULL array：O(N)
原有 depth-0 NULL checks：接近 O(N)
~~~

新增 partition、双数组管理和输出拼接可能抵消 branch savings。

first key 基本 unique 时，depth-0 comparison 次数更接近 O(N log N)，此时
消除 NULL branch 更可能有收益。但这不是 mksort 最有优势的数据分布。

所以该优化对 standard sort 的潜在吸引力通常高于对 duplicate-heavy
mksort 的吸引力。

### 当前 radix path 已经部分实现

当前 radix_sort_tuple() 已经在排序入口按 isnull1 对同一个 SortTuple array
做原地 partition：

~~~text
NULL first-key partition
non-NULL first-key partition
~~~

随后 NULL partition 从 depth 1 排序，non-NULL partition 使用 radix sort
或 standard qsort。因此 radix path 已经获得了“分区后跳过 first-key NULL
comparison”的大部分算法收益。

John 的方案更进一步：

- 在 tuple ingestion 阶段就维护两个物理 arrays。
- 让 generic qsort/mksort 也使用已知 NULL 状态的输入。
- 删除每个 SortTuple 中的 isnull1。
- 为更紧凑的数据布局创造条件。

因此相对于当前 radix path，单纯改变 NULL partition 时机的增量收益可能
较小。

### 16-byte SortTuple 是另一项独立假设

当前 64-bit 平台上的 SortTuple 包含：

~~~c
void  *tuple;
Datum  datum1;
bool   isnull1;
uint8  curbyte;
int    srctape;
~~~

当前结构通常占 24 bytes。若最终只保留 tuple pointer 和 datum1，可以缩小
到 16 bytes：

- entry memory footprint 下降约 1/3。
- 64-byte cache line 可以容纳 4 个 16-byte entries。
- partition、swap、copy 和 scan 的 cache density 提高。
- 相同 work_mem 可以容纳更多 tuples，可能减少 external runs。

这些收益影响所有 depths，因为每层算法移动的都是 SortTuple entries，不只
是 depth 0。

但是仅删除 isnull1 并不能让当前结构自动变成 16 bytes；curbyte 和 srctape
仍然会使结构产生额外空间和 alignment。要真正达到 16 bytes，还需要设计：

- 将 radix-only curbyte 移到 scratch storage，或从 tuple entry 中消除。
- 将 merge-only srctape 移到独立 metadata 或其他 representation。
- 可能为 in-memory sort 和 external merge 使用不同 entry layout。

因此“分离 first-key NULL tuples”只是 16-byte layout 的一个前提，不是
充分条件。结构压缩的潜在收益也不能全部归因于 NULL branch elimination。

### 实现范围和风险

维护两个物理 arrays 会影响完整 tuplesort lifecycle：

- work_mem accounting 和两个 arrays 的扩容。
- bounded/top-N sort。
- external run generation。
- tape merge 和 srctape metadata。
- parallel sort。
- abbreviation abort 后的 datum representation。
- 输出阶段的拼接。

这已经超出 mk_qsort_tuple() 的局部重构范围，是 tuplesort 数据布局级别的
长期优化。

### 建议拆成两个实验

应将 John 的建议拆成两个独立假设：

#### 实验 A：只分离 first-key NULL input

保持 SortTuple layout 不变，只评估：

- first-key comparator branch 数量。
- branch misses。
- upfront partition/双数组管理成本。
- standard sort、mksort 和 radix path 的时间差异。

预期该实验对 standard sort 可能有小幅收益；对 duplicate-heavy mksort 和
现有 radix path 的增量收益可能很小。

#### 实验 B：实现真正的 16-byte SortTuple

在实验 A 之外重构 curbyte、srctape 和 in-memory/external representations，
单独测量：

- cache misses 和 memory bandwidth。
- tuple swap/copy 成本。
- 相同 work_mem 下可容纳的 tuple 数量。
- external run 数量和整体排序时间。

该实验的潜在收益可能明显高于 branch-only 优化，但实现成本和影响范围也
远大于当前 mksort patch。

### 总体判断

如果不改变 SortTuple 大小，只分离 first-key NULL tuples：

- 不能消除后续 keys 的 NULL handling。
- 对 standard sort 可能有条件收益。
- 对 mksort 的典型 first-key duplicate 场景，收益大概率有限。
- 对当前 radix path，很多算法收益已经存在。

如果同时实现可靠的 16-byte SortTuple，数据布局收益可能更重要，但它应被
视为独立的 tuplesort-wide project。John 将其称为 “Side note” 是合适的；
它不应成为当前 mksort compare-abstraction 重构的前置条件。

## 4：不要把所有 optimized comparators 塞进同一条热路径

John 所说的 “stuff all our optimized comparators in the same path”，指当前
mksort 试图用同一组 generic functions 覆盖所有 comparator 变体。在一次
tuple comparison 的热路径中，代码可能反复判断：

- 当前是 first-key shortcut、abbreviated full comparison，还是普通 depth。
- shortcut 是 signed、int32，还是 generic SortSupport comparator。
- tuple 来自 heap 还是 index btree，应使用哪个 datum accessor。
- 当前 partition 是否已经排除了 NULL。
- 是否 reverse、是否到达最后 depth，以及是否需要特殊 duplicate/TID 处理。

这些条件大多在进入一个 recursive partition 时已经固定，但当前实现可能在
该 partition 的每一次 inner-loop comparison 中重新判断。问题不只是一两个
额外 branch，而是两类相互关联的成本：

1. 大量 comparator 变体及其处理代码集中或 inline 到同一条路径，使热函数
   变大，增加 instruction cache（I-cache）工作集。CPU 更可能需要重新取指，
   真正高频的 partition loop 也更难持续留在 I-cache 中。
2. 同一个 branch site 服务多种 comparator mode。虽然 mode 在单个 partition
   内通常稳定，但不同 partition 会改变 mode，增加 branch predictor 的负担；
   更重要的是，即使预测正确，每次 comparison 仍执行了 mode selection。

### John 建议的 dispatch 时机

John 并不是要求再增加一套 template，或为所有条件组合生成大量函数。他的
建议是：在递归进入 partition 时选择一次适合该 partition 的比较路径，然后
让 inner loop 只执行已经确定的 comparator。例如概念上可以分为：

~~~text
recurse(partition, depth):
    mode = select_compare_mode(state, depth, partition_properties)
    partition_with_mode(partition, mode)
~~~

这里适合在 recursion boundary 提前决定的条件包括 depth、shortcut 类型、
abbreviation、tuple representation、reverse、已知 non-NULL partition，以及
最后显式 key 或 btree TID depth。真正依赖当前两个 tuples 的条件，例如比较
结果和未被预先分区的 NULL，仍应留在 comparator 内部。

实现不一定需要一个 runtime mode enum 和间接函数调用。更直接的方式是在
递归入口做少量 branch，进入几个小型、静态可 inline 的 partition helper；
关键是 mode branch 每个 partition 执行一次，而不是每次 tuple comparison
执行一次。必须控制 specialization 数量，避免组合爆炸再次扩大代码体积。

### 与 comparetup_mk 的关系

这项意见与 depth-range **comparetup_mk()** 方案直接相关，但解决的是不同
层面的问题：

- **comparetup_mk()** 重新定义语义和 ownership：比较哪些 depths，以及 heap
  或 btree variant 如何拥有 datum extraction、unique/NULL 和 TID ordering。
- comment 4 重新定义执行时机：何时选择具体 comparator path，避免 mode
  selection 留在最内层 comparison loop。

因此两者是互补而不是互相替代。depth-range comparator 提供了自然的
dispatch boundary，因为每次递归已经知道 start_depth、max_depth 和当前
partition 的属性；但如果将 **comparetup_mk()** 实现成一个包含所有 runtime
branches 的大型通用函数，再在每次 comparison 中调用，它会保留甚至加重
John 在 comment 4 中指出的问题。

建议采用两层结构：

1. recursion/partition 层根据 depth range 和 partition properties 选择一次
   mode-specific comparison path。
2. tuple-specific comparator 层实现该 mode 下固定的 datum extraction 和
   ordering semantics，包括 btree 的隐式 TID depth。

这也意味着 comparator abstraction 的整洁性不能以牺牲热路径为代价。
接口可以统一语义，但执行代码应允许少量、经过测量证明有价值的 specialization。

### 验证方法

重构前后应针对固定数据分布测量：

- instructions、cycles 和 IPC，确认 comparison 内的重复 dispatch 已减少。
- branch instructions 和 branch misses，区分“少执行 branch”与“只是预测正确”。
- I-cache load/miss 指标，必要时结合 perf annotate 检查热代码布局。
- 各 comparator mode 的实际进入次数，避免优化了很少执行的分支。
- 2、3、4、5 keys 以及 shortcut、abbreviation、NULL、heap/btree 各场景的时间。

只有 branch misses 很低并不能否定该问题：一个稳定可预测但每次 comparison
都执行的 branch，仍然消耗 instructions 和前端带宽。

### 当前实现和验证结果

当前原型只对有 perf 证据的 heap、depth > 0 整数比较做有限 specialization，
没有展开 abbreviation、NULL、reverse、btree 等条件的组合：

- 递归进入 partition 时，`mkqs_select_partition_compare_kind()` 根据 tuple type、
  depth 和 SortSupport comparator 选择 generic、signed、unsigned 或 int32。
- `mkqs_partition()` 每个 partition 只进行一次 switch，之后进入固定的三向
  partition loop。
- 三个整数 loop 直接完成 heap datum extraction、NULL ordering 和整数比较，
  不再在每次比较中经过 `mkqs_apply_sort_comparator()` 的 comparator 类型链。
- depth 0、text/generic comparator 和 btree 继续使用完整的
  `comparetup_mk()` 路径；没有在热循环中使用函数指针。

这样做刻意限制了代码变体数量。它实现了 John 所说的 recursion/partition
boundary dispatch，但没有把所有固定属性都组合成专用函数，避免 specialization
爆炸反过来扩大 I-cache 工作集。

固定 100k-row、5-key duplicate-heavy heap case 的 8 轮 perf stat 中位数：

| case | metric | before | after | change |
| --- | ---: | ---: | ---: | ---: |
| int | execution ms | 37.99 | 36.57 | -3.75% |
| int | instructions | 268.83M | 254.17M | -5.45% |
| int | branches | 50.63M | 45.62M | -9.89% |
| int | cycles | 82.48M | 79.00M | -4.22% |
| text control | execution ms | 124.34 | 124.66 | +0.26% |
| text control | cycles | 256.04M | 255.88M | -0.06% |

完整 `mksort_test.sh` 的 `mk_enabled=yes only` 逐 case 中位数结果为：

- 最差 case median：-0.69%，满足 1% regression 限制。
- 全部 case median 平均收益：从 +22.96% 提升到 +23.81%。
- 全部 case median 的中位数：从 +16.51% 提升到 +17.31%。
- John Naylor candidate 的 median gain：+46.00%。

最低收益的 timestamptz/random/50/8 case 另做了三组复跑。原型 9 个有效
样本的平均 gain 为 +0.54%，基准为 +0.52%；原型有一个 -1.85% 单轮尾值，
但其余 8 个样本均不低于 -0.51%，没有稳定执行层回退证据。完整结果保存在
`/home/wy/mksort/new_result_comment4.txt`。第二次完整矩阵保存在
`new_result_comment4_repeat.txt`，其 423 个 `mk_enabled=yes` 有效样本精确最差
为 -0.975%，逐 case 最差中位数为 -0.720%，平均收益为 +24.41%；第一份中
-1.72% 的单样本尾值没有复现。perf 原始结果保存在
`/home/wy/mksort/comment4-perf-prototype1.csv` 和对应的 `.data` 文件中。

## 未采用的 depth-aware comparator 方案实施顺序

1. 为当前 heap 和 non-unique btree 行为增加 focused correctness tests。
2. 定义 depth numbering、inclusive range 和 per-variant maximum depth。
3. 实现 heap depth-range comparator，暂时保持现有执行路径可切换。
4. 实现 non-unique btree comparator，并将 depth == nKeys 映射到 TID。
5. 将 partition、presort 和 fallback comparison 切换到新接口。
6. 删除 btree MkqsHandleDupFunc 路径和 seenNull。
7. 删除独立 MkqsGetDatumFunc abstraction。
8. 在 recursion boundary 选择 comparator mode，消除 inner comparison loop 中
   重复的 mode branches；只对有测量依据的模式使用小型 inline specialization。
9. 检查生成代码大小和 I-cache 指标，避免 specialization 组合爆炸。
10. 比较 standard sort 与 mksort 的 correctness、instructions、CPI 和时间。
11. 最后再决定是否以及如何支持 unique btree。

这套顺序记录的是隐式 TID depth 方案，不是当前实施计划。当前代码保留
**MkqsHandleDupFunc**，只删除了 **seenNull** 和不可达的 unique-check 分支。

## 必要测试

### Correctness

- heap：2、3、4、5 keys。
- btree：2、3、4、5 explicit keys，加隐式 TID。
- ASC/DESC 和 NULLS FIRST/LAST。
- abbreviated 和 non-abbreviated types。
- 所有显式键相同但 TID 不同。
- 前键大量重复、后键唯一。
- 多层 keys 都大量重复。
- presorted、reverse-sorted 和 random input。
- external sort 和 in-memory sort。

### Performance

- standard sort 路径不得因新接口产生变化。
- mksort 最坏情况 regression 仍不得超过 1%。
- 比较现有 accessor-specialized 实现与 depth-range 实现的 instructions、
  cycles、IPC、branch misses 和 cache misses。
- single-depth hot comparison 不得因 dynamic callback 或 range loop 明显变慢。

## 结论

John 的建议不是因为某个 helper 只有一个调用点而简单删除函数，而是要求
重新划分 abstraction boundary：

- generic mksort 拥有 partition 和 depth recursion。
- tuple-specific comparator 拥有 datum extraction 和完整 ordering semantics。
- btree 自己拥有 explicit keys、unique/NULL 规则和 implicit TID。

如果未来重新采用完整的 depth-aware 方案，**mkqs_handle_dup_index_btree()** 可被
comparator 取代，TID 成为普通的隐式最后 depth。mkqs_compare_datum 系列、
独立 getDatum callback 和 generic duplicate handling 也应相应合并或删除。
