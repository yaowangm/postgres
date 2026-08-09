# mksort 单键单深度 sanity check

## 背景和目标

John Naylor 提出了下面的 sanity check：

> If we actually only have one sort key, a multi-key sort with a single
> depth should ideally have no significant performance difference than
> standard sort. That seems like a good sanity check. Has this been tried?

正常代码要求 `nKeys > 1` 才允许进入 mksort，因此只有一个 sort key
时不能直接测试。这个实验临时允许 HeapTuple 的单键排序进入 mksort，
用来回答两个不同的问题：

1. 单深度 `mk_qsort_tuple()` 与 standard tuple quicksort 相比，是否有
   明显的固有开销？
2. 如果只是简单地放宽单键准入条件，现有顶层排序方法选择是否会带来
   其他干扰？

本文中的性能值按下面的公式计算：

```text
gain = standard_off_time / mksort_on_time - 1
```

正值表示 mksort 更快，负值表示 mksort 更慢。

## 实验方法

### 保证使用 HeapTuple

只选择一个输出列时，PostgreSQL 会使用 DatumTuple 排序，而当前 mksort
不支持 DatumTuple。测试表因此使用两个输出列：

```sql
CREATE UNLOGGED TABLE mkqs_single_key
  (c1 data_type NOT NULL, payload integer NOT NULL);

SELECT * FROM mkqs_single_key ORDER BY c1;
```

这里只有 `c1` 是 sort key，但结果中同时包含 `payload`，所以执行的是
HeapTuple 排序。

### 临时代码改动

第一阶段只把 mksort 的准入条件从：

```c
state->base.nKeys > 1
```

临时改成：

```c
state->base.nKeys > 0
```

第二阶段为了直接比较两种 quicksort，又临时使单键场景在 mksort 和
standard 两个分支中都不进入 radix sort：

- off 根据 standard dispatch 使用 `qsort_tuple()` 或 `qsort_ssup()`；
- on 使用单深度 `mk_qsort_tuple()`。

这些改动只用于实验，测试完成后已经全部恢复，没有进入正式代码。

### 测量控制

- 100,000 行；
- `work_mem = 1GB`，保证内存排序；
- 禁止并行查询；
- 关闭 autovacuum；
- backend 固定到同一个 CPU；
- 每个场景预热 4 轮；
- 测量 15 组配对结果；
- 奇偶轮交替使用 off/on 和 on/off 顺序；
- 每个场景只生成一次数据，on/off 使用完全相同的数据；
- 通过 EXPLAIN 的 Sort Method 检查 on 路径确实执行了
  `multi-key quick sort`。

测试使用与现有性能测试一致的 `-O3` 构建。

当前保留的明细结果位于远程测试目录：

- `/home/wy/mksort/single_key_text_result.txt`
- `/home/wy/mksort/single_key_hash_result.txt`
- `/home/wy/mksort/single_key_int_result.txt`
- `/home/wy/mksort/single_key_bytea_mod_result.txt`

`single_key_hash_result.txt` 是第二阶段禁用单键 radix 后的最终复测结果；
第一阶段 MD5 bytea 的文件曾被复测覆盖，其汇总值记录在本文下一节。按模
运算生成的第一阶段 bytea 明细仍保存在
`single_key_bytea_mod_result.txt`。

后续针对 text 中等重复度回退的复测和硬件计数结果位于：

- `/home/wy/mksort/singledepth-threshold16_repeat`
- `/home/wy/mksort/singledepth-recursive_presort`
- `/home/wy/mksort/singledepth-perf-original`
- `/home/wy/mksort/singledepth-perf-recursive_presort`

## Standard quicksort 的实际路径

`qsort_tuple()` 和 `qsort_ssup()` 都由 `sort_template.h` 生成，使用相同的
pivot、presort check、partition、insertion sort 和尾递归算法。区别在于比较
接口：

- `qsort_tuple()` 接受运行时 tuple-level comparator 和
  `Tuplesortstate`，能够通过 `comparetup_heap()` 及其 tiebreak 函数处理
  多列、完整 datum 和不同 tuple variant；
- `qsort_ssup()` 只接受一个 `SortSupport`，直接比较 `SortTuple` 中缓存的
  `datum1/isnull1`，省去了 tuple-level comparator 回调，但
  `ApplySortComparator()` 最终仍会调用 `ssup->comparator`。

HeapTuple tuplesort 只在下面两个条件同时满足时设置 `onlyKey`：

```c
nkeys == 1 && !base->sortKeys->abbrev_converter
```

普通内存 quicksort 随后根据 `onlyKey` 选择路径：

```text
onlyKey != NULL: qsort_ssup()
onlyKey == NULL: qsort_tuple()
```

因此，本实验中没有启用 abbreviation 的单键 text HeapTuple，其 standard
路径可以确定为：

```text
qsort_ssup() -> ApplySortComparator() -> text SortSupport comparator
```

这不是“所有 text sort 都使用 `qsort_ssup()`”的通用结论。多键 text、启用
abbreviation 的 text、其他 tuple variant，以及 external merge 或 top-N heap
等阶段可以使用不同路径。

## 第一阶段：只放宽单键准入

text 的 standard 路径本来就是 quicksort；在本实验的单键且无 abbreviation
条件下，更精确地说是专用的 `qsort_ssup()`。因此可以直接用它观察单深度
mksort 相对于 standard 单键 quicksort 的开销。

| 场景 | off 中位数 | on 中位数 | gain 中位数 |
|---|---:|---:|---:|
| text，伪随机唯一值 | 151.967 ms | 152.792 ms | -0.59% |
| text，2,000 distinct，每值约 50 行 | 82.176 ms | 83.106 ms | -1.18% |
| text，10 distinct，每值约 10,000 行 | 23.724 ms | 23.969 ms | -0.95% |

其中 2,000 distinct 场景的回退很稳定：去掉一个最好值和一个最差值后，
gain 范围仍为 `-1.37%` 到 `-0.75%`。因此不能把 `-1.18%` 完全解释为
偶然抖动。它略微超过当前项目使用的 1% 回退限制，应作为一个后续的
focused benchmark 保留。

### bytea 的虚假大回退

只放宽准入后，MD5 随机 bytea 得到如下结果：

| 场景 | off 中位数 | on 中位数 | gain 中位数 |
|---|---:|---:|---:|
| bytea，MD5 唯一值 | 22.592 ms | 41.696 ms | -45.89% |
| bytea，2,000 distinct | 22.395 ms | 34.328 ms | -34.66% |

使用按模运算生成的 bytea 也得到近似结果，因此可以排除特定输入排列造成
的假象。但是，这并不是 `qsort_tuple()` 与 `mk_qsort_tuple()` 的比较。

bytea abbreviation 把 leading datum 的 comparator 设置为
`ssup_datum_unsigned_cmp`。standard 分支看到这个 comparator 后会选择
radix sort；mksort 分支的 radix 条件则明确要求
`abbrev_converter == NULL`，所以 on 路径使用 mk quicksort。这里实际比较
的是：

```text
off: radix sort
on:  mk_qsort_tuple
```

EXPLAIN 把 standard radix 路径显示为 `quicksort`，仅根据 Sort Method
无法识别这个区别。该路径通过 `tuplesort_sort_memtuples()` 的 dispatch
条件和第二阶段禁用单键 radix 后的对照结果确认。

这个结果不能用于否定单深度 mksort，但说明如果将来真的支持单键 mksort，
必须保持 standard radix 的优先级，不能让 mksort 准入提前截获 bytea
abbreviated-key radix 路径。

## 第二阶段：对等比较 quicksort

第二阶段让单键场景的 off 和 on 都绕过 radix。结果如下：

| 场景 | standard 中位数 | mksort 中位数 | gain 中位数 |
|---|---:|---:|---:|
| text，伪随机唯一值 | 151.967 ms | 152.792 ms | -0.59% |
| text，MD5 随机唯一值 | 152.634 ms | 152.978 ms | +0.39% |
| text，2,000 distinct | 82.176 ms | 83.106 ms | -1.18% |
| text，10 distinct | 23.724 ms | 23.969 ms | -0.95% |
| bytea，MD5 唯一值 | 44.165 ms | 42.072 ms | +5.70% |
| bytea，2,000 distinct | 36.655 ms | 33.952 ms | +8.17% |
| bigint，唯一值 | 31.677 ms | 28.629 ms | +11.42% |
| bigint，2,000 distinct | 24.398 ms | 22.487 ms | +8.88% |
| int4，唯一值 | 30.397 ms | 27.912 ms | +9.64% |

### 结果解释

text 的比较成本主要在 collation/comparator 内部。两种排序实现相对于这个
成本的额外控制流很小，因此随机唯一值场景基本持平。具有重复值时，当前
mksort 的递归、partition setup 和小数组处理与 standard qsort 不完全相同，
其中 2,000 distinct、每个值约 50 行的中等重复度场景出现约 1.18% 的稳定
回退。这里的 `-1.18%` 不是唯一值或 fully distinct 场景；伪随机唯一值的
中位回退只有 `-0.59%`。

后续计数确认，回退由两个部分组成。第一部分来自递归 presort 策略不同：
`qsort_ssup()` 在每个递归子区间执行 presort check，而当前 mksort 只在最外层
执行一次 full presort check，深度 0 的递归子区间不再检查。原始计数如下：

| 路径 | 比较次数 | 交换次数 |
|---|---:|---:|
| standard `qsort_ssup()` | 1,095,511 | 330,638 |
| 单深度 mksort | 1,102,354 | 331,438 |
| mksort 增量 | +0.625% | +0.242% |

临时让单深度 mksort 在每个递归子区间执行与 `sort_template.h` 相同的
presort check 后，两边都变为 1,095,511 次比较和 330,638 次交换，完全
一致；时间中位回退则从约 `-1.16%` 降到约 `-0.67%`。因此缺少递归
presort check 可以解释约半个百分点，但不是全部差距。

剩余差距是通用 mksort 框架相对于单键专用 `qsort_ssup()` 的固定执行开销，
包括递归入口的 compare/partition 选择、partition bounds 状态传递、
lesser/equal/greater 处理、两侧真实递归，以及单键情况下实际不需要的 depth、
NULL 传播和 duplicate-handler 判断。原始实现的硬件计数中，mksort 相对
standard 多执行约 1.50% instructions 和 0.36% branches，而 branch misses
低约 0.60%，cache misses 只高约 0.39%。这说明剩余问题主要是额外指令和
控制流，不是 cache miss 或 branch prediction 失效。

把 `MKQS_INSERTION_SORT_THRESHOLD` 从 16 临时改成 standard qsort 使用的 7
没有改善该场景，回退反而扩大，因此 insertion-sort threshold 不是原因。

bigint 和 int4 的单深度 mksort 明显更快。mksort 在递归入口选择类型版本后，
partition 内可以直接内联原生整数比较；`qsort_ssup()` 虽然避免了 tuple-level
compare callback，`ApplySortComparator()` 最终仍通过 SortSupport comparator
函数指针完成类型比较。当前结果实测覆盖 `int64` 和 `int32`，没有单独隔离
测试 `uint64`。`uint64` 使用结构相同的 typed fastpath，预计会有类似收益，
但不能把 `+8%` 到 `+11%` 声称为已经测得的 uint64 结果。

还必须区分这个 quicksort-to-quicksort sanity check 与正常顶层 dispatch。
在 100,000 行的正常 standard sort 中，int64、uint64 和 int32 comparator 通常
会优先进入 radix sort；这里的整数收益是在实验中临时禁止单键 radix 后测得，
不能直接解释为 mksort 相对于正常生产分派的收益。

bytea 在双方都使用 quicksort 后也明显更快。mksort 的类型/tuple 路径在递归
入口确定，partition 可以直接比较 cached abbreviated datum，减少 standard
`qsort_tuple -> comparetup_heap -> SortSupport comparator` 路径中的间接调用和
通用 tuple-level 比较开销。

全相等输入没有列入表格。`mk_qsort_tuple()` 的 full presort check 会直接返回，
而且返回发生在设置 `mkqsUsed` 之前，所以 EXPLAIN 显示为 `quicksort`。该场景
不会进入 mksort partition，不能用于评估单深度递归实现的成本。

## 结论

如果 John 的 sanity check 指的是 mksort quicksort 与 standard quicksort 的
对等比较，那么当前实现总体通过：

- generic text 唯一值场景基本持平；
- 实测的 int64/int32 和 bytea quicksort 场景中 mksort 更快；
- 没有发现普遍性的单深度固有开销；
- 但 text 的 2,000 distinct、每值约 50 行的中等重复度场景存在约 1.18%
  的稳定回退，略微超过项目的 1% 标准，不能声称所有分布都严格通过限制；
- 该 text 回退约有半个百分点来自 mksort 缺少递归子区间 presort check，
  其余主要来自通用 mksort 框架相对于专用 `qsort_ssup()` 的额外指令；
- 不能把 text 个例推广成“所有 generic 类型都会慢”：text 唯一值接近持平，
  bytea quicksort 则有明确收益，generic 类型的结果取决于 comparator 成本、
  重复度、presort 行为和框架开销。

因此，最精确的类型结论是：int64/int32 typed fastpath 已实测比
`qsort_ssup()` 快约 9% 到 11%，uint64 只有代码结构上的同类预期、尚无独立
实测；generic comparator 类型可能略快、持平或略慢，不能仅按“是否为整数”
划出统一的性能边界。

如果把 sanity check 理解为“简单允许单键进入当前完整 mksort dispatch”，则
bytea 会因为 radix 路径被 mksort 截获而出现巨大回退。这属于顶层算法选择问题，
不是 `mk_qsort_tuple()` 核心性能问题。未来若扩大 mksort 适用范围，应该先判断
并保留更有利的 radix 路径。

实验结束后已恢复临时源码、重新构建并安装正常二进制、重启服务器，并确认：

- 远程 PostgreSQL checkout 没有遗留实验修改；
- autovacuum 已恢复为 `on`。
