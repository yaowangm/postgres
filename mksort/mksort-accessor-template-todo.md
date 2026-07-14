# TODO: 用模板统一 mksort accessor 专用路径

## 背景

此前为了解决 datum accessor 位于比较热路径中的性能问题，我们为不同 tuple 场景提供了专用访问方式，例如 heap 和 index btree。这样可以避免每次比较都通过动态函数指针访问 datum，但容易让算法代码逐渐分成多套实现，增加维护和行为漂移风险。

当前需要评估一种折中方案：使用 C template/macro 保留一份 mksort 算法源码，在编译期为不同 tuple 类型生成专用函数。

这个方案需要明确区分两种“同一条代码路径”：

- 源码和算法层面：heap/index 共用同一份模板，可以做到。
- 最终机器码层面：仍会生成 heap/index 两条专用路径，无法也不应该强行合并。

如果只生成一条通用机器码路径，那么运行时仍然必须通过 tuple-type 分支或动态函数指针选择 accessor，这正是此前确认过的热路径开销。

## 目标

1. 保留一份 multi-key quicksort 算法实现。
2. 在排序入口只进行一次 tuple 类型分派。
3. 在 comparator、partition 和递归热路径中消除动态 accessor 函数指针。
4. 允许编译器内联 heap/index 各自的 datum accessor。
5. 保持现有排序语义、NULL 顺序、排序方向、collation、abbreviation 和 duplicate handling 行为。
6. 不修改 planner、统计信息或 mksort 的适用性判断。

## 非目标

- 不要求 heap 和 index btree 共用同一份机器码。
- 不为了减少代码尺寸而重新引入每次比较的动态分派。
- 不在没有性能数据的情况下同时重写 pivot、partition、presort 或递归算法。
- 在 index btree 支持重新进入范围前，不改变其现有行为。

## 建议设计

### 1. 把算法主体整理成模板

将当前 mksort 的公共算法主体放入类似 `mk_qsort_tuple_template.h` 的模板文件。模板只暴露少量 policy macro，例如：

```c
#define MKQS_NAME              mk_qsort_tuple_heap
#define MKQS_GET_DATUM         mkqs_get_datum_heap
#define MKQS_CHECK_NULL        mkqs_check_null_heap
#define MKQS_HANDLE_DUP        mkqs_handle_dup_heap
#include "mk_qsort_tuple_template.h"
```

index btree 可以用另一组 policy 重新实例化：

```c
#define MKQS_NAME              mk_qsort_tuple_index_btree
#define MKQS_GET_DATUM         mkqs_get_datum_index_btree
#define MKQS_CHECK_NULL        mkqs_check_null_index_btree
#define MKQS_HANDLE_DUP        mkqs_handle_dup_index_btree
#include "mk_qsort_tuple_template.h"
```

模板展开后生成两份专用函数，但 pivot、partition、presort 和递归逻辑只维护一份模板源码。

### 2. accessor 使用 inline helper，不把复杂逻辑写进宏

macro 只负责选择 helper。具体 datum 提取逻辑应放在类型明确的 `static inline` 或 `pg_attribute_always_inline` 函数中。

heap helper 可以直接处理：

- `MinimalTuple` 到 `HeapTupleData` 的转换
- `TupleDesc`
- 当前 `SortSupport` 对应的 `AttrNumber`
- `heap_getattr()`

index btree helper 保留自己的 tuple 布局和 accessor。这样既能内联，又不会把复杂代码塞入宏，避免类型错误和调试困难。

### 3. 只在排序入口分派一次

公共入口根据 tuple 类型选择生成后的专用函数：

```text
mk_qsort_tuple()
  -> heap tuple:        mk_qsort_tuple_heap()
  -> index btree tuple: mk_qsort_tuple_index_btree()
```

这个分支位于 tuple group 外部。进入专用函数后，递归调用必须继续调用同一实例，不能回到通用入口，否则 tuple-type 判断会重新进入热路径。

### 4. duplicate handling 作为独立 policy

index btree 的 duplicate handling 不只是 datum accessor 差异，可能涉及唯一性检查、NULL 语义、TID tiebreak 或重复 tuple 处理。

因此不能假设 heap 和 index 只需要不同的 `GET_DATUM`。模板至少需要把 duplicate handling 作为显式 policy；如果它导致大量条件宏，应重新评估模板边界，而不是继续增加宏复杂度。

### 5. “只剩最后一个键”的 standard qsort 也可使用模板

当 `depth == nKeys - 1` 且不需要特殊 duplicate handling 时，multi-key sort 已退化为 single-key sort。可以用 `sort_template.h` 生成 accessor-specialized 的最后键 qsort：

- `qsort_mkqs_last_key_heap`
- `qsort_mkqs_last_key_index_btree`

对应 comparator 在进入排序前保存当前 `SortSupport`、attribute number 和 tuple descriptor。热循环只访问最后一个键，不再使用固定从第二键开始的 `comparetup_tiebreak`，也不需要运行时 accessor 指针。

这部分应作为独立优化验证，不能与整个 mksort 模板化一次性提交。

## 实施边界

建议按以下顺序进行，且每一步都保持可单独回退：

1. 先为当前已启用的 heap 路径建立模板实例，确认生成代码与现有行为一致。
2. 保留现有通用实现用于对照，使用相同输入进行结果校验和 perf 对比。
3. 确认模板化本身没有 regression 后，再决定是否删除旧的通用 accessor 路径。
4. 只有在重新考虑 index btree 支持时，才增加 index 模板实例。
5. 最后单独评估“只剩最后一个键时使用专用 standard qsort”。

## 风险

- 模板生成多份函数，会增加二进制尺寸和 instruction-cache 压力。
- helper、递归函数和静态符号都需要实例化前缀，否则可能发生符号冲突或意外调用通用版本。
- 宏 policy 过多会降低可读性，掩盖 heap/index 的真实语义差异。
- index duplicate handling 如果被错误抽象，可能产生唯一性或排序稳定性问题。
- 编译器是否真正内联 accessor 需要通过反汇编或 perf 验证，不能只根据源码推断。
- 模板化可能改善 accessor 成本，但不一定改善 branch miss、cache miss 或 pivot/partition 成本。

## 验证要求

### 正确性

- PostgreSQL regression tests 全部通过。
- 覆盖 2、3、4、5 键排序。
- 覆盖 ASC/DESC、NULLS FIRST/LAST、NULL 和非 NULL 混合数据。
- 覆盖 abbreviated key 启用和取消的情况。
- 如果启用 index btree，必须覆盖 unique、NULLS NOT DISTINCT 和重复 TID 相关路径。
- 对相同数据比较 standard sort、旧 mksort 和模板 mksort 的完整排序结果。

### 性能

- 使用同一 CPU 绑定、关闭 autovacuum，并保持与 `mksort_test.sh` 相同的测量方法。
- 单独统计 heap/index 和不同键数，不能只看总平均值。
- 使用 perf 或轻量计数确认动态 accessor 调用和 tuple-type 热路径分支已经消失。
- 比较 cycles、instructions、CPI、branch misses 和 cache misses。
- 最坏情况 regression 不超过 2%，忽略已经确认的单次 tailer。
- 同时报告全矩阵平均收益和 `mk_enabled=yes` 条件平均，避免两种指标混淆。

## 决策标准

只有同时满足以下条件，才值得用模板替换当前实现：

1. 算法行为和排序结果完全不变。
2. accessor 分派从 comparator 热路径移动到排序入口。
3. perf 或反汇编能证明专用 accessor 已内联。
4. 最坏情况 regression 保持在 2% 以内。
5. 平均收益有可重复的改善，而不是仅改变 `mkqsUsed` 分类。
6. 模板 policy 数量保持有限，代码仍可审查和调试。

## 当前状态

这是候选设计，尚未实施。下一步应先做 heap-only 的最小原型和汇编/perf 验证；任何执行代码修改都需要单独确认后再开始。
