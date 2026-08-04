# John Naylor 最大收益场景硬件计数实验

## 目的

John Naylor 建议对最大收益或最大回退场景进一步解释硬件层变化：

> For the biggest benefit/regression cases, it'd be good to know what
> changed at the hardware level. # comparisons? # swaps? # cache
> misses? # branch mispredicts?

当前结果中没有需要单独调查的稳定大幅 mksort regression，因此本实验只
选择一个最大稳定收益场景，测量：

- key comparisons；
- SortTuple swaps；
- cycles；
- instructions；
- branches；
- branch misses；
- cache misses。

实验的目标不是全面刻画所有数据分布，而是回答这个最大收益究竟来自减少
算法工作量、改善 branch/cache 行为，还是两者兼有。

## 测试场景

场景取自 `new_result_3.txt` 中收益最大的稳定区域：

```text
rows=100000
type=text
distribution=correlated
reps=10000
sort keys=8
```

固定随机种子后，每列使用与 `mksort_test.sh` 相同的表达式生成：

```sql
(((i / 10000) + random())::int::text)
```

测试查询是：

```sql
SELECT *
FROM mkqs_john_hw
ORDER BY 1,2,3,4,5,6,7,8;
```

实际生成的数据为：

```text
rows:          100000
distinct c1:  12
distinct rows across all eight keys: 2552
```

这个分布包含大量相同的 leading keys，并且完整八列 tuple 也有较高重复度，
是 mksort 按 depth 分组、避免反复比较后续列的典型优势场景。

## 测试方法

完整脚本为：

```text
/home/wy/postgres/mksort/mksort_john_hardware_test.sh
```

默认执行完整实验：

```bash
cd /home/wy/postgres
./mksort/mksort_john_hardware_test.sh
```

也可以分别执行两个阶段：

```bash
PHASE=profile ./mksort/mksort_john_hardware_test.sh
PHASE=perf ./mksort/mksort_john_hardware_test.sh
```

### 软件计数阶段

脚本临时对 standard qsort 和 mksort 增加 comparison/swap 计数。计数定义为：

- comparison：实际执行的一次 sort-key 比较；abbreviated datum 比较和发生
  collision 后的 authoritative full comparison 分别计数；
- swap：实际交换两个不同位置的 SortTuple；vector swap 按交换的 SortTuple
  数量计数，而不是只计一次函数调用；
- mksort 的 full presort check 也包含在总 comparison 数中。

standard 路径的计数加在 `comparetup_heap()` 和
`comparetup_heap_tiebreak()` 的每次 key comparison 上；mksort 的计数加在
模板生成的每-depth comparison 和 abbreviation fallback 上。

计数器会影响指令流和代码布局，所以这个 build 只用来取得算法次数，不用
来判断硬件性能。脚本在计数完成后恢复所有临时源码，并执行 clean release
build。

### perf 阶段

硬件计数在没有任何插桩的 clean release build 上采集。构建参数包括：

```text
-O3 -g -fno-omit-frame-pointer
```

测量控制为：

- backend 固定在 CPU 2；
- CPU governor 为 performance；
- CPU 频率固定为 2 GHz；
- boost 关闭；
- autovacuum 关闭；
- `work_mem=1GB`；
- parallel query 关闭；
- 2 轮预热；
- 5 轮正式 AB/BA 配对测试；
- perf 通过 control FIFO，只在 EXPLAIN ANALYZE 查询执行期间启用；
- 五个事件均为 100% time running，没有发生 multiplexing。

perf 事件为：

```text
cycles,instructions,branches,branch-misses,cache-misses
```

perf 覆盖完整 backend 查询，而不是只包围某个排序函数。因此其中包含相同的
Seq Scan 和 executor 开销；off/on 使用相同数据和查询，这部分是共同背景。

测试时确认实际路径：

```text
off: Sort Method: quicksort
on:  Sort Method: multi-key quick sort
```

## 软件工作量结果

| 指标 | standard sort | mksort | mksort 相对变化 |
|---|---:|---:|---:|
| key comparisons | 4,203,099 | 1,420,099 | -66.21% |
| SortTuple swaps | 296,987 | 851,099 | +186.58% |

mksort 只执行了 standard sort 约 33.8% 的 key comparisons，但执行了约
2.87 倍的 swaps。

这符合算法预期：standard qsort 每次比较两个 tuple 时，会连续比较后续 key，
直到找到差异；相同 leading-key 前缀会导致同一批后续 key 在排序过程中被
反复访问。mksort 在某一 depth 完成 partition 后，只对 equal group 进入下一
depth，因此大幅减少后续列比较，但每一层 partition 都可能重新移动 tuple，
所以 swap 数明显增加。

## 运行时间和硬件计数结果

五轮正式配对结果：

| run | standard | mksort | `standard / mksort - 1` |
|---:|---:|---:|---:|
| 1 | 179.839 ms | 74.815 ms | +140.38% |
| 2 | 177.705 ms | 74.627 ms | +138.12% |
| 3 | 181.600 ms | 74.605 ms | +143.42% |
| 4 | 181.901 ms | 75.268 ms | +141.67% |
| 5 | 178.908 ms | 75.673 ms | +136.42% |
| median | 179.839 ms | 74.815 ms | +140.38% |

这里 `+140.38%` 表示 standard 用时是 mksort 的约 2.40 倍，或者换一种
表示方式，mksort 的运行时间降低约 58.4%。

硬件事件使用五轮中位数。最后一列按 `1 - mksort / standard` 计算，正值
表示 mksort 减少了该事件：

| 事件 | standard 中位数 | mksort 中位数 | 减少比例 |
|---|---:|---:|---:|
| cycles | 362,031,287 | 151,188,897 | 58.24% |
| instructions | 1,692,297,246 | 600,005,855 | 64.55% |
| branches | 372,491,882 | 124,182,844 | 66.66% |
| branch misses | 1,061,750 | 560,021 | 47.26% |
| cache misses | 276,567 | 259,950 | 6.01% |

派生指标：

| 指标 | standard | mksort |
|---|---:|---:|
| IPC | 4.6745 | 3.9686 |
| branch miss rate | 0.2850% | 0.4510% |

## 分析

### 1. 收益的主因是比较次数下降

key comparisons 减少 66.21%，与 branches 减少 66.66% 和 instructions
减少 64.55% 高度一致。说明最大收益主要来自 mksort 避免了大量重复的
later-key comparisons，而不是同样数量的比较执行得更快。

cycles 减少 58.24%，与运行时间降低约 58.4% 几乎完全一致，硬件计数和
wall-clock 结果相互验证。

### 2. 更多 swaps 没有抵消比较收益

mksort 的 swaps 增加到 standard 的 2.87 倍，但总 instructions 仍减少
64.55%。SortTuple swap 是固定大小的数据移动；text key comparison 则可能
涉及 tuple attribute extraction、abbreviation fallback 和 collation comparator。
在这个八列、高重复度场景中，省掉一次 key comparison 的收益远大于增加
一次 SortTuple swap 的成本。

### 3. branch predictor 不是收益来源

branch misses 的绝对数量减少 47.26%，但 branch miss rate 从 0.2850% 上升
到 0.4510%。这是因为总 branches 下降得更快，而不是 mksort 的分支预测比
standard 更好。

因此不能把收益描述为 branch prediction 改善。更准确的描述是：mksort
执行的 branches 少了约三分之二，即使剩余分支的 miss rate 稍高，总 branch
misses 仍明显下降。

### 4. cache misses 基本没有变化

cache misses 只减少约 6%，远小于 cycles、instructions 和 branches 的下降。
这说明 cache miss reduction 不是本场景的主要收益来源。

同时，mksort 在 swaps 增加 186.58% 的情况下没有出现 cache misses 大幅增加，
说明额外 partition 数据移动没有造成明显的外层 cache miss 压力。需要注意，
这里使用的是 perf 通用 `cache-misses` 事件，并且覆盖完整查询，不能进一步区分
L1、LLC 或 instruction-cache；本实验按照 review comment 的范围没有增加这些
事件。

### 5. mksort 的单周期效率反而略低

mksort IPC 从 4.6745 降到 3.9686，下降约 15%。结合更高的 branch miss rate
和更多 swaps，可以认为 mksort 每单位工作并不比 standard 更高效；它的优势
来自总工作量大幅减少。

这也是本实验最重要的硬件层结论：

```text
mksort wins by doing much less comparison work,
not by making the same work run faster.
```

## 结论

在 `text / 100000 rows / 8 cols / correlated / reps=10000` 最大收益场景中：

1. mksort 将 key comparisons 减少 66.21%；
2. 代价是 SortTuple swaps 增加 186.58%；
3. instructions、branches 和 cycles 分别减少 64.55%、66.66% 和 58.24%；
4. branch miss rate 和 IPC 都略差，所以收益并非来自更好的 branch prediction
   或单周期执行效率；
5. cache misses 只减少 6.01%，不是主要因素；
6. 最终 mksort 用时降低约 58.4%，standard 用时约为 mksort 的 2.40 倍。

因此，这个最大收益可以清楚地解释为：mksort 按 key depth partition equal
groups，避免 standard tuple comparator 反复访问和比较后续 text keys。减少的
比较工作远大于额外 swaps 的成本。

## 结果和恢复状态

完整原始输出保存在：

```text
/home/wy/mksort/john-hardware-artifacts/profile/
/home/wy/mksort/john-hardware-artifacts/perf/
```

脚本执行完成后会：

- 反向应用临时 profiling patch；
- 执行 clean release build 并重新安装；
- 恢复 `kernel.perf_event_paranoid`；
- 以正常配置重启 PostgreSQL；
- 恢复 autovacuum。

本次实验完成后已确认源码没有遗留插桩，PostgreSQL 正常运行且 autovacuum
为 `on`。
