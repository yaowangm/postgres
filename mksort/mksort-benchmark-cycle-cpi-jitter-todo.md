# TODO: 规避短查询中的 cycle/CPI 波动

## 状态和基准

从现在起，完整性能矩阵使用以下结果作为基准：

```text
/home/wy/mksort/new_result_5.txt
```

该结果由 `mksort_pg20` 分支的提交
`b7adc65cbf953d85d7bb7abfca2e7ce3d0ba7736` 生成。不要覆盖这个文件；
后续结果应写入新的 `new_result_N.txt` 并与它比较。

`new_result_5.txt` 中：

- text overall 最差有效结果为 `-0.01`；
- text `mk_enabled=yes only` 最差结果为 `+0.05`；
- bigint overall 最差有效结果为 `-0.06`；
- bigint `mk_enabled=yes only` 最差结果为 `-0.01`。

因此，之前 text 随列数增加而放大的稳定 presort 回退已不再出现。当前待解决的
benchmark 问题是 bigint `mk_enabled=no` 中的短查询计时波动，而不是 text
presort 性能问题。

## bigint 异常场景

`-0.06` 来自以下 case：

```text
nrows=100000
type=bigint
distribution=random
reps=10
cols=8
mk_enabled=no
raw gains=-0.03,-0.06,+0.03,+0.03,-0.10
```

当前汇总方法去掉一个最大值和一个最小值，将其余三次分别作为有效结果。因此
`-0.06` 被保留并成为 bigint overall 的全局 minimum。该 minimum 是单次有效
sample，不是 40 次查询的聚合差异。

## 已确认的事实

### 1. 不是 mksort presort 回退

bigint 使用 typed/radix 路径，不执行 generic/text 路径的
`mkqs_full_order_presorted()`。因此，两份 presort loop 的机器码差异不能解释这个
bigint case。

### 2. on/off 最终都使用 standard qsort

该数据的第一键约有 10,000 个 distinct。实测 radix tie group 大小为：

```text
min=1, median=10, max=23
groups with size >= 64: 0
```

所有 group 都小于 `MKQS_RADIX_TIEBREAK_THRESHOLD=64`。off 和 on 最终都调用
standard qsort。on 路径只多执行 `use_mksort_tiebreak && num_elements >= 64` 的
条件检查，实际不会调用 `mk_qsort_tuple()`。

### 3. 没有 6% 的固定执行层开销

在 CPU 2 固定为 2 GHz、关闭 boost、NMI watchdog 和 autovacuum 后，对相同 case
执行 10 组 AB/BA，每种模式累计 400 次查询。perf 聚合结果为：

```text
instructions: on/off = +0.0018%
branches:     on/off = +0.0017%
cycles:       on/off = -0.1851%
```

这排除了 on 路径多执行约 6% 工作的解释。额外条件判断的实际成本约为万分之几。

### 4. 波动来自相同指令流的 cycles/CPI 变化

单查询 perf 中，instructions 的变异系数只有约 `0.03%`，cycles 的变异系数约为
`1.2%`，配对 cycles 差异范围达到 `-2.05%` 到 `+3.90%`。

两次测试还分别观察到约 `38.2 ms` 的异常轮次，而正常值约为 `30.5 ms`。异常轮次：

- instructions 没有相应增加；
- context switches 没有相应增加；
- page faults 没有相应增加；
- 通用 cache-miss 计数没有显示稳定相关性；
- 异常可以落在 off 或 on 上。

因此当前确认的直接原因是短查询中偶发的 cycle/CPI stall 被单次配对增益放大，并被
保留三条有效 sample 的汇总方式记录为 regression，而不是 on/off 代码工作量不同。

## 尚未确认的底层来源

目前不能把 stall 确定归因于 cache、调度抢占、SMI 或某个 PostgreSQL 分支：

- 独占整个 L3 domain 的对照没有消除异常；
- `rtla hwnoise` 在 CPU 2 上连续采样 45 秒没有检测到 hardware/NMI noise；
- context-switch 和通用 cache-miss 计数不能解释异常轮次；
- 相同查询的 retired instructions 基本不变。

底层来源可能需要 AMD IBS、更多 PMU stall/TLB 事件、内核 tracing 或更长时间的
同步采样才能定位。在有直接计数证据前，不应将其表述为 cache 或 SMI 问题。

## 后续 TODO

1. 建立 A/A 控制：同一 GUC、同一查询、同一 backend，验证相同的有效值规则会产生
   多大的假 regression。
2. 同时记录每条查询的 wall time、task-clock、cycles、instructions、CPI、context
   switches 和主要 TLB/cache stall 事件，而不是只记录 `EXPLAIN` 时间。
