# mksort insertion sort 阈值实验

## 结论

保留：

```c
#define MKQS_INSERTION_SORT_THRESHOLD 16
```

`16` 最初没有经过系统调优，但本次实验表明，它位于两类相反输入之间的合理
平衡点：

- 对随机小分区，阈值继续增大会迅速引入二次方级别的比较和 tuple 搬运；
- 对已经有序或接近有序的小分区，较高阈值可以避免额外的 pivot 和 partition；
- `12` 对随机主矩阵略好，但明显伤害 John Naylor tied-first/unique-second
  场景；
- `20` 对 John 场景更好，但降低完整矩阵平均收益，并把最差结果推到 1%
  回退边界；
- `18` 没有稳定胜过 `16`。

因此，当前没有证据支持把阈值改成 `QSORT_THRESHOLD`，也没有证据支持用
`12`、`18` 或 `20` 替换 `16`。

## 两个 threshold 的语义不同

`QSORT_THRESHOLD` 和 `MKQS_INSERTION_SORT_THRESHOLD` 不是同一层次的
阈值：

- `QSORT_THRESHOLD = 40` 决定顶层是否值得使用 radix sort，较小输入改用
  qsort；
- `MKQS_INSERTION_SORT_THRESHOLD` 决定 `mk_qsort_tuple_impl()` 的递归
  小分区何时改用 insertion sort；
- standard `sort_template.h` 自己的小数组 insertion sort threshold 是 `7`，
  不是 `QSORT_THRESHOLD`。

mksort 的判断使用：

```c
n < MKQS_INSERTION_SORT_THRESHOLD
```

所以阈值 `16` 覆盖最多 15 个 tuple，阈值 `40` 则覆盖最多 39 个 tuple。
不能因为两个常量都与 qsort 有关，就认为它们应该使用相同数值。

## 为什么阈值 40 会大幅回退

mksort 的小数组路径不是只比较当前 depth。它通过
`mkqs_compare_tuple_range()` 比较从当前 depth 到最后一列的完整剩余排序键：

```text
for each tuple
    move it left while the complete remaining key range is out of order
```

当前实现还通过相邻 `mkqs_swap()` 移动 tuple。随机输入时：

- insertion sort 的比较和移动数接近 `O(n²)`；
- partition 路径的平均工作量接近 `O(n log n)`；
- 每次比较可能读取多列、调用 generic comparator 或执行 text collation；
- 每次交换搬运完整 `SortTuple`。

阈值从 12 增加到 40 后的计数如下：

| 场景 | threshold 12 | threshold 40 | 增量 |
|---|---:|---:|---:|
| text unique/2列 comparisons | 1,728,477 | 2,035,074 | +17.7% |
| text unique/2列 swaps | 490,721 | 929,055 | +89.3% |
| text dup50/8列 comparisons | 1,654,531 | 1,924,427 | +16.3% |
| text dup50/8列 swaps | 560,395 | 975,693 | +74.1% |

对应执行时间分别增加约 18.2% 和 15.2%。因此，阈值 40 的回退来自实际
算法工作量增加，不是 threshold 判断、branch prediction 或测量抖动。

## 实验方法

测试使用：

- 100,000 行；
- `work_mem = 1GB`；
- 禁止 parallel query；
- benchmark 期间关闭 autovacuum；
- backend 固定到 CPU 2；
- CPU 固定为 2 GHz，关闭 boost；
- focused 测试预热 3 轮、正式测量 7 组；
- 奇偶轮使用 AB/BA 顺序；
- 检查 on 路径出现 `multi-key quick sort`；
- 完整矩阵使用 `mksort_test.sh` 的正式采样和汇总规则。

focused 测试覆盖：

- text unique/2列；
- text 中等和高重复度，2列及8列；
- bigint/int radix-to-mksort tie groups；
- timestamptz generic/typed comparator 场景；
- John Naylor tied-first/unique-second、逆序物理输入场景。

## Focused threshold sweep

下面的 gain 为：

```text
standard_time / mksort_time - 1
```

正值表示 mksort 更快。

| threshold | text unique/2列 gain | 观察 |
|---:|---:|---|
| 7 | +4.36% | 与 12/16 接近，但对近有序小分区预期不利 |
| 12 | +4.51% | 随机 focused cases 中表现最好 |
| 16 | +3.51% | 随机输入和近有序输入之间的平衡点 |
| 18 | +2.84% | text 已开始下降，没有稳定胜过 16 |
| 20 | +1.27% | text 明显下降，但尚未回退 |
| 24 | -1.31% | 已超过项目允许的 1% 回退 |
| 40 | -10.53% | insertion sort 覆盖范围过大 |

其他 text 重复度场景也显示相同趋势。threshold 40 相对于 16 通常损失
8 到 17 个 gain 百分点。

## 近有序小分区的相反结果

John Naylor 场景使用：

- 第一键大量重复；
- 第二键在每个第一键 group 内唯一；
- 物理输入按完整 key 逆序；
- mksort 对第一键 group 逐层排序。

虽然原始 group 逆序，但上层 pivot/partition 产生的小分区往往已经接近有序。
这时 insertion sort 接近线性，而继续 qsort 会多做一层 pivot 和 partition。

在相同当前代码和相同数据上，专门配对复测得到：

| threshold | John 场景 gain |
|---:|---:|
| 12 | +66.10% |
| 16 | +70.35% |
| 18 | +72.49% |
| 20 | +75.03% |

这解释了为什么不能只根据随机 focused cases 选择 `12`。较低阈值虽然减少
随机数组的 insertion sort 工作，却会让接近有序的 12 到 19 tuple 分区重新
进入 partition 路径。

## 完整矩阵

`mk_enabled=yes only` 汇总如下。表中的数值使用测试脚本原始 gain 比例，
例如 `+0.32` 表示平均约 32% 收益，`-0.01` 表示约 1% 回退。

| threshold | total average | worst retained sample | 结论 |
|---:|---:|---:|---|
| 12 | +0.32 | 接近 0.00 | 主矩阵略好，但 John 场景回退明显 |
| 16 参考结果 | +0.31 | 约 -0.01 | 两类场景之间最平衡 |
| 20 | +0.30 | -0.01 | 平均收益下降，最差值达到限制 |

threshold 20 虽然没有明确突破 1% 限制，但缺少安全余量，而且没有提高完整
矩阵平均性能。因此不适合作为默认值。

## 尝试过的 insertion sort 优化

### 二分定位加整体移动

实验把 threshold 40 的 insertion sort 改为：

1. 先检查相邻 tuple 是否已经有序；
2. 乱序时通过 binary search 找到插入位置；
3. 使用整体移动腾出插入位置。

它把 text unique/2列从 `-10.53%` 修复到 `+3.93%`，证明 threshold 40 的
主要问题确实是线性查找产生的二次方比较。不过，bigint、int、timestamptz
和多个重复度场景仍明显弱于 threshold 12/16。binary search 对很小数组还会
增加非顺序访问和固定控制流，因此没有保留。

### 保存 tuple 后连续右移

另一个实验保持 threshold 16 和线性查找不变，只把每个 inversion 的相邻
三份 tuple swap 改为：

1. 保存待插入 tuple；
2. 将较大 tuple 连续右移；
3. 最后写入保存的 tuple。

该版本在部分 typed integer 和高重复度 focused cases 中更快，但 text unique
与 John 场景没有稳定改善。完整矩阵的 `mk_enabled=yes` 总体平均仍为约
`+0.31`，并出现一个明显慢样本，没有形成足够清晰的整体收益，因此也没有
保留。

## 后续优化空间

理论上可以使用自适应策略：

- `n < 16` 总是使用 insertion sort；
- 对 16 到 23 个 tuple，只有检测到接近有序时才使用 insertion sort；
- 随机或明显乱序时继续 partition。

这种方案可能同时保留 threshold 12 的随机输入表现和 threshold 20 的近有序
表现。但它会引入额外 presort scan、full-range comparator 调用和新的经验阈值，
还可能与现有 top-level/depth presort 逻辑重复。在出现更明确的实际回退之前，
增加这种复杂度并不值得。

当前最合理的选择仍是简单的固定值 `16`。

## 结果文件

focused threshold sweep：

```text
/home/wy/mksort/threshold-focus-t7
/home/wy/mksort/threshold-focus-t12
/home/wy/mksort/threshold-focus-t16
/home/wy/mksort/threshold-focus-t18
/home/wy/mksort/threshold-focus-t20
/home/wy/mksort/threshold-focus-t24
/home/wy/mksort/threshold-focus-t40
```

完整矩阵及实现实验：

```text
/home/wy/mksort/new_result_threshold12.txt
/home/wy/mksort/new_result_threshold20.txt
/home/wy/mksort/new_result_threshold16_linear_move.txt
/home/wy/mksort/threshold-focus-t40_binary
/home/wy/mksort/threshold-focus-t16_linear_move
```

John 场景：

```text
/home/wy/mksort/threshold-john-t12_current
/home/wy/mksort/threshold-john-t16_current
/home/wy/mksort/threshold-john-t18_current
/home/wy/mksort/threshold-john-t20_current
```

所有临时代码均已撤销，安装的 PostgreSQL 已恢复 threshold 16，benchmark
结束后 autovacuum 已恢复为 `on`。
