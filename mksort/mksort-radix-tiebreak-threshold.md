# radix tiebreak 与 insertion threshold 调优

## 结论

删除 `MKQS_RADIX_TIEBREAK_THRESHOLD`。radix 完成第一键后，直接使用已有的
insertion threshold 决定是否进入 mksort：

```c
#define MKQS_INSERTION_SORT_THRESHOLD 16
```

但不能只把 `64` 改成 `16`。原代码禁止带 terminal duplicate handler 的
tuple 类型使用 mksort 的递归 insertion-sort 收尾路径：

```c
if (n < MKQS_INSERTION_SORT_THRESHOLD &&
    !state->base.mkqsHandleDupFunc)
```

index btree 设置了 `mkqsHandleDupFunc`，因此它的所有递归小 partition 都继续做
pivot、三向 partition 和递归，直到只剩一个 tuple。此前测出的 index by-value
约 256、index generic 约 2048 的“交叉点”主要是这一额外算法工作造成的，不是
不同 tuple 类型需要不同 radix threshold。

修复方法是允许这些小 partition 使用 insertion sort，并通过 tuple 类型已有的
完整 standard comparator 完成隐式最终键语义。对于 index btree，这包含 heap
TID 排序；因此不会跳过原来 terminal handler 负责的最终全序。

修复后 heap/index 及 by-value/generic 的安全交叉点都回到 16。radix handoff
之所以在 16 切换，正是因为 `<16` 进入 mksort 后只会选择 insertion sort；
此时 standard tiebreak qsort 更合适。因此不需要第二个同值常量，也不需要在
未来每增加一种 mksort tuple 类型时增加一组 threshold。

两套 insertion-sort 循环也已合并为模板中的
`mkqs_insertion_sort_<base>()` always-inline 函数。不同 tuple 类型在递归入口
调用相应的模板实例，避免动态 comparator 或模式判断进入比较热循环。

这里没有改成接受 comparator 函数指针的普通 helper。实验表明，统一走 standard
comparator 会让 heap integer 丢失 typed range comparator 的优势；在单循环内部
按 tuple 类型判断也会使 index group 16 慢约 8%。模板只为 heap generic 和 index
btree 生成 insertion 函数：带 terminal handler 的 index 使用完整 standard
comparator，heap 使用可内联的 `mkqs_compare_tuple_range()`。三个 typed heap
模板实例不生成重复的 insertion 函数。

最初为全部五个模板实例生成 insertion 函数时，低收益 bigint 用例出现 `-1.68%`
中位回退。收缩为两个必要实例后，31-run AB/BA 复测 bigint 为 `+1.57%`，
timestamptz 为 `+0.47%`。`tuplesort.o` 中没有 `mkqs_insertion_sort_*` 符号，
确认两个函数均被内联，没有增加独立的运行时函数。

## 两个阈值的准确关系

### `MKQS_INSERTION_SORT_THRESHOLD = 16`

它只在已经进入 `mk_qsort_tuple_impl()` 后生效：

- `n < 16`：使用 insertion sort 完成整个剩余排序键范围；
- `n >= 16`：进入 mksort median/pivot/partition 路径，其递归产生的小 partition
  再由 insertion sort 收尾。

因此强制所有 radix tie group 使用 mksort 时，15→16 的突变确实由这个阈值
造成，不能被解释为 heap accessor 的固有交叉点。

### `QSORT_THRESHOLD = 40`

它用于：

1. 决定整个输入是否值得进入 radix sort；
2. 决定 radix 尚未处理完第一键所有字节时，一个 byte partition 是否提前改走
   完整 qsort；
3. 决定顶层 non-NULL partition 是否进入 radix。

它不直接决定“第一键已经完整相等”的最终 tie group 使用 mksort 还是 standard
tiebreak qsort。最终 handoff 使用 `MKQS_INSERTION_SORT_THRESHOLD`，因为这是
mksort 是否会进入 insertion path 的直接边界。

不过，一个小于 40 的中间 byte partition 可能提前被完整 qsort，所以并非所有
最终大小 16～39 的相等第一键 group 都一定到达最终 handoff；这取决于第一键的
字节分布。focused 测试通过实际 `mkqsUsed`/trace 识别路径，没有仅根据 GUC
推断执行了 mksort。

radix 已经确认完整第一键相等后，按 insertion threshold 决定：

```text
group size < threshold  -> qsort_tuple(comparetup_tiebreak)
group size >= threshold -> mk_qsort_tuple(depth = 1)
```

第一键 NULL partition 也是一个完整第一键相等的 group，因此应使用相同阈值，
不应绕过阈值无条件进入 mksort。

## 为什么 heap、index by-value、index generic 原来差别很大

### 主要原因：index 没有递归 insertion 收尾

100,000 行、精确第一键 group、仅计 `tuplesort_sort_memtuples()` 的配对结果：

| 场景 | 原代码 mksort gain | 修复 index insertion 后 |
|---|---:|---:|
| heap int/5列，group 256 | +38.36% | +37.96% |
| heap text/5列，group 2048 | +9.58% | +9.48% |
| index int/5列，group 256 | +4.45% | +15.38% |
| index text/5列，group 2048 | -0.44% | +8.53% |

generic text 的 heap/index 差距从约 10 个百分点缩小到不足 1 个百分点，证明
主要瓶颈不是 `index_getattr()`，而是 index 将所有递归小 partition 做到底。

### 次要原因：index 没有 integer comparator specialization

heap 会根据当前 depth 的 SortSupport comparator 选择 int32/int64/uint64 直接
比较模板；index 当前只有 generic `sortKey->comparator()` 模板。

临时给 index 使用同样的 integer comparator dispatch 后：

| group size | heap int gain | index int gain |
|---:|---:|---:|
| 256 | +39.30% | +35.66% |
| 512 | +44.16% | +43.72% |
| 1024 | +48.30% | +48.57% |

这确认修复 insertion 后剩余的 by-value 差异主要来自 comparator specialization。
它是独立的性能优化问题，不应通过提高 index radix threshold 规避。本次候选不
保留额外 index 类型模板，以避免函数和 i-cache 膨胀。

## 修复后的统一交叉点

下面的测试暂时强制所有 group 进入 mksort，以观察算法本身的交叉点：

| 场景 | group 15 | group 16 | group 20 |
|---|---:|---:|---:|
| heap int/5列 | +4.21% | +21.44% | +23.87% |
| heap text/5列 | -11.58% | +1.69% | +0.55% |
| index int/5列 | -13.69% | +7.03% | +5.40% |
| index text/5列 | -8.90% | +2.14% | +0.12% |

因此：

- 15 不能作为阈值，generic 和 index 输入存在 8%～14% 的稳定回退；
- 16 是所有路径同时转正的第一个值；
- 17 或更高会放弃 group 16 已经验证的正收益。

使用真正的 threshold 16 复测时，group 12/15 的 `mkqsUsed=false`，由 standard
tiebreak qsort 处理；group 16 起 `mkqsUsed=true`，四类路径全部获得正收益。

## 完整矩阵

heap `mksort_test.sh`：

| scope | min | max | average | n |
|---|---:|---:|---:|---:|
| int, mksort executed | -0.00 | +0.95 | +0.23 | 117 |
| bigint, mksort executed | -0.00 | +0.88 | +0.22 | 117 |
| timestamptz, mksort executed | -0.00 | +0.87 | +0.28 | 84 |
| text, mksort executed | +0.06 | +1.42 | +0.32 | 207 |
| total, mksort executed | -0.00 | +1.42 | +0.27 | 525 |

John Naylor tied-first/unique-second 场景的中位收益为 `+71.28%`。

合并 insertion-sort 循环并删除独立 radix threshold 后，31 组 AB/BA 定点复测：

| 场景 | 中位 gain |
|---|---:|
| bigint random/count 5/5列 | +0.20% |
| timestamptz random/count 25/8列 | -0.06% |

两者都在最大 1% 回退限制内。此前 5-run 完整矩阵中的 `-2%/-4%` 是单次运行
抖动；31-run 样本的单次极值仍可达到约 `-7.8%/+10.5%`，但配对中位数稳定。

index `mksort_index.sh` 的 grouped、nullable 及实际进入 mksort 的 text duplicate
场景均正常；amcheck 全部通过。typed duplicate 场景的个别 `-2%/-3%` 样本经
`trace_sort` 确认为 `method: quicksort`，没有实际执行 mksort。该脚本当前把
`enable_mk_sort=on` 错误推断为 `mk_enabled=yes`，不能用其 inferred 列判断
executor 最坏回退。

最终源码还通过了全部 245 个 core regression tests。

## 结果文件

```text
/home/wy/mksort/radix-internal-baseline
/home/wy/mksort/radix-internal-index_insertion
/home/wy/mksort/radix-internal-insertion_sweep
/home/wy/mksort/radix-internal-threshold16
/home/wy/mksort/radix-internal-index_typed
/home/wy/mksort/index_result_radix_generic_candidate.txt
/home/wy/mksort/new_result_radix_generic_candidate.txt
/home/wy/mksort/new_result_single_insertion_threshold.txt
/home/wy/mksort/index_result_single_insertion_threshold.txt
/home/wy/mksort/focused-insertion-macro-int-31
```
