查到了：**当前实现与论文有两处规则不一致。隔离修正后，三条路径都得到 16,356 个节点，must/may 边数也一致。** 这解释了你观察到的差异。

**1．按论文规则，构图时提前剪枝、提前做部分后向 Chain，不影响最终正规形。**

load 逆向遍历相当于提前删除 \(ToRead\) 外的节点；构图 DSU 合并的是“唯一 must 前驱、没有 may 入边”的 consume 节点，它们不是 store-yield，符合 ChainBwd。[构图代码](/home/yhx/PTA/code/lopa/svf/lib/WPA/LOPA/VDGBuilder.cpp:505)

因此，只要后续规则与论文一致并执行到正规形，这些操作可以提前。但**当前真实实现里的 Prune 有一个例外，破坏了这个结论**。

**2．节点数不同的两个具体原因。**

第一处，[真实 Prune](/home/yhx/PTA/code/lopa/svf/lib/Graphs/VDG.cpp:910) 有：

```cpp
if (reachable.test(repV))
    return;
if (node->isLoadConsume())
    return;  // 即使没有 store 能到达，也保留 load
```

而[profiling 的 Prune](/home/yhx/PTA/code/lopa/svf/lib/WPA/LOPA/Profiling.cpp:903) 和论文都删除 \(FromWrite\cap ToRead\) 外的**所有**节点。

这个例外确实会造成不同正规形。考虑没有任何 store 的图，两条边都是 must：

```text
       ┌──→ load₁
   x ──┤
       └──→ load₂
```

- 先 Prune：删除中间点 \(x\)，保留两个孤立 load，最终 **2 个节点**。
- 先后向 Chain：两个 load 都可以合并到 \(x\)，随后 Prune 保留这个带 load 标记的节点，最终 **1 个节点**。

我用真实 `VDG` 类验证了这个反例。**所以当前实现中，提前 DSU 确实可能改变最终节点数；不是多跑几轮就能解决。**

第二处，[profiling 的 merge](/home/yhx/PTA/code/lopa/svf/lib/WPA/LOPA/Profiling.cpp:688) 会同时保留同一对端点间的 must 和 may 边。真实 VDG 和论文则规定：

\[
\mathbf{must}\sqcup\mathbf{may}=\mathbf{must}.
\]

profiling 遗留的 may 边会使 `virtualIn/Out.empty()` 不成立，阻挡本应发生的 Chain。

我用当前二进制和 `lab/benchmark/lua.bc` 复测，数值与你报告的略有不同，但差异被这两处修改消除了：

| 路径 | 当前实现 | 对齐论文规则后 |
|---|---:|---:|
| real DSU＋SPC | 28,185 | **16,356** |
| real no-DSU＋SPC | 73,254 | **16,356** |
| profiling SPC | 17,241 | **16,356** |

对齐后的三者还都有 **12,671 条 must 边、6,576 条 may 边**。各配置追加 `CSPC` 后均不再减少。这里验证了规模一致，尚未做完整图同构比较。

**3．可以避免全图反复跑 SPC，但“唯一正规形”不等于能一次批量 union 所有候选。**

对论文规则、固定 must/may 标签的离线图，下面就足够：

```text
收缩所有 must-SCC              // 一次
保留 FromWrite ∩ ToRead        // 一次
用共享工作队列执行 Fwd/Bwd Chain，直到队列为空
```

关键是：**S 和 P 都不需要重跑，只有 C 需要增量闭包。**

理由很短：

- SCC 收缩后，must 图是 DAG；合法 Chain 的唯一前驱/后继条件保证收缩不会产生新的 must 环。
- Prune 后每个节点都处于某条可能的 store-to-load 通路上；Chain 收缩保留这一性质，不会产生新的可剪节点。

因此，你现在的整体算法形状已经合适。效率优化应放在 **Chain 的邻接维护和候选更新**：按大小合并，规范化重边，只重新检查度数或边标签发生变化的节点。采用哈希邻接表和反向索引，可以设计期望 \(O((N+M)\log N)\) 的实现；当前实现不能仅凭使用 DSU 就获得这个界。

另外，不应把初始所有 Fwd/Bwd 候选边一起 union：同一个中间点可能分别允许向两端合并，但把两端也合到一起可能不合法。这也说明它是**这套规则下的唯一正规形**，并非唯一的原节点划分或所有保语义图中的全局最小图。

实验修改和[复现记录](/tmp/lopa-vdg-audit-O0ndvQ/report.md)都在 `/tmp`，工作区源码未改动。