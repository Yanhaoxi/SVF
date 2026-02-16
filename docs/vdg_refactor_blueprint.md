# VDG / VSFS Refactor Blueprint

## 1. 目标与范围
- 目标：在不改变 VFS 语义的前提下，降低 `VDG` 相关内存占用，收敛冗余 API，简化后续大改（`vector-mode`）风险。
- 范围：
1. `VDG`、`VDGManager` 的数据结构与 API。
2. `VersionedFlowSensitive` 中依赖 VDG 的构建/简化/传播链路。
3. 与版本依赖、语句依赖、等价对象映射相关的生命周期管理。
- 非目标（当前轮不做）：
1. 指针分析语义变更。
2. 重新定义 meld 版本算法本身。
3. 一次性推翻全部结构（采用分阶段替换）。

## 2. 当前实现快照

### 2.1 VDG 结构（现状）
- 节点：`VDGNode`（继承 `GenericNode<VDGNode, VDGEdge>`）
1. 核心属性：`version`、`loadConsume`、`storeYield`、`stmtReliance`。
2. 入/出边容器：来自 `GenericNode` 的 `OrderedSet`。
- 边：`VDGEdge`
1. 仅保留 `isVirtualEdge`（虚边/实边）；不再保存 provenance kind。
- 图：`VDG`
1. `verVec_`: `version -> rep node*`
2. `repVec_`: `sub version -> rep version`
3. `subVec_`: `rep version -> sub versions`
4. `nodeVec`: `nodeId -> node*`
5. `superNodes`: super-node 标记
6. `updatedNodes_`: 待传播 rep node id 列表

### 2.2 VSFS 与 VDG 的关键流程（现状）
初始化路径：
1. `prelabel()`
2. `meldLabel()`
3. `expandEquivalentObjectVersions()`
4. `buildVersionDependencyGraphs()`
5. `simplifyVDGGraphs()`
6. `bindStmtRelianceToVDGNodes()`

求解期路径：
1. `processStore()` 写 `yield` 版本 pts，并 `markVersionUpdated`
2. `updateConnectedNodes()` 动态加边并 `markEdgeAdded`
3. `propagateAllVersions()` 调 `graph->propagateInTopoOrder(...)`
4. `processLoad()` 读 rep version 对应 pts（含 load cache）

### 2.3 已知问题
1. 初始 VDG 规模大（节点/边在 simplify 前显著高于 simplify 后）。
2. 构图和简化之间存在短期峰值内存重叠。
3. `rep/sub`、边容器、reliance map 多处重复索引，API 面较宽。
4. 部分路径仍有“先建再裁剪”的内存浪费（尤其是大对象集）。

## 3. 重构必须满足的不变量
1. `solid` 边语义：必须传播；`virtual` 边语义：保守连接/可能传播用途，不得误当 solid。
2. 任何时刻 `getNode(version)` 必须返回当前 rep 节点。
3. merge 后：
   - 语义属性需并入 rep（`loadConsume/storeYield/stmtReliance`）。
   - 边重定向后不出现自环脏边。
4. 简化后参与求解的版本查询必须可映射到有效 rep（或显式 invalid）。
5. 动态新增边（indirect call / runtime store）必须保持增量正确性。

## 4. 目标结构（分阶段）

### 4.1 第一阶段：API 收敛 + 生命周期瘦身（低风险）
- 目标：先减少“冗余状态长期驻留”，不改核心图结构。
- 动作：
1. 明确 VDG 公开 API 最小集：
   - 节点：`getOrAddNode/getNode/hasVersion/getRepVersion`
   - 边：`addEdge`
   - 传播：`markVersionUpdated/propagateInTopoOrder`
   - 简化：`sccMerge/prune/transitive/chain`
2. reliance 生命周期前移释放：
   - `buildVersionDependencyGraphs()` 后释放 `versionReliance`（已在做）。
   - `bindStmtRelianceToVDGNodes()` 后释放 `stmtReliance`（已在做）。
3. 文档化“禁止绕过 API 直接操作底层容器”。

### 4.2 第二阶段：rep 体系改造评估（中风险）
- 候选 A：保留 `repVec_ + subVec_`（当前实现，便于枚举子版本）。
- 候选 B：改为 node-level DSU（并查集）为主，`sub` 只在必要时按需构建。
- 评估点：
1. 是否仍需要频繁“枚举全部 sub”用于数据合并。
2. `stmtReliance` 已绑定 rep 后，对 `sub` 的硬依赖是否减少。
3. simplify/propagate 中对 `subVec_` 的热路径频率。

### 4.3 第三阶段：边存储重构（高风险，单独分支）
- 当前争议方案：
1. 继续 `GenericNode + OrderedSet`（维护成本低，内存较高）。
2. “四向容器”(`in/out x solid/virtual`)。
3. edge-pool + adjacency vector + 高出度 fallback。
- 建议策略：
1. 先在 `vector-mode` 分支隔离实现。
2. 先做接口兼容层，避免一次改穿全部算法。
3. 每次替换只改一层：存储层 -> SCC/merge -> simplify passes。

## 5. 算法改造清单（按流程）

### 5.1 meld + 构图阶段
1. `meldLabel()` 输出：`consume/yield` + canonical reliance 映射。
2. `buildVersionDependencyGraphs()` 负责把 version reliance 物化成结构边。
3. 约束：
   - 不重复建自环。
   - 尽量避免“先建无效节点，后剪枝”。
4. 可优化点：
   - 合并“建图 + 部分简化”的流式策略（需验证正确性与并发影响）。

### 5.2 simplify 阶段
当前 pass 顺序：
1. SCC merge（solid）
2. prune to load-consume
3. prune from store-yield
4. transitive redundancy elimination
5. chain contraction

后续重构要求：
1. 每个 pass 输入输出都只依赖稳定 API。
2. pass 内不泄露底层容器细节到上层。
3. pass 后可选立即释放不再使用的辅助结构。

### 5.3 runtime propagation 阶段
1. `processStore/updateConnectedNodes` 仅做“增量写入 + 标记更新”。
2. `propagateInTopoOrder` 统一完成：
   - 必要 SCC merge
   - rep 传播
   - stmt reliance 回推工作队列
3. 目标：减少额外缓存，避免重复遍历 `sub`。

## 6. 推荐最小 API 契约（对外）
`VDG` 建议保留：
1. `getOrAddNode(ver, loadConsume, storeYield)`
2. `hasVersion(ver)`
3. `getRepVersion(ver)`
4. `addEdge(srcVer, dstVer, isVirtual)`
5. `markVersionUpdated(ver)`
6. `hasPendingUpdates()/getUpdatedNodes()/clearUpdateMarkers()`
7. `propagateInTopoOrder(...)`
8. `sccMergeSolidEdges(...)`
9. `prune.../transitive.../chainContraction()`
10. `bindStmtReliance(ver, stmts)` 与 `getStmtReliance(ver)`

`VDGManager` 建议保留：
1. `getOrCreateVDG/tryGetVDG/getVDG`
2. `markVersionUpdated/markEdgeAdded/hasPendingVDGs/popPendingVDG`
3. `getRepVersionOrInvalid/tryAtRepKey`
4. `clear/dumpStats/writeToFile`

## 7. 分阶段实施计划（建议）
1. Phase-0 基线
   - 固定 benchmark（如 `tmux.bc`）和日志口径（Build/Run/Simpl/End）。
   - 记录 `total_nodes/total_supernodes/total_edges` 与 VmRSS/VmSize。
2. Phase-1 清理
   - 删除未使用 API/注释漂移项。
   - 保证当前结构行为稳定，可编译可跑。
3. Phase-2 rep 结构实验
   - 在不改边存储的前提下评估 DSU 方案。
4. Phase-3 边存储实验（`vector-mode`）
   - 引入新容器后逐个迁移 pass。
5. Phase-4 收敛
   - 保留收益显著方案，回退收益差方案。

## 8. 验证与回归检查
每轮改动至少检查：
1. 语义一致性：`wpa -vfspta` 结果不回退（关键 case）。
2. 图规模变化：init/simplified 节点边数量趋势合理。
3. 内存指标：
   - `VFSMemAfterBuild*`
   - `VFSMemAfterSimpl*`
   - `VFSMemAfterRun*`
   - `VFSMemDelta*`
4. 性能：总耗时 + 关键阶段耗时（`meld/build/simplify/propagate`）。

## 9. 待确认决策
1. `rep/sub` 是否转 DSU 为主（以及何时落地）。
2. 边存储是否进入 `vector-mode` 深改，还是先做局部压缩。
3. `expandEquivalentObjectVersions()` 是否彻底改为 canonical 引用策略（延后到下一轮）。
4. 是否采用“流式建图后立刻简化”的管线（按对象批处理）。
