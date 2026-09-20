# VDG Vector-Mode Design

## 1. Design Goals
1. 在不改变 VFS 语义的前提下，降低 VDG 常驻内存和峰值内存。
2. 使用面向 `version` 的向量索引，减少 map/tree 的额外开销。
3. 将 VDG 状态拆分为可管理生命周期，支持阶段性释放结构。
4. 保持增量求解能力：运行期允许动态加边与再次传播。

## 2. Scope
1. `VDG` / `VDGManager` 数据结构与 API。
2. `VersionedFlowSensitive` 中 VDG 相关流程：
   - `buildVersionDependencyGraphs`
   - `simplifyVDGGraphs`
   - `bindStmtRelianceToVDGNodes`
   - `propagateAllVersions` / `updateConnectedNodes` / `processStore`
3. 不涉及 `meldLabel` 语义本身重写（仅接口对接）。

## 3. State Machine
VDG 增加显式状态：
1. `Build`：构图阶段，可添加节点和四类边。
2. `Simplify`：执行 SCC/剪枝/收缩，允许边重定向与节点合并。
3. `Solve`：运行期传播，允许动态加边，仍可能触发局部合并。
4. `Finalized`：分析结束，释放求解态缓存。

状态迁移：
1. `Build -> Simplify`：构图完成后进入简化。
2. `Simplify -> Solve`：完成简化并绑定 stmt reliance。
3. `Solve -> Finalized`：求解结束，释放工作缓存。

状态约束：
1. `Build` 和 `Simplify` 阶段不可读取最终拓扑结论。
2. `Solve` 阶段禁止执行“破坏语义的全图重编号”。
3. `Finalized` 阶段仅允许统计与 dump，不允许改图。

## 4. Core Metadata

### 4.1 containerSize
1. 定义：当前容器上界，满足 `containerSize > maxVersionSeen`。
2. 规则：按需增长，不使用固定初值语义。
3. 建议：初始可 `reserve`，但必须支持运行期扩容。

### 4.2 version
1. `version` 为全局单调递增 id。
2. 不变量：单调递增，但允许稀疏，不要求连续。
3. 所有外部查询以 version 为主键，内部可选压缩映射。

## 5. Data Structure

### 5.1 Edge Storage (四向容器)
每个 version 节点维护：
1. `solidOut: SmallMap<Version, dstversion>`
2. `solidIn: SmallMap<Version, dstversion>`
3. `virtualOut: SmallMap<Version, dstversion>`
4. `virtualIn: SmallMap<Version, dstversion>`

容器实现建议：
1. 低度节点优先小连续存储（small-vector 风格）。
2. 高度节点升级为 hash fallback。
3. 对外 API 屏蔽具体容器类型。

生命周期：
1. `solidOut/solidIn`：全生命周期保留。
2. `virtualOut/virtualIn`：保留到 `Solve` 开始前。
3. 验证运行期不再依赖 virtual in/out，在 `Solve` 入口释放。

### 5.2 Node Flags
1. `loadConsume: vector<bool>`，单调 `false -> true`。
2. `storeYield: vector<bool>`，单调 `false -> true`。
3. 生命周期：`Build/Simplify` 可能读取，简化后释放。

### 5.3 Stmt Reliance
1. 结构：`unordered_map<Version, NodeBS>`（按需分配）。
2. 绑定策略：在 `Simplify` 后统一绑定到 rep version。
3. 生命周期：`Solve` 阶段使用，`Finalized` 前可释放。

### 5.4 Rep/Sub/Super
1. `rep: vector<Version>`：
   - `rep[v] = rep` 一次映射到位
2. `sub`：
   - 初期保留 `vector<NodeBS>` 兼容现有实现；
   - 后续可改为按需 materialize，避免全量常驻。
3. `super: vector<bool>`：//简化后清空，简化时常需要使用它来遍历
   - `true` 表示当前存活代表节点。

## 6. Invariants
1. `getRepVersion(v)` 必须稳定返回当前代表 version。
2. 合并后属性单调并入 rep：
   - `loadConsume`
   - `storeYield`
   - `stmtReliance`
3. 合并后禁止遗留自环与悬空边。
4. 任何阶段都不允许通过“非 rep version”直接访问最终语义节点。
5. 动态新增边必须通过统一 API，确保去重与状态一致。

## 7. Required API

### 7.1 Node/Version API
1. `getOrAddNode(version, loadConsume, storeYield)`
2. `hasVersion(version)`
3. `getRepVersion(version)`
4. `isSuper(version)`
5. `mergeVersionsIntoRep(subVersions, repVersion)`

### 7.2 Edge API
1. `addSolidEdge(srcV, dstV)`
2. `addVirtualEdge(srcV, dstV)`
3. `hasEdge(srcV, dstV, kind)`
4. `removeEdge(srcV, dstV, kind)`
5. `retargetEdgeSrc/retargetEdgeDst`

说明：
1. 对外不暴露底层容器迭代器类型。
2. 所有边操作自动使用 rep version。

### 7.3 Solve API
1. `markVersionUpdated(version)`
2. `hasPendingUpdates()`
3. `propagateInTopoOrder(propagateCb, stmtCb)`
4. `clearUpdateMarkers()`

### 7.4 Lifecycle API
1. `enterSimplify()`
2. `enterSolve()`
3. `finalizeAndRelease()`
4. `compactIfNeeded()`

## 8. Algorithm Flow

### 8.1 Build
1. 物化 version reliance 为 solid/virtual 边。
2. 标注 `loadConsume/storeYield`。
3. 仅创建必要 version 节点，避免无效节点预分配。

### 8.2 Simplify
1. `sccMergeSolidEdges`（仅 solid 图上做 SCC）。
2. `pruneUnreachableToLoadConsume`
3. `pruneUnreachableFromStoreYield`
4. `transitiveRedundancyElimination`（solid）
5. `chainContraction`
6. 完成后统一 `bindStmtRelianceToVDGNodes`。

### 8.3 Solve
1. `processStore` 更新 yield version pts，标记 updated。
2. `updateConnectedNodes` 动态加边并标记 updated。
3. `propagateInTopoOrder`：
   - 必要时局部 SCC merge
   - solid 边上传播
   - 触发 stmt reliance 回推 worklist

## 9. Complexity Targets
1. `getRepVersion`: O(1)
2. 稀疏图上边查找：低度节点近似 O(deg)，高度节点 O(1) 平均。
3. 合并代价与受影响邻接边规模线性相关。
4. 避免任何 `O(maxVersion^2)` 全量位图常驻结构。

## 10. Memory Strategy
1. 容器按需扩容，不做“按最大版本一次性全量构建”。
2. 大对象优先释放顺序：
   - `versionReliance` 在建图后立即释放。
   - `stmtReliance` 在绑定到 VDG 后释放原 map。
   - `virtualIn/virtualOut` 在进入 solve 后释放。
3. 对高峰结构提供 `shrinkToFit` 或 swap 释放入口。

## 11. Convert / Compact Design
`convert()` 定义为可选压缩步骤，不是求解必需路径。

输入条件：
1. 当前没有待处理更新。
2. 不在活跃传播循环中。

行为：
1. 将活跃 rep versions 重映射为稠密区间 `[1..K]`。
2. 重写所有边端点、rep/sub/super、stmt reliance 索引。
3. 生成 `oldVersion -> newVersion` 映射供外部同步。

风险控制：
1. 默认关闭，仅用于离线压缩实验。
2. 必须通过一致性校验后才能启用。

## 12. Migration Plan
1. Phase-A：API 对齐，不改底层容器语义。
2. Phase-B：引入四向容器与统一边 API，保持算法不变。
3. Phase-C：替换 SCC/剪枝/传播内部遍历实现。
4. Phase-D：评估并切换 DSU + 按需 sub materialize。
5. Phase-E：可选 convert/compact 能力。

## 13. Validation Checklist
1. 语义回归：`wpa -vfspta` 关键 benchmark 结果一致。
2. 图规模回归：init/simplified 节点与边数量趋势合理。
3. 内存回归：当前版本不统计 VFS 内存 checkpoint。
4. 性能回归：
   - `meld/build/simplify/propagate` 分阶段耗时
   - 总耗时

## 14. Open Decisions
1. small-container 具体实现：
   - 复用 LLVM SmallDense* 风格
   - 还是自定义轻量 SmallHash
