# 未压缩 LOPA 的 soundness 问题（已定位并修复）

## 根因与修复

根因在 `VDG::sccMergeSolidEdges()` 与 union-by-size 合并的接口，不在
`equiv` 的边方向，也不是 load cache 导致的。

`mergeVersionsIntoRep()` 现在可能保留比 Tarjan 根节点更大的类，并返回实际
代表元。但 `sccMergeSolidEdges()` 原来忽略返回值，仍返回 Tarjan 旧根组成的
`topoOrder`。随后 `propagateInTopoOrder()` 执行：

```cpp
if (!hasVersion(repV) || !isSuperVersion(repV))
    continue;
```

当旧根被合并掉时，这会跳过整个 SCC：即使它的 points-to 已经汇总到新代表元，
并且 `updatedSet` 已经标记新代表元，也不会触发该 SCC 的 load 通知或向后继
传播。最后 `clearUpdates()` 清空待处理更新，形成漏解。

最小反例是 `a <-> b -> load`，其中 `a` 的类大小为 1，`b` 的类大小为 2。
从 `a` 出发做 Tarjan 时，旧拓扑序为 `[a, load]`，但合并保留 `b`。
若不把拓扑序改为 `[b, load]`，`a` 上的新事实虽然汇总到了 `b`，却到不了 load。
`tests/graph/vdg_scc_representative.cpp` 覆盖这一情况，以及事实本来就位于 `b`
时仍必须继续传播的情况。

修复保持 SCC 的拓扑位置，只更新该位置的代表元：

```cpp
for (Version& repV : topoOrder) {
    // ...收集该 SCC 的成员...
    repV = mergeVersionsIntoRep(versions, repV);
}
```

只应用这一修复，按下文相同参数运行未压缩 Lua：

| 指标 | 修复前 | 修复后 / 参考 |
|---|---:|---:|
| AvgTopLvlPtsSize | 59.9558 | 60.0267 |
| 顶层指针数 | 19,251 | 19,251 |
| 顶层 points-to 大小总和 | 1,154,209 | 1,155,574 |
| 空集指针数 | 1,521 | 1,506 |
| size=91 的指针数 | 11,152 | 11,167 |
| IndEdgeSolved | 294 | 318 |
| 三个 warning callsite 各自的目标数 | 0 | 8 |

完整大小直方图恢复为 SFS 的直方图。该检查与调用目标恢复证实了本例的缺失传播
已经恢复；大小直方图相同本身不是逐指针 points-to 集相等或全程序 soundness 的证明。
关闭 load cache 的对照仍为 59.9558，排除了它是本例根因。

验证还包括：上述 C++ 回归在修复前失败、修复后通过；现有 50 个 simple 用例在
SPC 和 `-lopa-no-offline` 两种模式下，逐指针 points-to 集均与 SFS 完全一致。
Lua 的全部 71 个间接 callsite 的目标函数集合也与 SFS 一致。

“代表元选择不影响图正规形”只适用于图结构；在线 solver 还必须同步所有保存了
代表元 ID 的辅助状态。此次遗漏的正是 SCC 的拓扑序。

## 背景

- 目标：让 `-lopa-no-offline`（“offline off”）成为**完全物化图 + 直接求解**的干净 baseline，用于 ablation。
- 现状：`-lopa-no-offline` 现在会完全物化（对象=所有间接边 points-to，起点=所有间接边 dst），不做 DSU、不做 passes，直接求解。
- 修复前已确认：**未压缩 LOPA 的解与参考（SFS/VSFS/LOPA 压缩）不一致，且是漏 points-to（unsound）**。以下保留原始排查记录。

## 实验配置（必须完全一致）

```
<flags> = -ptd=mutable -node-alloc-strat=dense -ff-eq-base=true -extapi=./lib/extapi.bc
```

工作目录：`/home/yhx/PTA/lab-final`，被测：`benchmark/lua.bc`

```bash
# SFS
./wpa_svf -fspta <flags> benchmark/lua.bc
# VSFS
./wpa_svf -vfspta <flags> benchmark/lua.bc
# LOPA 压缩
/home/yhx/PTA/code/lopa/Release-build/bin/wpa -lopa -vdg-pass-order=SPC <flags> benchmark/lua.bc
# LOPA 未压缩（完全物化）
/home/yhx/PTA/code/lopa/Release-build/bin/wpa -lopa -lopa-no-offline <flags> benchmark/lua.bc
```

## 统计结果（lua）

注意每个 run 会先跑一次 Andersen 预分析，输出里有**两个**统计块；下表是第二个（目标分析）块。

| 指标 | SFS | VSFS | LOPA 压缩 | LOPA 未压缩 |
|---|---|---|---|---|
| 统计块 | `Flow-Sensitive ...` | `Versioned Flow-Sensitive ...` | `Versioned Flow-Sensitive ...` | `Versioned Flow-Sensitive ...` |
| **AvgTopLvlPtsSize** | **60.0267** | **60.0267** | **60.0267** | **59.9558** |
| MaxTopLvlPtsSize | 125 | 125 | 125 | 125 |
| AvgPtsSize | 84.5018 | 165.18 | 176.886 | 164.594 |
| MaxPtsSize | 125 | 125 | 125 | 125 |
| AvgVersionPtsSize | 无 | 87.6321 | 89.9312 | 85.8614 |

（Andersen 块里 `AvgTopLvlPtsSize` 四者都是 60.0743。）

## 关键事实：不是分母/口径假象

`AvgTopLvlPtsSize = Σ(顶层指针 pts 大小) / 有效顶层指针数`。

用 `-print-pts` 实测（会打印 Andersen + FS 两遍 dump）：

| dump | SFS | VSFS | LOPA_c | LOPA_u |
|---|---|---|---|---|
| FS pass 指针数 / Σsize / avg | 19251 / 1155574 / 60.026700 | 同 | 同 | 19251 / **1154209** / **59.955795** |

- 分母完全相同（19251），`-print-pts` 与统计块逐位吻合。
- 所以是**分子少了 1365**（0.118%），不是口径问题。

## 差异定位：只有 15 个顶层指针（size 91 → 0）

对 19251 个顶层指针做 **pts 大小直方图**（对 id 置换不变；注意：指针/对象 id 跨 run 非确定，同一配置连跑两次有上万处纯 id 置换，所以逐行 id diff 不可靠）：

| size | 0 | 1 | … | **91** | 92 | 93 | … | 125 |
|---|---|---|---|---|---|---|---|---|
| SFS / VSFS / LOPA_c | 1506 | 4514 | … | **11167** | 615 | 650 | … | 2 |
| LOPA_u | **1521** | 4514 | … | **11152** | 615 | 650 | … | 2 |

- 唯一差异：**15 个指针从 size=91 变成 size=0**（15×91=1365，正好等于 Σsize 之差）。
- SFS、VSFS、LOPA_c 的直方图**逐 bin 完全一致**（LOPA_c 连跑两次也一致）。

这 15 个指针（LOPA_c 与 LOPA_u 同一 id family）：
```
4294936168, 4294936169, 4294936176, 4294936177, 4294936178,
4294936180, 4294936181, 4294936188, 4294936189, 4294936190,
4294936192, 4294936193, 4294936200, 4294936201, 4294936202
```

用 `-dump-pag`（`svfir_initial.dot`）及 callsite 输出定位，全部来自 `lstate.c` 的 `luaE_warnerror`：
- `%31/%38/%45 = load ptr, ptr %16`  → `G(L)`（`L->l_G`），@413:25
- `%32/%39/%46 = getelementptr %struct.global_State ... i32 ...`（`&g->warnf`），@413:31
- `%33/%40/%47 = load ptr, ptr %32/%39/%46` → **`g->warnf` 的值（函数指针）**，@413:31
- `%36/%43/%50 = getelementptr ...`（`&g->ud_warn`），@415:14
- `%37/%44/%51 = load ptr, ptr %36/%43/%50` → `g->ud_warn`，@415:14

参考里它们都指向同一组 **91 个对象**（`warnfon`/`warnfoff`/`warnfcont`、`luaopen_*`、`searcher_*`、`io_*` 等）；LOPA_u 里为**空集**。

## 直接后果：3 个间接调用丢全部目标

`-print-fp`（间接调用目标）在每个 run 里也打印两遍。三个 callsite `CallICFGNode24750 / 24759 / 24768`（都是 `lstate.c:415:5` 的 `wf(G(L)->ud_warn, ...)`，即 `%33/%40/%47`）：

| pass | SFS / VSFS / LOPA_c | LOPA_u |
|---|---|---|
| Andersen pass | 8 个目标 | 8 个目标（相同） |
| **FS pass** | **8 个目标**（含 `warnfon/warnfoff/warnfcont`） | **`!!!has no targets!!!`（空）** |

即未压缩 LOPA 的 flow-sensitive 结果把 `wf` 这 3 个函数指针 load 置空，导致这 3 个间接调用解析不出任何被调函数。它自己的 Andersen 预分析是有目标的 → **是 FS 求解阶段丢的**。

## 性质判定

`g->warnf` 在 `lauxlib.c` 的 `lua_setwarnf` 里确实会被赋为 `warnfon/warnfoff`，`wf` 又在 `if (wf != NULL) wf(...)` 内被调用。因此 LOPA_u 的空集是**真实的漏对象（under-approximation）**，属 **soundness 问题**，不是“精度提升”。

## 修复前现象与推断修正

- **LOPA 压缩、SFS、VSFS 的顶层 points-to 大小直方图一致**；这一统计证据不能单独推出逐指针的集相等或全程序 soundness。
- **LOPA 未压缩丢传播**；旧的 load-anchored 构图模式（`-lopa -lopa-no-dsu -vdg-pass-order=none`）也得到 59.9558。
- 先前据此判断“不是本次改动引入”不成立：这两个构图模式都使用当前同一个在线 SCC solver，都受 union-by-size 后旧拓扑序失效的影响。它们并不是改动前后的代码版本对照。

## 排查结论

1. `equiv` 物化的 `singlePredV -> dstConsumeV` 方向正确，此次修复没有修改构图。
2. `mergeVersionsIntoRep` 返回的实际代表元必须写回 SCC 拓扑序。只修正这一接口即可恢复本文的 Lua 结果。
3. 旧代码跳过被合并掉的 Tarjan 根，导致相应 SCC 的事实和 load 通知没有继续传播；不能把 Andersen 有目标而 FS 没目标直接归因于构图或未激活的边。

## 相关代码位置

- `svf/lib/WPA/LOPA/VDGBuilder.cpp`
  - `prelabel()`（`-lopa-no-offline` 时锚定所有间接边 dst）
  - `labelObjectVersions()`（`getOrCreateConsumeVersion/StoreYieldVersion`）
  - `compressEquivVersions()`（no-offline 分支）
  - `materializeAndSimplify()`（C→Y 边、`consumeV != yieldV` 判据）
- `svf/lib/Graphs/VDG.cpp`（prune、chainContraction、mergeVersionsIntoRep）
- `svf/lib/WPA/LOPA/Profiling.cpp`（估计图，n0 已与 real 完全物化图逐字段一致）
- `svf/lib/WPA/LOPA.cpp`（initialize/solve 流程）

## 附：本次会话已做的其他改动（供上下文，均未提交）

1. **Prune 对齐论文**：`VDG::pruneUnreachableFromStoreYield` 去掉 `isLoadConsume()` 例外，使 Prune 严格 = `FromWrite ∩ ToRead`（`svf/lib/Graphs/VDG.cpp`）。修复后 real `DSU+SPC = no-DSU+SPC = profiling SPC = 16,658`（lua），达到唯一正规形。
2. **Profiling callgraph 修复**：`Profiling.cpp` 的 delta 索引改用 `svfg->getCallGraph()`（原 `pta.getCallGraph()` 只有直接边，导致 delta 虚边全丢）。
3. **Profiling must⊔may=must**：`addProfileEdge` / `mergeProfileNodesIntoRep` 中 must 边吸收同端点 may 边。
4. **Profiling store C→Y 对齐**：只对该对象 footprint 里真正作为 `StoreYield` 出现的 store 加 C→Y，不再对仅 `StoreConsume` 的 store 凭空补 yield 节点。修复后 profiling n0 与 real 完全物化图逐字段一致（lua：nodes 1,079,922 / solid 1,443,706 / virtual 39,013）。
5. **union-by-size**：`VDG::mergeVersionsIntoRep` 选最大类作代表元并返回；`chainContraction` enqueue 返回的 rep。lua 不动点不变（16,658），`test/soundness/verify/_verify.sh simple` 50/50 通过。
6. **新增 `-lopa-no-dsu`**（只关 DSU、保留 passes）与完全物化版 `-lopa-no-offline`。
7. **Profiling 新增统计**：`n0_plain/n1_plain` 与每 pass 的 `plain`（非 store/load 节点数）。

改动文件：`svf/include/Util/Options.h`、`svf/lib/Util/Options.cpp`、`svf/lib/Graphs/VDG.cpp`、`svf/lib/Graphs/VDG.h`、`svf/lib/WPA/LOPA/Profiling.cpp`、`svf/lib/WPA/LOPA/VDGBuilder.cpp`。
