# LOPA 与 CG 使用说明

在 `/home/yhx/PTA/code/lopa_new` 中，`-lopa` 直接进入 `LOPA` 类，采用 PUS 调度：保留 VDG 构建时的 early merge DSU 和离线简化，将存活状态直接导出为 PUS 约束图节点，再按受影响的 Copy 子图调度传播。virtual 边仅用于离线简化，求解阶段由 Load/Store 和间接调用解析建立 Copy 边。GEP 保留 SVF 的对象与字段传递规则。

PUS 调度按 Copy SCC 拓扑传播、GEP/Load/Store 处理交替推进；新增 Copy 边会传播源节点已有事实。此实现没有引入 `simplifyWithHVN` 或其他 Aser 实验性离线合并。性能对比对象为下表中的 LOPA+CG Wave/SFR。

Copy 图只保存当前代表节点之间的边。新增边将源节点置为 `copyDirty`，points-to 增长也将节点置为 dirty；两者共同作为 SCC 遍历的起点。Copy 统一在拓扑阶段传播：dirty 节点向全部出边传递完整集合，再清除标记。拓扑传播直接使用图中的端点，值和内存状态映射在访问图时解析代表节点。

同一原始源节点上的 GEP/Load/Store 共用一组已处理目标缓存。SCC 合并后，各组先处理尚未见过的目标，随后收拢为一个组，缓存取各组已处理集合的交集。通常这些集合相同；若 GEP 处理期间源集合增长，交集保证下一轮补处理遗漏的目标。退役组释放约束列表及缓存内容，不再参与调度。缓存支持 `-ptd=mutable/persistent`，不需要额外开关。

LOPA 使用固定的 Andersen Wave 前分析，并要求 `-pre-field-sensitive=true`，保留前分析已确定的 FI 标记。本构建已修复 Andersen 合并后的两处漏传播：Load/Store 的类型检查允许多成员代表通过，新合并的多节点 SCC 重新入队。相关实例见 [根因报告](../../../labv2/lopa-pus/fi-root-cause/REPORT.md)。LOPA 和 CG 保留 variant GEP 的字段处理，并分别用 `PUSNewFIObjects`、`CGNewFIObjects` 统计主求解期间首次转为 FI 的对象；不再为这类事件全局清除缓存或重放约束。这两个计数预期为零，非零意味着需要检查前分析覆盖及结果，不能当作已由求解器补全。新发现递归调用仍会重查 Store 的强更新资格。

内存状态映射采用连续桶的哈希表，构图时插入，求解时只查询。Copy 图节点连续存放；每份邻接在最多四条边时内联保存有序 ID，超过后使用有序集合，兼顾低出度节点的内存开销和高出度节点的插删成本。SCC 遍历和边重建缓冲跨轮复用。这些实现保持原来的遍历顺序和传播规则，无需新增配置。

以下模式均固定使用 Andersen Wave 前分析。CG 与 LOPA+CG 共用 CG 求解器，`-cg-sfr=true` 为这两种模式启用 SFR 后端。

| 模式 | 参数 |
| --- | --- |
| SFS | `-fspta` |
| 原生 VSFS | `-vfspta` |
| LOPA | `-lopa` |
| LOPA + VSFS | `-lopa-vsfs` |
| CG Wave | `-cgfspta` |
| CG SFR | `-cgfspta -cg-sfr=true` |
| LOPA + CG Wave | `-lopa-cgfspta` |
| LOPA + CG SFR | `-lopa-cgfspta -cg-sfr=true` |

依赖 Linux x86-64、CMake 3.23 及以上、Ninja、Clang/LLVM 16、GCC 13 的 libstdc++ 和 Z3 开发库。以下命令在 `/home/yhx/PTA/code/lopa_new` 下执行：

```sh
cmake -S . -B PUS-build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=/usr/bin/clang-16 \
  -DCMAKE_CXX_COMPILER=/usr/bin/clang++-16 \
  -DCMAKE_C_FLAGS=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
  -DCMAKE_CXX_FLAGS=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
  -DLLVM_DIR=/usr/lib/llvm-16/lib/cmake/llvm \
  -DSVF_WARN_AS_ERROR=OFF -DSVF_ENABLE_ASSERTIONS=OFF \
  -DBUILD_SHARED_LIBS=OFF
cmake --build PUS-build --target wpa -j 24
```

产物为 `PUS-build/bin/wpa` 和 `PUS-build/lib/extapi.bc`。新增源码后重新执行配置命令。比较不同模式时统一使用相同的工具链、构建类型、断言设置和 extapi 文件。

例如，用 LOPA 分析 lua，并记录运行时间与峰值内存：

```sh
setarch "$(uname -m)" -R /usr/bin/time -v \
  PUS-build/bin/wpa -lopa \
  -ptd=persistent -node-alloc-strat=dense \
  -lopa-cg-store-policy=deferred \
  -extapi=/home/yhx/PTA/labv2/lib/extapi.bc \
  /home/yhx/PTA/labv1/benchmark/lua.bc \
  > lua.lopa-pus.log 2>&1
```

切换分析时替换表中的模式参数，其余参数保持一致。分析其他程序时，将最后的输入路径换成 LLVM 16 生成的 `.bc` 或 `.ll` 文件。单独使用本构建时，extapi 也可指定为 `PUS-build/lib/extapi.bc`。

常用选项：

| 选项 | 用途 |
| --- | --- |
| `-print-pts` | 输出完整顶层 points-to 集合，用于正确性比较。 |
| `-ptd=mutable/persistent` | 选择集合存储，覆盖 CG 的值状态、内存状态和 delta 传播。 |
| `-lopa-profile=true` | 输出 `-lopa`（LOPA）的阶段时间，用于诊断。 |
| `-cg-profile=true` | 输出 CG 和 LOPA+CG 的阶段时间，用于诊断。 |
| `-lopa-no-offline=true` | 关闭 LOPA 离线压缩，用于消融比较。 |
| `-vdg-stat` | 输出离线压缩后的对象 VDG 统计，支持 PUS、LOPA+CG 和 LOPA+VSFS。 |
| `-vdg-pass-order=SPC` | 设置 LOPA 简化顺序，默认 `SPC`。 |
| `-help` | 查看完整参数列表。 |

PUS 和 CG 使用默认的 `-pre-field-sensitive=true`。PUS 与 LOPA+CG 使用默认的 `-opt-svfg=false`，并保持 `-vdg-pass-profile` 为空。SFR 采用显式字段表示，具体实现范围见 [SFR_IMPLEMENTATION.md](../../cgfspta/SFR_IMPLEMENTATION.md)。

`-vdg-stat` 输出 `# VDG stats`，包括对象图数、`total_supernodes`、solid/virtual 边数及节点数分布。PUS 和 CG 在导出并释放每个对象图之前累计这些统计，因此无需保留整张 VDG。它描述离线压缩结果；在线 Copy SCC 合并效果查看下文的 PUS 计数。

CG 主求解通过独立的 `DiffPTData` 保存以 `CellID` 为键的集合。`persistent` 使用 SVF 现有的集合 ID、集合共享和运算缓存；`mutable` 使用可变集合。SCC 合并、已传播集合与 delta 均经过所选存储；最终再把顶层结果导出到以 PAG ID 为键的结果存储。两种键空间分别维护。

本次 CG 存储修复的验证构建为 `CGPTD-build/bin/wpa`，检查记录见[修复报告](../../../labv3/cg-ptd/REPORT.md)。旧 CG 构建仅在前分析和最终导出时使用 persistent；既有测量需按二进制版本区分。

LOPA 和 LOPA+CG 的 Store 旧值保留规则由 `-lopa-cg-store-policy` 选择：

| 值 | 行为 |
| --- | --- |
| `deferred`（默认） | 等 Store 目标非空后，由求解器按强弱更新条件决定是否保留旧值。与纯 CG 对比时使用此值。 |
| `object-lower-bound` | 沿用 LOPA 对象下界规则，提前保留部分对象的旧值；仍受 `-lopa-obj-fs-lower-bound` 控制。 |

该选项影响 `-lopa` 和 `-lopa-cgfspta`。两种规则在空目标 Store 上可能产生不同结果，实验中需明确记录所选值。

该策略在 VDG 简化前决定边类型，因此会影响压缩后的状态映射和导出的依赖。PUS 和 CG 将 solid 边转为 Copy。`object-lower-bound` 在空目标 Store 上提前保留旧值的行为作为已知语义差异保留，与 CG 参考结果逐项对齐时使用 `deferred`。比较压缩收益时固定策略，分别记录两种配置的结果。LOPA+VSFS 继续使用其原有对象下界规则和版本依赖。

构建后可运行集合存储、Store 策略和间接递归回归：

```sh
python3 /home/yhx/PTA/labv2/lopa-pus/semantic/run.py PUS-build/bin/wpa \
  --require-pus --extapi /home/yhx/PTA/labv2/lib/extapi.bc
python3 tests/solver/check_cg_ptd.py PUS-build/bin/wpa \
  --extapi /home/yhx/PTA/labv1/lib/extapi.bc
python3 tests/solver/check_lopa_vdg_stats.py PUS-build/bin/wpa \
  --extapi /home/yhx/PTA/labv1/lib/extapi.bc
python3 tests/solver/check_store_policy.py PUS-build/bin/wpa \
  --extapi /home/yhx/PTA/labv1/lib/extapi.bc
python3 tests/solver/check_indirect_recursion.py PUS-build/bin/wpa \
  --extapi /home/yhx/PTA/labv1/lib/extapi.bc \
  --analysis=-lopa-cgfspta --flag=-cg-sfr=true
```

完整测试集位于 `/home/yhx/PTA/labv1/test/soundness/{simple,difficult}`。布局优化的测评见 [测评报告](../../../labv2/lopa-pus/layout-optimization/REPORT.md)，对照版本使用相同的已修复 Andersen 前分析。simple 逐项比较完整 points-to 集合；difficult 和 benchmark 核对平均、最大集合大小等聚合数据。复杂程序的节点编号可能变化，聚合一致不代表逐节点集合完全相等。

读取输出时，取最终分析的 `Pointer Analysis Stat` 段；前面的 Andersen 预分析也会输出 `TotalTime`。PUS 和 CG 的计时含义如下：

| 指标 | 含义 |
| --- | --- |
| `TotalTime` | 分析构图、求解、导出和归一化时间，排除共享 Andersen、MemorySSA、SVFG 前分析。 |
| `CGConstructionTime` | CG 构图时间，LOPA+CG 中已包含离线压缩与导出。 |
| `PUSConstructionTime` | PUS 构图时间，已包含离线压缩与导出。 |
| `LOPAOfflineTime`、`LOPAExportTime` | 对应构图时间的子项，不再额外相加。 |
| `PUSValueBuildTime` | `compileValues()` 注册值约束的时间，包含在 `PUSConstructionTime` 中。PUS 的 `LOPAExportTime` 只计内存状态导出。 |
| `SolveTime` | 求解时间；CG 同时输出 `CGSolveTime`。 |
| `/usr/bin/time -v` 的 wall time、峰值 RSS | 整个进程的时间和峰值内存，包含共享前分析。 |

性能比较使用相同输入、extapi、公共选项和资源限制，关闭 `-lopa-profile` 和 `-cg-profile`，保留关闭 ASLR 的设置。各分析进程为单线程，可跨程序和模式并行运行；同批重复测量后取中位数，并保存完整命令、二进制及输入散列、退出状态和原始日志。

`-lopa` 默认输出以下在线 Copy SCC 合并统计，与 `-lopa-profile` 是否开启无关。节点数指约束图节点，已经经过 LOPA 离线压缩；GEP、Load、Store 是节点上登记的约束，不是这里的图边。

| 指标 | 含义 |
| --- | --- |
| `PUSInitialNodes`、`PUSInitialCopyEdges` | 离线导出和值约束注册结束、开始求解前的图规模。 |
| `PUSMemoryBindings`、`PUSValueBindings` | 内存位置键和值编号到约束节点的映射条目数。多个条目可以共享同一节点，因此映射大小可能远大于图节点数。 |
| `PUSConstraintGroups`、`PUSCoalescedGroups`、`PUSLiveConstraintGroups` | 初始复杂约束组数、处理后收拢掉的组数、剩余活跃组数。第一项减第二项等于第三项；组表编号不复用。 |
| `PUSNewFIObjects` | LOPA 主求解期间首次转为 FI 的对象数，不计 Andersen 已设置的 FI 标记。 |
| `CGNewFIObjects` | CG 和 LOPA+CG 主求解期间首次转为 FI 的对象数，含义与 `PUSNewFIObjects` 相同。 |
| `PUSNodes`、`PUSLiveNodes`、`PUSMergedNodes` | 累计创建节点数、最终代表节点数、SCC 合并消除的节点数。 |
| `PUSNodeReductionPct` | `100 × PUSMergedNodes / PUSNodes`。不含离线压缩收益。 |
| `PUSSCCMerges`、`PUSMaxSCCMembers` | 多节点 SCC 的合并次数、单次合并最多涉及的当前代表节点数；后者不展开以前已合并的成员。 |
| `PUSCopyEdgesInserted`、`PUSLiveCopyEdges` | 构图和求解期间成功新增的 Copy 数、最终 Copy 数。新增数不含 SCC 重建的边。 |
| `PUSSCCEdgesRemoved` | 各次 SCC 合并净减少的 Copy 数之和，包含环内边和合并后重复边。等于 `PUSCopyEdgesInserted - PUSLiveCopyEdges`。 |
| `PUSEdgeReductionPct` | `100 × PUSSCCEdgesRemoved / PUSCopyEdgesInserted`，衡量实际插入边中被合并消除的比例。 |
| `PUSSCCEdgesTouched`、`PUSSCCEdgesRebuilt` | 合并时累计拆除和成功重建的边数。两者之差为 `PUSSCCEdgesRemoved`；同一依赖在多次合并中可能重复计入。 |
| `PUSCopyAttempts`、`PUSCopyInvalid`、`PUSCopySelf`、`PUSCopyDuplicates` | 普通 `addCopy` 调用数，以及依次因缺失状态、自环、重复边而跳过的次数。总调用数等于三个跳过计数加成功新增数。 |

在线求解会增加 Load/Store 和调用 Copy，因此不能直接用初始边数减最终边数代表 SCC 压缩收益。这些统计也不等同于关闭 SCC 合并后的内存或时间收益；后者需要单独的消融实验。

加 `-lopa-profile=true` 可进一步观察 `PUSExportNodeTime`、`PUSExportCopyTime`、`PUSExportMapTime`，分别计量内存节点创建、solid Copy 插入、位置映射及 Store 状态对登记，三项构成 `LOPAExportTime`。`PUSProfileSCC` 包含 SCC 查找及合并，`PUSProfileMerge` 是其中合并阶段的子项；`PUSProfileCopy`、`PUSProfileIndirect` 分别计量 Copy 传播和 GEP/Load/Store 处理。诊断计时不改变 `TotalTime` 的起止范围。

默认分析类为 `LOPA`，代码入口如下。各步骤通过小函数组织，Copy 合并分别处理边重定向、事实与监听器合并、边重建和传播。

| 文件 | 职责 |
| --- | --- |
| [LOPA.h](../svf/include/WPA/LOPA.h)、[LOPA.cpp](../svf/lib/WPA/LOPA.cpp) | 默认 LOPA 求解器、Load/Store/GEP 处理和主循环。 |
| [LOPAFrontend.h](../svf/include/WPA/LOPAFrontend.h)、[Frontend.cpp](../svf/lib/WPA/LOPA/Frontend.cpp)、[VDGBuilder.cpp](../svf/lib/WPA/LOPA/VDGBuilder.cpp) | LOPA、CG 和 VSFS 共用的离线 VDG 构建与导出。 |
| [LOPA/Builder.cpp](../svf/lib/WPA/LOPA/Builder.cpp) | 依次创建内存节点、导入 Copy、登记位置映射，注册值约束。 |
| [PUSGraph.h](../svf/include/Graphs/PUSGraph.h)、[PUSMemoryMap.h](../svf/include/Graphs/PUSMemoryMap.h) | Copy 图及只在构图时写入的内存状态映射。 |
| [LOPA/CopySolver.cpp](../svf/lib/WPA/LOPA/CopySolver.cpp) | Copy SCC 查找、合并、拓扑传播。 |
| [LOPA/Stat.cpp](../svf/lib/WPA/LOPA/Stat.cpp) | LOPA 统计；`PUS*` 字段记录默认调度算法的计数。 |
| [LOPAVSFS.cpp](../svf/lib/WPA/LOPAVSFS.cpp) | VSFS 求解、结果读写和统计。 |
