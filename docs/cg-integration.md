# LOPA 与 CG 使用说明

本分支通过 `wpa` 运行以下分析。CG 与 LOPA+CG 共用求解器，LOPA+CG 在求解前压缩内存状态；`-cg-sfr=true` 为两种模式启用 SFR。

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

依赖 Linux x86-64、CMake 3.23 及以上、Ninja、Clang/LLVM 16、GCC 13 的 libstdc++ 和 Z3 开发库。以下命令在 `/home/yhx/PTA/code/lopa` 下执行：

```sh
cmake -S . -B Release-build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=/usr/bin/clang-16 \
  -DCMAKE_CXX_COMPILER=/usr/bin/clang++-16 \
  -DCMAKE_C_FLAGS=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
  -DCMAKE_CXX_FLAGS=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
  -DLLVM_DIR=/usr/lib/llvm-16/lib/cmake/llvm \
  -DSVF_WARN_AS_ERROR=OFF -DSVF_ENABLE_ASSERTIONS=ON \
  -DBUILD_SHARED_LIBS=OFF
cmake --build Release-build --target wpa -j 24
```

产物为 `Release-build/bin/wpa` 和 `Release-build/lib/extapi.bc`。新增源码后重新执行配置命令。比较不同模式时统一使用相同的工具链、构建类型、断言设置和 extapi 文件。

例如，用 LOPA+CG SFR 分析 lua，并记录运行时间与峰值内存：

```sh
setarch "$(uname -m)" -R /usr/bin/time -v \
  Release-build/bin/wpa -lopa-cgfspta -cg-sfr=true \
  -ptd=mutable -node-alloc-strat=dense -ff-eq-base=true \
  -lopa-cg-store-policy=deferred \
  -extapi=/home/yhx/PTA/labv1/lib/extapi.bc \
  /home/yhx/PTA/labv1/benchmark/lua.bc \
  > lua.lopa-cg-sfr.log 2>&1
```

切换分析时替换表中的模式参数，其余参数保持一致。分析其他程序时，将最后的输入路径换成 LLVM 16 生成的 `.bc` 或 `.ll` 文件。单独使用本构建时，extapi 也可指定为 `Release-build/lib/extapi.bc`。

常用选项：

| 选项 | 用途 |
| --- | --- |
| `-print-pts` | 输出完整顶层 points-to 集合，用于正确性比较。 |
| `-cg-profile=true` | 输出 CG 的逐轮阶段时间和图规模，仅用于诊断。 |
| `-lopa-no-offline=true` | 关闭 LOPA 离线压缩，用于消融比较。 |
| `-vdg-stat` | 输出 LOPA 的 VDG 统计。 |
| `-vdg-pass-order=SPC` | 设置 LOPA 简化顺序，默认 `SPC`。 |
| `-help` | 查看完整参数列表。 |

CG 使用默认的 `-pre-field-sensitive=true`。LOPA+CG 使用默认的 `-opt-svfg=false`，并保持 `-vdg-pass-profile` 为空。SFR 采用显式字段表示，具体实现范围见 [SFR_IMPLEMENTATION.md](../../cgfspta/SFR_IMPLEMENTATION.md)。

LOPA+CG 的 Store 旧值保留规则由 `-lopa-cg-store-policy` 选择：

| 值 | 行为 |
| --- | --- |
| `deferred`（默认） | 等 Store 目标非空后，由共同求解器按强弱更新条件决定是否保留旧值。与纯 CG 对比时使用此值。 |
| `object-lower-bound` | 沿用 LOPA 对象下界规则，提前保留部分对象的旧值；仍受 `-lopa-obj-fs-lower-bound` 控制。 |

该选项只影响 `-lopa-cgfspta`。两种规则在空目标 Store 上可能产生不同结果，实验中需明确记录所选值。

构建后可运行 Store 策略和间接递归回归：

```sh
python3 tests/solver/check_store_policy.py Release-build/bin/wpa \
  --extapi /home/yhx/PTA/labv1/lib/extapi.bc
python3 tests/solver/check_indirect_recursion.py Release-build/bin/wpa \
  --extapi /home/yhx/PTA/labv1/lib/extapi.bc \
  --analysis=-lopa-cgfspta --flag=-cg-sfr=true
```

完整测试集位于 `/home/yhx/PTA/labv1/test/soundness/{simple,difficult}`，批量验证方法见[实验脚本说明](../../../labv1/cgfspta/integration/README.md)。使用该脚本前，将协议中的 `binary`、`extapi` 和模式参数配置为本次构建，并选择独立的结果目录。同一构建比较完整集合；跨构建出现节点编号差异时，按 IR 与字段身份归一化。平均、最大集合大小用于聚合核对，不能代替完整集合相等。

读取输出时，取最终分析的 `Pointer Analysis Stat` 段；前面的 Andersen 预分析也会输出 `TotalTime`。CG 计时含义如下：

| 指标 | 含义 |
| --- | --- |
| `TotalTime` | 分析构图、求解、导出和归一化时间，排除共享 Andersen、MemorySSA、SVFG 前分析。 |
| `CGConstructionTime` | CG 构图时间，LOPA+CG 中已包含离线压缩与导出。 |
| `LOPAOfflineTime`、`LOPAExportTime` | `CGConstructionTime` 的子项，不再额外相加。 |
| `CGSolveTime` | CG 求解时间。 |
| `/usr/bin/time -v` 的 wall time、峰值 RSS | 整个进程的时间和峰值内存，包含共享前分析。 |

性能比较使用相同输入、extapi、公共选项和资源限制，关闭 `-cg-profile`，保留关闭 ASLR 的设置。各分析进程为单线程，可跨程序和模式并行运行；同批重复测量后取中位数，并保存完整命令、二进制及输入散列、退出状态和原始日志。
