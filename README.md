# Uniform exclusion of Landau–Siegel zeros：Lean 形式化

本项目形式化论文正文的数学结果和证明依赖。主定理使用 Mathlib 的实际
Dirichlet L 函数，不含额外解析或算术假设。逐项范围和证明对应见
[PAPER_COVERAGE.md](PAPER_COVERAGE.md)；最终整库检查、
逐定理公理依赖和源码校验值见 `verification/status.json`、`verification/axioms.txt`。

2026-10-10 最终验证通过：整库编译成功，406 个公开定理全部通过公理依赖审计；
没有 `sorryAx` 或自定义公理，只使用 Lean 的标准基础公理。

原文为同目录的九页论文 `OpenAI - Uniform exclusion of Landau–Siegel zeros.pdf`，
正文日期 October 1, 2026。原始 PDF 未修改；另两篇 Quasi-RH PDF 不属于本项目。

## 主定理

入口是 [Main.lean](Siegel/Main.lean)。展开全部量词的定理名为
`Siegel.uniform_exclusion_of_landau_siegel_zeros`：

```lean
∃ c : ℝ, 0 < c ∧
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
    3 ≤ q → χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
    0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
      c ≤ (1 - β) * Real.log (q : ℝ)
```

常数 `c` 在导子、特征和零点之前量化。`χ.IsQuadratic` 表示特征值属于
`{0, 1, -1}`；与非主条件合用，表达这里的实二次特征条件。
`Siegel.uniformExclusion : Siegel.UniformExclusion` 是同一定理的简写版本。
`UniformExclusion` 本身是命题定义，其证明由上述两个 `theorem` 提供。

## 检查

工具链固定为 Lean `v4.30.0`，Mathlib 固定为 `v4.30.0`，精确提交在
`lake-manifest.json` 中。在项目目录运行：

```sh
bash scripts/verify.sh
```

脚本重新生成定理清单、编译整个库，对每条公开定理运行 `#print axioms`，并检查
原始 PDF 的校验值。允许的公理只有 `propext`、`Classical.choice`、`Quot.sound`。
工程证明没有使用 `sorry`、`admit` 或自定义公理，也没有把未证估计作为最终定理的参数。

也可以分别运行：

```sh
lake build
lake env lean Audit.lean
```

`verification/status.json` 记录审计时间、定理数量、最终证明名称及逐文件 SHA-256；
`verification/build.txt` 和 `verification/axioms.txt` 保存完整检查日志。

仓库包含完整源码、工具链及依赖锁文件；依赖和构建缓存由 Lake 获取。
安装 Lean 工具链管理器 elan 后，可在新机器上复现：

```sh
git clone https://github.com/AolinHAN/landau-siegel-lean.git
cd landau-siegel-lean
lake exe cache get
bash scripts/verify.sh
```

原始论文 PDF 和已通过的构建、公理审计记录一并保存在仓库中。

## 阅读入口

1. [Main.lean](Siegel/Main.lean)：主定理及全部量词。
2. [PaperZeroIdentity.lean](Siegel/PaperZeroIdentity.lean)：
   `paper_equation_two_three_complete`，原文 (2.3) 的真实非平凡零点重数、级数可和性、非负性和等式。
3. [SingleZeroBound.lean](Siegel/SingleZeroBound.lean)：
   保留实零点 β 的项，由全局公式推出 (2.4)。主定理现在使用这条解析路径。
4. [TorusInterpretation.lean](Siegel/TorusInterpretation.lean)：
   Remark 5 的 Euler 导子恒等式及矩形 multiplicity estimate。
5. [PAPER_COVERAGE.md](PAPER_COVERAGE.md)：
   全部 24 个编号公式、各个 Theorem/Lemma/Corollary/Remark 的文件和定理对应。

在 VS Code 中打开整个项目文件夹，再打开上述 `.lean` 文件；将光标放在证明步骤上，
Lean InfoView 显示当前目标，用 F12 追踪引用的引理。某处 `No goals` 只说明该处目标已关闭；
整库完成状态以验证脚本和公理审计为准。

## 本轮补齐的正文内容

| 原文内容 | 文件与定理 |
|---|---|
| (2.3) 的全局零点公式，真实重数、收敛、非负性 | `PaperZeroIdentity.lean`：`paper_equation_two_three_complete`；`NontrivialZeros.lean` |
| 完成函数、函数方程、增长界、Γ 因子及两种奇偶性的一致界 | `CompletedLFunction.lean`、`CompletedGrowth.lean`、`CompletedLogDerivative.lean` |
| 原文完成函数的精确归一化和实轴 Γ′/Γ 记号 | `PaperCompletion.lean`、`PaperRealIdentity.lean` |
| 由 (2.3) 保留 β 项得到 (2.4) | `SingleZeroBound.lean`：`logDerivativeUpper_from_global_zeros` |
| Mertens 双边绝对误差 | `MertensTwoSided.lean`：`exists_mertens_absolute_error_bound` |
| ζ 对数导数极点的绝对误差 | `ZetaPoleError.lean`：`exists_zeta_logDerivative_absolute_error_bound` |
| Remark 5 的实际 Euler 导子与插值重述 | `TorusInterpretation.lean`：`remark_five_identity`、`rectangular_multiplicity_estimate` |
| 所有 q≥3 的平方自由 d、大小界、二次域与 Legendre 字符对应 | `SquarefreeCharacter.lean`：`exists_squarefree_character_radical`；`SectionFour.lean` |
| d≠1,2 时四生成元独立，实际数域次数与 Galois 自同构 | `SquarefreeIndependence.lean`、`BiquadraticFieldDegree.lean`、`BiquadraticField.lean` |
| 任意固定实 γ>0 的 N=⌈q^γ⌉、全部参数极限和最终矛盾 | `CeilingParameters.lean`：`ceilingCutoff_log_ratio_tendsto`、`ceiling_comparison_impossible` |
| 实值字符与 IsQuadratic 的等价，以及显式实值条件的主定理 | `RealCharacter.lean`、`RealCharacterMain.lean` |

此前已有的 Lemma 2、Lemma 3、Corollary 4、Lemma 6、Lemma 7、行列式上下界、
有限导子处理和最终统一间隙定理继续保留；详细对应在覆盖表中。

## 证明实现与范围

全局式 (2.3) 已有独立证明：完成函数的全局增长界 → 任意大圆盘的 Jensen 零点计数
与逆 Blaschke 因子 → 对数导数差的极限 → 非负实部级数可和 → 函数方程的反射配对
消去常数。它证明原文的零点恒等式，不另行构造无穷 Hadamard 乘积；
也不声称未经正规化的复数级数 Σρ 1/(s−ρ) 绝对收敛。

`nontrivialZeroMultiplicity` 直接取实际 `χ.LFunction` 在开临界带中的解析重数。
已证明它等于完成函数的零点 divisor；`PaperCompletion.lean` 另外定义原文精确归一化的
完成函数，并证明它与计算中使用的版本具有相同零点重数和对数导数。
没有把“零点和”定义成想要证明的等式右端。

旧的局部圆盘证明保留在 `LogDerivativeUpper.lean` 等模块中。算术主线可使用符号导子，
同时提供平方自由根式版本；最终参数可选择原文允许的整数幂 `N=q^k`，同时另证任意固定
实指数的 ceiling 版本。这些实现差别没有增加最终定理的假设。

这里的完成范围是正文数学结果及实际依赖，允许完整的等价证明；不是自然语言逐行转写，
也不宣称重新形式化引言引用的全部文献、基本判别式分类或一般 Galois 理论。
