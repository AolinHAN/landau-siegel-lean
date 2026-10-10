# 论文正文与 Lean 工程逐项对应

核对对象是项目中的九页论文 `OpenAI - Uniform exclusion of Landau–Siegel zeros.pdf`。本表按正文的公式编号和主命题组织，供从论文追踪 Lean 定义、定理及证明使用。

**验证状态：2026-10-10 整库编译及 406 个公开定理的公理依赖审计全部通过；无 `sorryAx` 或自定义公理，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。原论文 PDF 校验值保持不变。**

这里的“覆盖”指正文数学结果及其证明依赖的形式化，允许以证明同一结论的完整论证替代原文某一步；它不表示逐行翻译自然语言、图注和文献评论。表中的 `def` 是数学对象或命题的定义，`theorem` 才是相应证明入口。最终验证结果应以 [verification/status.json](verification/status.json) 及整库检查记录为准，不能仅凭本表判断编译状态。

表内定理名省略共同前缀 `Siegel.`。例如 `Interpolation.rectangular_interpolation` 的完整名称是 `Siegel.Interpolation.rectangular_interpolation`。文件中的辅助引理可通过编辑器“转到定义”继续追踪。

## 主结论与解析部分：§§1–2

| 论文位置 | 文件与实际入口 | 对应内容与编码说明 |
|---|---|---|
| Theorem 1；(1.1) | [Statement.lean](Siegel/Statement.lean)：`logGap`、`AdmissibleZero`、`UniformExclusion`；[Main.lean](Siegel/Main.lean)：`uniformExclusion`、`uniform_exclusion_of_landau_siegel_zeros` | 统一的正数先于所有导子、特征和零点量化。使用 Mathlib 的实际解析延拓 `χ.LFunction`；入口没有待证模型或解析输入，也没有零点简单性假设。 |
| 实本原非主特征，导子 `q≥3` | [RealCharacter.lean](Siegel/RealCharacter.lean)：`isQuadratic_iff_im_eq_zero`；[RealCharacterMain.lean](Siegel/RealCharacterMain.lean)：`uniform_exclusion_for_real_characters` | 证明 `χ.IsQuadratic` 与所有值虚部为零严格等价，并提供采用显式实值条件的主定理。`χ.IsPrimitive` 表示给定模数就是导子，`[NeZero q]` 与 `q≥3` 相容。 |
| `L(s,χ)` 的级数、解析延拓和 `L(1,χ)≠0` | [AnalyticBridge.lean](Siegel/AnalyticBridge.lean)、[Statement.lean](Siegel/Statement.lean)；Mathlib 的 `DirichletCharacter.LFunction` 及其级数、可微性、非零定理 | 复用 Mathlib 已定义的函数及其性质，没有另造一个满足目标结论的函数。 |
| Lemma 2；(2.1)、(2.2) | [PrimeBias.lean](Siegel/PrimeBias.lean)：`PrimeBiasStatement`；[LogDerivativeUpper.lean](Siegel/LogDerivativeUpper.lean)：`primeBias`；[PrimeBiasAssembly.lean](Siegel/PrimeBiasAssembly.lean)：`primeBias_of_logDerivative_upper` | 绝对常数 `C` 在 `H,q,χ,β,X` 前量化；`C_H` 只依赖 `H`。`X` 是实数，有限素数和通过自然数取整准确表达 `p≤X`。 |
| `ε=(1−χ(−1))/2` | [CompletedLogDerivative.lean](Siegel/CompletedLogDerivative.lean)：`dirichletParity`、`dirichletParity_cases`、`dirichletParity_eq_character` | 两种 parity 与原文特征值表达式相接。 |
| 完成函数、函数方程、零点所在带 | [CompletedLFunction.lean](Siegel/CompletedLFunction.lean)：`completedDirichlet`、`differentiable_completedDirichlet`、`completedDirichlet_reflection`、`rootNumber_ne_zero_of_quadratic`、`completedDirichlet_zero_re_mem_Ioo` | 使用真实完成函数。工程归一化与原文 `Λχ` 相差一个非零常数 `q^(ε/2)`；对数导数和零点重数不受这一常数影响。 |
| 原文 `Λχ=(q/π)^((s+ε)/2)Γ((s+ε)/2)L(s,χ)` | [PaperCompletion.lean](Siegel/PaperCompletion.lean)：`paperCompletedDirichlet_eq_formula`、`logDeriv_paperCompletedDirichlet`、`divisor_paperCompletedDirichlet` | 另行定义原文的精确归一化，在 `Re s>0` 证明显示乘积公式；证明非主特征的完成函数为整函数，并与全局求和所用版本具有相同的对数导数和零点重数。 |
| 完成函数与普通 `L` 的对数导数和零点重数桥接 | [CompletedLogDerivative.lean](Siegel/CompletedLogDerivative.lean)：`real_logDeriv_completedDirichlet_eq`、`meromorphicOrderAt_completedDirichlet_eq_of_re_pos`、`divisor_completedDirichlet_eq_of_re_pos` | 精确得到导子项 `½log(q/π)` 和 Gamma 项，并保持实际解析零点的重数。 |
| (2.3)，包括逐项非负与收敛 | [PaperZeroIdentity.lean](Siegel/PaperZeroIdentity.lean)：**`paper_equation_two_three_complete`**、`nontrivial_zero_sum`、`nontrivial_zero_summand_nonneg` | 入口同时陈述零点项非负、实部项级数可求和，以及原文的精确等式。求和指标遍历 `ℂ`，以实际非平凡零点重数作权；不在非平凡零点处的权重为零。没有把零点和定义成目标等式的右端。 |
| (2.3) 的实轴记号：`L′/L` 为实数，Γ 为实 Gamma 函数 | [PaperRealIdentity.lean](Siegel/PaperRealIdentity.lean)：`paper_equation_two_three_real_axis`；[GammaRealLogDerivative.lean](Siegel/GammaRealLogDerivative.lean)：`real_logDeriv_Gamma_eq` | 证明复 `L′/L` 等于其实际实值，并将复 Gamma 对数导数的实部识别为实 Gamma 的对数导数。 |
| (2.3) 中“非平凡零点，按重数求和” | [NontrivialZeros.lean](Siegel/NontrivialZeros.lean)：`nontrivialZeroMultiplicity`、`nontrivialZeroMultiplicity_ne_zero_iff`、`completed_divisor_eq_nontrivialZeroMultiplicity`；[CompletedZeroMultiplicity.lean](Siegel/CompletedZeroMultiplicity.lean) | 权重来自 `χ.LFunction` 的 divisor，并限制于开临界带；证明其非零当且仅当该点是真正的非平凡零点，再证明它与完成函数的 divisor 相同。 |
| (2.3) 中消去 Hadamard 实常数的论证 | [GlobalLogDerivativeLimit.lean](Siegel/GlobalLogDerivativeLimit.lean)：`tendsto_disk_logDeriv_difference_re`；[RadialZeroSums.lean](Siegel/RadialZeroSums.lean)：`summable_divisor_mul_of_radial_limit`；[ReflectedZeroSums.lean](Siegel/ReflectedZeroSums.lean)：`divisor_reflection`、`tsum_reflected_zero_kernel`；[SymmetricZeroSum.lean](Siegel/SymmetricZeroSum.lean)：`symmetric_real_zero_sum` | 用有限圆盘的部分分式展开、增长控制和函数方程反射证明同一全局实部恒等式。先得到两个点的对数导数差，再用反射消去常数；可求和性从非负径向和的有限极限推出，未把全局可求和性作为待证假设。 |
| 完成函数满足全局公式所需增长条件 | [CompletedGrowth.lean](Siegel/CompletedGrowth.lean)：`exists_completedDirichlet_log_growth`；[GlobalZeroFormula.lean](Siegel/GlobalZeroFormula.lean)：`completed_zero_sum`、`paper_equation_two_three` | 对真实完成函数证明 `log‖F‖=O(R log R)` 型上界，再实例化通用公式。增长常数可依赖固定特征；这不改变后续精确恒等式。 |
| 将非零基点 `2` 移到 `0` 的辅助函数 | [ZeroSumTranslation.lean](Siegel/ZeroSumTranslation.lean)：`divisor_translate_univ`、`logDeriv_translate`、`summable_zero_kernel_translate_iff`、`tsum_zero_kernel_translate` | `F(z)=completedDirichlet χ (z+2)` 只用于圆盘论证。平移对 divisor、重数、求和和对数导数的影响均有独立桥接。 |
| `1<s≤2` 上两个 parity 的 Gamma 项一致有界 | [CompletedLogDerivative.lean](Siegel/CompletedLogDerivative.lean)：`exists_gamma_logDerivative_parity_bound` | 对两个 parity 的相关实紧区间给出共同界，不把该界写成外部假设。 |
| `−ζ′/ζ(s)=1/(s−1)+O(1)` | [ZetaPoleError.lean](Siegel/ZetaPoleError.lean)：`exists_zeta_logDerivative_absolute_error_bound`；[ZetaPoleBound.lean](Siegel/ZetaPoleBound.lean)：`exists_zeta_logDerivative_error_bound` | 补有绝对误差版本；原先上界版本也保留。 |
| 保留实零点 `β` 的单项 | [CompletedZeroMultiplicity.lean](Siegel/CompletedZeroMultiplicity.lean)：`one_le_divisor_completedDirichlet_of_zero`、`real_zero_term_le_completed_zero_sum` | 不假设零点简单：其重数至少为一，因此整个非负零点和至少是 `1/(s−β)`。 |
| (2.4)，沿原文全局零点和路径 | [SingleZeroBound.lean](Siegel/SingleZeroBound.lean)：**`logDerivativeUpper_from_global_zeros`** | 将 (2.3)、Gamma 统一界、ζ 极点误差和保留 `β` 的单项接起来。 |
| (2.4)，原有局部圆盘替代证明 | [LogDerivativeUpper.lean](Siegel/LogDerivativeUpper.lean)：`logDerivativeUpper`；[LFunctionLogDerivative.lean](Siegel/LFunctionLogDerivative.lean) | 保留此前基于 Jensen、Blaschke 因子和全纯对数的独立证明；并非用该替代证明代替本轮新增的 (2.3)。 |
| Euler 非负级数及 split 素数和下界 | [AnalyticBridge.lean](Siegel/AnalyticBridge.lean)：`mangoldtCombination_summable`、`mangoldtCombination_LSeries_eq`、`logDerivativeCombination_nonneg`；[EulerPrimeComparison.lean](Siegel/EulerPrimeComparison.lean)：`splitPrimeSum_le_euler` | 包括实际 von Mangoldt 级数可求和，以及系数 `2/e`。 |
| `s=1+1/log X` 及两个分母之差 | [Estimates.lean](Siegel/Estimates.lean)：`reciprocal_difference`、`reciprocal_difference_le`、`reciprocal_at_log_scale` | 对应 Lemma 2 中的精确恒等式和上界。 |
| `Σ_{p≤X} log p/p = log X+O(1)` | [MertensTwoSided.lean](Siegel/MertensTwoSided.lean)：`mertens_upper_nat`、`exists_mertens_absolute_error_bound`；[MertensLower.lean](Siegel/MertensLower.lean)：`exists_mertens_lower_constant` | 包含双侧绝对误差，超出旧版仅供主证明使用的下界。 |
| `Σ_{p∣q} log p/p≤log q`；去掉 `p≤H` | [PrimePartition.lean](Siegel/PrimePartition.lean)：`prime_divisor_weight_sum_le`、`prime_partition_bound`、`exists_inert_lower_from_split_constant` | 对应 (2.2) 中的分割、导子误差和仅依赖 `H` 的误差。 |

## 插值与环面解释：§3

| 论文位置 | 文件与实际入口 | 对应内容与编码说明 |
|---|---|---|
| Lemma 3；(3.1) | [Interpolation.lean](Siegel/Interpolation.lean)：`Interpolation.interpolationStatement`；[InterpolationTheorem.lean](Siegel/InterpolationTheorem.lean)：`Interpolation.rectangular_interpolation` | 保留 `N≥1`、核向量的有理线性无关、分离次数及严格乘积不等式。次数以自然数编码，与原文下界一致。 |
| (3.2) | [InterpolationTheorem.lean](Siegel/InterpolationTheorem.lean)：`Interpolation.dual_eq_coordinate_sum`、`Interpolation.exists_nonzero_coordinate_of_dual` 及主证明中的对偶构造 | 从非满射取得真正非零的对偶向量，并证明它消去全部规定次数的多项式评价。 |
| (3.3) | [InterpolationPolynomial.lean](Siegel/InterpolationPolynomial.lean)：`Interpolation.exists_nonzero_vanishing_polynomial`、`Interpolation.exists_integer_nonzero_of_surjective`；[BoxHull.lean](Siegel/BoxHull.lean) | 维数计数构造非零 `R`。实现令其在包含 `4P` 的整个有限整数盒上消失，是保持原维数界的加强。 |
| 最近点与 (3.4) | [ConvexGeometry.lean](Siegel/ConvexGeometry.lean)：`Interpolation.exists_closest_nonzero_lattice_point`、`Interpolation.closest_point_supporting`、`Interpolation.supporting_vertex_sub_mem_three_hull` | 最近点存在、支撑超平面、至多四点的凸组合及 `y−u∈3P`。 |
| (3.5) | [Interpolation.lean](Siegel/Interpolation.lean)：`Interpolation.translated_distance_decrease`；[ConvexGeometry.lean](Siegel/ConvexGeometry.lean)：`Interpolation.translated_value_eq_zero` | 精确平方距离展开与严格下降。 |
| (3.6)；有理支撑面 | [FaceReduction.lean](Siegel/FaceReduction.lean)：`Interpolation.rational_face_reduction`；[RationalFace.lean](Siegel/RationalFace.lean)：`Interpolation.exists_rational_normal`、`Interpolation.complexifyNormal_transverse` | 移位消失和横截性；以有理法向量编码原文清分母后的整数超平面。 |
| `A` 在超平面上的仿射双射；Lagrange 多项式 `Q` | [Interpolation.lean](Siegel/Interpolation.lean)：`Interpolation.hyperplane_preimage_existsUnique`；[LagrangeFace.lean](Siegel/LagrangeFace.lean)：`Interpolation.exists_face_selector` | 选择单个顶点并控制总次数 `≤3(N−1)`。 |
| `B=Q·R(·+A(m−u))` 与最终孤立项矛盾 | [InterpolationPolynomial.lean](Siegel/InterpolationPolynomial.lean)：`Interpolation.degreeOf_translatePolynomial_le`；[InterpolationTheorem.lean](Siegel/InterpolationTheorem.lean)：`Interpolation.rectangular_interpolation` | 逐坐标次数、面外与面内消失，以及最后仅剩非零一项的求和矛盾均在证明内。 |
| Corollary 4 | [InterpolationBudgets.lean](Siegel/InterpolationBudgets.lean)：`Interpolation.degreeBudget`、`Interpolation.degreeBudget_lower`、`Interpolation.degreeBudget_product`、`Interpolation.floor_budget_hypotheses`、`Interpolation.uniform_budget_interpolation` | 保留原常数 `32` 以及三个实数次数预算和取整论证；界不依赖 `A`。 |
| Remark 5 | [TorusInterpretation.lean](Siegel/TorusInterpretation.lean)：`Torus.euler`、`Torus.euler_leibniz`、`Torus.euler_commute`、`Torus.remark_five_identity`、`Torus.rectangular_multiplicity_estimate`、`Torus.exists_nonzero_rectangular_jet` | 用真实 `MvPolynomial`、偏导数 `pderiv` 和 `D_j=Σ_i A_{ji}X_i∂_i`，证明混合导数在全一元组的值为 `(An)^α`，并推出矩形重数估计。正文使用 `n∈E_N⊂ℕ⁴`，普通多项式限制到复环面已覆盖此处内容；不宣称另建所有负整数指数的 Laurent 理论。 |

## 代数模型与加权行：§4

| 论文位置 | 文件与实际入口 | 对应内容与编码说明 |
|---|---|---|
| 实二次特征对应根式、导子大小与 Legendre 值 | [PrimitiveGaussSum.lean](Siegel/PrimitiveGaussSum.lean)、[QuadraticCharacter.lean](Siegel/QuadraticCharacter.lean)：`primitive_quadratic_eq_legendre`、`exists_signed_conductor_radical`；[QuadraticModel.lean](Siegel/QuadraticModel.lean)：`quadraticModel` | 通过本原 Gauss 和与 Frobenius 独立构造后续需要的特征实现，替代引用基本判别式分类的证明方式。 |
| 所有 `q≥3` 下取 squarefree `d`，`|d|≤q`，保持二次域与 Legendre 值 | [SquarefreeCharacter.lean](Siegel/SquarefreeCharacter.lean)：`exists_squarefree_character_radical`；[SquarefreeModel.lean](Siegel/SquarefreeModel.lean)：`exists_squarefree_part`、`adjoin_singleton_div_nat` | 剥离平方因子，同时保留大小、生成域及所有相关素数的 Legendre 符号，没有足够大导子的额外限制。 |
| 排除 `d=2`；四个根式有理线性无关 | [SquarefreeIndependence.lean](Siegel/SquarefreeIndependence.lean)：`biquadratic_linearIndependent_of_squarefree`；[SectionFour.lean](Siegel/SectionFour.lean)：`section_four_data` | 平方自由 `d≠1,2` 直接保证 `1,a,b,ab` 有理线性无关。全导子模型精确保留原文暂时排除的 `d=2` 情形。 |
| `K=ℚ(a,b)` 的次数 4 和 Galois 性 | [BiquadraticFieldDegree.lean](Siegel/BiquadraticFieldDegree.lean)：`Biquadratic.field_finrank`、`Biquadratic.field_isGalois`、`Biquadratic.field_card_aut` | 对实际 `IntermediateField.adjoin ℚ {a,b}` 证明次数为 4、Galois 性及自同构数为 4。 |
| `σ(a)=−a, σ(b)=b, τ(a)=a, τ(b)=−b` 生成 Galois 群 | [BiquadraticField.lean](Siegel/BiquadraticField.lean)：`Biquadratic.fieldAutSigns_bijective`、`Biquadratic.exists_field_automorphisms`；[SectionFour.lean](Siegel/SectionFour.lean)：`section_four_data` | 四种符号与实际域自同构一一对应；证明 `σ²=τ²=1`、交换性及 `1,σ,τ,στ` 穷尽全部自同构。全导子定理将原文平方自由模型与这些域论结论合并。 |
| `R=ℤ[a,b]`、唯一四坐标、四共轭及整数范数 | [BiquadraticRing.lean](Siegel/BiquadraticRing.lean)：`Biquadratic.coordinate_expression`、`Biquadratic.embed_injective`、`Biquadratic.norm_eq_polynomial`、`Biquadratic.norm_eq_embeddings_product` | 使用具体的迭代二次代数与嵌入实现原文所用的环、共轭和范数运算，不把抽象域模型当作外部假设。 |
| (4.1) | [Algebra.lean](Siegel/Algebra.lean)：`conjugateMatrix`、`conjugateKernel`、`conjugateMinor_det`、`conjugateMatrix_rank`；[ConjugateProjection.lean](Siegel/ConjugateProjection.lean)：`conjugateProjection_ker`、`conjugateKernel_linearIndependent`、`conjugateProjection_boxPoint` | 原矩阵、`4ab` 子式、秩三、核及三个共轭评价均有具体表达。 |
| (4.2) | [RowSelection.lean](Siegel/RowSelection.lean)：`WeightedRows.monomialRow`；[RowReplacement.lean](Siegel/RowReplacement.lean)：`rawRow`；[IntegralDeterminant.lean](Siegel/IntegralDeterminant.lean)：`Biquadratic.rawRow_images` | 行是原始单项式评价行；辅助插值多项式的系数不进入最终行列式。 |
| 加权贪心选择；(4.3) | [GreedyBasis.lean](Siegel/GreedyBasis.lean)：`WeightedRows.exists_weighted_basis`；[RowSelection.lean](Siegel/RowSelection.lean)：`WeightedRows.select_weighted_monomial_rows`；[SelectedIntegral.lean](Siegel/SelectedIntegral.lean)：`Biquadratic.exists_selected_exponents`；[IntegralDeterminant.lean](Siegel/IntegralDeterminant.lean)：`Biquadratic.evaluationNorm_ne_zero` | 选出恰好 `N^4` 行、证明非零行列式及严格降权行的先前 span 性质，再接到同一个整数范数。 |
| Lemma 6；(4.4) | [ScaledRows.lean](Siegel/ScaledRows.lean)：`WeightedRows.lemma_six`；[SelectedIntegral.lean](Siegel/SelectedIntegral.lean)：`Biquadratic.selected_exponents_moments` | 保留 `c₀=(4·97²)⁻¹`、`C₀=192`，并显式陈述充分大的 `N` 条件。 |
| Lemma 6 中的纤维容量与一阶矩计数 | [WeightedRows.lean](Siegel/WeightedRows.lean)：`WeightedRows.first_moment_lower_of_fiber_capacity`、`WeightedRows.first_coordinate_fiber_card`、`WeightedRows.first_coordinate_sum_lower`；[RowMoments.lean](Siegel/RowMoments.lean) | 用阈值亏损计数证明同一一阶矩下界，不要求照抄原文排序后的商余数计算。 |

## 同一整数范数的两个界：§5

| 论文位置 | 文件与实际入口 | 对应内容与编码说明 |
|---|---|---|
| 四嵌入点大小 `≤8N√q`；(5.1) | [Archimedean.lean](Siegel/Archimedean.lean)：`thetaPoint_norm_le_conductor`、`four_conjugate_archimedean_bound`；[Hadamard.lean](Siegel/Hadamard.lean)：`complex_hadamard`；[IntegralDeterminant.lean](Siegel/IntegralDeterminant.lean)：`Biquadratic.evaluationNorm_archimedean` | 保留 `8`、`M/2·log M` 和 `(S₁+S₂)(log N+½log q+log 8)`；正负 `d` 均适用。 |
| Euler 判别；(5.2) | [Frobenius.lean](Siegel/Frobenius.lean)：`euler_criterion_dvd`、`square_root_frobenius_dvd`、`inert_frobenius_alternatives`；[BiquadraticPoints.lean](Siegel/BiquadraticPoints.lean)：`Biquadratic.points_frobenius_alternatives` | 证明实际整数代数中的模 `p` 整除关系，并处理两种 Frobenius 共轭。 |
| Lemma 7；(5.3) | [RowReplacement.lean](Siegel/RowReplacement.lean)：`secondReplacement_determinant_dvd`、`thirdReplacement_determinant_dvd`；[IntegralDeterminant.lean](Siegel/IntegralDeterminant.lean)：`Biquadratic.evaluationNorm_prime_dvd` | 从替换行条目的整除推出行列式及其整数范数的素数幂整除。 |
| (5.4) | [Algebra.lean](Siegel/Algebra.lean)：`row_replacement_expansion`、`rowWeight_replace_second_lt`、`rowWeight_replace_third_lt`；[RowReplacement.lean](Siegel/RowReplacement.lean)：`secondReplacement_sub` | 精确二项式展开、指数变化和严格降权。 |
| (5.5) | [WeightedTriangular.lean](Siegel/WeightedTriangular.lean)：`determinant_eq_of_weight_lower_span`、`determinant_dvd_of_weight_lower_span`；[RowReplacement.lean](Siegel/RowReplacement.lean)：`secondReplacement_det_eq` | 行列式不变在域中证明，整除来自整数环中的替换条目；不额外假设三角变换矩阵有整数系数。 |
| (5.6) | [IntegerNormBounds.lean](Siegel/IntegerNormBounds.lean)：`integer_norm_log_lower`、`determinant_norm_prime_lower`；[Estimates.lean](Siegel/Estimates.lean)：`weighted_floor_lower` | 合并不同素数的幂次整除，并逐行使用取整下界。 |
| Chebyshev 误差；(5.7) | [IntegralDeterminant.lean](Siegel/IntegralDeterminant.lean)：`Biquadratic.evaluationNorm_inert_lower`；[SelectedIntegral.lean](Siegel/SelectedIntegral.lean)：`Biquadratic.exists_determinant_comparison`；Mathlib `Chebyshev.theta_le_log4_mul_x` | 将 Lemma 2 接到同一 `evaluationNorm` 的下界；Chebyshev 项可显式取 `log 4·MU`。 |

## 参数选择与最终矛盾：§6

| 论文位置 | 文件与实际入口 | 对应内容与编码说明 |
|---|---|---|
| (6.1) | [Statement.lean](Siegel/Statement.lean)：`fixed_character_gap_lower_bound`、`finite_family_gap_lower_bound`；[AnalyticBridge.lean](Siegel/AnalyticBridge.lean)：`bounded_conductor_gap_lower_bound`、`counterexample_sequence_of_not_uniform` | 从主定理的否定构造 `q→∞`、`δ→0` 的反例序列；包含有限导子和 `L(1,χ)≠0` 的处理。 |
| (6.2) 及分母正性 | [Estimates.lean](Siegel/Estimates.lean)：`comparison_normalization`；[ScalarComparison.lean](Siegel/ScalarComparison.lean)：`scalar_comparison_normalization`；[MainReduction.lean](Siegel/MainReduction.lean) | 先证明正性再归一化，并将 `S₂/S₁≤1/12` 代入等价的标量比较式。 |
| 先固定绝对整数 `H` | [Estimates.lean](Siegel/Estimates.lean)：`explicit_weight_choice`；[MainReduction.lean](Siegel/MainReduction.lean) | 可取 `H=86713344=12·192·4·97²`；选择先于导子和零点。 |
| 任意固定实数 `γ>0`，`N=⌈q^γ⌉` | [CeilingParameters.lean](Siegel/CeilingParameters.lean)：`ceilingPower`、`ceilingPower_tendsto`、`ceilingPower_ratio_tendsto`、`ceilingPower_log_ratio_tendsto` | 单独处理原文的实指数与 ceiling，相对取整误差趋于零。 |
| `U=N^(4/3)`，`log U/log q→4γ/3` | [CeilingParameters.lean](Siegel/CeilingParameters.lean)：`ceilingCutoff`、`ceilingCutoff_tendsto`、`ceilingCutoff_log_ratio_tendsto` | 对应原文显示的渐近式，不仅是整数指数特例。 |
| 固定 `γ` 后零点项及全部误差趋零，`1≤7/8` 矛盾 | [CeilingParameters.lean](Siegel/CeilingParameters.lean)：`ceilingCutoff_zero_term_tendsto`、`ceiling_comparison_impossible` | 对一般固定正实指数形式化归一化后的完整极限矛盾。 |
| 主证明采用的整数幂特例与最终装配 | [ParameterLimit.lean](Siegel/ParameterLimit.lean)：`exists_power_exponent`、`power_comparison_impossible`；[MainReduction.lean](Siegel/MainReduction.lean)：`uniformExclusion_of_primeBias_and_models`；[QuadraticModel.lean](Siegel/QuadraticModel.lean)：`uniformExclusion_of_logDerivative_upper`；[Main.lean](Siegel/Main.lean) | 主证明可保留 `N=q^k` 的合法选择；另外提供的实指数 ceiling 定理覆盖原文更一般的参数写法。所有中间模型输入在最终入口由已证结果消去。 |

## 范围及阅读边界

1. **两条解析路径均保留。** 旧的局部圆盘证明足以证明主定理；本轮新增的是原文全局式 (2.3)、真实非平凡零点重数、收敛与非负性，以及由它导出 (2.4) 的路径。不能把旧路径完成误说成此前已有 (2.3)。
2. **等价实现与原文记号不同。** 有理支撑超平面替代清分母后的整数写法，Gauss 和构造提供判别式分类在后续实际使用的特征实现。实际双二次域的次数和 Galois 自同构也有独立定理；整数范数计算使用与其四共轭一致的具体整数代数。工程没有宣称另行建立完整的基本判别式分类或一般 Galois 理论教材。
3. **收敛对象是实部项的重数加权级数。** 本表不宣称复数级数 `Σρ 1/(s−ρ)` 未经配对或正规化就绝对收敛。(2.3) 的正式入口明确使用 `Summable` 检查原文实际要求的实部项。
4. **引言文献背景不计作全部重证。** 经典零点区域、Siegel/Page 定理、Deuring–Heilbronn 现象、类数公式，以及 Laurent、Bost、Philippon、Fischler 等文献的历史和方法比较属于原文引用背景。本工程的范围是正文的具体数学结果、其实际依赖和上述明确列出的补充；不宣称把所有参考文献再形式化一遍。
5. **本表不代替内核检查。** 本次整库验证已检查主定理展开陈述、所有公开定理的公理依赖和源文件对应关系。日后修改证明源码后，应重新运行 `bash scripts/verify.sh` 并以新生成的验证记录为准。
