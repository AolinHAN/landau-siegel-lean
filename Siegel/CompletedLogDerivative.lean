import Siegel.CompletedGrowth
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

namespace Siegel

open Set Filter
open scoped Topology

open scoped Classical in
/-- The parity parameter appearing in the archimedean factor. -/
noncomputable def dirichletParity {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ :=
  if χ.Even then 0 else 1

/-- A real character has one of the two ordinary parity parameters. -/
theorem dirichletParity_cases {q : ℕ} (χ : DirichletCharacter ℂ q) :
    dirichletParity χ = 0 ∨ dirichletParity χ = 1 := by
  classical
  unfold dirichletParity
  split_ifs <;> simp

/-- Parity notation agrees with mathlib's gamma factor. -/
theorem gammaFactor_eq_parity {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    χ.gammaFactor s = Complex.Gammaℝ (s + (dirichletParity χ : ℂ)) := by
  classical
  by_cases h : χ.Even <;> simp [DirichletCharacter.gammaFactor, dirichletParity, h]

/-- The gamma function is holomorphic on the positive half-plane. -/
theorem analyticAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  filter_upwards [hU.mem_nhds hs] with z hz
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hh := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hh
  have := Nat.cast_nonneg (α := ℝ) m
  linarith

/-- Differentiability of the real gamma factor away from its poles. -/
theorem differentiableAt_GammaReal_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hh : 0 < (s / 2).re := by simp only [Complex.div_ofNat_re]; positivity
  exact (((differentiableAt_id.neg).div_const (2 : ℂ)).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
    ((analyticAt_Gamma_of_re_pos hh).differentiableAt.comp s
      (differentiableAt_id.div_const (2 : ℂ)))

/-- Exact logarithmic derivative of the normalized real gamma factor. -/
theorem logDeriv_GammaReal_eq {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -Complex.log (Real.pi : ℂ) / 2 +
      logDeriv Complex.Gamma (s / 2) / 2 := by
  have hh : 0 < (s / 2).re := by simp only [Complex.div_ofNat_re]; positivity
  have hpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hA := (((hasDerivAt_id s).neg).div_const (2 : ℂ)).const_cpow
    (c := (Real.pi : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  simp only [Pi.neg_apply, id_eq] at hA
  have hB := (analyticAt_Gamma_of_re_pos hh).differentiableAt
  change logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s = _
  rw [logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z : ℂ => Complex.Gamma (z / 2)) s hpow (Complex.Gamma_ne_zero_of_re_pos hh) hA.differentiableAt
    (hB.comp s (differentiableAt_id.div_const (2 : ℂ)))]
  have hLA : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -Complex.log (Real.pi : ℂ) / 2 := by
    rw [logDeriv_apply, hA.deriv]
    field_simp [hpow]
  have hLB : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
      logDeriv Complex.Gamma (s / 2) / 2 := by
    change logDeriv (Complex.Gamma ∘ (fun z : ℂ => z / 2)) s = _
    rw [logDeriv_comp (g := fun z : ℂ => z / 2) (x := s) hB
      (differentiableAt_id.div_const (2 : ℂ)),
      show deriv (fun z : ℂ => z / 2) s = 1 / 2 by simpa using
        (hasDerivAt_id s |>.div_const (2 : ℂ)).deriv]
    ring
  rw [hLA, hLB]

/-- The parity-dependent gamma factor is differentiable on the positive half-plane. -/
theorem differentiableAt_gammaFactor_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ χ.gammaFactor s := by
  have he : χ.gammaFactor = fun z => Complex.Gammaℝ (z + (dirichletParity χ : ℂ)) :=
    funext (gammaFactor_eq_parity χ)
  rw [he]
  apply (differentiableAt_GammaReal_of_re_pos (s := s + (dirichletParity χ : ℂ)) ?_).comp s
    (differentiableAt_id.add_const _)
  rcases dirichletParity_cases χ with hp | hp <;> simp [hp] <;> linarith

/-- Exact archimedean logarithmic derivative with the parity parameter. -/
theorem logDeriv_gammaFactor_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    logDeriv χ.gammaFactor s = -Complex.log (Real.pi : ℂ) / 2 +
      logDeriv Complex.Gamma ((s + (dirichletParity χ : ℂ)) / 2) / 2 := by
  have hp : 0 < (s + (dirichletParity χ : ℂ)).re := by
    rcases dirichletParity_cases χ with hp | hp <;> simp [hp] <;> linarith
  have he : χ.gammaFactor = Complex.Gammaℝ ∘ (fun z : ℂ => z + (dirichletParity χ : ℂ)) :=
    funext (gammaFactor_eq_parity χ)
  rw [he, logDeriv_comp (g := fun z : ℂ => z + (dirichletParity χ : ℂ)) (x := s)
    (differentiableAt_GammaReal_of_re_pos hp) (differentiableAt_id.add_const _),
    show deriv (fun z : ℂ => z + (dirichletParity χ : ℂ)) s = 1 by simpa using
      (hasDerivAt_id s |>.add_const (dirichletParity χ : ℂ)).deriv, mul_one,
    logDeriv_GammaReal_eq hp]

/-- The conductor factor contributes exactly one half of log(q). -/
theorem logDeriv_conductor_factor {q : ℕ} [NeZero q] (s : ℂ) :
    logDeriv (fun z : ℂ => (q : ℂ) ^ (z / 2)) s = Complex.log (q : ℂ) / 2 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hd := ((hasDerivAt_id s).div_const (2 : ℂ)).const_cpow (c := (q : ℂ)) (Or.inl hq)
  simp only [id_eq] at hd
  rw [logDeriv_apply, hd.deriv]
  have hpow : (q : ℂ) ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  field_simp [hpow]

/-- Exact relation between the completed and ordinary logarithmic derivatives. -/
theorem logDeriv_completedDirichlet_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (completedDirichlet χ) s =
      Complex.log (q : ℂ) / 2 - Complex.log (Real.pi : ℂ) / 2 +
      logDeriv Complex.Gamma ((s + (dirichletParity χ : ℂ)) / 2) / 2 +
      logDeriv χ.LFunction s := by
  have hspos : 0 < s.re := by linarith
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have he : completedDirichlet χ =ᶠ[𝓝 s]
      (fun z => (q : ℂ) ^ (z / 2) * (χ.gammaFactor z * χ.LFunction z)) := by
    filter_upwards [hU.mem_nhds hspos] with z hz
    rw [completedDirichlet_eq_product χ hz, mul_assoc]
  have hld : logDeriv (completedDirichlet χ) s =
      logDeriv (fun z => (q : ℂ) ^ (z / 2) * (χ.gammaFactor z * χ.LFunction z)) s := by
    simp only [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
  rw [hld]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hA : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (z / 2)) s :=
    (differentiableAt_id.div_const (2 : ℂ)).const_cpow (c := (q : ℂ)) (Or.inl hq)
  have hB := differentiableAt_gammaFactor_of_re_pos χ hspos
  have hC := DirichletCharacter.differentiable_LFunction hχ s
  have hAn : (q : ℂ) ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hq)
  have hBn := gammaFactor_ne_zero_of_re_pos χ hspos
  have hCn := χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hs.le
  rw [logDeriv_mul (f := fun z : ℂ => (q : ℂ) ^ (z / 2))
    (g := fun z : ℂ => χ.gammaFactor z * χ.LFunction z)
    s hAn (mul_ne_zero hBn hCn) hA (hB.mul hC),
    logDeriv_mul (f := χ.gammaFactor) (g := χ.LFunction) s hBn hCn hB hC,
    logDeriv_conductor_factor,
    logDeriv_gammaFactor_eq χ hspos]
  ring

/-- The exact real logarithmic derivative expression used in paper equation (2.3). -/
theorem real_logDeriv_completedDirichlet_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℝ) (hs : 1 < s) :
    (logDeriv (completedDirichlet χ) (s : ℂ)).re =
      (1 / 2) * Real.log ((q : ℝ) / Real.pi) +
      (1 / 2) * (logDeriv Complex.Gamma (((s + dirichletParity χ) / 2 : ℝ) : ℂ)).re +
      (logDeriv χ.LFunction (s : ℂ)).re := by
  have h := congrArg Complex.re (logDeriv_completedDirichlet_eq χ hχ (s := (s : ℂ)) hs)
  simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re,
    Complex.log_re, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at h
  rw [Real.log_div (by exact_mod_cast (NeZero.ne q)) Real.pi_ne_zero]
  push_cast
  linarith

/-- The gamma logarithmic derivative is continuous on the positive half-plane. -/
theorem continuousAt_logDeriv_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (logDeriv Complex.Gamma) s := by
  have h := analyticAt_Gamma_of_re_pos hs
  exact (h.deriv.div h (Complex.Gamma_ne_zero_of_re_pos hs)).continuousAt

/-- A common compact-interval bound for both archimedean parity factors. -/
theorem exists_gamma_logDerivative_parity_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, (ε = 0 ∨ ε = 1) → ∀ s : ℝ,
      1 < s → s ≤ 2 →
      |(logDeriv Complex.Gamma (((s + ε) / 2 : ℝ) : ℂ)).re| ≤ C := by
  let f : ℝ → ℝ := fun x => |(logDeriv Complex.Gamma (x : ℂ)).re|
  have hc : ContinuousOn f (Icc (1 / 2 : ℝ) (3 / 2)) := by
    intro x hx
    have hg := continuousAt_logDeriv_Gamma_of_re_pos
      (s := (x : ℂ)) (by simp only [Complex.ofReal_re]; linarith [hx.1])
    exact ((Complex.continuous_re.continuousAt.comp
      (hg.comp Complex.continuous_ofReal.continuousAt)).abs).continuousWithinAt
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (1 / 2 : ℝ) (3 / 2)).Nonempty from ⟨1, by norm_num⟩) hc
  refine ⟨f x, abs_nonneg _, ?_⟩
  intro ε hε s hs hs2
  apply hmax
  rcases hε with rfl | rfl <;> constructor <;> linarith

/-- The parity parameter equals the original paper's `(1-chi(-1))/2`. -/
theorem dirichletParity_eq_character {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (dirichletParity χ : ℂ) = (1 - χ (-1)) / 2 := by
  classical
  rcases χ.even_or_odd with he | ho
  · simp [dirichletParity, he, show χ (-1) = 1 from he]
  · simp [dirichletParity, ho.not_even, show χ (-1) = -1 from ho]

/-- In the positive half-plane the completion introduces no new zeros. -/
theorem completedDirichlet_eq_zero_iff_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    completedDirichlet χ s = 0 ↔ χ.LFunction s = 0 := by
  rw [completedDirichlet_eq_product χ hs]
  have hq : (q : ℂ) ^ (s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  simp [hq, gammaFactor_ne_zero_of_re_pos χ hs]

/-- Nontrivial L-function zeros retain exactly their multiplicities on completion. -/
theorem meromorphicOrderAt_completedDirichlet_eq_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (completedDirichlet χ) s = meromorphicOrderAt χ.LFunction s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hB : AnalyticAt ℂ χ.gammaFactor s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hU.mem_nhds hs] with z hz
    exact differentiableAt_gammaFactor_of_re_pos χ hz
  have hA : AnalyticAt ℂ (fun z : ℂ => (q : ℂ) ^ (z / 2)) s := by
    apply Differentiable.analyticAt
    exact (differentiable_id.div_const (2 : ℂ)).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have he : completedDirichlet χ =ᶠ[𝓝 s]
      ((fun z : ℂ => (q : ℂ) ^ (z / 2) * χ.gammaFactor z) * χ.LFunction) := by
    filter_upwards [hU.mem_nhds hs] with z hz
    exact completedDirichlet_eq_product χ hz
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
  apply meromorphicOrderAt_mul_of_ne_zero (hA.mul hB)
  exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))) (gammaFactor_ne_zero_of_re_pos χ hs)

/-- The global divisor therefore counts the ordinary nontrivial L zeros
with their actual analytic multiplicities. -/
theorem divisor_completedDirichlet_eq_of_re_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    MeromorphicOn.divisor (completedDirichlet χ) Set.univ s =
      MeromorphicOn.divisor χ.LFunction Set.univ s := by
  have hF : MeromorphicOn (completedDirichlet χ) Set.univ :=
    fun z _ => ((differentiable_completedDirichlet χ hχ).analyticAt z).meromorphicAt
  have hL : MeromorphicOn χ.LFunction Set.univ :=
    fun z _ => ((DirichletCharacter.differentiable_LFunction hχ).analyticAt z).meromorphicAt
  rw [hF.divisor_apply (Set.mem_univ _), hL.divisor_apply (Set.mem_univ _),
    meromorphicOrderAt_completedDirichlet_eq_of_re_pos χ hs]

end Siegel
