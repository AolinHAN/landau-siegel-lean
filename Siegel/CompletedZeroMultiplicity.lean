import Siegel.CompletedLogDerivative
import Mathlib.Analysis.Meromorphic.NormalForm

namespace Siegel

/-- The completed function is not identically zero, so every local order is finite. -/
theorem meromorphicOrderAt_completedDirichlet_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) :
    meromorphicOrderAt (completedDirichlet χ) z ≠ ⊤ := by
  have hf : AnalyticOnNhd ℂ (completedDirichlet χ) Set.univ :=
    fun w _ => (differentiable_completedDirichlet χ hχ).analyticAt w
  have htwo : meromorphicOrderAt (completedDirichlet χ) (2 : ℂ) = 0 :=
    ((hf 2 (Set.mem_univ _)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr
      (completedDirichlet_two_ne_zero χ hχ)
  exact hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) (Set.mem_univ z) (by simp [htwo])

/-- The support of the divisor is exactly the zero set of the actual completed function. -/
theorem divisor_completedDirichlet_ne_zero_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) :
    MeromorphicOn.divisor (completedDirichlet χ) Set.univ z ≠ 0 ↔
      completedDirichlet χ z = 0 := by
  have hf : AnalyticOnNhd ℂ (completedDirichlet χ) Set.univ :=
    fun w _ => (differentiable_completedDirichlet χ hχ).analyticAt w
  have he := hf.meromorphicNFOn.zero_set_eq_divisor_support
    (fun w => meromorphicOrderAt_completedDirichlet_ne_top χ hχ w)
  have hm := congrArg (fun S : Set ℂ => z ∈ S) he
  simpa only [Set.mem_inter_iff, Set.mem_univ, Set.mem_preimage, Set.mem_singleton_iff,
    true_and, Function.mem_support] using (Iff.of_eq hm.symm)

/-- Every zero has a positive integer multiplicity. -/
theorem one_le_divisor_completedDirichlet_of_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℂ}
    (hz : completedDirichlet χ z = 0) :
    (1 : ℤ) ≤ MeromorphicOn.divisor (completedDirichlet χ) Set.univ z := by
  have hf : AnalyticOnNhd ℂ (completedDirichlet χ) Set.univ :=
    fun w _ => (differentiable_completedDirichlet χ hχ).analyticAt w
  have hnonneg : (0 : ℤ) ≤ MeromorphicOn.divisor (completedDirichlet χ) Set.univ z :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf z
  have hne := (divisor_completedDirichlet_ne_zero_iff χ hχ z).mpr hz
  omega

/-- Every real-part summand in the global zero expansion is nonnegative. -/
theorem completed_zero_summand_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) (z : ℂ) :
    0 ≤ (MeromorphicOn.divisor (completedDirichlet χ) Set.univ z : ℝ) *
      (1 / ((s : ℂ) - z)).re := by
  by_cases hz : MeromorphicOn.divisor (completedDirichlet χ) Set.univ z = 0
  · simp [hz]
  have hzero := (divisor_completedDirichlet_ne_zero_iff χ hχ z).mp hz
  have hstrip := completedDirichlet_zero_re_mem_Icc χ hp hχ hquad hzero
  apply mul_nonneg
  · exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 1)
      (one_le_divisor_completedDirichlet_of_zero χ hχ hzero))
  · rw [one_div, Complex.inv_re]
    apply div_nonneg
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hstrip.2]
    · exact Complex.normSq_nonneg _

/-- A specified real zero contributes at least its single simple-zero term,
even when its actual multiplicity is larger. -/
theorem real_zero_term_le_completed_zero_summand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β s : ℝ)
    (hβ : 0 < β) (hβs : β < s) (hzero : χ.LFunction (β : ℂ) = 0) :
    1 / (s - β) ≤
      (MeromorphicOn.divisor (completedDirichlet χ) Set.univ (β : ℂ) : ℝ) *
        (1 / ((s : ℂ) - (β : ℂ))).re := by
  have hz := (completedDirichlet_eq_zero_iff_of_re_pos χ
    (s := (β : ℂ)) hβ).mpr hzero
  have hm : (1 : ℝ) ≤
      (MeromorphicOn.divisor (completedDirichlet χ) Set.univ (β : ℂ) : ℝ) := by
    exact_mod_cast one_le_divisor_completedDirichlet_of_zero χ hχ hz
  have hid : (1 / ((s : ℂ) - (β : ℂ))).re = 1 / (s - β) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hid]
  nlinarith [show (0 : ℝ) < 1 / (s - β) by positivity]

/-- Once the zero expansion is summable, its nonnegative sum dominates the
contribution of each specified real zero. -/
theorem real_zero_term_le_completed_zero_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) (β s : ℝ) (hβ : 0 < β) (hβs : β < s)
    (hs : 1 < s) (hzero : χ.LFunction (β : ℂ) = 0)
    (hsumm : Summable (fun z : ℂ =>
      (MeromorphicOn.divisor (completedDirichlet χ) Set.univ z : ℝ) *
        (1 / ((s : ℂ) - z)).re)) :
    1 / (s - β) ≤ ∑' z : ℂ,
      (MeromorphicOn.divisor (completedDirichlet χ) Set.univ z : ℝ) *
        (1 / ((s : ℂ) - z)).re := by
  apply (real_zero_term_le_completed_zero_summand χ hχ β s hβ hβs hzero).trans
  exact hsumm.le_tsum (β : ℂ)
    (fun z _ => completed_zero_summand_nonneg χ hp hχ hquad s hs z)

end Siegel
