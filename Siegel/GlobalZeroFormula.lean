import Siegel.SymmetricZeroSum
import Siegel.CompletedGrowth
import Siegel.CompletedLogDerivative
import Siegel.ZeroSumTranslation

namespace Siegel

open Set

/-- The actual nontrivial zeros of the primitive real Dirichlet L-function,
counted with their analytic multiplicities, have a convergent nonnegative
real Cauchy-kernel sum, equal to the completed logarithmic derivative. -/
theorem completed_zero_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hquad : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) :
    Summable (fun ρ : ℂ => (MeromorphicOn.divisor (completedDirichlet χ) univ ρ : ℝ) *
      (1 / ((s : ℂ) - ρ)).re) ∧
    (∑' ρ : ℂ, (MeromorphicOn.divisor (completedDirichlet χ) univ ρ : ℝ) *
      (1 / ((s : ℂ) - ρ)).re) = (logDeriv (completedDirichlet χ) (s : ℂ)).re := by
  let f : ℂ → ℂ := fun z => completedDirichlet χ (z + 2)
  have hF := differentiable_completedDirichlet χ hχ
  have hf : Differentiable ℂ f := hF.comp (differentiable_id.add_const (2 : ℂ))
  have hf0 : f 0 ≠ 0 := by simpa [f] using completedDirichlet_two_ne_zero χ hχ
  obtain ⟨A, hA, hgrowth⟩ := exists_completedDirichlet_log_growth χ hq hp hχ hquad
  have hb (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : ‖z‖ ≤ n) :
      Real.log ‖f z‖ ≤ A * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2) := by
    exact hgrowth n hn (z + 2) (by simpa using hz)
  have hzstrip (z : ℂ) (hz : f z = 0) : z.re ∈ Icc (-2 : ℝ) (-1) := by
    have h := completedDirichlet_zero_re_mem_Icc χ hp hχ hquad hz
    simp only [Complex.add_re, Complex.re_ofNat, mem_Icc] at h ⊢
    constructor <;> linarith
  have hreflect (z : ℂ) : f (-3 - z) = χ.rootNumber * f z := by
    change completedDirichlet χ (-3 - z + 2) = χ.rootNumber * completedDirichlet χ (z + 2)
    rw [show (-3 : ℂ) - z + 2 = 1 - (z + 2) by ring]
    exact completedDirichlet_reflection χ hp hquad (z + 2)
  have hld (z : ℂ) : logDeriv f (-3 - z) = -logDeriv f z := by
    change logDeriv (fun w => completedDirichlet χ (w + 2)) (-3 - z) =
      -logDeriv (fun w => completedDirichlet χ (w + 2)) z
    rw [logDeriv_translate _ hF, logDeriv_translate _ hF]
    rw [show (-3 : ℂ) - z + 2 = 1 - (z + 2) by ring]
    exact logDeriv_completedDirichlet_reflection χ hp hχ hquad (z + 2)
  obtain ⟨hsum, hvalue⟩ := symmetric_real_zero_sum f hf hf0 A hA hb hzstrip
    χ.rootNumber (rootNumber_ne_zero_of_quadratic χ hp hχ hquad) hreflect hld
    (s - 2) (by linarith)
  constructor
  · apply (summable_zero_kernel_translate_iff (completedDirichlet χ) hF 2 (s : ℂ)).mp
    simpa only [f, Complex.ofReal_sub, Complex.ofReal_ofNat] using hsum
  · rw [← tsum_zero_kernel_translate (completedDirichlet χ) hF 2 (s : ℂ)]
    simpa only [f, Complex.ofReal_sub, Complex.ofReal_ofNat, logDeriv_translate _ hF,
      sub_add_cancel] using hvalue

/-- Equation (2.3): the real logarithmic derivative expressed through the
actual completed zero divisor, with convergence proved in `completed_zero_sum`. -/
theorem paper_equation_two_three {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hquad : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) :
    -(logDeriv χ.LFunction (s : ℂ)).re =
      (1 / 2) * Real.log ((q : ℝ) / Real.pi) +
      (1 / 2) * (logDeriv Complex.Gamma (((s + dirichletParity χ) / 2 : ℝ) : ℂ)).re -
      ∑' ρ : ℂ, (MeromorphicOn.divisor (completedDirichlet χ) univ ρ : ℝ) *
        (1 / ((s : ℂ) - ρ)).re := by
  have hsum := (completed_zero_sum χ hq hp hχ hquad s hs).2
  have hld := real_logDeriv_completedDirichlet_eq χ hχ s hs
  linarith

end Siegel
