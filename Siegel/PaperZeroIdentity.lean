import Siegel.GlobalZeroFormula
import Siegel.NontrivialZeros

namespace Siegel

/-- Summability and the value of the sum over actual nontrivial L-function zeros. -/
theorem nontrivial_zero_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hquad : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) :
    Summable (fun ρ : ℂ => (nontrivialZeroMultiplicity χ ρ : ℝ) *
      (1 / ((s : ℂ) - ρ)).re) ∧
    (∑' ρ : ℂ, (nontrivialZeroMultiplicity χ ρ : ℝ) *
      (1 / ((s : ℂ) - ρ)).re) = (logDeriv (completedDirichlet χ) (s : ℂ)).re := by
  simpa only [completed_divisor_eq_nontrivialZeroMultiplicity χ hp hχ hquad] using
    completed_zero_sum χ hq hp hχ hquad s hs

/-- Every term in the paper's multiplicity-weighted zero sum is nonnegative. -/
theorem nontrivial_zero_summand_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) (ρ : ℂ) :
    0 ≤ (nontrivialZeroMultiplicity χ ρ : ℝ) * (1 / ((s : ℂ) - ρ)).re := by
  rw [← completed_divisor_eq_nontrivialZeroMultiplicity χ hp hχ hquad]
  exact completed_zero_summand_nonneg χ hp hχ hquad s hs ρ

/-- Paper equation (2.3), including its asserted convergence and positivity.
The index runs over ℂ, with zero weight except at genuine nontrivial L zeros;
`nontrivialZeroMultiplicity` is their actual analytic order. -/
theorem paper_equation_two_three_complete {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hquad : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) :
    (∀ ρ : ℂ, 0 ≤ (nontrivialZeroMultiplicity χ ρ : ℝ) * (1 / ((s : ℂ) - ρ)).re) ∧
    Summable (fun ρ : ℂ => (nontrivialZeroMultiplicity χ ρ : ℝ) *
      (1 / ((s : ℂ) - ρ)).re) ∧
    -(logDeriv χ.LFunction (s : ℂ)).re =
      (1 / 2) * Real.log ((q : ℝ) / Real.pi) +
      (1 / 2) * (logDeriv Complex.Gamma (((s + dirichletParity χ) / 2 : ℝ) : ℂ)).re -
      ∑' ρ : ℂ, (nontrivialZeroMultiplicity χ ρ : ℝ) *
        (1 / ((s : ℂ) - ρ)).re := by
  refine ⟨nontrivial_zero_summand_nonneg χ hp hχ hquad s hs,
    (nontrivial_zero_sum χ hq hp hχ hquad s hs).1, ?_⟩
  simpa only [completed_divisor_eq_nontrivialZeroMultiplicity χ hp hχ hquad] using
    paper_equation_two_three χ hq hp hχ hquad s hs

end Siegel
