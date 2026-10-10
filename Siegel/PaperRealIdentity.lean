import Siegel.PaperZeroIdentity
import Siegel.RealCharacter
import Siegel.GammaRealLogDerivative

namespace Siegel

/-- Equation (2.3) in the paper's real-axis notation: the actual complex
logarithmic derivative equals the inclusion of the real Gamma/zero expression. -/
theorem paper_equation_two_three_real_axis {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hquad : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) :
    -logDeriv χ.LFunction (s : ℂ) =
      (((1 / 2) * Real.log ((q : ℝ) / Real.pi) +
        (1 / 2) * logDeriv Real.Gamma ((s + dirichletParity χ) / 2) -
        ∑' ρ : ℂ, (nontrivialZeroMultiplicity χ ρ : ℝ) *
          (1 / ((s : ℂ) - ρ)).re : ℝ) : ℂ) := by
  have hx : 0 < (s + dirichletParity χ) / 2 := by
    rcases dirichletParity_cases χ with h | h <;> rw [h] <;> linarith
  have heq := (paper_equation_two_three_complete χ hq hp hχ hquad s hs).2.2
  rw [real_logDeriv_Gamma_eq _ hx] at heq
  rw [logDeriv_LFunction_eq_ofReal_re χ hquad s hs, ← Complex.ofReal_neg]
  exact congrArg (fun r : ℝ => (r : ℂ)) heq

end Siegel
