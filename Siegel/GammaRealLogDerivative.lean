import Siegel.CompletedLogDerivative
import Mathlib.Analysis.Complex.RealDeriv

namespace Siegel

/-- The complex logarithmic derivative of Gamma on the positive real axis
has the real logarithmic derivative used in the paper as its real part. -/
theorem real_logDeriv_Gamma_eq (x : ℝ) (hx : 0 < x) :
    (logDeriv Complex.Gamma (x : ℂ)).re = logDeriv Real.Gamma x := by
  have hdiff : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hderiv : deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re :=
    hdiff.hasDerivAt.real_of_complex.deriv
  rw [logDeriv_apply, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re,
    hderiv]

end Siegel
