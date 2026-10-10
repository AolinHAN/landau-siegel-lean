import Siegel.LFunctionLogDerivative
import Siegel.ZetaPoleBound
import Siegel.PrimeBiasAssembly

namespace Siegel

/-- Equation (2.4), proved for the actual analytically continued L-functions.
The L-function term is obtained from local zero removal and Jensen's formula. -/
theorem logDerivativeUpper : LogDerivativeUpperStatement := by
  obtain ⟨C₁, hC₁, hL⟩ := exists_LFunction_logDeriv_lower
  obtain ⟨C₂, hC₂, hζ⟩ := exists_zeta_logDerivative_error_bound
  refine ⟨C₁ + C₂, by linarith, ?_⟩
  intro q _ χ β hβ s hs hs2
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hβ.1
  have hlogq : 1 ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq3
    linarith [Real.log_three_gt_d9]
  have hLb := hL χ β hβ s hs hs2
  have hζb := hζ s hs hs2
  have herror : C₂ ≤ C₂ * Real.log q := by nlinarith
  simp only [logDerivativeCombination, Complex.sub_re, logDeriv_apply] at *
  nlinarith

/-- Lemma 2, with all constants quantified before the character and zero. -/
theorem primeBias : PrimeBiasStatement :=
  primeBias_of_logDerivative_upper logDerivativeUpper

end Siegel
