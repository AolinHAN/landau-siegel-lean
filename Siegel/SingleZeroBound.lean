import Siegel.GlobalZeroFormula
import Siegel.CompletedZeroMultiplicity
import Siegel.ZetaPoleBound
import Siegel.PrimeBiasAssembly

namespace Siegel

/-- Keeping a specified real zero in the nonnegative global expansion gives
the exact single-zero upper bound used after paper equation (2.3). -/
theorem LFunction_single_zero_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ) (hβ : AdmissibleZero χ β)
    (s : ℝ) (hs : 1 < s) :
    -(logDeriv χ.LFunction (s : ℂ)).re ≤
      (1 / 2) * Real.log ((q : ℝ) / Real.pi) +
      (1 / 2) * (logDeriv Complex.Gamma (((s + dirichletParity χ) / 2 : ℝ) : ℂ)).re -
      1 / (s - β) := by
  rcases hβ with ⟨hq, hp, hχ, hquad, hβ0, hβ1, hzero⟩
  obtain ⟨hsumm, heq⟩ := completed_zero_sum χ (by omega) hp hχ hquad s hs
  have hsingle := real_zero_term_le_completed_zero_sum χ hp hχ hquad β s
    hβ0 (by linarith) hs hzero hsumm
  rw [heq] at hsingle
  have hfactor := real_logDeriv_completedDirichlet_eq χ hχ s hs
  linarith

/-- Equation (2.4) proved by the original global-zero route: retain the real
zero in (2.3), bound the gamma term on its compact parity ranges, and remove
the zeta pole.  All constants are uniform in the character and conductor. -/
theorem logDerivativeUpper_from_global_zeros : LogDerivativeUpperStatement := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := exists_gamma_logDerivative_parity_bound
  obtain ⟨Cζ, hCζ, hζ⟩ := exists_zeta_logDerivative_error_bound
  refine ⟨CΓ + Cζ + 2, by positivity, ?_⟩
  intro q _ χ β hβ s hs hs2
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hβ.1
  have hqpos : (0 : ℝ) < q := by linarith
  have hlogq : 1 ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq3
    linarith [Real.log_three_gt_d9]
  have hsingle := LFunction_single_zero_bound χ β hβ s hs
  have hgamma := hΓ (dirichletParity χ) (dirichletParity_cases χ) s hs hs2
  have hgamma_upper :
      (logDeriv Complex.Gamma (((s + dirichletParity χ) / 2 : ℝ) : ℂ)).re ≤ CΓ :=
    (le_abs_self _).trans hgamma
  have hlogratio : Real.log ((q : ℝ) / Real.pi) ≤ Real.log (q : ℝ) := by
    rw [Real.log_div hqpos.ne' Real.pi_ne_zero]
    have hp : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hL : -(logDeriv χ.LFunction (s : ℂ)).re ≤
      (1 / 2) * Real.log (q : ℝ) + (1 / 2) * CΓ - 1 / (s - β) := by
    linarith
  have hzetab := hζ s hs hs2
  have hΓabsorb : CΓ ≤ CΓ * Real.log (q : ℝ) := by nlinarith
  have hζabsorb : Cζ ≤ Cζ * Real.log (q : ℝ) := by nlinarith
  have hcomb : (logDerivativeCombination χ (s : ℂ)).re =
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re -
        (logDeriv χ.LFunction (s : ℂ)).re := by
    simp only [logDerivativeCombination, Complex.sub_re, logDeriv_apply]
  rw [hcomb]
  nlinarith

end Siegel
