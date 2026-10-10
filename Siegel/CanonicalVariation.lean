import Siegel.CanonicalProductLogDeriv

namespace Siegel

open ComplexConjugate

/-- The Blaschke correction has variation of size R^-2 on the inner quarter disk. -/
theorem canonical_correction_variation (R : ℝ) (hR : 0 < R) (w z : ℂ)
    (hw : ‖w‖ ≤ R) (hz : ‖z‖ ≤ R / 4) :
    ‖conj w / ((R : ℂ) ^ 2 - conj w * z) - conj w / (R : ℂ) ^ 2‖ ≤
      2 / R ^ 2 * ‖z‖ := by
  have hRn : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hmul : ‖conj w * z‖ ≤ R * (R / 4) := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hw hz (norm_nonneg _) hR.le
  have hden : R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2 - conj w * z‖ := by
    have h := norm_sub_norm_le ((R : ℂ) ^ 2) (conj w * z)
    rw [hRn] at h
    nlinarith
  have hdpos : 0 < ‖(R : ℂ) ^ 2 - conj w * z‖ := lt_of_lt_of_le (by positivity) hden
  have hd : (R : ℂ) ^ 2 - conj w * z ≠ 0 := norm_pos_iff.mp hdpos
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have heq : conj w / ((R : ℂ) ^ 2 - conj w * z) - conj w / (R : ℂ) ^ 2 =
      (conj w) ^ 2 * z / (((R : ℂ) ^ 2 - conj w * z) * (R : ℂ) ^ 2) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_conj, hRn]
  apply (div_le_iff₀ (mul_pos hdpos (sq_pos_of_pos hR))).mpr
  have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg w]
  have hstep : R ^ 2 ≤ 2 * ‖(R : ℂ) ^ 2 - conj w * z‖ := by linarith
  have hc : (2 / R ^ 2 * ‖z‖) * (‖(R : ℂ) ^ 2 - conj w * z‖ * R ^ 2) =
      2 * ‖z‖ * ‖(R : ℂ) ^ 2 - conj w * z‖ := by field_simp
  rw [hc]
  nlinarith [norm_nonneg z]

end Siegel
