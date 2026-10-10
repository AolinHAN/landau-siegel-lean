import Mathlib

namespace Siegel

open ComplexConjugate Metric

/-- The logarithmic derivative of the inverse Blaschke factor, separating
its pole from a uniformly bounded correction. -/
theorem logDeriv_canonicalFactor (R : ℝ) (w z : ℂ)
    (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R) (hzw : z ≠ w) :
    logDeriv (Complex.canonicalFactor R w) z =
      -(conj w / ((R : ℂ) ^ 2 - conj w * z)) - 1 / (z - w) := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg w) (mem_ball_zero_iff.mp hw)
  have hnum : (R : ℂ) ^ 2 - conj w * z ≠ 0 := by
    intro h
    have hc := Complex.canonicalFactor_ne_zero hw hz hzw
    exact hc (by simp [Complex.canonicalFactor, h])
  have hden : (R : ℂ) * (z - w) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hR.ne') (sub_ne_zero.mpr hzw)
  have hA : HasDerivAt (fun x : ℂ => (R : ℂ) ^ 2 - conj w * x) (-conj w) z := by
    convert (hasDerivAt_const z ((R : ℂ) ^ 2)).sub ((hasDerivAt_id z).const_mul (conj w)) using 1 <;> simp
  have hB : HasDerivAt (fun x : ℂ => (R : ℂ) * (x - w)) (R : ℂ) z := by
    convert ((hasDerivAt_id z).sub_const w).const_mul (R : ℂ) using 1 <;> simp
  rw [Complex.canonicalFactor_def, logDeriv_div z hnum hden hA.differentiableAt hB.differentiableAt]
  rw [logDeriv_apply, logDeriv_apply, hA.deriv, hB.deriv]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hcancel : (R : ℂ) / ((R : ℂ) * (z - w)) = 1 / (z - w) := by
    rw [div_mul_eq_div_div, div_self hR0]
  rw [hcancel, neg_div]

/-- The correction term is bounded uniformly for all zeros in the
radius-7/4 disk and all evaluation points in the unit disk. -/
theorem canonical_correction_norm_le (w z : ℂ)
    (hw : ‖w‖ ≤ 7 / 4) (hz : ‖z‖ ≤ 1) :
    ‖conj w / ((7 / 4 : ℂ) ^ 2 - conj w * z)‖ ≤ 4 / 3 := by
  have hn : ‖conj w * z‖ ≤ 7 / 4 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg w)).trans (by simpa using hw)
  have hden : (21 / 16 : ℝ) ≤ ‖(7 / 4 : ℂ) ^ 2 - conj w * z‖ := by
    have h := norm_sub_norm_le ((7 / 4 : ℂ) ^ 2) (conj w * z)
    have ha : ‖(7 / 4 : ℂ) ^ 2‖ = (49 / 16 : ℝ) := by norm_num
    rw [ha] at h
    linarith
  rw [norm_div, Complex.norm_conj]
  apply (div_le_iff₀ (by linarith : 0 < ‖(7 / 4 : ℂ) ^ 2 - conj w * z‖)).mpr
  linarith

end Siegel
