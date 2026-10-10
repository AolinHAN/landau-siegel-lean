import Mathlib

namespace Siegel

open Filter
open scoped Topology

/-- Growth of size R log R is negligible after division by R squared. -/
theorem tendsto_logarithmic_radius_error (A B : ℝ) :
    Tendsto (fun n : ℕ =>
      (A * (2 * ((n : ℝ) + 1) + 1) * Real.log (2 * ((n : ℝ) + 1) + 2) + B) /
        ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    ht.const_div_atTop 1
  have hx : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 (ht.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hl := (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2 : ℝ) (-1) 1 (by norm_num)).comp hx
  have hl' : Tendsto (fun n : ℕ => Real.log (2 * ((n : ℝ) + 1) + 2) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    convert hl using 1
    ext n
    simp only [pow_one]
    congr 1
    ring
  have hratio : Tendsto (fun n : ℕ => 2 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (2 + 0)) := tendsto_const_nhds.add hi
  have hmain := ((hratio.const_mul A).mul hl').add ((hi.pow 2).const_mul B)
  convert hmain using 1
  · ext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  · simp

end Siegel
