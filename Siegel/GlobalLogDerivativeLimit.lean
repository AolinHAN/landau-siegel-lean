import Siegel.LargeDiskExpansion
import Siegel.LogarithmicRadius
import Siegel.RadialZeroSums

namespace Siegel

open Metric Filter Function
open scoped Topology

/-- The finite zero expansion converges after subtracting the center value. -/
theorem tendsto_disk_logDeriv_centered (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (A : ℝ) (hA : 0 < A)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ w : ℂ, ‖w‖ ≤ n →
      Real.log ‖f w‖ ≤ A * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2))
    (z : ℂ) (hfz : f z ≠ 0) :
    Tendsto (fun n : ℕ => ∑ᶠ w,
      (MeromorphicOn.divisor f (ball 0 ((n : ℝ) + 1)) w : ℂ) *
        (1 / (z - w) - 1 / (0 - w))) atTop (𝓝 (logDeriv f z - logDeriv f 0)) := by
  have herr := ((tendsto_logarithmic_radius_error A (-Real.log ‖f 0‖ + 1)).const_mul
    (192 + 2 / Real.log 2)).mul_const ‖z‖
  simp only [mul_zero, zero_mul] at herr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ herr
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * ‖z‖)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hz : ‖z‖ ≤ ((n : ℝ) + 1) / 4 := by linarith
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have hb (w : ℂ) (hw : w ∈ closedBall 0 (2 * ((n : ℝ) + 1))) :
      Real.log ‖f w‖ ≤ A * (2 * ((n : ℝ) + 1) + 1) * Real.log (2 * ((n : ℝ) + 1) + 2) := by
    have h := hbound (2 * (n + 1)) (by omega) w (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
        mem_closedBall_zero_iff.mp hw)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using h
  have hB : 0 ≤ A * (2 * ((n : ℝ) + 1) + 1) * Real.log (2 * ((n : ℝ) + 1) + 2) := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    linarith
  have h := large_disk_logDeriv_expansion f ((n : ℝ) + 1) _ hp hB
    (fun w _ => hf.analyticAt w) hf0 hb z hz hfz
  rw [norm_sub_rev]
  convert h using 1 <;> ring

/-- Multiplication by any complex weight retains the finite support of a disk divisor. -/
theorem finiteSupport_divisor_mul_complex (f : ℂ → ℂ) (hf : MeromorphicOn f Set.univ)
    (R : ℝ) (k : ℂ → ℂ) :
    HasFiniteSupport (fun w => (MeromorphicOn.divisor f (ball 0 R) w : ℂ) * k w) := by
  apply (finiteSupport_divisor_ball f hf R).subset
  intro w hw
  change MeromorphicOn.divisor f (ball 0 R) w ≠ 0
  intro heq
  exact hw (by simp [heq])

/-- Subtracting two centered expansions cancels the unknown constant. -/
theorem tendsto_disk_logDeriv_difference (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (A : ℝ) (hA : 0 < A)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ w : ℂ, ‖w‖ ≤ n →
      Real.log ‖f w‖ ≤ A * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2))
    (x y : ℂ) (hfx : f x ≠ 0) (hfy : f y ≠ 0) :
    Tendsto (fun n : ℕ => ∑ᶠ w,
      (MeromorphicOn.divisor f (ball 0 ((n : ℝ) + 1)) w : ℂ) *
        (1 / (x - w) - 1 / (y - w))) atTop (𝓝 (logDeriv f x - logDeriv f y)) := by
  have h := (tendsto_disk_logDeriv_centered f hf hf0 A hA hbound x hfx).sub
    (tendsto_disk_logDeriv_centered f hf hf0 A hA hbound y hfy)
  have hm : MeromorphicOn f Set.univ := (show AnalyticOnNhd ℂ f Set.univ from fun w _ => hf.analyticAt w).meromorphicOn
  convert h using 1
  · ext n
    rw [← finsum_sub_distrib (finiteSupport_divisor_mul_complex f hm _ _)
      (finiteSupport_divisor_mul_complex f hm _ _)]
    apply finsum_congr
    intro w
    ring
  · congr 1
    abel

/-- The real parts of the radial zero sums converge to the real logarithmic derivative difference. -/
theorem tendsto_disk_logDeriv_difference_re (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (A : ℝ) (hA : 0 < A)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ w : ℂ, ‖w‖ ≤ n →
      Real.log ‖f w‖ ≤ A * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2))
    (x y : ℂ) (hfx : f x ≠ 0) (hfy : f y ≠ 0) :
    Tendsto (fun n : ℕ => ∑ᶠ w,
      (MeromorphicOn.divisor f (ball 0 ((n : ℝ) + 1)) w : ℝ) *
        ((1 / (x - w)).re - (1 / (y - w)).re)) atTop
      (𝓝 ((logDeriv f x).re - (logDeriv f y).re)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_disk_logDeriv_difference f hf hf0 A hA hbound x y hfx hfy)
  convert h using 1
  · ext n
    change _ = Complex.reAddGroupHom (∑ᶠ w,
      (MeromorphicOn.divisor f (ball 0 ((n : ℝ) + 1)) w : ℂ) *
        (1 / (x - w) - 1 / (y - w)))
    rw [Complex.reAddGroupHom.map_finsum
      (finiteSupport_divisor_mul_complex f (show AnalyticOnNhd ℂ f Set.univ from fun w _ => hf.analyticAt w).meromorphicOn _ _)]
    apply finsum_congr
    intro w
    simp

end Siegel
