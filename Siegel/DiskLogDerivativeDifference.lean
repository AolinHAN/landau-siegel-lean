import Siegel.LogDerivativeVariation
import Siegel.CanonicalVariation

namespace Siegel

open Metric Filter ComplexConjugate
open scoped Topology

/-- The finite zero expansion of a logarithmic derivative, with a remainder
which is quadratic in the reciprocal radius after subtracting its center value. -/
theorem disk_logDeriv_difference_bound (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (S : Finset ℂ) (m : ℂ → ℕ) (hS : ∀ w ∈ S, w ∈ ball 0 R) (h0 : (0 : ℂ) ∉ S)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hgnz : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M)
    (heq : ∀ z ∈ closedBall 0 R, g =ᶠ[𝓝[≠] z] (fun w => f w * canonicalProduct R S m w))
    (hf0 : f 0 ≠ 0) (z : ℂ) (hz : ‖z‖ ≤ R / 4) (hzn : z ∉ S) (hfz : f z ≠ 0) :
    ‖logDeriv f z - logDeriv f 0 -
        ∑ w ∈ S, (m w : ℂ) * (1 / (z - w) - 1 / (0 - w))‖ ≤
      (192 * M + 2 * ∑ w ∈ S, (m w : ℝ)) / R ^ 2 * ‖z‖ := by
  have hzcl : z ∈ closedBall 0 R := by rw [mem_closedBall_zero_iff]; linarith
  have h0cl : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have hiz := logDeriv_eq_regular_add_zero_terms R S m hS f g z hzcl hzn hfz
    (hf z hzcl).differentiableAt (hg z hzcl).differentiableAt (heq z hzcl)
  have hi0 := logDeriv_eq_regular_add_zero_terms R S m hS f g 0 h0cl h0 hf0
    (hf 0 h0cl).differentiableAt (hg 0 h0cl).differentiableAt (heq 0 h0cl)
  have he : logDeriv f z - logDeriv f 0 -
      ∑ w ∈ S, (m w : ℂ) * (1 / (z - w) - 1 / (0 - w)) =
      (logDeriv g z - logDeriv g 0) +
        ∑ w ∈ S, (m w : ℂ) *
          (conj w / ((R : ℂ) ^ 2 - conj w * z) - conj w / (R : ℂ) ^ 2) := by
    rw [hiz, hi0]
    simp only [mul_zero, sub_zero, mul_sub, Finset.sum_sub_distrib]
    abel
  rw [he]
  have hvariation := norm_logDeriv_sub_center_le g R M hR hM
    (hg.differentiableOn.mono ball_subset_closedBall) hgnz hbound z hz
  have hcorr : ‖∑ w ∈ S, (m w : ℂ) *
      (conj w / ((R : ℂ) ^ 2 - conj w * z) - conj w / (R : ℂ) ^ 2)‖ ≤
      (∑ w ∈ S, (m w : ℝ)) * (2 / R ^ 2 * ‖z‖) := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w hw
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      (canonical_correction_variation R hR w z (mem_ball_zero_iff.mp (hS w hw)).le hz)
      (Nat.cast_nonneg _)
  apply (norm_add_le _ _).trans
  calc
    _ ≤ 192 * M / R ^ 2 * ‖z‖ + (∑ w ∈ S, (m w : ℝ)) * (2 / R ^ 2 * ‖z‖) :=
      add_le_add hvariation hcorr
    _ = _ := by ring

end Siegel
