import Mathlib

namespace Siegel

open Metric

/-- Translating both a disk and the argument preserves its total zero order. -/
theorem divisor_sum_translate (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) :
    (∑ᶠ z, MeromorphicOn.divisor (fun w => f (w + c)) (closedBall 0 R) z) =
      ∑ᶠ z, MeromorphicOn.divisor f (closedBall c R) z := by
  have hmem (z : ℂ) : z + c ∈ closedBall c R ↔ z ∈ closedBall 0 R := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero]
  have hshift : AnalyticOnNhd ℂ (fun w => f (w + c)) (closedBall 0 R) := by
    intro z hz
    exact (hf (z + c) ((hmem z).mpr hz)).comp (f := fun w : ℂ => w + c) (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + c) z)
  apply finsum_eq_of_bijective (fun z => z + c) (Equiv.addRight c).bijective
  intro z
  by_cases hz : z ∈ closedBall 0 R
  · rw [hshift.meromorphicOn.divisor_apply hz,
      hf.meromorphicOn.divisor_apply ((hmem z).mpr hz)]
    congr 1
    exact meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + c) z)
      (by simp)
  · have hzc : z + c ∉ closedBall c R := by simpa only [hmem] using hz
    simp [hz, hzc]

end Siegel
