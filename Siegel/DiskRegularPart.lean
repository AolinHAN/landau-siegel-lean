import Siegel.CanonicalZeroRemoval
import Siegel.DiskZeroData
import Siegel.LogDerivativeDisk

namespace Siegel

open Metric Filter
open scoped Topology

/-- Separate the zeros from the regular part on a fixed disk, with a
quantitative bound for the latter's logarithmic derivative. -/
theorem exists_disk_regular_part (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (7 / 4 : ℝ))) (hf0 : f 0 ≠ 0)
    (M : ℝ) (hM : 0 < M) (hbound : ∀ z ∈ sphere 0 (7 / 4 : ℝ), ‖f z‖ ≤ M) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ w ∈ S, w ∈ ball 0 (7 / 4 : ℝ) ∧ f w = 0 ∧ 0 < m w) ∧ (0 : ℂ) ∉ S ∧
      AnalyticOnNhd ℂ g (closedBall 0 (7 / 4 : ℝ)) ∧
      (∀ z ∈ ball 0 (7 / 4 : ℝ), g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 (7 / 4 : ℝ),
        g =ᶠ[𝓝[≠] z] (fun w => f w * canonicalProduct (7 / 4) S m w)) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 →
        ‖logDeriv g z‖ ≤ 160 * (Real.log M - Real.log ‖f 0‖ + 1)) ∧
      ((∑ w ∈ S, m w : ℕ) : ℤ) ≤
        ∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 (7 / 4 : ℝ)) z := by
  obtain ⟨S, m, hS, h0, hord, hexact, hcount⟩ := exists_disk_zero_data f (7 / 4) (by norm_num) hf hf0
  obtain ⟨g, hg, hgnz, heq⟩ := canonical_zero_removal (7 / 4) S m (fun w hw => (hS w hw).1)
    f hf hord hexact
  have hnorm := continued_canonicalProduct_norm_le (7 / 4) (by norm_num) S m
    (fun w hw => (hS w hw).1) f g hf hg heq M hbound
  have hz0 : (0 : ℂ) ∈ closedBall 0 (7 / 4 : ℝ) := by norm_num
  have h0b : (0 : ℂ) ∈ ball 0 (7 / 4 : ℝ) := by norm_num
  have hpt := ((hg 0 hz0).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hf 0 hz0).continuousAt.mul (canonicalProduct_analyticAt (7 / 4) S m 0 h0).continuousAt)).mp
      (heq 0 hz0) |>.eq_of_nhds
  change g 0 = f 0 * canonicalProduct (7 / 4) S m 0 at hpt
  have hnorm0 : ‖f 0‖ ≤ ‖g 0‖ := by
    rw [hpt, norm_mul]
    have h := canonicalProduct_norm_zero_ge (7 / 4) (by norm_num) S m
      (fun w hw => (hS w hw).1) h0
    nlinarith [norm_nonneg (f 0)]
  have hf0p := norm_pos_iff.mpr hf0
  have hlog0 : Real.log ‖f 0‖ ≤ Real.log ‖g 0‖ := Real.log_le_log hf0p hnorm0
  have hlogM : Real.log ‖f 0‖ ≤ Real.log M :=
    Real.log_le_log hf0p (hnorm0.trans (hnorm 0 h0b))
  refine ⟨S, m, g, hS, h0, hg, hgnz, heq, ?_, hcount⟩
  intro z hz
  have hsub : ball (0 : ℂ) (3 / 2 : ℝ) ⊆ ball 0 (7 / 4 : ℝ) :=
    ball_subset_ball (by norm_num)
  apply norm_logDeriv_le_of_log_norm_bound g
    (hg.differentiableOn.mono (hsub.trans ball_subset_closedBall))
    (fun w hw => hgnz w (hsub hw)) (Real.log M - Real.log ‖f 0‖ + 1) (by linarith) ?_ z hz
  intro w hw
  have hp := norm_pos_iff.mpr (hgnz w (hsub hw))
  have hl := Real.log_le_log hp (hnorm w (hsub hw))
  linarith

end Siegel
