import Siegel.DiskLogDerivativeDifference
import Siegel.DiskZeroData

namespace Siegel

open Metric Filter
open scoped Topology

/-- A finite partial fraction expansion on an arbitrary large disk. -/
theorem large_disk_logDeriv_expansion (f : ℂ → ℂ) (R B : ℝ) (hR : 0 < R) (hB : 0 ≤ B)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 (2 * R))) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z ∈ closedBall 0 (2 * R), Real.log ‖f z‖ ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ R / 4) (hfz : f z ≠ 0) :
    ‖logDeriv f z - logDeriv f 0 -
        ∑ᶠ w, (MeromorphicOn.divisor f (ball 0 R) w : ℂ) *
          (1 / (z - w) - 1 / (0 - w))‖ ≤
      (192 + 2 / Real.log 2) * (B - Real.log ‖f 0‖ + 1) / R ^ 2 * ‖z‖ := by
  classical
  have hfR := hf.mono (closedBall_subset_closedBall (by linarith : R ≤ 2 * R))
  obtain ⟨S, m, hS, h0, hord, hexact, hcount⟩ := exists_disk_zero_data f R hR hfR hf0
  have hSball := fun w hw => (hS w hw).1
  obtain ⟨g, hg, hgnz, heq⟩ := canonical_zero_removal R S m hSball f hfR hord hexact
  have hBnorm (w : ℂ) (hw : w ∈ closedBall 0 (2 * R)) : ‖f w‖ ≤ Real.exp B :=
    Real.le_exp_of_log_le (hbound w hw)
  have hnorm := continued_canonicalProduct_norm_le R hR S m hSball f g hfR hg heq
    (Real.exp B) (fun w hw => hBnorm w
      (closedBall_subset_closedBall (by linarith : R ≤ 2 * R) (sphere_subset_closedBall hw)))
  have h0cl : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have h0b : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hpt := ((hg 0 h0cl).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hfR 0 h0cl).continuousAt.mul (canonicalProduct_analyticAt R S m 0 h0).continuousAt)).mp
      (heq 0 h0cl) |>.eq_of_nhds
  change g 0 = f 0 * canonicalProduct R S m 0 at hpt
  have hnorm0 : ‖f 0‖ ≤ ‖g 0‖ := by
    rw [hpt, norm_mul]
    have h := canonicalProduct_norm_zero_ge R hR S m hSball h0
    nlinarith [norm_nonneg (f 0)]
  have hf0p := norm_pos_iff.mpr hf0
  have hlog0 := Real.log_le_log hf0p hnorm0
  have hcenter := hbound 0 (mem_closedBall_self (by linarith : 0 ≤ 2 * R))
  let M := B - Real.log ‖f 0‖ + 1
  have hM : 0 < M := by dsimp [M]; linarith
  have hglog (w : ℂ) (hw : w ∈ ball 0 R) : Real.log ‖g w‖ - Real.log ‖g 0‖ ≤ M := by
    have h := Real.log_le_log (norm_pos_iff.mpr (hgnz w hw)) (hnorm w hw)
    rw [Real.log_exp] at h
    dsimp [M]
    linarith
  have hzn : z ∉ S := fun h => hfz (hS z h).2.1
  have herr := disk_logDeriv_difference_bound R M hR hM S m hSball h0
    f g hfR hg hgnz hglog heq hf0 z hz hzn hfz
  have hcoeff (w : ℂ) : MeromorphicOn.divisor f (ball 0 R) w =
      ((if w ∈ S then m w else 0 : ℕ) : ℤ) := by
    by_cases hw : w ∈ ball 0 R
    · rw [(hfR.mono ball_subset_closedBall).meromorphicOn.divisor_apply hw, hexact w hw]
      simp
    · have hwS : w ∉ S := fun h => hw (hS w h).1
      simp [hw, hwS]
  have hsum : (∑ᶠ w, (MeromorphicOn.divisor f (ball 0 R) w : ℂ) *
      (1 / (z - w) - 1 / (0 - w))) =
      ∑ w ∈ S, (m w : ℂ) * (1 / (z - w) - 1 / (0 - w)) := by
    rw [finsum_eq_sum_of_support_subset _ (s := S) (by
      intro w hw
      by_contra hn
      change (MeromorphicOn.divisor f (ball 0 R) w : ℂ) * (1 / (z - w) - 1 / (0 - w)) ≠ 0 at hw
      simp only [Finset.mem_coe] at hn
      simp [hcoeff, hn] at hw)]
    apply Finset.sum_congr rfl
    intro w hw
    simp [hcoeff, hw]
  rw [hsum]
  have hj := AnalyticOnNhd.sum_divisor_le (f := f) (c := (0 : ℂ))
    (r := R) (R := 2 * R) (M := Real.exp B)
    (by simpa [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR, abs_of_pos (by positivity : 0 < 2 * R)]; linarith)
    (Real.one_le_exp_iff.mpr hB)
    (by simpa [abs_of_pos (by positivity : 0 < 2 * R)] using hf)
    hf0 (fun w hw => hBnorm w (by
      simpa only [abs_of_pos (by positivity : 0 < 2 * R)] using sphere_subset_closedBall hw))
  rw [abs_of_pos hR, Real.log_div (Real.exp_pos B).ne' hf0p.ne', Real.log_exp,
    mul_div_cancel_right₀ 2 hR.ne'] at hj
  have hNR : (∑ w ∈ S, (m w : ℝ)) ≤
      ((∑ᶠ w, MeromorphicOn.divisor f (closedBall 0 R) w : ℤ) : ℝ) := by exact_mod_cast hcount
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hNm : (∑ w ∈ S, (m w : ℝ)) ≤ M / Real.log 2 := by
    apply (hNR.trans hj).trans
    apply div_le_div_of_nonneg_right _ hl2.le
    dsimp [M]
    linarith
  apply herr.trans
  have he : (192 + 2 / Real.log 2) * M = 192 * M + 2 * (M / Real.log 2) := by ring
  change (192 * M + 2 * ∑ w ∈ S, (m w : ℝ)) / R ^ 2 * ‖z‖ ≤
    (192 + 2 / Real.log 2) * M / R ^ 2 * ‖z‖
  rw [he]
  gcongr

end Siegel
