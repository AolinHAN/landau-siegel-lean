import Siegel.HolomorphicLog

/-! A quantitative logarithmic derivative estimate on a zero-free disk. -/

namespace Siegel

open Metric Set

/-- On a fixed smaller disk, the logarithmic derivative of a nonvanishing
holomorphic function is bounded by its logarithmic growth. -/
theorem norm_logDeriv_le_of_log_norm_bound (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (ball 0 (3 / 2 : ℝ)))
    (hzero : ∀ z ∈ ball 0 (3 / 2 : ℝ), g z ≠ 0)
    (M : ℝ) (hM : 0 < M)
    (hbound : ∀ z ∈ ball 0 (3 / 2 : ℝ), Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖logDeriv g z‖ ≤ 160 * M := by
  obtain ⟨f, hf, heq⟩ := exists_holomorphic_log_ball 0 (3 / 2 : ℝ) (by norm_num) g hg hzero
  let h : ℂ → ℂ := fun w => f w - f 0
  have hh : DifferentiableOn ℂ h (ball 0 (3 / 2 : ℝ)) := hf.sub_const _
  have hh0 : h 0 = 0 := sub_self _
  have hre (w : ℂ) (hw : w ∈ ball 0 (3 / 2 : ℝ)) : (h w).re ≤ M := by
    have hfw := congrArg (fun v : ℂ => Real.log ‖v‖) (heq w hw)
    have hf0 := congrArg (fun v : ℂ => Real.log ‖v‖) (heq 0 (by norm_num))
    simp only [Complex.norm_exp, Real.log_exp] at hfw hf0
    simpa only [h, Complex.sub_re, hfw, hf0] using hbound w hw
  have hsmall (w : ℂ) (hw : ‖w‖ ≤ 5 / 4) : ‖h w‖ ≤ 10 * M := by
    have hw' : w ∈ ball 0 (3 / 2 : ℝ) := by
      rw [mem_ball_zero_iff]
      linarith
    have he := Complex.borelCaratheodory_zero hM hh (fun w hw => hre w hw)
      (by norm_num : (0 : ℝ) < 3 / 2) hw' hh0
    apply he.trans
    apply (div_le_iff₀ (by linarith : 0 < (3 / 2 : ℝ) - ‖w‖)).mpr
    nlinarith
  have hsub : ball z (1 / 8 : ℝ) ⊆ ball 0 (3 / 2 : ℝ) := by
    intro w hw
    rw [mem_ball_zero_iff]
    have hwz : ‖w - z‖ < 1 / 8 := by simpa only [mem_ball, dist_eq_norm] using hw
    have ht := norm_le_norm_sub_add w z
    linarith
  have hmaps : MapsTo h (ball z (1 / 8 : ℝ)) (closedBall (h z) (20 * M)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    have hwz : ‖w - z‖ < 1 / 8 := by simpa only [mem_ball, dist_eq_norm] using hw
    have hnw : ‖w‖ ≤ 5 / 4 := by linarith [norm_le_norm_sub_add w z]
    have hnz : ‖z‖ ≤ 5 / 4 := by linarith
    exact (norm_sub_le _ _).trans (by linarith [hsmall w hnw, hsmall z hnz])
  have hder := Complex.norm_deriv_le_div_of_mapsTo_ball (hh.mono hsub) hmaps
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hz' : z ∈ ball 0 (3 / 2 : ℝ) := by rw [mem_ball_zero_iff]; linarith
  have hid : deriv h z = logDeriv g z := by
    rw [show deriv h z = deriv f z from deriv_sub_const _]
    exact deriv_holomorphic_log isOpen_ball f g hf heq z hz'
  rw [hid] at hder
  linarith

end Siegel
