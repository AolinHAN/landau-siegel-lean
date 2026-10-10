import Siegel.HolomorphicLog

namespace Siegel

open Metric Set

/-- A logarithmic growth bound controls the variation, rather than just the
size, of the logarithmic derivative. The extra inverse radius is essential
when the disk radius tends to infinity. -/
theorem norm_logDeriv_sub_center_le (g : ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball 0 R))
    (hzero : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hbound : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ ≤ R / 4) :
    ‖logDeriv g z - logDeriv g 0‖ ≤ 192 * M / R ^ 2 * ‖z‖ := by
  obtain ⟨f, hf, heq⟩ := exists_holomorphic_log_ball 0 R hR g hg hzero
  let h : ℂ → ℂ := fun w => f w - f 0
  have hh : DifferentiableOn ℂ h (ball 0 R) := hf.sub_const _
  have hh0 : h 0 = 0 := sub_self _
  have hre (w : ℂ) (hw : w ∈ ball 0 R) : (h w).re ≤ M := by
    have hfw := congrArg (fun v : ℂ => Real.log ‖v‖) (heq w hw)
    have hf0 := congrArg (fun v : ℂ => Real.log ‖v‖) (heq 0 (mem_ball_self hR))
    simp only [Complex.norm_exp, Real.log_exp] at hfw hf0
    simpa only [h, Complex.sub_re, hfw, hf0] using hbound w hw
  have hsmall (w : ℂ) (hw : ‖w‖ ≤ R / 2) : ‖h w‖ ≤ 2 * M := by
    have hw' : w ∈ ball 0 R := by rw [mem_ball_zero_iff]; linarith
    have he := Complex.borelCaratheodory_zero hM hh hre hR hw' hh0
    apply he.trans
    apply (div_le_iff₀ (by linarith : 0 < R - ‖w‖)).mpr
    nlinarith
  have hder (w : ℂ) (hw : ‖w‖ ≤ R / 3) : ‖deriv h w‖ ≤ 32 * M / R := by
    have hsub : ball w (R / 8) ⊆ ball 0 R := by
      intro v hv
      have hd : ‖v - w‖ < R / 8 := by simpa only [mem_ball, dist_eq_norm] using hv
      rw [mem_ball_zero_iff]
      linarith [norm_le_norm_sub_add v w]
    have hmaps : MapsTo h (ball w (R / 8)) (closedBall (h w) (4 * M)) := by
      intro v hv
      have hd : ‖v - w‖ < R / 8 := by simpa only [mem_ball, dist_eq_norm] using hv
      have hv' : ‖v‖ ≤ R / 2 := by linarith [norm_le_norm_sub_add v w]
      have hw' : ‖w‖ ≤ R / 2 := by linarith
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hsmall v hv', hsmall w hw'])
    have hd := Complex.norm_deriv_le_div_of_mapsTo_ball (hh.mono hsub) hmaps (by positivity : 0 < R / 8)
    convert hd using 1 <;> ring
  have hhder : DifferentiableOn ℂ (deriv h) (ball 0 (R / 3)) :=
    (hh.deriv isOpen_ball).mono (ball_subset_ball (by linarith))
  have hmaps : MapsTo (deriv h) (ball 0 (R / 3)) (closedBall (deriv h 0) (64 * M / R)) := by
    intro w hw
    have hw' : ‖w‖ ≤ R / 3 := (mem_ball_zero_iff.mp hw).le
    have h0' : ‖(0 : ℂ)‖ ≤ R / 3 := by simp; positivity
    rw [mem_closedBall, dist_eq_norm]
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ 32 * M / R + 32 * M / R := add_le_add (hder w hw') (hder 0 h0')
      _ = 64 * M / R := by ring
  have hz' : z ∈ ball 0 (R / 3) := by rw [mem_ball_zero_iff]; linarith
  have hd := Complex.dist_le_div_mul_dist_of_mapsTo_ball hhder hmaps hz'
  have hid (w : ℂ) (hw : w ∈ ball 0 R) : deriv h w = logDeriv g w := by
    rw [show deriv h w = deriv f w from deriv_sub_const _]
    exact deriv_holomorphic_log isOpen_ball f g hf heq w hw
  have hzR : z ∈ ball 0 R := by rw [mem_ball_zero_iff]; linarith
  rw [hid z hzR, hid 0 (mem_ball_self hR), dist_eq_norm, dist_zero_right] at hd
  convert hd using 1 <;> field_simp <;> ring

end Siegel
