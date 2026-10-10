import Mathlib

/-! Holomorphic logarithms on disks, with an explicit derivative identity. -/

namespace Siegel

open Set Metric Filter
open scoped Topology

/-- A continuous branch of the logarithm of a holomorphic function is
holomorphic. The proof uses the principal logarithm only locally. -/
theorem differentiableOn_of_continuous_log {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hfc : ContinuousOn f U) (hgd : DifferentiableOn ℂ g U)
    (heq : ∀ z ∈ U, Complex.exp (f z) = g z) : DifferentiableOn ℂ f U := by
  intro z hz
  have hfc' : ContinuousAt f z := (hfc z hz).continuousAt (hU.mem_nhds hz)
  have hgd' : DifferentiableAt ℂ g z := (hgd z hz).differentiableAt (hU.mem_nhds hz)
  have hg0 : g z ≠ 0 := by rw [← heq z hz]; exact Complex.exp_ne_zero _
  have hnear : ∀ᶠ w in 𝓝 z, ‖f w - f z‖ < Real.pi := by
    simpa only [mem_ball, dist_eq_norm] using
      hfc'.tendsto.eventually (ball_mem_nhds (f z) Real.pi_pos)
  have hloc : f =ᶠ[𝓝 z] (fun w => Complex.log (g w / g z) + f z) := by
    filter_upwards [hU.mem_nhds hz, hnear] with w hw hn
    have hi := Complex.abs_im_le_norm (f w - f z)
    have hlow : -Real.pi < (f w - f z).im := by linarith [neg_abs_le (f w - f z).im]
    have hhigh : (f w - f z).im ≤ Real.pi := by linarith [le_abs_self (f w - f z).im]
    rw [← heq w hw, ← heq z hz, ← Complex.exp_sub, Complex.log_exp hlow hhigh]
    ring
  have hlog : DifferentiableAt ℂ (fun w => Complex.log (g w / g z) + f z) z := by
    apply DifferentiableAt.add_const
    apply DifferentiableAt.clog
    · exact hgd'.div_const (g z)
    · simpa [hg0] using Complex.one_mem_slitPlane
  exact (hlog.congr_of_eventuallyEq hloc).differentiableWithinAt

/-- A nonvanishing holomorphic function on a disk has a holomorphic logarithm. -/
theorem exists_holomorphic_log_ball (c : ℂ) (R : ℝ) (hR : 0 < R)
    (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (ball c R))
    (hzero : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball c R) ∧
      ∀ z ∈ ball c R, Complex.exp (f z) = g z := by
  letI : ContractibleSpace (ball c R) :=
    (convex_ball c R).contractibleSpace ⟨c, mem_ball_self hR⟩
  have hsim : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨f, hfc, heq⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsim isOpen_ball
    hg.continuousOn (by rintro ⟨z, hz, he⟩; exact hzero z hz he)
  refine ⟨f, differentiableOn_of_continuous_log isOpen_ball hfc hg ?_, ?_⟩
  · intro z hz
    exact heq hz
  · intro z hz
    exact heq hz

/-- The derivative of any holomorphic logarithm is the actual logarithmic
derivative of the original function. -/
theorem deriv_holomorphic_log {U : Set ℂ} (hU : IsOpen U) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (heq : ∀ z ∈ U, Complex.exp (f z) = g z)
    (z : ℂ) (hz : z ∈ U) : deriv f z = logDeriv g z := by
  have hfd := (hf z hz).differentiableAt (hU.mem_nhds hz)
  have hlocal : (fun w => Complex.exp (f w)) =ᶠ[𝓝 z] g := by
    filter_upwards [hU.mem_nhds hz] with w hw using heq w hw
  have hder := ((Complex.hasDerivAt_exp (f z)).comp z hfd.hasDerivAt).congr_of_eventuallyEq hlocal.symm
  rw [logDeriv_apply, hder.deriv, ← heq z hz]
  exact (mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)).symm

end Siegel
