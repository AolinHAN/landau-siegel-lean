import Siegel.CanonicalZeroRemoval

namespace Siegel

open Metric Filter ComplexConjugate
open scoped Topology

theorem canonicalProduct_ne_zero (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w ∈ ball 0 R) (z : ℂ) (hz : z ∈ closedBall 0 R) (hzn : z ∉ S) :
    canonicalProduct R S m z ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro w hw
  exact pow_ne_zero _ (Complex.canonicalFactor_ne_zero (hS w hw) hz (fun h => hzn (h ▸ hw)))

theorem logDeriv_canonicalProduct (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w ∈ ball 0 R) (z : ℂ) (hz : z ∈ closedBall 0 R) (hzn : z ∉ S) :
    logDeriv (canonicalProduct R S m) z =
      ∑ w ∈ S, (m w : ℂ) * (-(conj w / ((R : ℂ) ^ 2 - conj w * z)) - 1 / (z - w)) := by
  classical
  unfold canonicalProduct
  rw [logDeriv_prod (f := fun w x => Complex.canonicalFactor R w x ^ m w)
    (fun w hw => pow_ne_zero _ (Complex.canonicalFactor_ne_zero (hS w hw) hz (fun h => hzn (h ▸ hw))))
    (fun w hw => ((Complex.analyticOnNhd_canonicalFactor R w z
      (fun h => hzn (h ▸ hw))).differentiableAt).pow _)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [logDeriv_fun_pow (Complex.analyticOnNhd_canonicalFactor R w z
    (fun h => hzn (h ▸ hw))).differentiableAt,
    logDeriv_canonicalFactor R w z (hS w hw) hz (fun h => hzn (h ▸ hw))]

/-- The logarithmic derivative splits into its regular part, explicit zero
poles, and the small correction terms from the Blaschke factors. -/
theorem logDeriv_eq_regular_add_zero_terms (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w ∈ ball 0 R) (f g : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ closedBall 0 R) (hzn : z ∉ S) (hf0 : f z ≠ 0)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (heq : g =ᶠ[𝓝[≠] z] (fun w => f w * canonicalProduct R S m w)) :
    logDeriv f z = logDeriv g z +
      (∑ w ∈ S, (m w : ℂ) * (1 / (z - w))) +
      ∑ w ∈ S, (m w : ℂ) * (conj w / ((R : ℂ) ^ 2 - conj w * z)) := by
  have hC := (canonicalProduct_analyticAt R S m z hzn).differentiableAt
  have hlocal := (hg.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hf.continuousAt.mul hC.continuousAt)).mp heq
  have hprod : logDeriv g z = logDeriv f z + logDeriv (canonicalProduct R S m) z := by
    calc
      _ = logDeriv (fun w => f w * canonicalProduct R S m w) z := by
        simp only [logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds]
        rfl
      _ = _ := logDeriv_mul z hf0 (canonicalProduct_ne_zero R S m hS z hz hzn) hf hC
  rw [logDeriv_canonicalProduct R S m hS z hz hzn] at hprod
  simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hprod
  linear_combination -hprod

/-- A one-sided local estimate retaining every zero term. -/
theorem real_logDeriv_lower_from_regular_part (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w ∈ ball 0 (7 / 4 : ℝ)) (f g : ℂ → ℂ) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (hzn : z ∉ S) (hf0 : f z ≠ 0)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (heq : g =ᶠ[𝓝[≠] z] (fun w => f w * canonicalProduct (7 / 4) S m w)) :
    (∑ w ∈ S, (m w : ℝ) * (1 / (z - w)).re) -
      (‖logDeriv g z‖ + (4 / 3 : ℝ) * ∑ w ∈ S, (m w : ℝ)) ≤ (logDeriv f z).re := by
  have hzcl : z ∈ closedBall 0 (7 / 4 : ℝ) := by
    rw [mem_closedBall_zero_iff]
    linarith
  have hid := congrArg Complex.re
    (logDeriv_eq_regular_add_zero_terms (7 / 4) S m hS f g z hzcl hzn hf0 hf hg heq)
  simp only [Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, Complex.ofReal_div, Complex.ofReal_ofNat] at hid
  have hcorr : -(4 / 3 : ℝ) * (∑ w ∈ S, (m w : ℝ)) ≤
      ∑ w ∈ S, (m w : ℝ) * (conj w / ((7 / 4 : ℂ) ^ 2 - conj w * z)).re := by
    rw [mul_comm, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w hw
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hn := canonical_correction_norm_le w z (mem_ball_zero_iff.mp (hS w hw)).le hz
    have hr := Complex.abs_re_le_norm (conj w / ((7 / 4 : ℂ) ^ 2 - conj w * z))
    linarith [neg_abs_le (conj w / ((7 / 4 : ℂ) ^ 2 - conj w * z)).re]
  have hgRe := Complex.abs_re_le_norm (logDeriv g z)
  linarith [neg_abs_le (logDeriv g z).re]

end Siegel
