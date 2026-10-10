import Siegel.GlobalLogDerivativeLimit
import Siegel.ReflectedZeroSums

namespace Siegel

open Set Metric Filter
open scoped Topology

/-- For a reflected entire function of order-one growth, the real zero sum
is convergent and the reflection removes the constant in its logarithmic derivative. -/
theorem symmetric_real_zero_sum (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (A : ℝ) (hA : 0 < A)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ w : ℂ, ‖w‖ ≤ n →
      Real.log ‖f w‖ ≤ A * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2))
    (hstrip : ∀ z, f z = 0 → z.re ∈ Icc (-2 : ℝ) (-1))
    (c : ℂ) (hc : c ≠ 0) (hreflect : ∀ z, f (-3 - z) = c * f z)
    (hld : ∀ z, logDeriv f (-3 - z) = -logDeriv f z)
    (x : ℝ) (hx : -1 < x) :
    Summable (fun z : ℂ => (MeromorphicOn.divisor f univ z : ℝ) * (1 / ((x : ℂ) - z)).re) ∧
      (∑' z : ℂ, (MeromorphicOn.divisor f univ z : ℝ) * (1 / ((x : ℂ) - z)).re) =
        (logDeriv f (x : ℂ)).re := by
  have han : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hm := han.meromorphicOn
  let y : ℂ := -3 - (x : ℂ)
  have hfx : f (x : ℂ) ≠ 0 := by
    intro hz
    have h := (hstrip _ hz).2
    simpa using (not_le_of_gt hx h)
  have hfy : f y ≠ 0 := by
    intro hz
    have h := (hstrip _ hz).1
    simp only [y, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.ofReal_re] at h
    linarith
  have hD (z : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor f univ z : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg han z
  have hzero (z : ℂ) (hz : MeromorphicOn.divisor f univ z ≠ 0) : f z = 0 := by
    by_contra hn
    have ho : meromorphicOrderAt f z = 0 :=
      ((hf.analyticAt z).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr hn
    have he : MeromorphicOn.divisor f univ z = 0 := by
      rw [hm.divisor_apply (mem_univ z), ho]
      simp
    exact hz he
  let a : ℂ → ℝ := fun z => (MeromorphicOn.divisor f univ z : ℝ) * (1 / ((x : ℂ) - z)).re
  let b : ℂ → ℝ := fun z => -(MeromorphicOn.divisor f univ z : ℝ) * (1 / (y - z)).re
  have ha (z : ℂ) : 0 ≤ a z := by
    by_cases hz : MeromorphicOn.divisor f univ z = 0
    · simp [a, hz]
    have hr := (hstrip z (hzero z hz)).2
    apply mul_nonneg (hD z)
    rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hb (z : ℂ) : 0 ≤ b z := by
    by_cases hz : MeromorphicOn.divisor f univ z = 0
    · simp [b, hz]
    have hr := (hstrip z (hzero z hz)).1
    change 0 ≤ -(MeromorphicOn.divisor f univ z : ℝ) * (1 / (y - z)).re
    rw [neg_mul, ← mul_neg]
    apply mul_nonneg (hD z)
    rw [one_div, Complex.inv_re, ← neg_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [y, Complex.sub_re, Complex.neg_re, Complex.re_ofNat, Complex.ofReal_re]
    linarith
  have hpos (z : ℂ) : 0 ≤ (MeromorphicOn.divisor f univ z : ℝ) *
      ((1 / ((x : ℂ) - z)).re - (1 / (y - z)).re) := by
    have hp := add_nonneg (ha z) (hb z)
    dsimp only [a, b] at hp
    nlinarith
  obtain ⟨hsum, hvalue⟩ := summable_divisor_mul_of_radial_limit f hm
    (fun z => (1 / ((x : ℂ) - z)).re - (1 / (y - z)).re) hpos
    ((logDeriv f (x : ℂ)).re - (logDeriv f y).re)
    (tendsto_disk_logDeriv_difference_re f hf hf0 A hA hbound (x : ℂ) y hfx hfy)
  have he : (fun z : ℂ => (MeromorphicOn.divisor f univ z : ℝ) *
      ((1 / ((x : ℂ) - z)).re - (1 / (y - z)).re)) = a + b := by
    ext z
    simp only [Pi.add_apply, a, b]
    ring
  rw [he] at hsum hvalue
  have hsa : Summable a := Summable.of_nonneg_of_le ha
    (fun z => le_add_of_nonneg_right (hb z)) hsum
  have hsb : Summable b :=
    (summable_reflected_zero_kernel_iff f hm (-3) c hc hreflect (x : ℂ)).mpr hsa
  have heq : (∑' z, a z) = ∑' z, b z :=
    tsum_reflected_zero_kernel f hm (-3) c hc hreflect (x : ℂ)
  change tsum (fun z : ℂ => a z + b z) = _ at hvalue
  rw [Summable.tsum_add hsa hsb] at hvalue
  have hy : (logDeriv f y).re = -(logDeriv f (x : ℂ)).re := by
    dsimp only [y]
    rw [hld, Complex.neg_re]
  refine ⟨hsa, ?_⟩
  change (∑' z, a z) = _
  rw [hy] at hvalue
  linarith only [hvalue, heq]

end Siegel
