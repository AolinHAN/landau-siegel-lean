import Siegel.CanonicalZeroRemoval

namespace Siegel

open Metric Filter
open scoped Topology

/-- A zero not listed among the removed factors would remain a zero of the regular part. -/
theorem zero_mem_of_regular_part (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (f g : ℂ → ℂ) (z : ℂ) (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (hgnz : g z ≠ 0)
    (heq : g =ᶠ[𝓝[≠] z] (fun w => f w * canonicalProduct R S m w))
    (hfz : f z = 0) : z ∈ S := by
  by_contra hz
  have hlocal := (hg.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hf.mul (canonicalProduct_analyticAt R S m z hz).continuousAt)).mp heq
  apply hgnz
  simpa [hfz] using hlocal.eq_of_nhds

/-- Positivity of the other zero poles allows the distinguished real zero to
be retained. Zeros below one half cost only an absolute additive constant. -/
theorem real_zero_pole_sum_lower (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w.re ≤ -1 ∧ 0 < m w)
    (s β : ℝ) (hs : 1 < s) (hβ : β < 1)
    (hmem : 1 / 2 < β → ((β - 2 : ℝ) : ℂ) ∈ S) :
    1 / (s - β) - 2 ≤
      ∑ w ∈ S, (m w : ℝ) * (1 / (((s - 2 : ℝ) : ℂ) - w)).re := by
  classical
  have hn (w : ℂ) (hw : w ∈ S) :
      0 ≤ (m w : ℝ) * (1 / (((s - 2 : ℝ) : ℂ) - w)).re := by
    apply mul_nonneg (Nat.cast_nonneg _)
    rw [one_div, Complex.inv_re]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [(hS w hw).1]
  by_cases hb : 1 / 2 < β
  · have hw := hmem hb
    have hsingle := Finset.single_le_sum hn hw
    have hterm : (1 / (((s - 2 : ℝ) : ℂ) - ((β - 2 : ℝ) : ℂ))).re = 1 / (s - β) := by
      rw [← Complex.ofReal_sub]
      have he : s - 2 - (β - 2) = s - β := by ring
      rw [he]
      norm_cast
    rw [hterm] at hsingle
    have hm : (1 : ℝ) ≤ m (((β - 2 : ℝ) : ℂ)) := by
      exact_mod_cast (hS _ hw).2
    have hp : 0 ≤ 1 / (s - β) := div_nonneg zero_le_one (by linarith)
    nlinarith
  · have hsum := Finset.sum_nonneg hn
    have hden : 1 / 2 ≤ s - β := by linarith
    have hrec : 1 / (s - β) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith

end Siegel
