import Siegel.CompletedLFunction
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Siegel

open Set

/-- Translation preserves the multiplicity at the translated point. -/
theorem divisor_translate_univ (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c z : ℂ) :
    MeromorphicOn.divisor (fun w => f (w + c)) univ z =
      MeromorphicOn.divisor f univ (z + c) := by
  have ha : AnalyticOnNhd ℂ f univ := fun w _ => hf.analyticAt w
  have hb : AnalyticOnNhd ℂ (fun w => f (w + c)) univ := by
    intro w hw
    exact (hf.analyticAt (w + c)).comp (f := fun v : ℂ => v + c) (by fun_prop)
  rw [hb.meromorphicOn.divisor_apply (mem_univ z),
    ha.meromorphicOn.divisor_apply (mem_univ (z + c))]
  congr 1
  exact meromorphicOrderAt_comp_of_deriv_ne_zero
    (by fun_prop : AnalyticAt ℂ (fun w : ℂ => w + c) z) (by simp)

/-- Logarithmic derivatives commute with translations. -/
theorem logDeriv_translate (f : ℂ → ℂ) (hf : Differentiable ℂ f) (c z : ℂ) :
    logDeriv (fun w => f (w + c)) z = logDeriv f (z + c) := by
  change logDeriv (f ∘ (fun w : ℂ => w + c)) z = _
  rw [logDeriv_comp (g := fun w : ℂ => w + c) (hf (z + c)) (by fun_prop)]
  simp

/-- Translating the origin does not change summability of the real zero kernel. -/
theorem summable_zero_kernel_translate_iff (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c s : ℂ) :
    Summable (fun z => (MeromorphicOn.divisor (fun w => f (w + c)) univ z : ℝ) *
      (1 / (s - c - z)).re) ↔
    Summable (fun z => (MeromorphicOn.divisor f univ z : ℝ) * (1 / (s - z)).re) := by
  have he (z : ℂ) : s - c - z = s - (z + c) := by ring
  simpa only [Function.comp_def, Equiv.coe_addRight, divisor_translate_univ f hf, he]
    using ((Equiv.addRight c).summable_iff (f := fun z =>
      (MeromorphicOn.divisor f univ z : ℝ) * (1 / (s - z)).re))

/-- Translation merely reindexes the multiplicity-weighted sum over zeros. -/
theorem tsum_zero_kernel_translate (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c s : ℂ) :
    (∑' z, (MeromorphicOn.divisor (fun w => f (w + c)) univ z : ℝ) *
      (1 / (s - c - z)).re) =
    ∑' z, (MeromorphicOn.divisor f univ z : ℝ) * (1 / (s - z)).re := by
  have he (z : ℂ) : s - c - z = s - (z + c) := by ring
  simpa only [Equiv.coe_addRight, divisor_translate_univ f hf, he]
    using (Equiv.addRight c).tsum_eq (fun z =>
      (MeromorphicOn.divisor f univ z : ℝ) * (1 / (s - z)).re)

end Siegel
