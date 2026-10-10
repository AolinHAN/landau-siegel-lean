import Siegel.RadialZeroSums

/-! # Reflection of the zero divisor and the real zero kernels

A functional equation `f(c₀-z) = c*f(z)` with `c ≠ 0` preserves zero
multiplicities. Reindexing by the reflection identifies the two nonnegative
kernel sums at reflected evaluation points.
-/

namespace Siegel

open Filter Topology Function

/-- Reflection about `c₀/2` as an equivalence of the complex plane. -/
def affineReflection (c₀ : ℂ) : ℂ ≃ ℂ where
  toFun z := c₀ - z
  invFun z := c₀ - z
  left_inv z := sub_sub_cancel c₀ z
  right_inv z := sub_sub_cancel c₀ z

theorem meromorphicOrderAt_reflection (f : ℂ → ℂ) (c₀ c : ℂ) (hc : c ≠ 0)
    (hreflect : ∀ z, f (c₀ - z) = c * f z) (z : ℂ) :
    meromorphicOrderAt f (c₀ - z) = meromorphicOrderAt f z := by
  have hcomp : f ∘ (fun w => c₀ - w) = (fun _ => c) * f := by
    funext w
    exact hreflect w
  have hd : deriv (fun w : ℂ => c₀ - w) z = -1 := by
    exact ((hasDerivAt_id z).const_sub c₀).deriv
  calc
    meromorphicOrderAt f (c₀ - z) =
        meromorphicOrderAt (f ∘ (fun w => c₀ - w)) z :=
      (meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by rw [hd]; norm_num)).symm
    _ = meromorphicOrderAt ((fun _ => c) * f) z := congrArg (fun g => meromorphicOrderAt g z) hcomp
    _ = meromorphicOrderAt f z :=
      meromorphicOrderAt_mul_of_ne_zero (by fun_prop : AnalyticAt ℂ (fun _ => c) z) hc

/-- Multiplicities in the global divisor are preserved by the functional
 equation's reflection. -/
theorem divisor_reflection (f : ℂ → ℂ) (hf : MeromorphicOn f Set.univ)
    (c₀ c : ℂ) (hc : c ≠ 0) (hreflect : ∀ z, f (c₀ - z) = c * f z) (z : ℂ) :
    MeromorphicOn.divisor f Set.univ (c₀ - z) = MeromorphicOn.divisor f Set.univ z := by
  rw [hf.divisor_apply (Set.mem_univ _), hf.divisor_apply (Set.mem_univ _),
    meromorphicOrderAt_reflection f c₀ c hc hreflect z]

/-- The real Cauchy kernel at the reflected zero is the negative kernel at
 the reflected evaluation point. -/
theorem reflected_zero_kernel (f : ℂ → ℂ) (hf : MeromorphicOn f Set.univ)
    (c₀ c : ℂ) (hc : c ≠ 0) (hreflect : ∀ z, f (c₀ - z) = c * f z) (x z : ℂ) :
    (MeromorphicOn.divisor f Set.univ (c₀ - z) : ℝ) * (1 / (x - (c₀ - z))).re =
      -(MeromorphicOn.divisor f Set.univ z : ℝ) * (1 / ((c₀ - x) - z)).re := by
  rw [divisor_reflection f hf c₀ c hc hreflect z]
  have hden : x - (c₀ - z) = -((c₀ - x) - z) := by ring
  rw [hden]
  simp only [one_div, inv_neg, Complex.neg_re]
  ring

/-- The reflected kernels are summable simultaneously. -/
theorem summable_reflected_zero_kernel_iff (f : ℂ → ℂ)
    (hf : MeromorphicOn f Set.univ) (c₀ c : ℂ) (hc : c ≠ 0)
    (hreflect : ∀ z, f (c₀ - z) = c * f z) (x : ℂ) :
    Summable (fun z => -(MeromorphicOn.divisor f Set.univ z : ℝ) *
      (1 / ((c₀ - x) - z)).re) ↔
    Summable (fun z => (MeromorphicOn.divisor f Set.univ z : ℝ) * (1 / (x - z)).re) := by
  have heq : (fun z => -(MeromorphicOn.divisor f Set.univ z : ℝ) *
      (1 / ((c₀ - x) - z)).re) =
      (fun z => (MeromorphicOn.divisor f Set.univ z : ℝ) * (1 / (x - z)).re) ∘
        affineReflection c₀ := by
    funext z
    exact (reflected_zero_kernel f hf c₀ c hc hreflect x z).symm
  rw [heq]
  exact (affineReflection c₀).summable_iff

/-- Reflection identifies the two global kernel sums. The reindexing
identity itself is valid even before establishing summability. -/
theorem tsum_reflected_zero_kernel (f : ℂ → ℂ) (hf : MeromorphicOn f Set.univ)
    (c₀ c : ℂ) (hc : c ≠ 0) (hreflect : ∀ z, f (c₀ - z) = c * f z) (x : ℂ) :
    (∑' z, (MeromorphicOn.divisor f Set.univ z : ℝ) * (1 / (x - z)).re) =
      ∑' z, -(MeromorphicOn.divisor f Set.univ z : ℝ) * (1 / ((c₀ - x) - z)).re := by
  calc
    _ = ∑' z, (MeromorphicOn.divisor f Set.univ (c₀ - z) : ℝ) *
        (1 / (x - (c₀ - z))).re :=
      ((affineReflection c₀).tsum_eq _).symm
    _ = _ := tsum_congr (reflected_zero_kernel f hf c₀ c hc hreflect x)

end Siegel
