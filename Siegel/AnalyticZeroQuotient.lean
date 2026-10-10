import Mathlib

namespace Siegel

open Filter Function
open scoped Topology

/-- Remove a finite divisor bounded by the zero orders of an analytic function.
The quotient is constructed by removable continuation, including at the zeros. -/
theorem exists_analytic_zero_quotient (f : ℂ → ℂ) (U : Set ℂ)
    (hf : AnalyticOnNhd ℂ f U) (D : ℂ → ℤ) (hfin : D.HasFiniteSupport)
    (hD : ∀ z, 0 ≤ D z)
    (horder : ∀ z ∈ U, (D z : WithTop ℤ) ≤ meromorphicOrderAt f z) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U, f z = (∏ᶠ w, (· - w) ^ D w) z * g z) ∧
      (∀ z ∈ U, meromorphicOrderAt f z = (D z : WithTop ℤ) → g z ≠ 0) := by
  let P : ℂ → ℂ := ∏ᶠ w, (· - w) ^ D w
  have hPa (z : ℂ) : AnalyticAt ℂ P z := Function.FactorizedRational.analyticAt (hD z)
  have hPm : MeromorphicOn P U := fun z _ => (hPa z).meromorphicAt
  have hQ : MeromorphicOn (P⁻¹ * f) U := hPm.inv.mul hf.meromorphicOn
  let g : ℂ → ℂ := toMeromorphicNFOn (P⁻¹ * f) U
  have hgNF : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn _ _
  have hgo (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt g z = -(D z : WithTop ℤ) + meromorphicOrderAt f z := by
    rw [meromorphicOrderAt_congr (hQ.toMeromorphicNFOn_eq_self_on_nhdsNE hz),
      meromorphicOrderAt_mul (hPm z hz).inv (hf.meromorphicOn z hz), meromorphicOrderAt_inv]
    rw [show meromorphicOrderAt P z = (D z : WithTop ℤ) from
      Function.FactorizedRational.meromorphicOrderAt_eq D hfin]
  have hga : AnalyticOnNhd ℂ g U := by
    intro z hz
    apply (hgNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [hgo z hz]
    have h := add_le_add_left (horder z hz) (-(D z : WithTop ℤ))
    simpa [add_comm] using h
  refine ⟨g, hga, ?_, ?_⟩
  · intro z hz
    have hPnz : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hPa z).meromorphicAt).mp
        (Function.FactorizedRational.meromorphicOrderAt_ne_top D)
    have he : f =ᶠ[𝓝[≠] z] P * g := by
      filter_upwards [hPnz, hQ.toMeromorphicNFOn_eq_self_on_nhdsNE hz] with w hw hgw
      simp only [Pi.mul_apply, Pi.inv_apply] at hgw ⊢
      change g w = (P w)⁻¹ * f w at hgw
      rw [hgw]
      field_simp
    exact ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hPa z).continuousAt.mul (hga z hz).continuousAt)).mp he |>.eq_of_nhds
  · intro z hz hze
    apply (hgNF hz).meromorphicOrderAt_eq_zero_iff.mp
    rw [hgo z hz, hze]
    simp

end Siegel
