import Siegel.CanonicalFactorBounds

namespace Siegel

open Metric Filter
open scoped Topology

noncomputable def canonicalProduct (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) : ℂ → ℂ :=
  fun z => ∏ w ∈ S, Complex.canonicalFactor R w z ^ m w

theorem canonicalProduct_meromorphic (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ) :
    MeromorphicOn (canonicalProduct R S m) Set.univ := by
  intro z _
  exact MeromorphicAt.fun_prod (fun w _ =>
    (Complex.meromorphicOn_canonicalFactor R w z trivial).pow (m w))

theorem canonicalProduct_order (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w ∈ ball 0 R) (z : ℂ) (hz : z ∈ closedBall 0 R) :
    meromorphicOrderAt (canonicalProduct R S m) z =
      -(((if z ∈ S then m z else 0 : ℕ) : ℤ) : WithTop ℤ) := by
  classical
  unfold canonicalProduct
  rw [meromorphicOrderAt_fun_prod (f := fun w x => Complex.canonicalFactor R w x ^ m w) (fun w _ =>
    (Complex.meromorphicOn_canonicalFactor R w z trivial).pow (m w))]
  have hterm (w : ℂ) (hw : w ∈ S) :
      meromorphicOrderAt (fun x => Complex.canonicalFactor R w x ^ m w) z =
        if w = z then -((m w : ℤ) : WithTop ℤ) else 0 := by
    rw [fun_meromorphicOrderAt_pow (Complex.meromorphicOn_canonicalFactor R w z trivial)]
    by_cases he : w = z
    · subst w
      rw [Complex.meromorphicOrderAt_canonicalFactor (hS z hw), if_pos rfl]
      change ((m z : ℤ) : WithTop ℤ) * ((-1 : ℤ) : WithTop ℤ) = _
      rw [← WithTop.coe_mul]
      simp
    · have hc : meromorphicOrderAt (Complex.canonicalFactor R w) z = 0 :=
        ((Complex.analyticOnNhd_canonicalFactor R w z (Ne.symm he)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr
          (Complex.canonicalFactor_ne_zero (hS w hw) hz (Ne.symm he))
      simp only [hc, mul_zero, if_neg he]
  rw [Finset.sum_congr rfl hterm]
  by_cases hzS : z ∈ S <;> simp [hzS]

/-- Removing the prescribed zeros with inverse Blaschke factors produces an
analytic function on the closed disk and a nonvanishing one in its interior. -/
theorem canonical_zero_removal (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w ∈ ball 0 R) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hord : ∀ z ∈ closedBall 0 R,
      (((if z ∈ S then m z else 0 : ℕ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z)
    (hexact : ∀ z ∈ ball 0 R,
      meromorphicOrderAt f z = (((if z ∈ S then m z else 0 : ℕ) : ℤ) : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 R) ∧
      (∀ z ∈ ball 0 R, g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 R,
        g =ᶠ[𝓝[≠] z] (fun w => f w * canonicalProduct R S m w)) := by
  classical
  let C := canonicalProduct R S m
  have hC : MeromorphicOn C (closedBall 0 R) :=
    fun z _ => canonicalProduct_meromorphic R S m z trivial
  have hraw : MeromorphicOn (f * C) (closedBall 0 R) := hf.meromorphicOn.mul hC
  let g := toMeromorphicNFOn (f * C) (closedBall 0 R)
  have hgNF : MeromorphicNFOn g (closedBall 0 R) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hgo (z : ℂ) (hz : z ∈ closedBall 0 R) : meromorphicOrderAt g z =
      -(((if z ∈ S then m z else 0 : ℕ) : ℤ) : WithTop ℤ) + meromorphicOrderAt f z := by
    rw [meromorphicOrderAt_congr (hraw.toMeromorphicNFOn_eq_self_on_nhdsNE hz),
      meromorphicOrderAt_mul (hf.meromorphicOn z hz) (hC z hz),
      canonicalProduct_order R S m hS z hz]
    exact add_comm _ _
  refine ⟨g, ?_, ?_, ?_⟩
  · intro z hz
    apply (hgNF hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [hgo z hz]
    have h := add_le_add_left (hord z hz)
      (-(((if z ∈ S then m z else 0 : ℕ) : ℤ) : WithTop ℤ))
    simpa [add_comm] using h
  · intro z hz
    apply (hgNF (ball_subset_closedBall hz)).meromorphicOrderAt_eq_zero_iff.mp
    rw [hgo z (ball_subset_closedBall hz), hexact z hz]
    simp
  · intro z hz
    exact hraw.toMeromorphicNFOn_eq_self_on_nhdsNE hz

theorem canonicalProduct_analyticAt (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (z : ℂ) (hz : z ∉ S) : AnalyticAt ℂ (canonicalProduct R S m) z := by
  apply S.analyticAt_fun_prod
  intro w hw
  exact (Complex.analyticOnNhd_canonicalFactor R w z
    (fun h => hz (h ▸ hw))).pow (m w)

theorem canonicalProduct_norm_sphere (R : ℝ) (S : Finset ℂ) (m : ℂ → ℕ)
    (hS : ∀ w ∈ S, w ∈ ball 0 R) (z : ℂ) (hz : z ∈ sphere 0 R) :
    ‖canonicalProduct R S m z‖ = 1 := by
  simp only [canonicalProduct, norm_prod, norm_pow]
  apply Finset.prod_eq_one
  intro w hw
  rw [Complex.norm_canonicalFactor_eval_circle_eq_one (hS w hw) hz, one_pow]

theorem canonicalProduct_norm_zero_ge (R : ℝ) (hR : 0 < R)
    (S : Finset ℂ) (m : ℂ → ℕ) (hS : ∀ w ∈ S, w ∈ ball 0 R) (h0 : (0 : ℂ) ∉ S) :
    1 ≤ ‖canonicalProduct R S m 0‖ := by
  simp only [canonicalProduct, norm_prod, norm_pow]
  apply Finset.one_le_prod
  intro w hw
  apply one_le_pow₀
  have hw0 : w ≠ 0 := fun h => h0 (h ▸ hw)
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hwR : ‖w‖ < R := mem_ball_zero_iff.mp (hS w hw)
  simp only [Complex.canonicalFactor, mul_zero, sub_zero, zero_sub,
    norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg,
    abs_of_pos hR]
  apply (le_div_iff₀ (mul_pos hR hwn)).mpr
  nlinarith

/-- A continued Blaschke product preserves boundary modulus, so the original
upper bound also holds throughout the disk. -/
theorem continued_canonicalProduct_norm_le (R : ℝ) (hR : 0 < R)
    (S : Finset ℂ) (m : ℂ → ℕ) (hS : ∀ w ∈ S, w ∈ ball 0 R)
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (heq : ∀ z ∈ closedBall 0 R,
      g =ᶠ[𝓝[≠] z] (fun w => f w * canonicalProduct R S m w))
    (M : ℝ) (hM : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M) :
    ∀ z ∈ ball 0 R, ‖g z‖ ≤ M := by
  have hd : DiffContOnCl ℂ g (ball 0 R) :=
    ⟨hg.differentiableOn.mono ball_subset_closedBall,
      hg.continuousOn.mono closure_ball_subset_closedBall⟩
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ (subset_closure hz)
  intro w hw
  have hwsp : w ∈ sphere 0 R := frontier_ball_subset_sphere hw
  have hwcl := sphere_subset_closedBall hwsp
  have hwn : w ∉ S := by
    intro hwS
    have hwlt := mem_ball_zero_iff.mp (hS w hwS)
    have hweq := mem_sphere_zero_iff_norm.mp hwsp
    linarith
  have hc := (canonicalProduct_analyticAt R S m w hwn).continuousAt
  have hpt := ((hg w hwcl).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hf w hwcl).continuousAt.mul hc)).mp (heq w hwcl) |>.eq_of_nhds
  rw [hpt, Pi.mul_apply, norm_mul, canonicalProduct_norm_sphere R S m hS w hwsp, mul_one]
  exact hM w hwsp

end Siegel
