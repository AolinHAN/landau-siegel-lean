import Siegel.ConvexGeometry

/-! Rational hyperplanes containing the integer supporting face in Lemma 3. -/

namespace Siegel.Interpolation

open scoped InnerProductSpace

/-- Rational vectors viewed in real Euclidean four-space. -/
noncomputable def rationalPoint : (Fin 4 → ℚ) →ₗ[ℚ] EuclideanSpace ℝ (Fin 4) where
  toFun x := (EuclideanSpace.equiv (Fin 4) ℝ).symm (fun i => (x i : ℝ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Rat.smul_def]

/-- Restriction of a real inner-product functional to rational vectors. -/
noncomputable def rationalNormal (h : EuclideanSpace ℝ (Fin 4)) :
    (Fin 4 → ℚ) →ₗ[ℚ] ℝ :=
  ((innerSL ℝ h).toLinearMap.restrictScalars ℚ).comp rationalPoint

theorem rationalNormal_ne_zero (h : EuclideanSpace ℝ (Fin 4)) (hh : h ≠ 0) :
    rationalNormal h ≠ 0 := by
  intro hz
  apply hh
  ext i
  have htest := congrArg (fun l : (Fin 4 → ℚ) →ₗ[ℚ] ℝ => l (Pi.single i 1)) hz
  simpa [rationalNormal, rationalPoint, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Pi.single_apply, apply_ite] using htest

/-- A real nonzero normal annihilating rational differences implies the
existence of a nonzero rational normal annihilating the same differences.
This avoids assuming a rational normal merely from a real supporting plane. -/
theorem exists_rational_normal (D : Set (Fin 4 → ℚ))
    (h : EuclideanSpace ℝ (Fin 4)) (hh : h ≠ 0)
    (hD : ∀ d ∈ D, ⟪h, rationalPoint d⟫_ℝ = 0) :
    ∃ r : (Fin 4 → ℚ) →ₗ[ℚ] ℚ, r ≠ 0 ∧ ∀ d ∈ D, r d = 0 := by
  let V := Submodule.span ℚ D
  have hle : V ≤ LinearMap.ker (rationalNormal h) := by
    apply Submodule.span_le.mpr
    intro d hd
    exact hD d hd
  have hproper : V ≠ ⊤ := by
    intro htop
    apply rationalNormal_ne_zero h hh
    ext x
    exact hle (by rw [htop]; trivial)
  obtain ⟨r, hr, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hproper) inferInstance
  refine ⟨r, hr, ?_⟩
  intro d hd
  have hdV : d ∈ V := Submodule.subset_span hd
  have hrV : r d ∈ V.map r := Submodule.mem_map_of_mem hdV
  rwa [hmap, Submodule.mem_bot] at hrV

theorem rational_functional_eq_sum (r : (Fin 4 → ℚ) →ₗ[ℚ] ℚ) (x : Fin 4 → ℚ) :
    r x = ∑ i, r (Pi.single i 1) * x i := by
  have hx : (∑ i, x i • Pi.single i (1 : ℚ)) = x := by
    ext i
    simp [Pi.single_apply]
  calc
    r x = r (∑ i, x i • Pi.single i (1 : ℚ)) := congrArg r hx.symm
    _ = _ := by simp [map_sum, mul_comm]

/-- Scalar extension of a rational hyperplane normal to complex space. -/
noncomputable def complexifyNormal (r : (Fin 4 → ℚ) →ₗ[ℚ] ℚ) :
    (Fin 4 → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i, (r (Pi.single i 1) : ℂ) • LinearMap.proj i

theorem complexifyNormal_rat (r : (Fin 4 → ℚ) →ₗ[ℚ] ℚ) (x : Fin 4 → ℚ) :
    complexifyNormal r (fun i => (x i : ℂ)) = (r x : ℂ) := by
  rw [rational_functional_eq_sum]
  simp [complexifyNormal]

theorem complexifyNormal_transverse (r : (Fin 4 → ℚ) →ₗ[ℚ] ℚ) (hr : r ≠ 0)
    (c : Fin 4 → ℂ) (hc : LinearIndependent ℚ c) : complexifyNormal r c ≠ 0 := by
  have hr' : (fun i => r (Pi.single i 1)) ≠ 0 := by
    intro hz
    apply hr
    apply LinearMap.ext
    intro x
    change r x = 0
    rw [rational_functional_eq_sum]
    have hzero (i : Fin 4) : r (Pi.single i 1) = 0 := congrFun hz i
    simp [hzero]
  have h := rational_normal_transverse c hc (fun i => r (Pi.single i 1)) hr'
  simpa [complexifyNormal] using h

end Siegel.Interpolation
