import Siegel.RationalFace

/-! The complete nearest-point and supporting-face reduction of Lemma 3. -/

namespace Siegel.Interpolation

open Set
open scoped InnerProductSpace

/-- Four times the convex hull of a finite set of integer points. -/
noncomputable def fourHull (S : Finset (Fin 4 → ℤ)) :
    Set (EuclideanSpace ℝ (Fin 4)) :=
  (fun x => (4 : ℝ) • x) '' convexHull ℝ (latticePoint '' (S : Set (Fin 4 → ℤ)))

theorem latticePoint_add_sub (m n u : Fin 4 → ℤ) :
    latticePoint (m + n - u) = latticePoint m + latticePoint n - latticePoint u := by
  ext i
  simp [latticePoint]

/-- The geometric engine of Lemma 3. Translating about a suitable `m,u`
leaves nonzero values only on a rational hyperplane through `u`.
The hypotheses are precisely nonvanishing somewhere and vanishing on
the integer points of four times the convex hull. -/
theorem rational_face_reduction (S : Finset (Fin 4 → ℤ)) (hS : S.Nonempty)
    (F : (Fin 4 → ℤ) → ℂ) (hF : ∃ m, F m ≠ 0)
    (hvanish : ∀ m, latticePoint m ∈ fourHull S → F m = 0) :
    ∃ (m u : Fin 4 → ℤ) (r : (Fin 4 → ℚ) →ₗ[ℚ] ℚ),
      F m ≠ 0 ∧ u ∈ S ∧ r ≠ 0 ∧
      ∀ n ∈ S, F (m + n - u) ≠ 0 →
        r (fun i => (n i : ℚ) - (u i : ℚ)) = 0 := by
  classical
  let T : Set (EuclideanSpace ℝ (Fin 4)) := latticePoint '' (S : Set (Fin 4 → ℤ))
  let P := convexHull ℝ T
  let K := fourHull S
  have hPc : Convex ℝ P := convex_convexHull ℝ T
  have hPk : IsCompact P := (S.finite_toSet.image latticePoint).isCompact_convexHull ℝ
  have hKc : Convex ℝ K := by
    simpa [K, fourHull, P, T] using hPc.linear_image ((4 : ℝ) • LinearMap.id)
  have hKk : IsCompact K := hPk.image (by fun_prop)
  have hKn : K.Nonempty := by
    obtain ⟨u, hu⟩ := hS
    exact ⟨4 • latticePoint u, latticePoint u,
      subset_convexHull ℝ T ⟨u, hu, rfl⟩, rfl⟩
  obtain ⟨m, hm, y, ⟨x, hx, rfl⟩, hmin⟩ :=
    exists_closest_nonzero_lattice_point F hF hKk hKn
  have hy : (4 : ℝ) • x ∈ K := ⟨x, hx, rfl⟩
  let h := latticePoint m - (4 : ℝ) • x
  have hh : h ≠ 0 := by
    intro hz
    have heq : latticePoint m = (4 : ℝ) • x := sub_eq_zero.mp hz
    exact hm (hvanish m (heq.symm ▸ hy))
  let l : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℝ := (innerSL ℝ h).toLinearMap
  have hl : l ≠ 0 := by
    intro hz
    have htest := congrArg (fun f : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℝ => f h) hz
    have hinner : ⟪h, h⟫_ℝ = 0 := htest
    exact hh (inner_self_eq_zero.mp hinner)
  have hsupport : ∀ z ∈ T, l z ≤ l x := by
    intro z hz
    have hzP : z ∈ P := subset_convexHull ℝ T hz
    have hh' := closest_point_supporting hKc (latticePoint m) (4 • x) hy
      (hmin m hm) (4 • z) ⟨z, hzP, rfl⟩
    change ⟪h, (4 : ℝ) • z - (4 : ℝ) • x⟫_ℝ ≤ 0 at hh'
    simp only [inner_sub_right, inner_smul_right] at hh'
    change ⟪h, z⟫_ℝ ≤ ⟪h, x⟫_ℝ
    linarith
  obtain ⟨uu, ⟨u, hu, rfl⟩, huface, v, hv, hcalc⟩ :=
    supporting_vertex_sub_mem_three_hull T x hx l hl hsupport
  have hnonzero_on_face (n : Fin 4 → ℤ) (hn : n ∈ S) (hFn : F (m + n - u) ≠ 0) :
      ⟪h, latticePoint n - latticePoint u⟫_ℝ = 0 := by
    have hle := hsupport (latticePoint n) ⟨n, hn, rfl⟩
    rw [← huface] at hle
    change ⟪h, latticePoint n⟫_ℝ ≤ ⟪h, latticePoint u⟫_ℝ at hle
    by_contra hne
    have hpos : 0 < ⟪h, latticePoint u - latticePoint n⟫_ℝ := by
      simp only [inner_sub_right] at hne ⊢
      have hlt : ⟪h, latticePoint n⟫_ℝ < ⟪h, latticePoint u⟫_ℝ := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact False.elim (hne (by rw [heq]; ring))
      linarith
    have hnP : latticePoint n ∈ P := subset_convexHull ℝ T ⟨n, hn, rfl⟩
    have hpoint : (4 : ℝ) • x + latticePoint n - latticePoint u ∈ K := by
      refine ⟨(3 / 4 : ℝ) • v + (1 / 4 : ℝ) • latticePoint n,
        hPc hv hnP (by norm_num) (by norm_num) (by norm_num), ?_⟩
      calc
        (4 : ℝ) • ((3 / 4 : ℝ) • v + (1 / 4 : ℝ) • latticePoint n) =
            (3 : ℝ) • v + latticePoint n := by module
        _ = (4 : ℝ) • x + latticePoint n - latticePoint u := by rw [hcalc]; abel
    obtain ⟨η, hη, hη1, hdecrease⟩ :=
      translated_distance_decrease (latticePoint m) (4 • x) (latticePoint n) (latticePoint u) hpos
    have hz : ((4 : ℝ) • x + latticePoint n - latticePoint u) +
        η • ((4 : ℝ) • x - ((4 : ℝ) • x + latticePoint n - latticePoint u)) ∈ K := by
      have hc := hKc hpoint hy (sub_nonneg.mpr hη1.le) hη.le (by ring : 1 - η + η = 1)
      convert hc using 1
      module
    have hnmin := hmin (m + n - u) hFn _ hz
    rw [latticePoint_add_sub] at hnmin
    nlinarith [norm_nonneg (latticePoint m - (4 : ℝ) • x),
      norm_nonneg ((latticePoint m + latticePoint n - latticePoint u) -
        (((4 : ℝ) • x + latticePoint n - latticePoint u) +
          η • ((4 : ℝ) • x - ((4 : ℝ) • x + latticePoint n - latticePoint u))))]
  let D : Set (Fin 4 → ℚ) :=
    (fun n : Fin 4 → ℤ => fun i => (n i : ℚ) - (u i : ℚ)) ''
      {n | n ∈ S ∧ F (m + n - u) ≠ 0}
  have hD : ∀ d ∈ D, ⟪h, rationalPoint d⟫_ℝ = 0 := by
    rintro d ⟨n, ⟨hn, hFn⟩, rfl⟩
    have heq : rationalPoint (fun i => (n i : ℚ) - (u i : ℚ)) =
        latticePoint n - latticePoint u := by ext i; simp [rationalPoint, latticePoint]
    rw [heq]
    exact hnonzero_on_face n hn hFn
  obtain ⟨r, hr, hrD⟩ := exists_rational_normal D h hh hD
  refine ⟨m, u, r, hm, hu, hr, ?_⟩
  intro n hn hFn
  exact hrD _ ⟨n, ⟨hn, hFn⟩, rfl⟩

end Siegel.Interpolation
