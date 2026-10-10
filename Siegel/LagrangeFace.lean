import Siegel.InterpolationPolynomial

/-! Bounded-degree Lagrange selectors for the supporting face in Lemma 3. -/

namespace Siegel.Interpolation

open MvPolynomial

/-- A univariate Lagrange selector composed with one affine coordinate. -/
noncomputable def coordinateSelector (N u : ℕ) (P : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 3) ℂ :=
  ∏ a ∈ (Finset.range N).erase u,
    C (((u : ℂ) - (a : ℂ))⁻¹) * (P - C (a : ℂ))

theorem eval_coordinateSelector_self (N u : ℕ) (P : MvPolynomial (Fin 3) ℂ)
    (z : Fin 3 → ℂ) (hz : eval z P = (u : ℂ)) :
    eval z (coordinateSelector N u P) = 1 := by
  classical
  rw [coordinateSelector, map_prod]
  apply Finset.prod_eq_one
  intro a ha
  have hau : a ≠ u := (Finset.mem_erase.mp ha).1
  have hne : (u : ℂ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hau)
  simp [hz, hne]

theorem eval_coordinateSelector_other (N u v : ℕ) (hv : v < N) (hvu : v ≠ u)
    (P : MvPolynomial (Fin 3) ℂ) (z : Fin 3 → ℂ) (hz : eval z P = (v : ℂ)) :
    eval z (coordinateSelector N u P) = 0 := by
  classical
  rw [coordinateSelector, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hvu, Finset.mem_range.mpr hv⟩)
  simp [hz]

theorem totalDegree_coordinateSelector_le (N u : ℕ) (hu : u < N)
    (P : MvPolynomial (Fin 3) ℂ) (hP : P.totalDegree ≤ 1) :
    (coordinateSelector N u P).totalDegree ≤ N - 1 := by
  classical
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _a ∈ (Finset.range N).erase u, 1 := by
      apply Finset.sum_le_sum
      intro a ha
      apply (totalDegree_mul _ _).trans
      simpa only [totalDegree_C, zero_add] using
        (totalDegree_sub_C_le P (a : ℂ)).trans hP
    _ = N - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_range.mpr hu)]

/-- Three coordinates determine a point on a hyperplane whose remaining
coordinate has a nonzero coefficient. -/
theorem hyperplane_eq_of_other_coordinates
    (r : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (i₀ : Fin 4)
    (hr : r (Pi.single i₀ 1) ≠ 0) (x y : Fin 4 → ℂ)
    (hxy : r x = r y) (hcoords : ∀ i, i ≠ i₀ → x i = y i) : x = y := by
  classical
  have hdiff : x - y = (x i₀ - y i₀) • Pi.single i₀ 1 := by
    ext i
    by_cases hi : i = i₀
    · subst i
      simp
    · simp [hi, hcoords i hi]
  have heq : (x i₀ - y i₀) * r (Pi.single i₀ 1) = 0 := by
    rw [← smul_eq_mul, ← map_smul, ← hdiff, map_sub, hxy, sub_self]
  have hzero := (mul_eq_zero.mp heq).resolve_right hr
  apply sub_eq_zero.mp
  rw [hdiff, hzero, zero_smul]

/-- The full three-coordinate selector used on page 5: it has total degree
at most `3*(N-1)` and isolates `u` among the box points on the hyperplane. -/
theorem exists_face_selector
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ)
    (r : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (k : ℂ)
    (hA : Function.Surjective A) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hrc : r c ≠ 0) (i₀ : Fin 4) (hr : r (Pi.single i₀ 1) ≠ 0)
    (N : ℕ) (u : IntegerBox N) (hu : r (boxPoint u) = k) :
    ∃ Q : MvPolynomial (Fin 3) ℂ,
      Q.totalDegree ≤ 3 * (N - 1) ∧ eval (A (boxPoint u)) Q = 1 ∧
      ∀ n : IntegerBox N, r (boxPoint n) = k → n ≠ u →
        eval (A (boxPoint n)) Q = 0 := by
  classical
  obtain ⟨L, hL, hcoord⟩ := exists_hyperplane_coordinate_polynomials A c r k hA hker hrc
  let Q : MvPolynomial (Fin 3) ℂ :=
    ∏ i ∈ (Finset.univ : Finset (Fin 4)).erase i₀,
      coordinateSelector N (u i : ℕ) (L i)
  have hdeg : Q.totalDegree ≤ 3 * (N - 1) := by
    apply (totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 4)).erase i₀, (N - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact totalDegree_coordinateSelector_le N (u i) (u i).isLt (L i) (hL i)
      _ = _ := by simp [Finset.card_erase_of_mem, Nat.mul_comm]
  refine ⟨Q, hdeg, ?_, ?_⟩
  · rw [show Q = _ from rfl, map_prod]
    apply Finset.prod_eq_one
    intro i hi
    exact eval_coordinateSelector_self N (u i) (L i) _ (hcoord _ hu i)
  · intro n hn hnu
    have hex : ∃ i : Fin 4, i ≠ i₀ ∧ n i ≠ u i := by
      by_contra! h
      have hbox : boxPoint n = boxPoint u :=
        hyperplane_eq_of_other_coordinates r i₀ hr _ _ (hn.trans hu.symm)
          (fun i hi => by simp [boxPoint, h i hi])
      apply hnu
      funext i
      apply Fin.ext
      have hi := congrFun hbox i
      simp only [boxPoint] at hi
      exact_mod_cast hi
    obtain ⟨i, hi, hni⟩ := hex
    rw [show Q = _ from rfl, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    exact eval_coordinateSelector_other N (u i) (n i) (n i).isLt
      (fun h => hni (Fin.ext h)) (L i) _ (hcoord _ hn i)

end Siegel.Interpolation
