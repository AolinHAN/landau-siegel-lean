import Siegel.Interpolation

/-! Polynomial constructions for Lemma 3. -/

namespace Siegel.Interpolation

open scoped BigOperators
open MvPolynomial

/-- The exponent vector corresponding to an index in the monomial rectangle. -/
noncomputable def rectangleExponent {t : Fin 3 → ℕ} (α : MonomialRectangle t) :
    Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => (α j : ℕ))

@[simp] theorem rectangleExponent_apply {t : Fin 3 → ℕ}
    (α : MonomialRectangle t) (j : Fin 3) : rectangleExponent α j = (α j : ℕ) := by
  simp [rectangleExponent]

theorem rectangleExponent_injective (t : Fin 3 → ℕ) :
    Function.Injective (@rectangleExponent t) := by
  intro α β h
  funext j
  apply Fin.ext
  have := congrArg (fun d : Fin 3 →₀ ℕ => d j) h
  simpa using this

/-- The actual polynomial represented by a rectangular coefficient vector. -/
noncomputable def rectanglePolynomial (t : Fin 3 → ℕ)
    (a : MonomialRectangle t → ℂ) : MvPolynomial (Fin 3) ℂ :=
  ∑ α, monomial (rectangleExponent α) (a α)

@[simp] theorem coeff_rectanglePolynomial (t : Fin 3 → ℕ)
    (a : MonomialRectangle t → ℂ) (α : MonomialRectangle t) :
    coeff (rectangleExponent α) (rectanglePolynomial t a) = a α := by
  classical
  simp [rectanglePolynomial, coeff_sum, coeff_monomial, (rectangleExponent_injective t).eq_iff]

theorem rectanglePolynomial_ne_zero (t : Fin 3 → ℕ)
    (a : MonomialRectangle t → ℂ) (ha : a ≠ 0) : rectanglePolynomial t a ≠ 0 := by
  intro h
  apply ha
  funext α
  have := congrArg (coeff (rectangleExponent α)) h
  simpa using this

@[simp] theorem eval_rectanglePolynomial (t : Fin 3 → ℕ)
    (a : MonomialRectangle t → ℂ) (z : Fin 3 → ℂ) :
    eval z (rectanglePolynomial t a) = evaluate t a z := by
  classical
  simp [rectanglePolynomial, evaluate, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem degreeOf_rectanglePolynomial_le (t : Fin 3 → ℕ)
    (a : MonomialRectangle t → ℂ) (j : Fin 3) :
    (rectanglePolynomial t a).degreeOf j ≤ t j := by
  classical
  apply (degreeOf_sum_le j Finset.univ _).trans
  apply Finset.sup_le
  intro α _
  by_cases ha : a α = 0
  · simp [ha]
  · rw [degreeOf_monomial_eq _ _ ha, rectangleExponent_apply]
    exact Nat.le_of_lt_succ (α j).isLt

/-- Equation (3.3), with an actual nonzero polynomial and the exact separate
degree bounds, for an arbitrary finite family of evaluation points. -/
theorem exists_nonzero_vanishing_polynomial {ι : Type*} [Fintype ι]
    (t : Fin 3 → ℕ) (z : ι → Fin 3 → ℂ)
    (hcard : Fintype.card ι < ∏ j, (t j + 1)) :
    ∃ R : MvPolynomial (Fin 3) ℂ, R ≠ 0 ∧
      (∀ j, R.degreeOf j ≤ t j) ∧ ∀ i, eval (z i) R = 0 := by
  obtain ⟨a, ha, haz⟩ := exists_nonzero_vanishing_coefficients t z hcard
  exact ⟨rectanglePolynomial t a, rectanglePolynomial_ne_zero t a ha,
    degreeOf_rectanglePolynomial_le t a, by simpa using haz⟩

/-- A complex polynomial cannot vanish on the entire integer lattice. -/
theorem exists_integer_nonzero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ m : Fin n → ℤ, eval (fun i => (m i : ℂ)) P ≠ 0 := by
  classical
  by_contra! h
  apply hP
  have hinfinite : (Set.range (fun m : ℤ => (m : ℂ))).Infinite :=
    Set.infinite_range_of_injective Int.cast_injective
  apply MvPolynomial.funext_set (fun _ => Set.range (fun m : ℤ => (m : ℂ)))
    (fun _ => hinfinite)
  intro z hz
  choose m hm using fun i => hz i (Set.mem_univ i)
  have hz' : z = fun i => (m i : ℂ) := funext fun i => (hm i).symm
  simp [hz', h]

/-- The degree-one polynomial attached to a linear functional. -/
noncomputable def linearPolynomial {n : ℕ}
    (l : (Fin n → ℂ) →ₗ[ℂ] ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ i, C (l (Pi.single i 1)) * X i

@[simp] theorem eval_linearPolynomial {n : ℕ}
    (l : (Fin n → ℂ) →ₗ[ℂ] ℂ) (z : Fin n → ℂ) :
    eval z (linearPolynomial l) = l z := by
  classical
  have hz : (∑ i, z i • Pi.single i (1 : ℂ)) = z := by
    ext j
    simp [Pi.single_apply]
  calc
    eval z (linearPolynomial l) = ∑ i, l (Pi.single i 1) * z i := by
      simp [linearPolynomial]
    _ = l (∑ i, z i • Pi.single i (1 : ℂ)) := by
      simp [map_sum, mul_comm]
    _ = l z := congrArg l hz

/-- Polynomial pullback by a complex linear map. -/
noncomputable def linearPullback {m n : ℕ}
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) :
    MvPolynomial (Fin n) ℂ →+* MvPolynomial (Fin m) ℂ :=
  eval₂Hom C (fun j => linearPolynomial ((LinearMap.proj j).comp A))

@[simp] theorem eval_linearPullback {m n : ℕ}
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (R : MvPolynomial (Fin n) ℂ) (z : Fin m → ℂ) :
    eval z (linearPullback A R) = eval (A z) R := by
  simp only [linearPullback, coe_eval₂Hom]
  rw [eval_eval₂]
  simp only [eval_linearPolynomial, LinearMap.comp_apply, LinearMap.proj_apply]
  have hC : (eval z).comp C = RingHom.id ℂ := by ext; simp
  rw [hC, eval₂_id]

theorem linearPullback_ne_zero {m n : ℕ}
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (hA : Function.Surjective A)
    (R : MvPolynomial (Fin n) ℂ) (hR : R ≠ 0) : linearPullback A R ≠ 0 := by
  intro h
  apply hR
  apply MvPolynomial.funext
  intro z
  obtain ⟨x, rfl⟩ := hA z
  rw [← eval_linearPullback, h]
  simp

/-- The nonvanishing lattice point required before the nearest-point
construction, with the surjective linear map in Lemma 3. -/
theorem exists_integer_nonzero_of_surjective
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (hA : Function.Surjective A)
    (R : MvPolynomial (Fin 3) ℂ) (hR : R ≠ 0) :
    ∃ m : Fin 4 → ℤ, eval (A (fun i => (m i : ℂ))) R ≠ 0 := by
  obtain ⟨m, hm⟩ := exists_integer_nonzero (linearPullback A R)
    (linearPullback_ne_zero A hA R hR)
  exact ⟨m, by simpa using hm⟩

/-- Translation of a polynomial by a fixed vector. -/
noncomputable def translatePolynomial {n : ℕ} (d : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →+* MvPolynomial (Fin n) ℂ :=
  eval₂Hom C (fun j => X j + C (d j))

@[simp] theorem eval_translatePolynomial {n : ℕ} (d z : Fin n → ℂ)
    (R : MvPolynomial (Fin n) ℂ) :
    eval z (translatePolynomial d R) = eval (z + d) R := by
  simp only [translatePolynomial, coe_eval₂Hom]
  rw [eval_eval₂]
  have hC : (eval z).comp C = RingHom.id ℂ := by ext; simp
  simp only [hC, eval_add, eval_X, eval_C, eval₂_id]
  rfl

/-- Translating the coordinates does not increase any separate degree. -/
theorem degreeOf_translatePolynomial_le {n : ℕ} (d : Fin n → ℂ)
    (R : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    (translatePolynomial d R).degreeOf j ≤ R.degreeOf j := by
  classical
  have hmon (a : Fin n →₀ ℕ) (c : ℂ) :
      (translatePolynomial d (monomial a c)).degreeOf j ≤ a j := by
    simp only [translatePolynomial, eval₂Hom_monomial]
    apply (degreeOf_C_mul_le _ _ _).trans
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply (degreeOf_prod_le _ _ _).trans
    calc
      _ ≤ ∑ i : Fin n, a i * (if i = j then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        apply (degreeOf_pow_le _ _ _).trans
        apply Nat.mul_le_mul_left
        apply (degreeOf_add_le j (X i) (C (d i))).trans
        simp [degreeOf_X, eq_comm]
      _ = a j := by simp
  conv_lhs => rw [R.as_sum]
  rw [map_sum]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro a ha
  exact (hmon a (R.coeff a)).trans (le_degreeOf_of_mem_support j ha)

theorem totalDegree_linearPolynomial_le {n : ℕ}
    (l : (Fin n → ℂ) →ₗ[ℂ] ℂ) : (linearPolynomial l).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i hi
  exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])

/-- Every coordinate of the inverse on a transverse hyperplane is the
evaluation of an affine polynomial of total degree at most one. -/
theorem exists_hyperplane_coordinate_polynomials
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ)
    (r : (Fin 4 → ℂ) →ₗ[ℂ] ℂ) (k : ℂ)
    (hA : Function.Surjective A) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hr : r c ≠ 0) :
    ∃ L : Fin 4 → MvPolynomial (Fin 3) ℂ,
      (∀ i, (L i).totalDegree ≤ 1) ∧
      ∀ x : Fin 4 → ℂ, r x = k → ∀ i, eval (A x) (L i) = x i := by
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  let L : Fin 4 → MvPolynomial (Fin 3) ℂ := fun i =>
    linearPolynomial ((LinearMap.proj i).comp B) +
      C (c i / r c) * (C k + C (-1) * linearPolynomial (r.comp B))
  have hL : ∀ i, (L i).totalDegree ≤ 1 := by
    intro i
    apply (totalDegree_add _ _).trans
    apply max_le (totalDegree_linearPolynomial_le _)
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    exact (totalDegree_mul _ _).trans (by simpa using totalDegree_linearPolynomial_le (r.comp B))
  have hc : A c = 0 := by
    change c ∈ LinearMap.ker A
    rw [hker]
    exact Submodule.mem_span_singleton_self c
  refine ⟨L, hL, ?_⟩
  intro x hx i
  have hBx : A (B (A x)) = A x := by
    have := congrArg (fun f : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) => f (A x)) hB
    exact this
  have hcorr : hyperplaneCorrection r c k (B (A x)) = x := by
    apply hyperplane_preimage_unique A r c k hker hr
    · exact hyperplaneCorrection_mem r c k _ hr
    · exact hx
    · rw [hyperplaneCorrection_image A r c k _ hc, hBx]
  calc
    eval (A x) (L i) = hyperplaneCorrection r c k (B (A x)) i := by
      simp only [L, eval_add, eval_mul, eval_C, eval_linearPolynomial,
        LinearMap.comp_apply, LinearMap.proj_apply, hyperplaneCorrection,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    _ = x i := congrFun hcorr i

/-- Every polynomial with the separate degree bounds is represented by
the finite coefficient evaluation map used in the exact Lemma 3 target. -/
theorem polynomial_evaluation_mem_range
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (N : ℕ) (t : Fin 3 → ℕ)
    (P : MvPolynomial (Fin 3) ℂ) (hP : ∀ j, P.degreeOf j ≤ t j) :
    (fun n : IntegerBox N => eval (A (boxPoint n)) P) ∈
      LinearMap.range (evaluationMap A N t) := by
  classical
  have hsum : (fun n : IntegerBox N => eval (A (boxPoint n)) P) =
      ∑ d ∈ P.support, (fun n => eval (A (boxPoint n)) (monomial d (P.coeff d))) := by
    funext n
    simp only [Finset.sum_apply]
    rw [← map_sum, ← P.as_sum]
  rw [hsum]
  apply Submodule.sum_mem
  intro d hd
  let α : MonomialRectangle t := fun j =>
    ⟨d j, Nat.lt_succ_of_le ((le_degreeOf_of_mem_support j hd).trans (hP j))⟩
  refine ⟨Pi.single α (P.coeff d), ?_⟩
  funext n
  simp [evaluationMap, evaluate, Pi.single_apply, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), α]

end Siegel.Interpolation
