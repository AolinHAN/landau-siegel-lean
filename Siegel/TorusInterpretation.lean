import Siegel.InterpolationBudgets
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # The torus interpretation in Remark 5

The nonnegative exponents used in the paper define regular functions on the
four-dimensional torus. We use actual multivariate polynomials and partial
derivatives, then evaluate the resulting functions at the torus identity.
-/

namespace Siegel.Torus

open MvPolynomial Siegel.Interpolation
open scoped BigOperators

abbrev Polynomial := MvPolynomial (Fin 4) ℂ

/-- The Euler vector field `D_j = ∑ i, A_{ji} X_i ∂/∂X_i`. -/
noncomputable def euler
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (j : Fin 3) :
    Polynomial →ₗ[ℂ] Polynomial where
  toFun P := ∑ i, (A (Pi.single i 1) j) • (X i * pderiv i P)
  map_add' P Q := by
    simp [map_add, mul_add, smul_add, Finset.sum_add_distrib]
  map_smul' a P := by
    simp only [Derivation.map_smul, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact smul_comm (A (Pi.single i 1) j) a (X i * pderiv i P)

theorem euler_apply
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (j : Fin 3) (P : Polynomial) :
    euler A j P = ∑ i, (A (Pi.single i 1) j) • (X i * pderiv i P) := rfl

/-- Monomials are simultaneous eigenvectors for the Euler vector fields. -/
theorem euler_monomial
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (j : Fin 3)
    (n : Fin 4 →₀ ℕ) (a : ℂ) :
    euler A j (monomial n a) =
      A (fun i => (n i : ℂ)) j • monomial n a := by
  have hv : (∑ i : Fin 4, (n i : ℂ) • Pi.single i (1 : ℂ)) =
      (fun i => (n i : ℂ)) := by
    ext i
    simp [Pi.single_apply]
  have hA : A (fun i => (n i : ℂ)) j =
      ∑ i : Fin 4, A (Pi.single i 1) j * (n i : ℂ) := by
    rw [← hv, map_sum]
    simp [mul_comm]
  rw [euler_apply, hA, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [X_mul_pderiv_monomial, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

/-- Iterating one vector field raises its monomial eigenvalue to a power. -/
theorem euler_pow_monomial
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (j : Fin 3) (k : ℕ)
    (n : Fin 4 →₀ ℕ) (a : ℂ) :
    (euler A j ^ k) (monomial n a) =
      (A (fun i => (n i : ℂ)) j) ^ k • monomial n a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, euler_monomial, map_smul, ih, smul_smul]
    congr 1
    ring

/-- The rectangular mixed operator `D₁^α₁ D₂^α₂ D₃^α₃`. -/
noncomputable def mixedEuler
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (α : Fin 3 → ℕ) :
    Polynomial →ₗ[ℂ] Polynomial :=
  (euler A 0 ^ α 0) * (euler A 1 ^ α 1) * (euler A 2 ^ α 2)

theorem mixedEuler_monomial
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (α : Fin 3 → ℕ)
    (n : Fin 4 →₀ ℕ) (a : ℂ) :
    mixedEuler A α (monomial n a) =
      (∏ j, (A (fun i => (n i : ℂ)) j) ^ α j) • monomial n a := by
  simp only [mixedEuler, Module.End.mul_apply, euler_pow_monomial, map_smul,
    smul_smul, Fin.prod_univ_three]
  congr 1
  ring

/-- The displayed identity of Remark 5, including arbitrary monomial
coefficients. The tuple `(1,1,1,1)` is the identity of the torus. -/
theorem eval_one_mixedEuler_monomial
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (α : Fin 3 → ℕ)
    (n : Fin 4 →₀ ℕ) (a : ℂ) :
    eval (fun _ => 1) (mixedEuler A α (monomial n a)) =
      a * ∏ j, (A (fun i => (n i : ℂ)) j) ^ α j := by
  rw [mixedEuler_monomial]
  simp [MvPolynomial.smul_eq_C_mul, eval_monomial, Finsupp.prod, mul_comm]


/-- The Euler operators satisfy the Leibniz rule of vector fields. -/
theorem euler_leibniz
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (j : Fin 3) (P Q : Polynomial) :
    euler A j (P * Q) = euler A j P * Q + P * euler A j Q := by
  simp only [euler_apply, pderiv_mul, mul_add, smul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp [mul_assoc]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [mul_left_comm]

/-- The three vector fields commute on every polynomial. -/
theorem euler_commute
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (j k : Fin 3) (P : Polynomial) :
    euler A j (euler A k P) = euler A k (euler A j P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial n a => simp only [euler_monomial, map_smul, smul_smul, mul_comm]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- A polynomial supported in the exponent box `E_N`. -/
noncomputable def boxPolynomial (N : ℕ) (v : IntegerBox N → ℂ) : Polynomial :=
  ∑ n, monomial (Finsupp.equivFunOnFinite.symm (fun i => (n i : ℕ))) (v n)

/-- The rectangular jets of a box polynomial are exactly the finite sums
against the rows of Corollary 4. -/
theorem eval_one_mixedEuler_boxPolynomial
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (N : ℕ) (α : Fin 3 → ℕ)
    (v : IntegerBox N → ℂ) :
    eval (fun _ => 1) (mixedEuler A α (boxPolynomial N v)) =
      ∑ n, v n * ∏ j, (A (boxPoint n) j) ^ α j := by
  simp only [boxPolynomial, map_sum, eval_one_mixedEuler_monomial,
    Finsupp.coe_equivFunOnFinite_symm]
  rfl

/-- Surjective interpolation is equivalent to detecting every nonzero box
polynomial by one of its rectangular Euler jets. -/
theorem coefficients_eq_zero_of_rectangular_jets
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (N : ℕ) (t : Fin 3 → ℕ)
    (hsurj : Function.Surjective (evaluationMap A N t))
    (v : IntegerBox N → ℂ)
    (hjets : ∀ α : MonomialRectangle t,
      eval (fun _ => 1) (mixedEuler A (fun j => (α j : ℕ)) (boxPolynomial N v)) = 0) :
    v = 0 := by
  classical
  have hrows (α : MonomialRectangle t) :
      (∑ n, v n * ∏ j, (A (boxPoint n) j) ^ (α j : ℕ)) = 0 := by
    simpa only [eval_one_mixedEuler_boxPolynomial] using hjets α
  funext n₀
  obtain ⟨b, hb⟩ := hsurj (Pi.single n₀ 1)
  have hsum : (∑ n, v n * evaluationMap A N t b n) = 0 := by
    change (∑ n, v n * ∑ α, b α * ∏ j, (A (boxPoint n) j) ^ (α j : ℕ)) = 0
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hfactor (α : MonomialRectangle t) :
        (∑ n, v n * (b α * ∏ j, (A (boxPoint n) j) ^ (α j : ℕ))) =
          b α * (∑ n, v n * ∏ j, (A (boxPoint n) j) ^ (α j : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    simp_rw [hfactor, hrows, mul_zero]
    exact Finset.sum_const_zero
  rw [hb] at hsum
  simpa [Pi.single_apply] using hsum

/-- Remark 5's rectangular multiplicity estimate: under Corollary 4's
hypotheses, vanishing of all the indicated derivatives forces a box-supported
polynomial to be zero. -/
theorem rectangular_multiplicity_estimate
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ)
    (hA : Function.Surjective A) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hc : LinearIndependent ℚ c) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (v : IntegerBox N → ℂ)
    (hjets : ∀ α : MonomialRectangle (fun j => ⌊degreeBudget N H j⌋₊),
      eval (fun _ => 1) (mixedEuler A (fun j => (α j : ℕ)) (boxPolynomial N v)) = 0) :
    boxPolynomial N v = 0 := by
  have hv := coefficients_eq_zero_of_rectangular_jets A N _
    (uniform_budget_interpolation A c hA hker hc N H hH hHN) v hjets
  simp [boxPolynomial, hv]


/-- The formula `(D₁^α₁ D₂^α₂ D₃^α₃ X^n)(1,1,1,1) = (An)^α`
from Remark 5, written with the literal product of the four variables. -/
theorem remark_five_identity
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (α : Fin 3 → ℕ) (n : Fin 4 → ℕ) :
    eval (fun _ => 1) (mixedEuler A α (∏ i, (X i : Polynomial) ^ n i)) =
      ∏ j, (A (fun i => (n i : ℂ)) j) ^ α j := by
  have hx : monomial (Finsupp.equivFunOnFinite.symm n) (1 : ℂ) =
      ∏ i, (X i : Polynomial) ^ n i := by
    rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype]
    · rfl
    · intro i
      exact pow_zero _
  rw [← hx, eval_one_mixedEuler_monomial]
  simp

/-- Every nonzero box-supported polynomial has a nonzero Euler jet in the
explicit rectangle prescribed by Corollary 4. -/
theorem exists_nonzero_rectangular_jet
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ)
    (hA : Function.Surjective A) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hc : LinearIndependent ℚ c) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (v : IntegerBox N → ℂ) (hv : boxPolynomial N v ≠ 0) :
    ∃ α : MonomialRectangle (fun j => ⌊degreeBudget N H j⌋₊),
      eval (fun _ => 1) (mixedEuler A (fun j => (α j : ℕ)) (boxPolynomial N v)) ≠ 0 := by
  by_contra! h
  exact hv (rectangular_multiplicity_estimate A c hA hker hc N H hH hHN v h)

end Siegel.Torus
