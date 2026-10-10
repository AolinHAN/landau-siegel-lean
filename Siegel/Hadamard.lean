import Mathlib

/-! The complex Hadamard inequality used in the Archimedean bound. -/

namespace Siegel

open scoped InnerProductSpace
open InnerProductSpace Module

/-- Hadamard's inequality relative to any orthonormal basis. -/
theorem orthonormal_det_le_prod_norm {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (e : OrthonormalBasis ι ℂ E) (v : ι → E) :
    ‖e.toBasis.det v‖ ≤ ∏ i, ‖v i‖ := by
  have hdim : finrank ℂ E = Fintype.card ι := finrank_eq_card_basis e.toBasis
  let b := gramSchmidtOrthonormalBasis hdim v
  have hmul : e.toBasis.det b * b.toBasis.det v = e.toBasis.det v := by
    simp only [Basis.det_apply, ← Matrix.det_mul]
    change (e.toBasis.toMatrix b.toBasis * b.toBasis.toMatrix v).det =
      (e.toBasis.toMatrix v).det
    rw [Basis.toMatrix_mul_toMatrix]
  have hnorm : ‖e.toBasis.det v‖ = ‖b.toBasis.det v‖ := by
    rw [← hmul, norm_mul, e.det_to_matrix_orthonormalBasis b, one_mul]
  rw [hnorm, gramSchmidtOrthonormalBasis_det hdim v, norm_prod]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i hi
  simpa only [b.norm_eq_one i, one_mul] using norm_inner_le_norm (b i) (v i)

/-- Hadamard's row bound for complex square matrices. -/
theorem complex_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (A : Matrix ι ι ℂ) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  let v : ι → EuclideanSpace ℂ ι := fun i => (EuclideanSpace.equiv ι ℂ).symm (A i)
  have h := orthonormal_det_le_prod_norm (EuclideanSpace.basisFun ι ℂ) v
  have hmatrix : (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix v = A.transpose := by
    ext i j
    rfl
  rw [Basis.det_apply, hmatrix, Matrix.det_transpose] at h
  simpa only [EuclideanSpace.norm_eq] using h

/-- Entrywise row bounds give the precise square-root-of-dimension
factor needed for the first term of (5.1). -/
theorem det_norm_le_row_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (A : Matrix ι ι ℂ) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hA : ∀ i j, ‖A i j‖ ≤ C i) :
    ‖A.det‖ ≤ ∏ i, (Real.sqrt (Fintype.card ι) * C i) := by
  apply (complex_hadamard A).trans
  apply Finset.prod_le_prod (fun i _ => Real.sqrt_nonneg _)
  intro i hi
  have hsum : (∑ j, ‖A i j‖ ^ 2) ≤ (Fintype.card ι : ℝ) * (C i) ^ 2 := by
    calc
      _ ≤ ∑ _j : ι, (C i) ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hA i j) 2
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * (C i) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (hC i)]

end Siegel
