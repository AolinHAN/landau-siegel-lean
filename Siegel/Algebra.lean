import Mathlib

/-!
# Concrete algebra in Sections 4 and 5

These identities verify the displayed matrix (4.1), its rank, the weight
change used in (5.4), and the integer polynomial giving the product of the
four conjugates. They do not assert the interpolation or analytic estimates.
-/

namespace Siegel

open Matrix

section MatrixIdentities

variable {K : Type*} [Field K]

/-- The matrix in equation (4.1), with coordinates numbered from zero in Lean. -/
def conjugateMatrix (a b : K) : Matrix (Fin 3) (Fin 4) K :=
  !![1, a, b, a * b;
     1, -a, b, -(a * b);
     1, -a, -b, a * b]

/-- The kernel vector displayed after (4.1). -/
def conjugateKernel (a b : K) : Fin 4 → K := ![a * b, b, -a, -1]

/-- The first three columns of (4.1). -/
def conjugateMinor (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, a, b; 1, -a, b; 1, -a, -b]

theorem conjugateMatrix_mul_kernel (a b : K) :
    (conjugateMatrix a b).mulVec (conjugateKernel a b) = 0 := by
  ext i
  fin_cases i <;>
    simp [conjugateMatrix, conjugateKernel, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem conjugateMinor_det (a b : K) :
    (conjugateMinor a b).det = 4 * a * b := by
  simp [conjugateMinor, Matrix.det_fin_three]
  ring

theorem conjugateMinor_eq_submatrix (a b : K) :
    conjugateMinor a b = (conjugateMatrix a b).submatrix id Fin.castSucc := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable [CharZero K]

theorem conjugateMatrix_rank (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (conjugateMatrix a b).rank = 3 := by
  have hdet : (conjugateMinor a b).det ≠ 0 := by
    rw [conjugateMinor_det]
    exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
  have hminor : (conjugateMinor a b).rank = 3 := by
    simpa using Matrix.rank_of_isUnit (conjugateMinor a b)
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  apply le_antisymm (Matrix.rank_le_height _)
  calc
    3 = (conjugateMinor a b).rank := hminor.symm
    _ ≤ (conjugateMatrix a b).rank := by
      rw [conjugateMinor_eq_submatrix]
      exact Matrix.rank_submatrix_le _ _ _

/-- The full kernel assertion following (4.1): every vector killed by the
matrix is a scalar multiple of the displayed vector. -/
theorem conjugateMatrix_mulVec_eq_zero_iff (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : Fin 4 → K) :
    (conjugateMatrix a b).mulVec x = 0 ↔
      ∃ t : K, x = t • conjugateKernel a b := by
  constructor
  · intro hx
    have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    have h2 := congrFun hx 2
    simp [conjugateMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
    have hx0 : x 0 + a * b * x 3 = 0 := by
      linear_combination (1 / 2 : K) * h0 + (1 / 2 : K) * h2
    have hx1 : a * (x 1 + b * x 3) = 0 := by
      linear_combination (1 / 2 : K) * h0 - (1 / 2 : K) * h1
    have hx2 : b * (x 2 - a * x 3) = 0 := by
      linear_combination (1 / 2 : K) * h1 - (1 / 2 : K) * h2
    have hx1' : x 1 + b * x 3 = 0 := (mul_eq_zero.mp hx1).resolve_left ha
    have hx2' : x 2 - a * x 3 = 0 := (mul_eq_zero.mp hx2).resolve_left hb
    refine ⟨-x 3, ?_⟩
    ext i
    fin_cases i
    · simp [conjugateKernel]
      linear_combination hx0
    · simp [conjugateKernel]
      linear_combination hx1'
    · simp [conjugateKernel]
      linear_combination hx2'
    · simp [conjugateKernel]
  · rintro ⟨t, rfl⟩
    rw [Matrix.mulVec_smul, conjugateMatrix_mul_kernel, smul_zero]

end MatrixIdentities

/-- The row weight in Section 4, expressed on natural-number coordinates. -/
def rowWeight (H : ℕ) (α : Fin 3 → ℕ) : ℕ :=
  α 0 + H * α 1 + H * α 2

/-- Replacing `p*m` first factors by `m` second factors lowers the weight. -/
theorem rowWeight_replace_second_lt (H p m : ℕ) (α : Fin 3 → ℕ)
    (hp : H < p) (hm : 0 < m) (hblock : p * m ≤ α 0) :
    rowWeight H ![α 0 - p * m, α 1 + m, α 2] < rowWeight H α := by
  simp [rowWeight, mul_add]
  have hmul : H * m < p * m := Nat.mul_lt_mul_of_pos_right hp hm
  omega

/-- The corresponding replacement by third factors. -/
theorem rowWeight_replace_third_lt (H p m : ℕ) (α : Fin 3 → ℕ)
    (hp : H < p) (hm : 0 < m) (hblock : p * m ≤ α 0) :
    rowWeight H ![α 0 - p * m, α 1, α 2 + m] < rowWeight H α := by
  simp [rowWeight, mul_add]
  have hmul : H * m < p * m := Nat.mul_lt_mul_of_pos_right hp hm
  omega

/-- The integer polynomial for the product of four conjugates, when
`a² = d` and `b² = e`. In the paper `e = 2`. -/
def biquadraticNorm (d e z₁ z₂ z₃ z₄ : ℤ) : ℤ :=
  (z₁ ^ 2 + d * z₂ ^ 2 - e * z₃ ^ 2 - d * e * z₄ ^ 2) ^ 2 -
    4 * d * (z₁ * z₂ - e * z₃ * z₄) ^ 2

section NormIdentity

variable {R : Type*} [CommRing R]

/-- The binomial row replacement underlying equation (5.4), including the
leading term at `m = 0`. -/
theorem row_replacement_expansion (x y : R) (p k r : ℕ) :
    x ^ r * (x ^ p - y) ^ k =
      ∑ m ∈ Finset.range (k + 1),
        (-1 : R) ^ m * (k.choose m : R) * x ^ (p * (k - m) + r) * y ^ m := by
  rw [show x ^ p - y = -y + x ^ p by ring, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [neg_pow]
  simp only [pow_add, pow_mul]
  ring

/-- The divisibility of an individual replaced row entry in Lemma 7. -/
theorem row_replacement_dvd (x y z t c : R) (p k r u v : ℕ)
    (h : c ∣ x ^ p - y) :
    c ^ k ∣ x ^ r * (x ^ p - y) ^ k * z ^ u * t ^ v := by
  obtain ⟨q, hq⟩ := h
  refine ⟨x ^ r * q ^ k * z ^ u * t ^ v, ?_⟩
  rw [hq, mul_pow]
  ring

/-- Factoring the divisibility of the replaced entries out of every row,
the last determinant step in Lemma 7. -/
theorem determinant_dvd_of_row_powers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (c : R) (k : ι → ℕ)
    (h : ∀ i j, c ^ k i ∣ A i j) :
    c ^ (∑ i, k i) ∣ A.det := by
  choose B hB using h
  have hA : A = Matrix.of (fun i j => c ^ k i * B i j) := by
    ext i j
    exact hB i j
  refine ⟨Matrix.det B, ?_⟩
  rw [hA, Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]

/-- The determinant equality (5.5), for an explicitly given lower-triangular
replacement matrix with diagonal entries one. -/
theorem determinant_lower_triangular_replacement {ι : Type*} [Fintype ι]
    [DecidableEq ι] [LinearOrder ι] (L A : Matrix ι ι R)
    (hLower : ∀ i j, i < j → L i j = 0) (hDiag : ∀ i, L i i = 1) :
    (L * A).det = A.det := by
  have hTri : L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    exact hLower i j hij
  have hDet : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hTri]
    simp [hDiag]
  rw [Matrix.det_mul, hDet, one_mul]

/-- The exact algebraic mechanism of Lemma 7. The replacement matrix may
live in a larger ring; no integrality of its entries is assumed. Its action
preserves the determinant, while divisibility is checked in the original ring. -/
theorem determinant_dvd_of_triangular_replacement {ι S : Type*} [Fintype ι]
    [DecidableEq ι] [LinearOrder ι] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (A B : Matrix ι ι R) (L : Matrix ι ι S) (c : R) (k : ι → ℕ)
    (hReplace : B.map f = L * A.map f)
    (hLower : ∀ i j, i < j → L i j = 0) (hDiag : ∀ i, L i i = 1)
    (hDiv : ∀ i j, c ^ k i ∣ B i j) :
    c ^ (∑ i, k i) ∣ A.det := by
  have hdet : B.det = A.det := by
    apply hf
    rw [f.map_det, f.map_det]
    change (B.map f).det = (A.map f).det
    rw [hReplace]
    exact determinant_lower_triangular_replacement L (A.map f) hLower hDiag
  rw [← hdet]
  exact determinant_dvd_of_row_powers B c k hDiv

/-- Multiplication of a pair of conjugates, before substituting square roots. -/
theorem conjugate_pair_product (a b z₁ z₂ z₃ z₄ : R) :
    (z₁ + z₂ * a + z₃ * b + z₄ * a * b) *
        (z₁ + z₂ * a - z₃ * b - z₄ * a * b) =
      (z₁ ^ 2 + a ^ 2 * z₂ ^ 2 - b ^ 2 * z₃ ^ 2 - a ^ 2 * b ^ 2 * z₄ ^ 2) +
        2 * a * (z₁ * z₂ - b ^ 2 * z₃ * z₄) := by
  ring

/-- The four-factor expression belongs to the image of the integers.
This proves the concrete integrality assertion in Section 5 without
assuming the existence of a number-field norm. -/
theorem four_conjugates_eq_integer (a b : R) (d e z₁ z₂ z₃ z₄ : ℤ)
    (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = (e : R)) :
    ((z₁ : R) + z₂ * a + z₃ * b + z₄ * a * b) *
      (z₁ - z₂ * a + z₃ * b - z₄ * a * b) *
      (z₁ + z₂ * a - z₃ * b - z₄ * a * b) *
      (z₁ - z₂ * a - z₃ * b + z₄ * a * b) =
    (biquadraticNorm d e z₁ z₂ z₃ z₄ : R) := by
  have hpair := conjugate_pair_product a b (z₁ : R) (z₂ : R) (z₃ : R) (z₄ : R)
  have hpair' := conjugate_pair_product (-a) b (z₁ : R) (z₂ : R) (z₃ : R) (z₄ : R)
  simp only [neg_sq, ha, hb] at hpair hpair'
  calc
    _ = (((z₁ : R) + z₂ * a + z₃ * b + z₄ * a * b) *
          (z₁ + z₂ * a - z₃ * b - z₄ * a * b)) *
        ((z₁ + z₂ * (-a) + z₃ * b + z₄ * (-a) * b) *
          (z₁ + z₂ * (-a) - z₃ * b - z₄ * (-a) * b)) := by ring
    _ = _ := by
      rw [hpair, hpair']
      simp only [biquadraticNorm, Int.cast_sub, Int.cast_add, Int.cast_mul,
        Int.cast_pow, Int.cast_ofNat]
      linear_combination -4 * ((z₁ : R) * z₂ - (e : R) * z₃ * z₄) ^ 2 * ha

end NormIdentity

end Siegel
