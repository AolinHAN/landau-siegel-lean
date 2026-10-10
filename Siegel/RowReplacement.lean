import Siegel.WeightedTriangular

/-! Explicit binomial replacements and the greedy earlier-span property. -/

namespace Siegel

open Submodule Set

/-- Original monomial rows, in the three distinguished conjugates. -/
def rawRow {ι R : Type*} [CommRing R] (x y z : ι → R) (α : Fin 3 → ℕ) : ι → R :=
  fun n => x n ^ α 0 * y n ^ α 1 * z n ^ α 2

/-- The replacement using the second conjugate in Lemma 7. -/
def secondReplacement {ι R : Type*} [CommRing R]
    (x y z : ι → R) (p : ℕ) (α : Fin 3 → ℕ) : ι → R :=
  fun n => x n ^ (α 0 % p) * (x n ^ p - y n) ^ (α 0 / p) *
    y n ^ α 1 * z n ^ α 2

def secondIndex (α : Fin 3 → ℕ) (p m : ℕ) : Fin 3 → ℕ :=
  ![α 0 - p * m, α 1 + m, α 2]

/-- The expansion (5.4), with the leading original row removed. -/
theorem secondReplacement_sub {ι R : Type*} [CommRing R]
    (x y z : ι → R) (p : ℕ) (α : Fin 3 → ℕ) :
    secondReplacement x y z p α - rawRow x y z α =
      ∑ m ∈ (Finset.range (α 0 / p + 1)).erase 0,
        ((-1 : R) ^ m * ((α 0 / p).choose m : R)) • rawRow x y z (secondIndex α p m) := by
  classical
  have hsplit : p * (α 0 / p) + α 0 % p = α 0 := Nat.div_add_mod (α 0) p
  have hβ (m : ℕ) (hm : m ≤ α 0 / p) : p * (α 0 / p - m) + α 0 % p = α 0 - p * m := by
    rw [Nat.mul_sub_left_distrib]
    have hle := Nat.mul_le_mul_left p hm
    omega
  have hsum : secondReplacement x y z p α =
      ∑ m ∈ Finset.range (α 0 / p + 1),
        ((-1 : R) ^ m * ((α 0 / p).choose m : R)) • rawRow x y z (secondIndex α p m) := by
    ext n
    simp only [secondReplacement, row_replacement_expansion,
      Finset.sum_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hβ m (Nat.le_of_lt_succ (Finset.mem_range.mp hm))]
    dsimp [rawRow, secondIndex]
    rw [pow_add]
    ring
  rw [hsum, ← Finset.sum_erase_add _ _ (by simp : 0 ∈ Finset.range (α 0 / p + 1))]
  have hzero : secondIndex α p 0 = α := by
    ext i
    fin_cases i <;> simp [secondIndex]
  simp [hzero]

/-- The complete earlier-span deduction for the second-conjugate
replacement. Every correction exponent is shown to have lower weight. -/
theorem secondReplacement_sub_mem_earlier_span {ι κ K : Type*} [Field K]
    (x y z : ι → K) (α : κ → Fin 3 → ℕ) (H p : ℕ) (hp : H < p)
    (hprior : ∀ i β, rowWeight H β < rowWeight H (α i) →
      rawRow x y z β ∈ span K ((fun j => rawRow x y z (α j)) ''
        {j | rowWeight H (α j) < rowWeight H (α i)})) (i : κ) :
    secondReplacement x y z p (α i) - rawRow x y z (α i) ∈
      span K ((fun j => rawRow x y z (α j)) ''
        {j | rowWeight H (α j) < rowWeight H (α i)}) := by
  classical
  rw [secondReplacement_sub x y z p]
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  apply hprior i
  apply rowWeight_replace_second_lt H p m (α i) hp
  · exact Nat.pos_of_ne_zero (Finset.mem_erase.mp hm).1
  · have hmle : m ≤ α i 0 / p := Nat.le_of_lt_succ
      (Finset.mem_range.mp (Finset.mem_erase.mp hm).2)
    exact (Nat.mul_le_mul_left p hmle).trans (Nat.mul_div_le (α i 0) p)

/-- The determinant equality in Lemma 7 for the second conjugate,
deduced from the actual row expansion and the greedy span property. -/
theorem secondReplacement_det_eq {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x y z : ι → K) (α : ι → Fin 3 → ℕ) (H p : ℕ) (hp : H < p)
    (hprior : ∀ i β, rowWeight H β < rowWeight H (α i) →
      rawRow x y z β ∈ span K ((fun j => rawRow x y z (α j)) ''
        {j | rowWeight H (α j) < rowWeight H (α i)})) :
    (Matrix.of (fun i n => secondReplacement x y z p (α i) n)).det =
      (Matrix.of (fun i n => rawRow x y z (α i) n)).det := by
  exact determinant_eq_of_weight_lower_span (fun i => rowWeight H (α i)) _ _
    (secondReplacement_sub_mem_earlier_span x y z α H p hp hprior)

/-- Divisibility (5.3) for the second conjugate, in the original ring.
Only the Frobenius congruence and the verified earlier-span property are
inputs; the triangular matrix and binomial expansion are proved above. -/
theorem secondReplacement_determinant_dvd {ι R K : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (α : ι → Fin 3 → ℕ) (H p : ℕ) (hp : H < p)
    (hFrob : ∀ n, (p : R) ∣ x n ^ p - y n)
    (hprior : ∀ i β, rowWeight H β < rowWeight H (α i) →
      rawRow (f ∘ x) (f ∘ y) (f ∘ z) β ∈ span K
        ((fun j => rawRow (f ∘ x) (f ∘ y) (f ∘ z) (α j)) ''
          {j | rowWeight H (α j) < rowWeight H (α i)})) :
    (p : R) ^ (∑ i, α i 0 / p) ∣
      (Matrix.of (fun i n => rawRow x y z (α i) n)).det := by
  apply determinant_dvd_of_weight_lower_span f hf (fun i => rowWeight H (α i))
    (Matrix.of (fun i n => rawRow x y z (α i) n))
    (Matrix.of (fun i n => secondReplacement x y z p (α i) n)) (p : R)
    (fun i => α i 0 / p)
  · intro i
    have h := secondReplacement_sub_mem_earlier_span
      (f ∘ x) (f ∘ y) (f ∘ z) α H p hp hprior i
    have hA : (Matrix.of (fun i n => rawRow x y z (α i) n)).map f =
        Matrix.of (fun i n => rawRow (f ∘ x) (f ∘ y) (f ∘ z) (α i) n) := by
      ext i n
      simp [rawRow]
    have hB : (Matrix.of (fun i n => secondReplacement x y z p (α i) n)).map f =
        Matrix.of (fun i n => secondReplacement (f ∘ x) (f ∘ y) (f ∘ z) p (α i) n) := by
      ext i n
      simp [secondReplacement]
    rw [hA, hB]
    exact h
  · intro i n
    exact row_replacement_dvd (x n) (y n) (y n) (z n) (p : R) p
      (α i 0 / p) (α i 0 % p) (α i 1) (α i 2) (hFrob n)

/-- Interchange the two conjugate exponents, preserving the first. -/
def swapLast (α : Fin 3 → ℕ) : Fin 3 → ℕ := ![α 0, α 2, α 1]

@[simp] theorem swapLast_zero (α : Fin 3 → ℕ) : swapLast α 0 = α 0 := rfl

@[simp] theorem swapLast_twice (α : Fin 3 → ℕ) : swapLast (swapLast α) = α := by
  ext i
  fin_cases i <;> rfl

@[simp] theorem rowWeight_swapLast (H : ℕ) (α : Fin 3 → ℕ) :
    rowWeight H (swapLast α) = rowWeight H α := by
  dsimp [rowWeight, swapLast]
  omega

theorem rawRow_swap_variables {ι R : Type*} [CommRing R]
    (x y z : ι → R) (α : Fin 3 → ℕ) :
    rawRow x z y α = rawRow x y z (swapLast α) := by
  ext n
  dsimp [rawRow, swapLast]
  ring

@[simp] theorem rawRow_swapLast {ι R : Type*} [CommRing R]
    (x y z : ι → R) (α : Fin 3 → ℕ) :
    rawRow x z y (swapLast α) = rawRow x y z α := by
  rw [rawRow_swap_variables, swapLast_twice]

/-- Divisibility (5.3) for the third conjugate. This covers the other
Frobenius case in (5.2), with the same exponent sum and the same determinant. -/
theorem thirdReplacement_determinant_dvd {ι R K : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] [Field K]
    (f : R →+* K) (hf : Function.Injective f)
    (x y z : ι → R) (α : ι → Fin 3 → ℕ) (H p : ℕ) (hp : H < p)
    (hFrob : ∀ n, (p : R) ∣ x n ^ p - z n)
    (hprior : ∀ i β, rowWeight H β < rowWeight H (α i) →
      rawRow (f ∘ x) (f ∘ y) (f ∘ z) β ∈ span K
        ((fun j => rawRow (f ∘ x) (f ∘ y) (f ∘ z) (α j)) ''
          {j | rowWeight H (α j) < rowWeight H (α i)})) :
    (p : R) ^ (∑ i, α i 0 / p) ∣
      (Matrix.of (fun i n => rawRow x y z (α i) n)).det := by
  have hprior' : ∀ i β, rowWeight H β < rowWeight H (swapLast (α i)) →
      rawRow (f ∘ x) (f ∘ z) (f ∘ y) β ∈ span K
        ((fun j => rawRow (f ∘ x) (f ∘ z) (f ∘ y) (swapLast (α j))) ''
          {j | rowWeight H (swapLast (α j)) < rowWeight H (swapLast (α i))}) := by
    intro i β hβ
    rw [rawRow_swap_variables]
    simpa only [rowWeight_swapLast, rawRow_swapLast] using
      hprior i (swapLast β) (by simpa only [rowWeight_swapLast] using hβ)
  have h := secondReplacement_determinant_dvd f hf x z y (fun i => swapLast (α i))
    H p hp hFrob hprior'
  simpa only [swapLast_zero, rawRow_swapLast] using h

end Siegel
