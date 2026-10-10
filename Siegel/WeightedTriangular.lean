import Siegel.Algebra

/-! Determinant-preserving replacement using weights directly. -/

namespace Siegel

open Matrix Submodule Set

/-- A matrix with diagonal one and all other nonzero entries strictly
below their row's weight has determinant one. Equal weights cause no
problem and no tie-breaking order is required. -/
theorem det_eq_one_of_weight_lower {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (w : ι → ℕ) (L : Matrix ι ι R)
    (hdiag : ∀ i, L i i = 1)
    (hlower : ∀ i j, i ≠ j → w i ≤ w j → L i j = 0) : L.det = 1 := by
  classical
  rw [Matrix.det_apply, Finset.sum_eq_single (Equiv.refl ι)]
  · simp [hdiag]
  · intro σ hσ hne
    have hex : ∃ i, σ i ≠ i ∧ w (σ i) ≤ w i := by
      by_contra! h
      have hle (i : ι) : w i ≤ w (σ i) := by
        by_cases hi : σ i = i
        · rw [hi]
        · exact (h i hi).le
      have hmove : ∃ i, σ i ≠ i := by
        by_contra! heq
        apply hne
        ext i
        exact heq i
      obtain ⟨i, hi⟩ := hmove
      have hsum : (∑ j : ι, w j) < ∑ j : ι, w (σ j) :=
        Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, h i hi⟩
      rw [Equiv.sum_comp] at hsum
      exact (lt_irrefl _) hsum
    obtain ⟨i, hi, hwi⟩ := hex
    have hprod : (∏ j, L (σ j) j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hlower (σ i) i hi hwi)
    simp [hprod]
  · simp

/-- Replacing each row by itself plus a combination of strictly lighter
rows preserves the determinant. The coefficients need not be integral. -/
theorem determinant_eq_of_weight_lower_span {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (w : ι → ℕ) (A B : Matrix ι ι K)
    (hrow : ∀ i, B i - A i ∈ span K (A '' {j | w j < w i})) : B.det = A.det := by
  classical
  have hex (i : ι) : ∃ c : ι → K,
      (∑ j ∈ Finset.univ.filter (fun j => w j < w i), c j • A j) = B i - A i := by
    apply (Submodule.mem_span_image_finset_iff_exists_fun' K).mp
    simpa using hrow i
  choose c hc using hex
  let D : Matrix ι ι K := fun i j => if w j < w i then c i j else 0
  let L : Matrix ι ι K := 1 + D
  have hdet : L.det = 1 := by
    apply det_eq_one_of_weight_lower w L
    · intro i
      simp [L, D]
    · intro i j hij hle
      simp [L, D, hij, not_lt_of_ge hle]
  have hreplace : L * A = B := by
    rw [show L = 1 + D from rfl, Matrix.add_mul, Matrix.one_mul]
    ext i k
    have hi := congrFun (hc i) k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hi
    simp only [Matrix.add_apply, Matrix.mul_apply, D]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    linear_combination hi
  rw [← hreplace, Matrix.det_mul, hdet, one_mul]

/-- Lemma 7's divisibility mechanism with the earlier-span condition in
place of an assumed triangular replacement matrix. -/
theorem determinant_dvd_of_weight_lower_span {ι R K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [Field K] (f : R →+* K) (hf : Function.Injective f)
    (w : ι → ℕ) (A B : Matrix ι ι R) (p : R) (k : ι → ℕ)
    (hrow : ∀ i, (B.map f) i - (A.map f) i ∈
      span K ((A.map f) '' {j | w j < w i}))
    (hdiv : ∀ i j, p ^ k i ∣ B i j) : p ^ (∑ i, k i) ∣ A.det := by
  have hdet : B.det = A.det := by
    apply hf
    rw [f.map_det, f.map_det]
    exact determinant_eq_of_weight_lower_span w _ _ hrow
  rw [← hdet]
  exact determinant_dvd_of_row_powers B p k hdiv

end Siegel
