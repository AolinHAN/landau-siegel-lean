import Siegel.GreedyBasis
import Siegel.InterpolationBudgets
import Siegel.Algebra

/-! Actual monomial rows and weighted selection from Corollary 4. -/

namespace Siegel.WeightedRows

open Siegel.Interpolation Submodule Set

/-- The original evaluation row, before any auxiliary polynomial is used. -/
noncomputable def monomialRow
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (N : ℕ) (α : Fin 3 → ℕ) :
    IntegerBox N → ℂ := fun n => ∏ j, (A (boxPoint n) j) ^ α j

/-- The finite family of all natural exponent vectors of weight at most `W`. -/
noncomputable def weightBall (H W : ℕ) : Finset (Fin 3 → ℕ) :=
  (Finset.univ.image (fun α : Fin 3 → Fin (W + 1) => fun j => (α j : ℕ))).filter
    (fun α => rowWeight H α ≤ W)

theorem mem_weightBall (H W : ℕ) (hH : 1 ≤ H) (α : Fin 3 → ℕ) :
    α ∈ weightBall H W ↔ rowWeight H α ≤ W := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    have hb (j : Fin 3) : α j ≤ W := by
      have h1 : α 1 ≤ H * α 1 := Nat.le_mul_of_pos_left _ hH
      have h2 : α 2 ≤ H * α 2 := Nat.le_mul_of_pos_left _ hH
      dsimp [rowWeight] at h
      fin_cases j <;> dsimp at * <;> omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨fun j => ⟨α j, by have := hb j; omega⟩, Finset.mem_univ _, rfl⟩, h⟩

/-- The weight of every monomial in Corollary 4's rectangle is at most
`96 H^(2/3) N^(4/3)`. -/
theorem rectangle_rowWeight_bound (N H : ℕ) (hH : 1 ≤ H)
    (α : MonomialRectangle (fun j => ⌊degreeBudget N H j⌋₊)) :
    (rowWeight H (fun j => (α j : ℕ)) : ℝ) ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have ha (j) : (α j : ℝ) ≤ degreeBudget N H j := by
    have hf : (α j : ℝ) ≤ (⌊degreeBudget N H j⌋₊ : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ (α j).isLt
    exact hf.trans (Nat.floor_le (by fin_cases j <;> dsimp [degreeBudget] <;> positivity))
  have hpow : (H : ℝ) * (H : ℝ) ^ (-1 / 3 : ℝ) = (H : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      _ = (H : ℝ) ^ (1 : ℝ) * (H : ℝ) ^ (-1 / 3 : ℝ) := by rw [Real.rpow_one]
      _ = (H : ℝ) ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hHpos]; norm_num
  have h0 := ha 0
  have h1 := mul_le_mul_of_nonneg_left (ha 1) hHpos.le
  have h2 := mul_le_mul_of_nonneg_left (ha 2) hHpos.le
  dsimp [degreeBudget] at h0 h1 h2
  simp only [rowWeight, Nat.cast_add, Nat.cast_mul]
  calc
    _ ≤ 32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) +
        (H : ℝ) * (32 * (H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) +
        (H : ℝ) * (32 * (H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) := by linarith
    _ = _ := by rw [← hpow]; ring

/-- A surjective rectangular evaluation map implies spanning by every
weight ball containing the rectangle. -/
theorem span_weightBall_eq_top
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (N H W : ℕ) (hH : 1 ≤ H)
    (t : Fin 3 → ℕ) (hsurj : Function.Surjective (evaluationMap A N t))
    (hweight : ∀ α : MonomialRectangle t, rowWeight H (fun j => (α j : ℕ)) ≤ W) :
    span ℂ (monomialRow A N '' (weightBall H W : Set (Fin 3 → ℕ))) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨coeff, rfl⟩ := hsurj x
  have heval : evaluationMap A N t coeff =
      ∑ α, coeff α • monomialRow A N (fun j => (α j : ℕ)) := by
    ext n
    simp [evaluationMap, evaluate, monomialRow]
  rw [heval]
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.smul_mem
  exact subset_span ⟨_, (mem_weightBall H W hH _).mpr (hweight α), rfl⟩

/-- The selected original rows are independent, have exactly `N^4`
elements, span all column vectors, and retain the strict-weight property
needed for the later triangular replacement. -/
theorem select_weighted_monomial_rows
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ)
    (hA : Function.Surjective A) (hker : LinearMap.ker A = span ℂ {c})
    (hc : LinearIndependent ℚ c) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    ∃ P : Finset (Fin 3 → ℕ),
      LinearIndepOn ℂ (monomialRow A N) (P : Set (Fin 3 → ℕ)) ∧
      span ℂ (monomialRow A N '' (P : Set (Fin 3 → ℕ))) = ⊤ ∧
      P.card = N ^ 4 ∧
      (∀ α ∈ P, (rowWeight H α : ℝ) ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) ∧
      ∀ α ∈ P, ∀ β, rowWeight H β < rowWeight H α →
        monomialRow A N β ∈ span ℂ
          (monomialRow A N '' {γ | γ ∈ P ∧ rowWeight H γ < rowWeight H α}) := by
  classical
  let T : ℝ := 96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)
  let W := ⌊T⌋₊
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hsp := span_weightBall_eq_top A N H W hH _
    (uniform_budget_interpolation A c hA hker hc N H hH hHN)
    (fun α => (Nat.le_floor_iff hT).mpr (rectangle_rowWeight_bound N H hH α))
  obtain ⟨P, hP, hlin, hspan, hpriority⟩ := weighted_basis_earlier_span (K := ℂ)
    (weightBall H W) (rowWeight H) (monomialRow A N)
  have hPsp : span ℂ (monomialRow A N '' (P : Set (Fin 3 → ℕ))) = ⊤ := hspan.trans hsp
  refine ⟨P, hlin, hPsp, ?_, ?_, ?_⟩
  · let basis : Module.Basis P ℂ (IntegerBox N → ℂ) :=
      Module.Basis.mk hlin (by rw [Set.image_eq_range] at hPsp; exact hPsp.ge)
    have hd := Module.finrank_eq_card_basis basis
    simpa [IntegerBox, Module.finrank_pi, Fintype.card_pi] using hd.symm
  · intro α hα
    have hw : (rowWeight H α : ℝ) ≤ (W : ℝ) := by
      exact_mod_cast (mem_weightBall H W hH α).mp (hP hα)
    exact hw.trans (Nat.floor_le hT)
  · intro α hα β hβα
    have hαW := (mem_weightBall H W hH α).mp (hP hα)
    exact hpriority β ((mem_weightBall H W hH β).mpr (hβα.le.trans hαW)) α hβα

/-- Index the selected original rows by the column box. The resulting
square determinant is nonzero, without using coefficients of the
auxiliary interpolation polynomials. -/
theorem exists_nonzero_selected_determinant
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (N : ℕ)
    (P : Finset (Fin 3 → ℕ))
    (hlin : LinearIndepOn ℂ (monomialRow A N) (P : Set (Fin 3 → ℕ)))
    (hcard : P.card = N ^ 4) :
    ∃ α : IntegerBox N → (Fin 3 → ℕ), Function.Injective α ∧
      Set.range α = (P : Set (Fin 3 → ℕ)) ∧
      (Matrix.of (fun i n => monomialRow A N (α i) n)).det ≠ 0 := by
  classical
  have heq : Fintype.card (IntegerBox N) = Fintype.card P := by
    simp [IntegerBox, Fintype.card_pi, hcard]
  let e : IntegerBox N ≃ P := Fintype.equivOfCardEq heq
  let α : IntegerBox N → (Fin 3 → ℕ) := fun i => (e i).val
  refine ⟨α, Subtype.val_injective.comp e.injective, ?_, ?_⟩
  · ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro ha
      exact ⟨e.symm ⟨a, ha⟩, by simp [α]⟩
  · have hi : LinearIndependent ℂ (fun i => monomialRow A N (α i)) :=
      hlin.comp e e.injective
    have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hi
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

end Siegel.WeightedRows
