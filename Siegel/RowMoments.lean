import Siegel.WeightedRows
import Siegel.Estimates

/-! The constants of Lemma 6 from the actual finite row set. -/

namespace Siegel.WeightedRows

/-- Lemma 6's two bounds from the weight cap and the scale identities.
Here `X = H^(-1/3) U` and `Y = H^(2/3) U`; no fiber-capacity or first-
moment inequality is assumed. -/
theorem weighted_row_moment_bounds (P : Finset (Fin 3 → ℕ)) (H : ℕ)
    (X Y : ℝ) (hH : 1 ≤ H) (hX : 1 ≤ X) (hY : 2 * 97 ^ 2 ≤ Y)
    (hscale : (H : ℝ) * X = Y) (hcard : (P.card : ℝ) = X ^ 2 * Y)
    (hweight : ∀ α ∈ P, (rowWeight H α : ℝ) ≤ 96 * Y) :
    (P.card : ℝ) * Y / (4 * 97 ^ 2) ≤ ∑ α ∈ P, (α 0 : ℝ) ∧
      (∑ α ∈ P, ((α 1 : ℝ) + α 2)) ≤ 192 * P.card * X := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by linarith
  have hcoord (α : Fin 3 → ℕ) (hα : α ∈ P) :
      (α 1 : ℝ) ≤ 96 * X ∧ (α 2 : ℝ) ≤ 96 * X := by
    have hw := hweight α hα
    simp only [rowWeight, Nat.cast_add, Nat.cast_mul] at hw
    rw [← hscale] at hw
    have h0 : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (H : ℝ) * α 1 := by positivity
    have h2 : (0 : ℝ) ≤ (H : ℝ) * α 2 := by positivity
    constructor <;> nlinarith
  let B := ⌊96 * X⌋₊
  let Q : ℝ := (B + 1 : ℕ) ^ 2
  have hB : ∀ α ∈ P, α 1 ≤ B ∧ α 2 ≤ B := by
    intro α hα
    exact ⟨(Nat.le_floor_iff (by positivity)).mpr (hcoord α hα).1,
      (Nat.le_floor_iff (by positivity)).mpr (hcoord α hα).2⟩
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQbound : Q ≤ 97 ^ 2 * X ^ 2 := by
    have hb : (B : ℝ) ≤ 96 * X := Nat.floor_le (by positivity)
    have hb0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    dsimp [Q]
    push_cast
    nlinarith [sq_nonneg ((97 : ℝ) * X - (B + 1))]
  have hlarge : 2 * Q ≤ (P.card : ℝ) := by
    rw [hcard]
    nlinarith [mul_le_mul_of_nonneg_left hY (sq_nonneg X)]
  have hfirst : (P.card : ℝ) ^ 2 / (4 * Q) ≤ ∑ α ∈ P, (α 0 : ℝ) := by
    apply sum_lower_of_capacity _ Q _ hQpos hlarge
    simpa [Q] using first_coordinate_sum_lower P B hB
  constructor
  · apply le_trans ?_ hfirst
    apply (le_div_iff₀ (by positivity : 0 < 4 * Q)).mpr
    have hmul := mul_le_mul_of_nonneg_left hQbound
      (show 0 ≤ (P.card : ℝ) * Y from mul_nonneg (Nat.cast_nonneg _) hYpos.le)
    have hid : (P.card : ℝ) * Y * X ^ 2 = (P.card : ℝ) ^ 2 := by rw [hcard]; ring
    rw [show (P.card : ℝ) * Y * (97 ^ 2 * X ^ 2) =
      97 ^ 2 * ((P.card : ℝ) * Y * X ^ 2) by ring, hid] at hmul
    nlinarith
  · have hupper := other_coordinates_sum_upper P (96 * X) hcoord
    nlinarith

end Siegel.WeightedRows
