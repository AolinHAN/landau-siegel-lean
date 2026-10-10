import Siegel.RowSelection
import Siegel.RowMoments

/-! Lemma 6 with the actual fractional-power scales of the paper. -/

namespace Siegel.WeightedRows

open Siegel.Interpolation Submodule Set

theorem row_scale_identities (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    let X := (H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)
    let Y := (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)
    1 ≤ X ∧ (H : ℝ) * X = Y ∧ (N : ℝ) ^ 4 = X ^ 2 * Y := by
  dsimp
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpowH : (H : ℝ) * (H : ℝ) ^ (-1 / 3 : ℝ) = (H : ℝ) ^ (2 / 3 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (H : ℝ)]
    rw [← Real.rpow_add hHpos]
    norm_num
  have hcancel : (H : ℝ) ^ (-1 / 3 : ℝ) * (H : ℝ) ^ (-1 / 3 : ℝ) *
      (H : ℝ) ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hHpos, ← Real.rpow_add hHpos]
    norm_num
  have hNpow : (N : ℝ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) *
      (N : ℝ) ^ (4 / 3 : ℝ) = (N : ℝ) ^ 4 := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · calc
      (1 : ℝ) ≤ H := by exact_mod_cast hH
      _ = (H : ℝ) ^ (-1 / 3 : ℝ) * (H : ℝ) ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_add hHpos]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hHpos.le (by exact_mod_cast hHN) (by norm_num))
        (Real.rpow_nonneg hHpos.le _)
  · rw [← mul_assoc, hpowH]
  · calc
      _ = ((H : ℝ) ^ (-1 / 3 : ℝ) * (H : ℝ) ^ (-1 / 3 : ℝ) * (H : ℝ) ^ (2 / 3 : ℝ)) *
          ((N : ℝ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) := by
            rw [hcancel, hNpow, one_mul]
      _ = _ := by ring

/-- The complete numerical Lemma 6 for a selected row set, with the
explicit sufficient size condition given on page 6. -/
theorem lemma_six (P : Finset (Fin 3 → ℕ)) (N H : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (hcard : P.card = N ^ 4)
    (hlarge : 2 * 97 ^ 2 ≤ (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ))
    (hweight : ∀ α ∈ P, (rowWeight H α : ℝ) ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (N : ℝ) ^ 4 * ((H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) /
      (4 * 97 ^ 2) ≤ ∑ α ∈ P, (α 0 : ℝ) ∧
    (∑ α ∈ P, ((α 1 : ℝ) + α 2)) ≤
      192 * (N : ℝ) ^ 4 * ((H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) := by
  obtain ⟨hX, hscale, hsize⟩ := row_scale_identities N H hH hHN
  have hc : (P.card : ℝ) = (N : ℝ) ^ 4 := by exact_mod_cast hcard
  have hb := weighted_row_moment_bounds P H _ _ hH hX hlarge hscale (hc.trans hsize)
    (by intro α hα; simpa only [mul_assoc] using hweight α hα)
  simpa only [hc] using hb

end Siegel.WeightedRows
