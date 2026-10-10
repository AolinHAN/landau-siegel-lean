import Siegel.BiquadraticRing
import Siegel.ConjugateProjection
import Siegel.Frobenius
import Siegel.RowSelection

/-! The original three conjugate rows inside the concrete integral ring. -/

namespace Siegel.Biquadratic

open Siegel.Interpolation

def point {N : ℕ} (d : ℤ) (n : IntegerBox N) : Ring d :=
  (n 0 : ℕ) + (n 1 : ℕ) * genA d + (n 2 : ℕ) * genB d +
    (n 3 : ℕ) * genA d * genB d

def pointA {N : ℕ} (d : ℤ) (n : IntegerBox N) : Ring d :=
  (n 0 : ℕ) - (n 1 : ℕ) * genA d + (n 2 : ℕ) * genB d -
    (n 3 : ℕ) * genA d * genB d

def pointAB {N : ℕ} (d : ℤ) (n : IntegerBox N) : Ring d :=
  (n 0 : ℕ) - (n 1 : ℕ) * genA d - (n 2 : ℕ) * genB d +
    (n 3 : ℕ) * genA d * genB d

@[simp] theorem embed_point {N : ℕ} (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (n : IntegerBox N) :
    embed d a b ha hb (point d n) = thetaPoint a b n := by
  simp only [point, map_add, map_mul, map_natCast, embed_genA, embed_genB, thetaPoint]

@[simp] theorem embed_pointA {N : ℕ} (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (n : IntegerBox N) :
    embed d a b ha hb (pointA d n) = thetaPoint (-a) b n := by
  simp only [pointA, map_add, map_sub, map_mul, map_natCast, embed_genA, embed_genB, thetaPoint]
  ring

@[simp] theorem embed_pointAB {N : ℕ} (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (n : IntegerBox N) :
    embed d a b ha hb (pointAB d n) = thetaPoint (-a) (-b) n := by
  simp only [pointAB, map_add, map_sub, map_mul, map_natCast, embed_genA, embed_genB, thetaPoint]
  ring

/-- Formula (5.2) for the actual evaluation points of the determinant. -/
theorem points_frobenius_alternatives {N : ℕ} (d : ℤ)
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hinert : legendreSym p d = -1) :
    (∀ n : IntegerBox N, (p : Ring d) ∣ point d n ^ p - pointA d n) ∨
    (∀ n : IntegerBox N, (p : Ring d) ∣ point d n ^ p - pointAB d n) := by
  rcases inert_frobenius_alternatives p hp (genA d) (genB d) d
    (genA_sq d) (genB_sq d) hinert with h | h
  · left
    intro n
    simpa [point, pointA] using h (n 0) (n 1) (n 2) (n 3)
  · right
    intro n
    simpa [point, pointAB] using h (n 0) (n 1) (n 2) (n 3)

/-- The original integral row maps to precisely the monomial row used
in the already-proved weighted selection. -/
theorem embed_rawRow {N : ℕ} (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (α : Fin 3 → ℕ) (n : IntegerBox N) :
    embed d a b ha hb (rawRow (point d) (pointA d) (pointAB d) α n) =
      WeightedRows.monomialRow (conjugateProjection a b) N α n := by
  simp only [rawRow, map_mul, map_pow, embed_point, embed_pointA, embed_pointAB,
    WeightedRows.monomialRow, conjugateProjection_boxPoint, Fin.prod_univ_three]
  rfl

/-- Bounds for all three points at every one of the four embeddings. -/
theorem embeddings_points_bound {N : ℕ} (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (q : ℝ) (hq : 1 ≤ q)
    (hd : |(d : ℝ)| ≤ q) (ν : Fin 4) (n : IntegerBox N) :
    ‖embeddings d a b ha hb ν (point d n)‖ ≤ 8 * N * Real.sqrt q ∧
    ‖embeddings d a b ha hb ν (pointA d n)‖ ≤ 8 * N * Real.sqrt q ∧
    ‖embeddings d a b ha hb ν (pointAB d n)‖ ≤ 8 * N * Real.sqrt q := by
  have hna := norm_square_root_le a d q ha hd
  have hnb : ‖b‖ ≤ 2 := by
    have hn : ‖b‖ ^ 2 = 2 := by rw [← norm_pow, hb]; norm_num
    nlinarith [norm_nonneg b]
  have hpp := thetaPoint_norm_le_conductor a b n q hq hna hnb
  have hmp := thetaPoint_norm_le_conductor (-a) b n q hq (by simpa using hna) hnb
  have hpm := thetaPoint_norm_le_conductor a (-b) n q hq hna (by simpa using hnb)
  have hmm := thetaPoint_norm_le_conductor (-a) (-b) n q hq
    (by simpa using hna) (by simpa using hnb)
  fin_cases ν <;> dsimp [embeddings] <;>
    simp only [embed_point, embed_pointA, embed_pointAB, neg_neg] <;> aesop

end Siegel.Biquadratic
