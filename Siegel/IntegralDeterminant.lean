import Siegel.BiquadraticPoints
import Siegel.IntegerNormBounds

/-! A single integral determinant connecting selection, Frobenius and norm bounds. -/

namespace Siegel.Biquadratic

open Siegel.Interpolation Submodule Set

def evaluationMatrix (d : ℤ) (N : ℕ) (α : IntegerBox N → Fin 3 → ℕ) :
    Matrix (IntegerBox N) (IntegerBox N) (Ring d) :=
  Matrix.of (fun i n => rawRow (point d) (pointA d) (pointAB d) (α i) n)

noncomputable def evaluationNorm (d : ℤ) (N : ℕ) (α : IntegerBox N → Fin 3 → ℕ) : ℤ :=
  norm d (evaluationMatrix d N α).det

theorem rawRow_images (d : ℤ) (N : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (β : Fin 3 → ℕ) :
    rawRow (embed d a b ha hb ∘ point (N := N) d) (embed d a b ha hb ∘ pointA (N := N) d)
      (embed d a b ha hb ∘ pointAB (N := N) d) β =
      WeightedRows.monomialRow (conjugateProjection a b) N β := by
  ext n
  rw [← embed_rawRow d a b ha hb β n]
  simp only [rawRow, map_mul, map_pow, Function.comp_apply]

theorem evaluationMatrix_map (d : ℤ) (N : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (α : IntegerBox N → Fin 3 → ℕ) :
    (evaluationMatrix d N α).map (embed d a b ha hb) =
      Matrix.of (fun i n => WeightedRows.monomialRow (conjugateProjection a b) N (α i) n) := by
  ext i n
  exact embed_rawRow d a b ha hb (α i) n

/-- The selected nonzero complex determinant gives a nonzero integer norm
of the original integral matrix. -/
theorem evaluationNorm_ne_zero (d : ℤ) (N : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) (α : IntegerBox N → Fin 3 → ℕ)
    (hdet : (Matrix.of (fun i n =>
      WeightedRows.monomialRow (conjugateProjection a b) N (α i) n)).det ≠ 0) :
    evaluationNorm d N α ≠ 0 := by
  apply norm_ne_zero d a b ha hb hlin
  intro hzero
  apply hdet
  rw [← evaluationMatrix_map d N a b ha hb α]
  calc
    _ = embed d a b ha hb (evaluationMatrix d N α).det :=
      ((embed d a b ha hb).map_det _).symm
    _ = 0 := by rw [hzero, map_zero]

/-- The prime divisibility bound for this same integer norm, deduced
from the concrete Frobenius relation and the selected-row span property. -/
theorem evaluationNorm_prime_dvd (d : ℤ) (N : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b])
    (α : IntegerBox N → Fin 3 → ℕ) (H p : ℕ) [Fact p.Prime]
    (hp : H < p) (hp2 : p ≠ 2) (hinert : legendreSym p d = -1)
    (hprior : ∀ i β, rowWeight H β < rowWeight H (α i) →
      WeightedRows.monomialRow (conjugateProjection a b) N β ∈
        span ℂ ((fun j => WeightedRows.monomialRow (conjugateProjection a b) N (α j)) ''
          {j | rowWeight H (α j) < rowWeight H (α i)})) :
    (p : ℤ) ^ (4 * ∑ i, α i 0 / p) ∣ evaluationNorm d N α := by
  classical
  apply norm_divisibility
  have hprior' : ∀ i β, rowWeight H β < rowWeight H (α i) →
      rawRow (embed d a b ha hb ∘ point (N := N) d) (embed d a b ha hb ∘ pointA (N := N) d)
        (embed d a b ha hb ∘ pointAB (N := N) d) β ∈
        span ℂ ((fun j => rawRow (embed d a b ha hb ∘ point (N := N) d)
          (embed d a b ha hb ∘ pointA (N := N) d) (embed d a b ha hb ∘ pointAB (N := N) d) (α j)) ''
          {j | rowWeight H (α j) < rowWeight H (α i)}) := by
    simpa only [rawRow_images] using hprior
  rcases points_frobenius_alternatives (N := N) d p hp2 hinert with h | h
  · exact secondReplacement_determinant_dvd (embed d a b ha hb)
      (embed_injective d a b ha hb hlin) (point d) (pointA d) (pointAB d) α H p hp h hprior'
  · exact thirdReplacement_determinant_dvd (embed d a b ha hb)
      (embed_injective d a b ha hb hlin) (point d) (pointA d) (pointAB d) α H p hp h hprior'

/-- Both sides of the comparison use the norm of the same integral matrix. -/
theorem evaluationNorm_archimedean (d : ℤ) (N q : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (α : IntegerBox N → Fin 3 → ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hd : |(d : ℝ)| ≤ q) (hZ : evaluationNorm d N α ≠ 0) :
    Real.log |(evaluationNorm d N α : ℝ)| / 4 ≤
      (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
        (∑ i, ((α i 0 : ℝ) + α i 1 + α i 2)) *
          (Real.log N + Real.log q / 2 + Real.log 8) := by
  classical
  letI : Nonempty (IntegerBox N) := ⟨fun _ => ⟨0, by omega⟩⟩
  let e := Fintype.equivFin (IntegerBox N)
  letI : NeZero (Fintype.card (IntegerBox N)) := ⟨Fintype.card_ne_zero⟩
  let f := embeddings d a b ha hb
  let x : Fin 4 → Fin (Fintype.card (IntegerBox N)) → ℂ := fun ν k => f ν (point d (e.symm k))
  let y : Fin 4 → Fin (Fintype.card (IntegerBox N)) → ℂ := fun ν k => f ν (pointA d (e.symm k))
  let z : Fin 4 → Fin (Fintype.card (IntegerBox N)) → ℂ := fun ν k => f ν (pointAB d (e.symm k))
  have hm (ν : Fin 4) : Matrix.reindex e e ((evaluationMatrix d N α).map (f ν)) =
      Matrix.of (fun i n => rawRow (x ν) (y ν) (z ν) (α (e.symm i)) n) := by
    ext i n
    simp only [evaluationMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.map_apply, Matrix.of_apply, rawRow, map_mul, map_pow, x, y, z]
  have hprod : (evaluationNorm d N α : ℂ) =
      ∏ ν, (Matrix.of (fun i n => rawRow (x ν) (y ν) (z ν) (α (e.symm i)) n)).det := by
    change ((norm d) (evaluationMatrix d N α).det : ℂ) = _
    rw [determinant_norm_eq_product d a b ha hb]
    apply Finset.prod_congr rfl
    intro ν _
    rw [← hm, Matrix.det_reindex_self]
  have hprod0 : (∏ ν, (Matrix.of
      (fun i n => rawRow (x ν) (y ν) (z ν) (α (e.symm i)) n)).det) ≠ 0 := by
    rw [← hprod]
    exact_mod_cast hZ
  have hdet (ν : Fin 4) :
      (Matrix.of (fun i n => rawRow (x ν) (y ν) (z ν) (α (e.symm i)) n)).det ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hprod0 ν (Finset.mem_univ _)
  have hbound := four_conjugate_archimedean_bound x y z (α ∘ e.symm) N q hN hq
    (fun ν n => embeddings_points_bound d a b ha hb q (by exact_mod_cast hq) hd ν (e.symm n)) hdet
  have hsum : (∑ i, ((α (e.symm i) 0 : ℝ) + α (e.symm i) 1 + α (e.symm i) 2)) =
      ∑ i, ((α i 0 : ℝ) + α i 1 + α i 2) :=
    Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  dsimp only [Function.comp_apply] at hbound
  rw [← hprod, Complex.norm_intCast, hsum] at hbound
  simpa only [IntegerBox, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hbound

/-- The lower bound (5.6) for the same norm used in the upper bound.
The character hypothesis identifies its inert primes with the quadratic
radicand; no prime-divisibility estimate is assumed. -/
theorem evaluationNorm_inert_lower (d : ℤ) (N H q : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b])
    (χ : DirichletCharacter ℂ q)
    (hchar : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q →
      χ (p : ZMod q) = (legendreSym p d : ℂ))
    (α : IntegerBox N → Fin 3 → ℕ) (hZ : evaluationNorm d N α ≠ 0)
    (hprior : ∀ i β, rowWeight H β < rowWeight H (α i) →
      WeightedRows.monomialRow (conjugateProjection a b) N β ∈
        span ℂ ((fun j => WeightedRows.monomialRow (conjugateProjection a b) N (α j)) ''
          {j | rowWeight H (α j) < rowWeight H (α i)}))
    (X : ℝ) (hX : 0 ≤ X) :
    (∑ i, (α i 0 : ℝ)) * inertPrimeSum χ H X -
      (N : ℝ) ^ 4 * Real.log 4 * X ≤ Real.log |(evaluationNorm d N α : ℝ)| / 4 := by
  classical
  have h := determinant_norm_prime_lower Finset.univ (fun i => α i 0) χ H X hX
    (evaluationNorm d N α) hZ (by
      intro p hp
      have hpdata := (Finset.mem_filter.mp hp).2
      letI : Fact p.Prime := ⟨hpdata.1⟩
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact hpdata.2.2.1 (dvd_mul_right 2 q)
      have hi : legendreSym p d = -1 := by
        have hc := (hchar p hpdata.2.2.1).symm.trans hpdata.2.2.2
        exact_mod_cast hc
      exact evaluationNorm_prime_dvd d N a b ha hb hlin α H p hpdata.2.1 hp2 hi hprior)
  simpa only [Finset.card_univ, IntegerBox, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow] using h

end Siegel.Biquadratic
