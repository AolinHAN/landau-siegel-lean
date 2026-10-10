import Siegel.IntegralDeterminant
import Siegel.ScaledRows

/-! Original integral determinants, with row selection and both size bounds. -/

namespace Siegel.Biquadratic

open Siegel.Interpolation Siegel.WeightedRows Submodule Set

/-- Selection and enumeration preserve the strict-weight span property. -/
theorem exists_selected_exponents (N H : ℕ) (a b : ℂ)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) (hH : 1 ≤ H) (hHN : H ≤ N) :
    ∃ α : IntegerBox N → Fin 3 → ℕ, Function.Injective α ∧
      (Matrix.of (fun i n => monomialRow (conjugateProjection a b) N (α i) n)).det ≠ 0 ∧
      (∀ i, (rowWeight H (α i) : ℝ) ≤
        96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) ∧
      ∀ i β, rowWeight H β < rowWeight H (α i) →
        monomialRow (conjugateProjection a b) N β ∈
          span ℂ ((fun j => monomialRow (conjugateProjection a b) N (α j)) ''
            {j | rowWeight H (α j) < rowWeight H (α i)}) := by
  classical
  have ha : a ≠ 0 := by simpa using hlin.ne_zero (1 : Fin 4)
  have hb : b ≠ 0 := by simpa using hlin.ne_zero (2 : Fin 4)
  obtain ⟨P, hP, _, hcard, hweight, hprior⟩ := select_weighted_monomial_rows
    (conjugateProjection a b) (conjugateKernel a b)
    (conjugateProjection_surjective a b ha hb) (conjugateProjection_ker a b ha hb)
    (conjugateKernel_linearIndependent a b hlin) N H hH hHN
  obtain ⟨α, hα, hrange, hdet⟩ := exists_nonzero_selected_determinant _ N P hP hcard
  have hmem (i) : α i ∈ P := by
    change α i ∈ (P : Set (Fin 3 → ℕ))
    rw [← hrange]
    exact mem_range_self i
  refine ⟨α, hα, hdet, fun i => hweight _ (hmem i), ?_⟩
  intro i β hβ
  have heq : monomialRow (conjugateProjection a b) N ''
      {γ | γ ∈ P ∧ rowWeight H γ < rowWeight H (α i)} =
      (fun j => monomialRow (conjugateProjection a b) N (α j)) ''
        {j | rowWeight H (α j) < rowWeight H (α i)} := by
    ext v
    constructor
    · rintro ⟨γ, ⟨hγ, hw⟩, rfl⟩
      have hg : γ ∈ Set.range α := by rw [hrange]; exact hγ
      obtain ⟨j, rfl⟩ := hg
      exact ⟨j, hw, rfl⟩
    · rintro ⟨j, hw, rfl⟩
      exact ⟨α j, ⟨hmem j, hw⟩, rfl⟩
  rw [← heq]
  exact hprior _ (hmem i) β hβ

/-- Lemma 6 for the row enumeration actually used in the integral matrix. -/
theorem selected_exponents_moments (N H : ℕ) (α : IntegerBox N → Fin 3 → ℕ)
    (hα : Function.Injective α) (hH : 1 ≤ H) (hHN : H ≤ N)
    (hlarge : 2 * 97 ^ 2 ≤ (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ))
    (hweight : ∀ i, (rowWeight H (α i) : ℝ) ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (N : ℝ) ^ 4 * ((H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) /
      (4 * 97 ^ 2) ≤ ∑ i, (α i 0 : ℝ) ∧
    (∑ i, ((α i 1 : ℝ) + α i 2)) ≤
      192 * (N : ℝ) ^ 4 * ((H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) := by
  classical
  let P := Finset.univ.image α
  have hcard : P.card = N ^ 4 := by
    simp only [P, Finset.card_image_of_injective _ hα, Finset.card_univ,
      IntegerBox, Fintype.card_fun, Fintype.card_fin]
  have hsum (F : (Fin 3 → ℕ) → ℝ) : ∑ β ∈ P, F β = ∑ i, F (α i) := by
    dsimp [P]
    rw [Finset.sum_image]
    intro i hi j hj h
    exact hα h
  have h := lemma_six P N H hH hHN hcard hlarge (by
    intro β hβ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hβ
    exact hweight i)
  simpa only [hsum] using h

/-- Section 5's determinant comparison, with the determinant constructed
from interpolation and the row divisibilities proved inside the integral ring. -/
theorem exists_determinant_comparison (d : ℤ) (N H q : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b])
    (χ : DirichletCharacter ℂ q)
    (hchar : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q →
      χ (p : ZMod q) = (legendreSym p d : ℂ))
    (hq : 1 ≤ q) (hd : |(d : ℝ)| ≤ q) (hH : 1 ≤ H) (hHN : H ≤ N)
    (hlarge : 2 * 97 ^ 2 ≤ (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    ∃ S₁ S₂ : ℝ,
      0 < S₁ ∧ 0 ≤ S₂ ∧
      (N : ℝ) ^ 4 * ((H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) /
        (4 * 97 ^ 2) ≤ S₁ ∧
      S₂ ≤ 192 * (N : ℝ) ^ 4 *
        ((H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) ∧
      ∀ X : ℝ, 0 ≤ X →
        S₁ * inertPrimeSum χ H X - (N : ℝ) ^ 4 * Real.log 4 * X ≤
          (N : ℝ) ^ 4 / 2 * Real.log ((N : ℝ) ^ 4) +
            (S₁ + S₂) * (Real.log N + Real.log q / 2 + Real.log 8) := by
  obtain ⟨α, hinj, hdet, hweight, hprior⟩ := exists_selected_exponents N H a b hlin hH hHN
  have hZ := evaluationNorm_ne_zero d N a b ha hb hlin α hdet
  have hm := selected_exponents_moments N H α hinj hH hHN hlarge hweight
  let S₁ : ℝ := ∑ i, (α i 0 : ℝ)
  let S₂ : ℝ := ∑ i, ((α i 1 : ℝ) + α i 2)
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hS : 0 < S₁ := lt_of_lt_of_le (by positivity) hm.1
  refine ⟨S₁, S₂, hS, by dsimp [S₂]; positivity, hm.1, hm.2, ?_⟩
  intro X hX
  have hlower := evaluationNorm_inert_lower d N H q a b ha hb hlin χ hchar α hZ hprior X hX
  have hupper := evaluationNorm_archimedean d N q a b ha hb α (by omega) hq hd hZ
  have heq : (∑ i, ((α i 0 : ℝ) + α i 1 + α i 2)) = S₁ + S₂ := by
    simp only [S₁, S₂, Finset.sum_add_distrib, add_assoc]
  rw [heq] at hupper
  exact hlower.trans hupper

end Siegel.Biquadratic
