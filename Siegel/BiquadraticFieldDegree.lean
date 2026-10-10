import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Analysis.Complex.Basic

namespace Siegel.Biquadratic

open scoped Polynomial IntermediateField
open Polynomial IntermediateField Module

theorem isIntegral_of_sq_eq (a : ℂ) (d : ℚ) (ha : a ^ 2 = (d : ℂ)) :
    IsIntegral ℚ a := by
  refine ⟨X ^ 2 - C d, monic_X_pow_sub_C d (by decide), ?_⟩
  simpa using sub_eq_zero.mpr ha

theorem finrank_adjoin_le_two_of_sq_eq (a : ℂ) (d : ℚ)
    (ha : a ^ 2 = (d : ℂ)) : finrank ℚ ℚ⟮a⟯ ≤ 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_of_sq_eq a d ha)]
  have hroot : Polynomial.aeval a (X ^ 2 - C d : ℚ[X]) = 0 := by
    simpa using sub_eq_zero.mpr ha
  simpa using Polynomial.natDegree_le_natDegree
    (minpoly.min ℚ a (monic_X_pow_sub_C d (by decide)) hroot)

/-- The four independent radical monomials give degree four; both radical subfields
have degree two. -/
theorem field_degree_data (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) :
    finrank ℚ ℚ⟮a⟯ = 2 ∧ finrank ℚ ℚ⟮b⟯ = 2 ∧
      finrank ℚ (IntermediateField.adjoin ℚ ({a, b} : Set ℂ)) = 4 := by
  have ha' : a ^ 2 = ((d : ℚ) : ℂ) := by simpa using ha
  have hb' : b ^ 2 = ((2 : ℚ) : ℂ) := by simpa using hb
  have hai := isIntegral_of_sq_eq a d ha'
  have hbi := isIntegral_of_sq_eq b 2 hb'
  letI := IntermediateField.finiteDimensional_adjoin_pair hai hbi
  let K := IntermediateField.adjoin ℚ ({a, b} : Set ℂ)
  let aK : K := ⟨a, IntermediateField.mem_adjoin_pair_left ℚ a b⟩
  let bK : K := ⟨b, IntermediateField.mem_adjoin_pair_right ℚ a b⟩
  have hlinK : LinearIndependent ℚ (![1, aK, bK, aK * bK] : Fin 4 → K) := by
    apply LinearIndependent.of_comp K.val.toLinearMap
    convert hlin using 1
    ext i
    fin_cases i <;> rfl
  have hlow : 4 ≤ finrank ℚ K := by
    simpa using hlinK.fintype_card_le_finrank
  have hsup : finrank ℚ K ≤ finrank ℚ ℚ⟮a⟯ * finrank ℚ ℚ⟮b⟯ := by
    have hK : K = ℚ⟮a⟯ ⊔ ℚ⟮b⟯ := by
      dsimp [K]
      rw [← Set.singleton_union, IntermediateField.adjoin_union]
    exact (IntermediateField.equivOfEq hK).toLinearEquiv.finrank_eq.trans_le
      (IntermediateField.finrank_sup_le ℚ⟮a⟯ ℚ⟮b⟯)
  have hA := finrank_adjoin_le_two_of_sq_eq a d ha'
  have hB := finrank_adjoin_le_two_of_sq_eq b 2 hb'
  have hprod : finrank ℚ ℚ⟮a⟯ * finrank ℚ ℚ⟮b⟯ ≤ 4 := by nlinarith
  have heqK : finrank ℚ K = 4 := by omega
  have heqA : finrank ℚ ℚ⟮a⟯ = 2 := by nlinarith
  have heqB : finrank ℚ ℚ⟮b⟯ = 2 := by nlinarith
  exact ⟨heqA, heqB, heqK⟩

theorem field_finrank (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) :
    finrank ℚ (IntermediateField.adjoin ℚ ({a, b} : Set ℂ)) = 4 :=
  (field_degree_data d a b ha hb hlin).2.2

set_option backward.isDefEq.respectTransparency false in
theorem field_isGalois (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) :
    IsGalois ℚ (IntermediateField.adjoin ℚ ({a, b} : Set ℂ)) := by
  obtain ⟨hA, hB, _⟩ := field_degree_data d a b ha hb hlin
  letI : Algebra.IsQuadraticExtension ℚ ℚ⟮a⟯ := ⟨hA⟩
  letI : Algebra.IsQuadraticExtension ℚ ℚ⟮b⟯ := ⟨hB⟩
  letI : Normal ℚ ℚ⟮a⟯ := Algebra.IsQuadraticExtension.normal ℚ ℚ⟮a⟯
  letI : Normal ℚ ℚ⟮b⟯ := Algebra.IsQuadraticExtension.normal ℚ ℚ⟮b⟯
  letI : Normal ℚ (ℚ⟮a⟯ ⊔ ℚ⟮b⟯ : IntermediateField ℚ ℂ) :=
    IntermediateField.normal_sup ℚ ℂ ℚ⟮a⟯ ℚ⟮b⟯
  rw [← Set.singleton_union, IntermediateField.adjoin_union]
  exact ⟨⟩

theorem field_card_aut (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) :
    Nat.card ((IntermediateField.adjoin ℚ ({a, b} : Set ℂ)) ≃ₐ[ℚ]
      (IntermediateField.adjoin ℚ ({a, b} : Set ℂ))) = 4 := by
  letI := field_isGalois d a b ha hb hlin
  letI := IntermediateField.finiteDimensional_adjoin_pair
    (isIntegral_of_sq_eq a d (by simpa using ha))
    (isIntegral_of_sq_eq b 2 (by simpa using hb))
  rw [IsGalois.card_aut_eq_finrank, field_finrank d a b ha hb hlin]

end Siegel.Biquadratic
