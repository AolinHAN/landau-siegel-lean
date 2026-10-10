import Siegel.SquarefreeCharacter
import Siegel.SquarefreeIndependence
import Siegel.BiquadraticField

namespace Siegel

/-- The full algebraic input of §4 for every primitive real character.
The only possible exception to the four-dimensional basis is precisely the
paper's temporarily excluded radicand d=2; no conductor cutoff is imposed. -/
theorem section_four_data {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    ∃ (d : ℤ) (a b : ℂ), Squarefree d ∧ d ≠ 1 ∧
      a ^ 2 = (d : ℂ) ∧ b ^ 2 = 2 ∧ |(d : ℝ)| ≤ q ∧
      IntermediateField.adjoin ℚ ({a} : Set ℂ) =
        IntermediateField.adjoin ℚ ({gaussSum χ ZMod.stdAddChar} : Set ℂ) ∧
      (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q →
        χ (p : ZMod q) = (legendreSym p d : ℂ)) ∧
      (d ≠ 2 → LinearIndependent ℚ ![1, a, b, a * b] ∧
        Module.finrank ℚ (Biquadratic.Extension a b) = 4 ∧
        IsGalois ℚ (Biquadratic.Extension a b) ∧
        Nat.card (Biquadratic.Extension a b ≃ₐ[ℚ] Biquadratic.Extension a b) = 4 ∧
        ∃ σ τ : Biquadratic.Extension a b ≃ₐ[ℚ] Biquadratic.Extension a b,
          σ (Biquadratic.fieldGenA a b) = -Biquadratic.fieldGenA a b ∧
          σ (Biquadratic.fieldGenB a b) = Biquadratic.fieldGenB a b ∧
          τ (Biquadratic.fieldGenA a b) = Biquadratic.fieldGenA a b ∧
          τ (Biquadratic.fieldGenB a b) = -Biquadratic.fieldGenB a b ∧
          σ ^ 2 = 1 ∧ τ ^ 2 = 1 ∧ σ * τ = τ * σ ∧
          ∀ φ : Biquadratic.Extension a b ≃ₐ[ℚ] Biquadratic.Extension a b,
            φ = 1 ∨ φ = σ ∨ φ = τ ∨ φ = σ * τ) := by
  obtain ⟨d, a, hsq, hd1, ha, hsize, hfield, hchar⟩ :=
    exists_squarefree_character_radical χ hq hχ hprim
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) (by norm_num : 0 < (2 : ℕ))
  refine ⟨d, a, b, hsq, hd1, ha, hb, hsize, hfield, hchar, ?_⟩
  intro hd2
  have hlin := biquadratic_linearIndependent_of_squarefree hsq hd1 hd2 a b ha hb
  exact ⟨hlin, Biquadratic.field_finrank d a b ha hb hlin,
    Biquadratic.field_isGalois d a b ha hb hlin,
    Biquadratic.field_card_aut d a b ha hb hlin,
    Biquadratic.exists_field_automorphisms d a b ha hb hlin⟩

end Siegel
