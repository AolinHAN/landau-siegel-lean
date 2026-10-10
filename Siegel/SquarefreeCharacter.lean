import Siegel.SquarefreeModel

/-! The squarefree quadratic radicand for every primitive real character. -/

namespace Siegel

/-- A primitive quadratic character of level at least three cannot have a
square signed conductor: otherwise it agrees with the principal level-two character. -/
theorem signed_conductor_not_square {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hq : 3 ≤ q) : ¬ IsSquare (χ (-1) * (q : ℤ)) := by
  let D : ℤ := χ (-1) * (q : ℤ)
  intro hs
  have hdvd : q ∣ 2 := primitive_level_dvd_of_prime_agreement (by omega : 2 ≤ q * 2) χ
      (1 : DirichletCharacter ℤ 2) hprim (by
    intro p hp hpn
    letI : Fact p.Prime := ⟨hp⟩
    have hpq : ¬ p ∣ q := fun h => hpn (dvd_mul_of_dvd_left h 2)
    have hp2dvd : ¬ p ∣ 2 := fun h => hpn (dvd_mul_of_dvd_right h q)
    have hp2 : p ≠ 2 := by rintro rfl; exact hp2dvd dvd_rfl
    have hu := (IsUnit.map χ (ZMod.isUnit_prime_of_not_dvd hp hpq)).ne_zero
    have hDmod : (D : ZMod p) ≠ 0 := by
      intro hz
      apply hu
      rw [primitive_quadratic_eq_legendre χ hχ hprim p hp2 hpq]
      exact (legendreSym.eq_zero_iff p D).mpr hz
    rw [primitive_quadratic_eq_legendre χ hχ hprim p hp2 hpq,
      MulChar.one_apply (ZMod.isUnit_prime_of_not_dvd hp hp2dvd)]
    exact (legendreSym.eq_one_iff p hDmod).mpr (hs.map (Int.castRingHom (ZMod p))))
  have := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) hdvd
  omega

/-- The source's squarefree choice for every primitive real character of
conductor at least three. The Gauss root and the squarefree root generate
the same actual intermediate field, without any large-conductor cutoff. -/
theorem exists_squarefree_character_radical {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q)
    (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    ∃ (d : ℤ) (a : ℂ), Squarefree d ∧ d ≠ 1 ∧ a ^ 2 = (d : ℂ) ∧
      |(d : ℝ)| ≤ q ∧
      IntermediateField.adjoin ℚ ({a} : Set ℂ) =
        IntermediateField.adjoin ℚ ({gaussSum χ ZMod.stdAddChar} : Set ℂ) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q →
        χ (p : ZMod q) = (legendreSym p d : ℂ) := by
  let χZ := quadraticIntCharacter χ hχ
  have hquadZ := quadraticIntCharacter_isQuadratic χ hχ
  have hprimZ := quadraticIntCharacter_isPrimitive χ hχ hprim
  let D : ℤ := χZ (-1) * (q : ℤ)
  let A : ℂ := gaussSum χ ZMod.stdAddChar
  have hA : A ^ 2 = (D : ℂ) := by
    have h := primitive_quadratic_gaussSum_sq χ hprim hχ ZMod.stdAddChar
      (ZMod.isPrimitive_stdAddChar q)
    simpa only [A, D, Int.cast_mul, Int.cast_natCast, χZ, quadraticIntCharacter_cast] using h
  have hDabs : |(D : ℝ)| = q := by
    have hu : IsUnit (χZ (-1)) := IsUnit.map χZ (isUnit_one.neg)
    rcases hquadZ (-1) with h | h | h
    · exact (hu.ne_zero h).elim
    · simp [D, χZ, h]
    · simp [D, χZ, h]
  have hD0 : D ≠ 0 := by
    intro h
    simp only [h, Int.cast_zero, abs_zero] at hDabs
    exact (show (q : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne q)) hDabs.symm
  obtain ⟨d, k, hk, hsq, hdecomp, hdsize⟩ := exists_squarefree_part D hD0
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdecompC : (k : ℂ) ^ 2 * (d : ℂ) = (D : ℂ) := by exact_mod_cast hdecomp
  refine ⟨d, A / k, hsq, ?_, ?_, ?_, adjoin_singleton_div_nat A k hk, ?_⟩
  · intro hd
    apply signed_conductor_not_square χZ hquadZ hprimZ hq
    refine ⟨(k : ℤ), ?_⟩
    simpa [D, hd, pow_two] using hdecomp.symm
  · rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hkC)).mpr
    rw [hA]
    exact hdecompC.symm.trans (mul_comm _ _)
  · exact hdsize.trans hDabs.le
  · intro p _ hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hp (dvd_mul_right 2 q)
    have hpq : ¬ p ∣ q := fun h => hp (dvd_mul_of_dvd_right h 2)
    have hchar : χ (p : ZMod q) = (legendreSym p D : ℂ) := by
      rw [← quadraticIntCharacter_cast χ hχ]
      exact congrArg (fun z : ℤ => (z : ℂ))
        (primitive_quadratic_eq_legendre χZ hquadZ hprimZ p hp2 hpq)
    have hu : χ (p : ZMod q) ≠ 0 :=
      (IsUnit.map χ (ZMod.isUnit_prime_of_not_dvd (Fact.out : p.Prime) hpq)).ne_zero
    have hDmod : (D : ZMod p) ≠ 0 := by
      intro hz
      apply hu
      rw [hchar, (legendreSym.eq_zero_iff p D).mpr hz]
      simp
    have hkmod : ((k : ℤ) : ZMod p) ≠ 0 := by
      intro hz
      apply hDmod
      rw [← hdecomp]
      simp only [Int.cast_mul, Int.cast_pow, hz]
      norm_num
    rw [hchar, ← hdecomp, legendreSym.mul, legendreSym.sq_one' p hkmod, one_mul]

end Siegel
