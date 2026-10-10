import Siegel.QuadraticCharacter
import Siegel.ConductorComparison

/-! Nondegeneracy of the signed conductor outside the fixed small levels. -/

namespace Siegel

/-- The two square classes that would collapse the biquadratic field have
conductor at most eight. -/
theorem signed_conductor_nonsquares {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (hq : 8 < q) :
    ¬ IsSquare ((χ (-1) * (q : ℤ) : ℤ) : ℚ) ∧
    ¬ IsSquare (2 * ((χ (-1) * (q : ℤ) : ℤ) : ℚ)) := by
  let d : ℤ := χ (-1) * (q : ℤ)
  have hnm : 2 ≤ q * 8 := by omega
  have hprimes (p : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ q * 8) :
      p ≠ 2 ∧ ¬ p ∣ q ∧ ¬ p ∣ 8 := by
    refine ⟨?_, fun h => hpn (dvd_mul_of_dvd_left h 8),
      fun h => hpn (dvd_mul_of_dvd_right h q)⟩
    rintro rfl
    exact hpn (dvd_mul_of_dvd_right (by norm_num : 2 ∣ 8) q)
  have hdmod (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) :
      (d : ZMod p) ≠ 0 := by
    intro hz
    have hv := primitive_quadratic_eq_legendre χ hχ hprim p hp2 hpq
    have hu := (IsUnit.map χ (ZMod.isUnit_prime_of_not_dvd (Fact.out : p.Prime) hpq)).ne_zero
    apply hu
    rw [hv]
    exact (legendreSym.eq_zero_iff p d).mpr hz
  constructor
  · intro hs
    have hsZ : IsSquare d := Rat.isSquare_intCast_iff.mp hs
    have hdvd : q ∣ 8 := primitive_level_dvd_of_prime_agreement hnm χ
        (1 : DirichletCharacter ℤ 8) hprim (by
      intro p hp hpn
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨hp2, hpq, hp8⟩ := hprimes p hp hpn
      rw [primitive_quadratic_eq_legendre χ hχ hprim p hp2 hpq,
        MulChar.one_apply (ZMod.isUnit_prime_of_not_dvd hp hp8)]
      exact (legendreSym.eq_one_iff p (hdmod p hp2 hpq)).mpr
        (hsZ.map (Int.castRingHom (ZMod p))))
    exact (not_le.mpr hq) (Nat.le_of_dvd (by norm_num) hdvd)
  · intro hs
    have hsZ : IsSquare (2 * d) := Rat.isSquare_intCast_iff.mp (by simpa [d] using hs)
    have hdvd : q ∣ 8 := primitive_level_dvd_of_prime_agreement hnm χ
        ZMod.χ₈ hprim (by
      intro p hp hpn
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨hp2, hpq, hp8⟩ := hprimes p hp hpn
      have h2 : (2 : ZMod p) ≠ 0 := by
        exact (Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).trans_ne hp2))
      have hprod : legendreSym p (2 * d) = 1 :=
        (legendreSym.eq_one_iff p (by push_cast; exact mul_ne_zero h2 (hdmod p hp2 hpq))).mpr
          (hsZ.map (Int.castRingHom (ZMod p)))
      rw [legendreSym.mul] at hprod
      rw [primitive_quadratic_eq_legendre χ hχ hprim p hp2 hpq,
        ← legendreSym.at_two hp2]
      change legendreSym p d = legendreSym p 2
      rcases legendreSym.eq_one_or_neg_one p (a := 2) (by simpa using h2) with h | h
      · rw [h]
        simpa only [h, one_mul] using hprod
      · rw [h]
        rw [h, neg_one_mul] at hprod
        linarith)
    exact (not_le.mpr hq) (Nat.le_of_dvd (by norm_num) hdvd)

end Siegel
