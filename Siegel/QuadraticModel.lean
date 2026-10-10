import Siegel.MainReduction
import Siegel.SignedConductorNonsquare
import Siegel.RadicalIndependence

/-! The unconditional arithmetic realization required by the determinant argument. -/

namespace Siegel

/-- The actual primitive quadratic character has the biquadratic realization
used in Section 4 whenever its conductor is greater than eight. -/
theorem quadraticModel : QuadraticModelStatement := by
  refine ⟨9, ?_⟩
  intro q _ χ hq _ hprim _ hχ
  let χZ := quadraticIntCharacter χ hχ
  have hχZ := quadraticIntCharacter_isQuadratic χ hχ
  have hprimZ := quadraticIntCharacter_isPrimitive χ hχ hprim
  let d : ℤ := χZ (-1) * (q : ℤ)
  let a : ℂ := gaussSum χ ZMod.stdAddChar
  have ha : a ^ 2 = (d : ℂ) := by
    have h := primitive_quadratic_gaussSum_sq χ hprim hχ ZMod.stdAddChar
      (ZMod.isPrimitive_stdAddChar q)
    simpa only [a, d, Int.cast_mul, Int.cast_natCast, χZ, quadraticIntCharacter_cast] using h
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) (by norm_num : 0 < (2 : ℕ))
  obtain ⟨hd, h2d⟩ := signed_conductor_nonsquares χZ hχZ hprimZ (by omega)
  refine ⟨d, a, b, ha, hb, ?_, ?_, ?_⟩
  · exact biquadratic_generators_linearIndependent (d : ℚ) a b
      (by simpa using ha) hb hd h2d
  · have hu : IsUnit (χZ (-1)) := IsUnit.map χZ (isUnit_one.neg)
    rcases hχZ (-1) with h | h | h
    · exact (hu.ne_zero h).elim
    · simp [d, χZ, h]
    · simp [d, χZ, h]
  · intro p _ hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hp (dvd_mul_right 2 q)
    have hpq : ¬ p ∣ q := fun h => hp (dvd_mul_of_dvd_right h 2)
    have h := primitive_quadratic_eq_legendre χZ hχZ hprimZ p hp2 hpq
    rw [← quadraticIntCharacter_cast χ hχ]
    change (χZ (p : ZMod q) : ℂ) = (legendreSym p d : ℂ)
    exact congrArg (fun z : ℤ => (z : ℂ)) h

/-- Reduction to the explicit logarithmic-derivative estimate (2.4).
This input is discharged by `Siegel.logDerivativeUpper`; see `Siegel.Main`. -/
theorem uniformExclusion_of_logDerivative_upper
    (hld : LogDerivativeUpperStatement) : UniformExclusion :=
  uniformExclusion_of_logDerivative_upper_and_models hld quadraticModel

end Siegel
