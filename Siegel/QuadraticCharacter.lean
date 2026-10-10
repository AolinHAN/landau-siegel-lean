import Siegel.PrimitiveGaussSum

/-! Integer values and scalar changes for primitive quadratic characters. -/

namespace Siegel

noncomputable def quadraticIntValue {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ZMod q) : ℤ := by
  classical
  exact if χ x = 0 then 0 else if χ x = 1 then 1 else -1

theorem quadraticIntValue_cast {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (x : ZMod q) : (quadraticIntValue χ x : ℂ) = χ x := by
  rcases hχ x with h | h | h <;> norm_num [quadraticIntValue, h]

/-- The actual integer-valued character underlying a real character. -/
noncomputable def quadraticIntCharacter {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) : DirichletCharacter ℤ q where
  toFun := quadraticIntValue χ
  map_one' := by
    have h : (quadraticIntValue χ 1 : ℂ) = (1 : ℤ) := by
      rw [quadraticIntValue_cast χ hχ, map_one]
      norm_num
    exact_mod_cast h
  map_mul' x y := by
    have h : (quadraticIntValue χ (x * y) : ℂ) =
        ((quadraticIntValue χ x * quadraticIntValue χ y : ℤ) : ℂ) := by
      simp only [Int.cast_mul, quadraticIntValue_cast χ hχ, map_mul]
    exact_mod_cast h
  map_nonunit' x hx := by
    have h : (quadraticIntValue χ x : ℂ) = 0 := by
      rw [quadraticIntValue_cast χ hχ, MulChar.map_nonunit χ hx]
    exact_mod_cast h

theorem quadraticIntCharacter_cast {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (x : ZMod q) : (quadraticIntCharacter χ hχ x : ℂ) = χ x :=
  quadraticIntValue_cast χ hχ x

theorem quadraticIntCharacter_isQuadratic {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) : (quadraticIntCharacter χ hχ).IsQuadratic := by
  intro x
  change quadraticIntValue χ x = 0 ∨ quadraticIntValue χ x = 1 ∨ quadraticIntValue χ x = -1
  unfold quadraticIntValue
  split_ifs <;> simp

/-- The conductor is determined by the kernel on units. -/
theorem conductor_eq_of_unit_kernel {q : ℕ} [NeZero q]
    {R S : Type*} [CommMonoidWithZero R] [CommMonoidWithZero S]
    (χ : DirichletCharacter R q) (ψ : DirichletCharacter S q)
    (heq : ∀ x : (ZMod q)ˣ, χ x = 1 ↔ ψ x = 1) : χ.conductor = ψ.conductor := by
  have hker : χ.toUnitHom.ker = ψ.toUnitHom.ker := by
    ext x
    simp only [MonoidHom.mem_ker, ← Units.val_inj, MulChar.coe_toUnitHom, Units.val_one]
    exact heq x
  have hset : χ.conductorSet = ψ.conductorSet := by
    ext d
    change χ.FactorsThrough d ↔ ψ.FactorsThrough d
    by_cases hd : d ∣ q
    · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
        DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, hker]
    · constructor <;> intro h <;> exact (hd h.dvd).elim
  exact congrArg sInf hset

theorem quadraticIntCharacter_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    (quadraticIntCharacter χ hχ).IsPrimitive := by
  have hc := conductor_eq_of_unit_kernel (quadraticIntCharacter χ hχ) χ (by
    intro x
    have h := quadraticIntCharacter_cast χ hχ x
    constructor
    · intro hx
      rw [hx] at h
      simpa using h.symm
    · intro hx
      rw [hx] at h
      exact_mod_cast h)
  exact hc.trans hprim

/-- Scalar change preserves the conductor of an integer-valued quadratic
character whenever characteristic two is excluded. -/
theorem quadratic_character_cast_conductor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic)
    {R : Type*} [CommRing R] [Nontrivial R] (hR : ringChar R ≠ 2) :
    DirichletCharacter.conductor (χ.ringHomComp (Int.castRingHom R)) = χ.conductor := by
  apply conductor_eq_of_unit_kernel
  intro x
  change (χ x : R) = 1 ↔ χ x = 1
  constructor
  · intro h
    exact Int.cast_injOn_of_ringChar_ne_two hR (hχ x)
      (show (1 : ℤ) = 0 ∨ (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 from Or.inr (Or.inl rfl))
      (by simpa using h)
  · intro h
    simp [h]

/-- Quadratic reciprocity in the form needed for the determinant:
the value of a primitive quadratic character at an odd unramified prime
is the Legendre symbol of its signed conductor. -/
theorem primitive_quadratic_eq_legendre {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℤ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) :
    χ (p : ZMod q) = legendreSym p (χ (-1) * (q : ℤ)) := by
  have hqcast : (q : ZMod p) ≠ 0 := by
    intro h
    exact hpq ((CharP.cast_eq_zero_iff (ZMod p) p q).mp h)
  let ψ := AddChar.primitiveZModChar ⟨q, NeZero.pos q⟩ (ZMod p) hqcast
  let F := CyclotomicField ψ.n (ZMod p)
  have hchar : ringChar F = p := (Algebra.ringChar_eq (ZMod p) F).symm.trans (ZMod.ringChar_zmod_n p)
  letI : CharP F p := ringChar.of_eq hchar
  have hchar2 : ringChar F ≠ 2 := by rw [hchar]; exact hp2
  let χF : DirichletCharacter F q := χ.ringHomComp (Int.castRingHom F)
  have hquadF : χF.IsQuadratic := hχ.comp _
  have hprimF : χF.IsPrimitive := (quadratic_character_cast_conductor χ hχ hchar2).trans hprim
  have hsq := primitive_quadratic_gaussSum_sq χF hprimF hquadF ψ.char ψ.prim
  have hunit : IsUnit (p : ZMod q) := ZMod.isUnit_prime_of_not_dvd (Fact.out : p.Prime) hpq
  have hpw := Char.card_pow_char_pow hquadF ψ.char p 1 hunit hp2 (by simpa using hsq)
  let d : ℤ := χ (-1) * (q : ℤ)
  have hpow : (d : F) ^ (p / 2) = (χ (p : ZMod q) : F) := by
    simp only [ZMod.card, pow_one] at hpw
    change ((χ (-1) : F) * (q : F)) ^ (p / 2) = (χ (p : ZMod q) : F) at hpw
    change ((Int.castRingHom F) (χ (-1) * (q : ℤ))) ^ (p / 2) = _
    rw [map_mul]
    simpa using hpw
  have heuler : (legendreSym p d : F) = (d : F) ^ (p / 2) := by
    have h := congrArg (algebraMap (ZMod p) F) (legendreSym.eq_pow p d)
    simpa only [map_intCast, map_pow] using h
  exact Int.cast_injOn_of_ringChar_ne_two hchar2 (hχ (p : ZMod q))
    (quadraticChar_isQuadratic (ZMod p) (d : ZMod p)) (hpow.symm.trans heuler.symm)

/-- The signed conductor has the required absolute size, and its complex
square root is explicitly the quadratic Gauss sum. -/
theorem exists_signed_conductor_radical {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hprim : χ.IsPrimitive) :
    ∃ (d : ℤ) (a : ℂ), |(d : ℝ)| = q ∧ a ^ 2 = (d : ℂ) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q → χ (p : ZMod q) = (legendreSym p d : ℂ) := by
  let χZ := quadraticIntCharacter χ hχ
  have hχZ := quadraticIntCharacter_isQuadratic χ hχ
  have hprimZ := quadraticIntCharacter_isPrimitive χ hχ hprim
  let d : ℤ := χZ (-1) * (q : ℤ)
  refine ⟨d, gaussSum χ ZMod.stdAddChar, ?_, ?_, ?_⟩
  · have hu : IsUnit (χZ (-1)) := IsUnit.map χZ (isUnit_one.neg)
    rcases hχZ (-1) with h | h | h
    · exact (hu.ne_zero h).elim
    · simp [d, χZ, h]
    · simp [d, χZ, h]
  · have h := primitive_quadratic_gaussSum_sq χ hprim hχ ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar q)
    simpa only [d, Int.cast_mul, Int.cast_natCast, χZ, quadraticIntCharacter_cast] using h
  · intro p _ hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hp (dvd_mul_right 2 q)
    have hpq : ¬ p ∣ q := fun h => hp (dvd_mul_of_dvd_right h 2)
    have h := primitive_quadratic_eq_legendre χZ hχZ hprimZ p hp2 hpq
    rw [← quadraticIntCharacter_cast χ hχ]
    change (χZ (p : ZMod q) : ℂ) = (legendreSym p d : ℂ)
    exact congrArg (fun z : ℤ => (z : ℂ)) h

end Siegel
