import Siegel.Algebra

/-! Euler's criterion and Frobenius congruences for biquadratic generators. -/

namespace Siegel

/-- Euler's criterion as an integer divisibility statement. -/
theorem euler_criterion_dvd (p : ℕ) [Fact p.Prime] (d : ℤ) :
    (p : ℤ) ∣ d ^ (p / 2) - legendreSym p d := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [Int.cast_sub, Int.cast_pow, ← legendreSym.eq_pow, sub_self]

/-- The power of a square root modulo an odd prime. -/
theorem square_root_frobenius_dvd {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : R) (d : ℤ) (ha : a ^ 2 = (d : R)) :
    (p : R) ∣ a ^ p - (legendreSym p d : R) * a := by
  have hpodd : p % 2 = 1 := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
  have hsplit : p = 2 * (p / 2) + 1 := by omega
  have hEuler : (p : R) ∣ (d : R) ^ (p / 2) - (legendreSym p d : R) := by
    have h := map_dvd (Int.castRingHom R) (euler_criterion_dvd p d)
    simpa using h
  have heq : a ^ p - (legendreSym p d : R) * a =
      ((d : R) ^ (p / 2) - (legendreSym p d : R)) * a := by
    nth_rw 1 [hsplit]
    rw [pow_add, pow_mul, ha, pow_one]
    ring
  rw [heq]
  exact dvd_mul_of_dvd_left hEuler a

/-- A Frobenius congruence on two generators extends to every integer
linear combination of `1,a,b,ab`, in an arbitrary commutative ring. -/
theorem biquadratic_frobenius_dvd {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] (a b a' b' : R)
    (ha : (p : R) ∣ a ^ p - a') (hb : (p : R) ∣ b ^ p - b')
    (z₁ z₂ z₃ z₄ : ℤ) :
    (p : R) ∣
      ((z₁ : R) + z₂ * a + z₃ * b + z₄ * a * b) ^ p -
      ((z₁ : R) + z₂ * a' + z₃ * b' + z₄ * a' * b') := by
  let I : Ideal R := Ideal.span {(p : R)}
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.eq_zero_iff_mem (I := I)).mp
  change f _ = 0
  rw [map_sub, sub_eq_zero, map_pow]
  rcases subsingleton_or_nontrivial (R ⧸ I) with htriv | hnontriv
  · exact Subsingleton.elim _ _
  have hpzero : (p : R ⧸ I) = 0 := by
    rw [← map_natCast f]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _)
  letI : CharP (R ⧸ I) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpzero
  have ha' : (f a) ^ p = f a' := by
    have h := (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr (Ideal.mem_span_singleton.mpr ha)
    change f (a ^ p - a') = 0 at h
    apply sub_eq_zero.mp
    simpa using h
  have hb' : (f b) ^ p = f b' := by
    have h := (Ideal.Quotient.eq_zero_iff_mem (I := I)).mpr (Ideal.mem_span_singleton.mpr hb)
    change f (b ^ p - b') = 0 at h
    apply sub_eq_zero.mp
    simpa using h
  rw [← frobenius_def]
  simp only [map_add, map_mul, map_intCast, frobenius_def, ha', hb']

/-- The concrete congruence (5.2) when the quadratic character at `p` is
the Legendre symbol of `d` and is inert. The remaining sign is `(2/p)`. -/
theorem inert_biquadratic_frobenius_dvd {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : R) (d : ℤ)
    (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = 2) (hinert : legendreSym p d = -1)
    (z₁ z₂ z₃ z₄ : ℤ) :
    (p : R) ∣
      ((z₁ : R) + z₂ * a + z₃ * b + z₄ * a * b) ^ p -
      ((z₁ : R) - z₂ * a + (legendreSym p 2 : R) * (z₃ * b) -
        (legendreSym p 2 : R) * (z₄ * a * b)) := by
  have ha' : (p : R) ∣ a ^ p - (-a) := by
    simpa [hinert] using square_root_frobenius_dvd p hp a d ha
  have hb' : (p : R) ∣ b ^ p - (legendreSym p 2 : R) * b :=
    square_root_frobenius_dvd p hp b 2 (by simpa using hb)
  convert biquadratic_frobenius_dvd p a b (-a) ((legendreSym p 2 : R) * b)
    ha' hb' z₁ z₂ z₃ z₄ using 1
  ring

/-- The two alternatives for `g_p` in (5.2), uniformly for all four
integer coefficients. -/
theorem inert_frobenius_alternatives {R : Type*} [CommRing R]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : R) (d : ℤ)
    (ha : a ^ 2 = (d : R)) (hb : b ^ 2 = 2) (hinert : legendreSym p d = -1) :
    (∀ z₁ z₂ z₃ z₄ : ℤ, (p : R) ∣
      ((z₁ : R) + z₂ * a + z₃ * b + z₄ * a * b) ^ p -
      ((z₁ : R) - z₂ * a + z₃ * b - z₄ * a * b)) ∨
    (∀ z₁ z₂ z₃ z₄ : ℤ, (p : R) ∣
      ((z₁ : R) + z₂ * a + z₃ * b + z₄ * a * b) ^ p -
      ((z₁ : R) - z₂ * a - z₃ * b + z₄ * a * b)) := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have htwo : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp hz
    have hle := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) hd
    omega
  rcases legendreSym.eq_one_or_neg_one p htwo with h | h
  · left
    intro z₁ z₂ z₃ z₄
    simpa [h] using inert_biquadratic_frobenius_dvd p hp a b d ha hb hinert z₁ z₂ z₃ z₄
  · right
    intro z₁ z₂ z₃ z₄
    simpa [h, sub_eq_add_neg] using inert_biquadratic_frobenius_dvd p hp a b d ha hb hinert z₁ z₂ z₃ z₄

end Siegel
