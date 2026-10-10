import Mathlib

/-! Recovering conductor bounds from equality away from the ramified primes. -/

namespace Siegel

/-- Multiplicativity reduces equality of Dirichlet characters to prime values. -/
theorem dirichlet_eq_of_prime_values {n : ℕ} [NeZero n] [Nontrivial (ZMod n)]
    {R : Type*} [CommMonoidWithZero R] (χ ψ : DirichletCharacter R n)
    (hprime : ∀ p : ℕ, p.Prime → χ p = ψ p) : χ = ψ := by
  have hn : ∀ k : ℕ, χ k = ψ k := by
    apply induction_on_primes
    · simp only [Nat.cast_zero, MulChar.map_zero]
    · simp
    · intro p k hp hk
      simp only [Nat.cast_mul, map_mul, hprime p hp, hk]
  ext x
  simpa only [ZMod.natCast_zmod_val] using hn x.val.val

theorem changeLevel_natCast_of_coprime {n m : ℕ} {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R n) (hm : n ∣ m) (k : ℕ) (hk : k.Coprime m) :
    χ.changeLevel hm (k : ZMod m) = χ (k : ZMod n) := by
  have h := χ.changeLevel_eq_cast_of_dvd hm (ZMod.unitOfCoprime k hk)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hm] using h

/-- Agreement at all primes prime to both levels forces a primitive character's
level to divide the comparison level. -/
theorem primitive_level_dvd_of_prime_agreement {n m : ℕ} [NeZero n] [NeZero m]
    (hnm : 2 ≤ n * m) {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R n) (ψ : DirichletCharacter R m) (hχ : χ.IsPrimitive)
    (hprime : ∀ p : ℕ, p.Prime → ¬ p ∣ n * m → χ p = ψ p) : n ∣ m := by
  letI : Fact (1 < n * m) := ⟨by omega⟩
  have heq : χ.changeLevel (n.dvd_mul_right m) = ψ.changeLevel (m.dvd_mul_left n) := by
    apply dirichlet_eq_of_prime_values
    intro p hp
    by_cases hpd : p ∣ n * m
    · have hnu : ¬ IsUnit (p : ZMod (n * m)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact fun h => (hp.coprime_iff_not_dvd.mp h) hpd
      rw [MulChar.map_nonunit _ hnu, MulChar.map_nonunit _ hnu]
    · have hcop := hp.coprime_iff_not_dvd.mpr hpd
      rw [changeLevel_natCast_of_coprime _ _ _ hcop,
        changeLevel_natCast_of_coprime _ _ _ hcop]
      exact hprime p hp hpd
  have hfac := χ.factorsThrough_gcd ψ heq
  have hd := χ.conductor_dvd_of_mem_conductorSet hfac
  rw [hχ] at hd
  exact hd.trans (Nat.gcd_dvd_right n m)

end Siegel
