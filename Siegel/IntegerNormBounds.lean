import Siegel.Estimates
import Siegel.PrimeBias
import Mathlib.NumberTheory.Chebyshev

/-! Combining prime divisibilities in a nonzero integer norm. -/

namespace Siegel

/-- Powers of distinct primes dividing a nonzero integer can be
combined, giving the first inequality of (5.6). -/
theorem integer_norm_log_lower (Z : ℤ) (hZ : Z ≠ 0) (s : Finset ℕ) (E : ℕ → ℕ)
    (hprime : ∀ p ∈ s, p.Prime)
    (hdiv : ∀ p ∈ s, (p : ℤ) ^ (4 * E p) ∣ Z) :
    (∑ p ∈ s, (E p : ℝ) * Real.log p) ≤ Real.log |(Z : ℝ)| / 4 := by
  have hd (p : ℕ) (hp : p ∈ s) : p ^ (4 * E p) ∣ Z.natAbs := by
    have h := (Int.natAbs_dvd_natAbs).mpr (hdiv p hp)
    simpa using h
  have hprod : (∏ p ∈ s, p ^ (4 * E p)) ∣ Z.natAbs := by
    apply Finset.prod_dvd_of_isRelPrime ?_ hd
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      (Nat.coprime_pow_primes _ _ (hprime p hp) (hprime q hq) hpq)
  have hle : ((∏ p ∈ s, p ^ (4 * E p) : ℕ) : ℝ) ≤ Z.natAbs := by
    exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.mpr hZ) hprod
  have hpos : (0 : ℝ) < (∏ p ∈ s, p ^ (4 * E p) : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => pow_pos (hprime p hp).pos _)
  have hlog := Real.log_le_log hpos hle
  have hnatAbs : (Z.natAbs : ℝ) = |(Z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hnatAbs, Nat.cast_prod, Real.log_prod (fun p hp => by
    exact_mod_cast pow_ne_zero _ (hprime p hp).ne_zero)] at hlog
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hlog
  have heq : (∑ p ∈ s, (4 * (E p : ℝ)) * Real.log p) =
      4 * ∑ p ∈ s, (E p : ℝ) * Real.log p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [heq] at hlog
  linarith

/-- Chebyshev's bound for the actual admissible-prime set. -/
theorem admissible_prime_log_sum_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    (H : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    (∑ p ∈ admissiblePrimes χ H X, Real.log p) ≤ Real.log 4 * X := by
  apply le_trans ?_ (Chebyshev.theta_le_log4_mul_x hX)
  rw [Chebyshev.theta_eq_sum_primesLE]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have h := Finset.mem_filter.mp hp
    have hprime : p.Prime := h.2.1
    have hbound : p ≤ ⌊X⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp h.1)
    exact Nat.mem_primesLE.mpr ⟨hbound, hprime⟩
  · intro p hp hnot
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)

/-- The full two-step lower bound (5.6), with a nonzero integer norm
and the actual admissible primes as inputs. -/
theorem determinant_norm_prime_lower {ι : Type*} (rows : Finset ι) (a : ι → ℕ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (H : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (Z : ℤ) (hZ : Z ≠ 0)
    (hdiv : ∀ p ∈ admissiblePrimes χ H X,
      (p : ℤ) ^ (4 * ∑ i ∈ rows, a i / p) ∣ Z) :
    (∑ i ∈ rows, (a i : ℝ)) * inertPrimeSum χ H X -
      rows.card * Real.log 4 * X ≤ Real.log |(Z : ℝ)| / 4 := by
  have hp : ∀ p ∈ admissiblePrimes χ H X, p.Prime :=
    fun p h => (Finset.mem_filter.mp h).2.1
  have hlog := integer_norm_log_lower Z hZ (admissiblePrimes χ H X)
    (fun p => ∑ i ∈ rows, a i / p) hp hdiv
  have hfloor := weighted_floor_lower rows a (admissiblePrimes χ H X)
    (fun p h => (hp p h).pos)
  have htheta := mul_le_mul_of_nonneg_left (admissible_prime_log_sum_le χ H X hX)
    (Nat.cast_nonneg rows.card : (0 : ℝ) ≤ rows.card)
  simp only [Nat.cast_sum] at hlog
  dsimp [inertPrimeSum]
  linarith

end Siegel
