import Siegel.PrimeBias
import Siegel.MertensLower

/-! The passage from split primes to admissible inert primes in Lemma 2. -/

namespace Siegel

open scoped BigOperators

private theorem sum_union_le_nonneg {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ s ∪ t, f i) ≤ (∑ i ∈ s, f i) + ∑ i ∈ t, f i := by
  have h : (∑ i ∈ s ∪ t, f i) + (∑ i ∈ s ∩ t, f i) =
      (∑ i ∈ s, f i) + ∑ i ∈ t, f i := Finset.sum_union_inter
  have hn : 0 ≤ ∑ i ∈ s ∩ t, f i := Finset.sum_nonneg (fun i _ => hf i)
  linarith

/-- The elementary bound for prime divisors of a nonzero integer. -/
theorem prime_divisor_weight_sum_le (q : ℕ) (hq : q ≠ 0) :
    (∑ p ∈ q.primeFactors, Real.log p / p) ≤ Real.log q := by
  have hpos : (0 : ℝ) < (∏ p ∈ q.primeFactors, p : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have hle : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  have hl := Real.log_le_log hpos hle
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)] at hl
  apply le_trans _ hl
  apply Finset.sum_le_sum
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  exact div_le_self (Real.log_natCast_nonneg p) hp1

/-- Removing primes at most `H` and primes dividing `2q` costs exactly
an `H`-dependent finite sum and at most `log (2q)`. -/
theorem prime_partition_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (H : ℕ) (X : ℝ) :
    (∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p / p) ≤
      splitPrimeSum χ X + inertPrimeSum χ H X +
        (∑ p ∈ Nat.primesLE H, Real.log p / p) + Real.log (2 * (q : ℝ)) := by
  classical
  let f : ℕ → ℝ := fun p => Real.log p / p
  let S := (Finset.range (⌊X⌋₊ + 1)).filter
    (fun p => Nat.Prime p ∧ χ (p : ZMod q) = 1)
  let I := admissiblePrimes χ H X
  let B := Nat.primesLE H
  let D := (2 * q).primeFactors
  have hf (p : ℕ) : 0 ≤ f p := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hq : 2 * q ≠ 0 := mul_ne_zero (by norm_num) (NeZero.ne q)
  have hcover : Nat.primesLE ⌊X⌋₊ ⊆ ((S ∪ I) ∪ B) ∪ D := by
    intro p hp
    obtain ⟨hpX, hpprime⟩ := Nat.mem_primesLE.mp hp
    have hprange : p ∈ Finset.range (⌊X⌋₊ + 1) := Finset.mem_range.mpr (by omega)
    by_cases hd : p ∣ 2 * q
    · exact Finset.mem_union_right _ (Nat.Prime.mem_primeFactors hpprime hd hq)
    by_cases hsmall : p ≤ H
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Nat.mem_primesLE.mpr ⟨hsmall, hpprime⟩))
    have hunit : IsUnit (χ (p : ZMod q)) :=
      IsUnit.map χ (ZMod.isUnit_prime_of_not_dvd hpprime
        (fun h => hd (dvd_mul_of_dvd_right h 2)))
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rcases hχ (p : ZMod q) with hz | ho | hn
    · exact False.elim (hunit.ne_zero hz)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hprange, hpprime, ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hprange, hpprime, by omega, hd, hn⟩)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hcover (fun p _ _ => hf p)
  have h1 := sum_union_le_nonneg S I f hf
  have h2 := sum_union_le_nonneg (S ∪ I) B f hf
  have h3 := sum_union_le_nonneg ((S ∪ I) ∪ B) D f hf
  have hd := prime_divisor_weight_sum_le (2 * q) hq
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hd
  change (∑ p ∈ Nat.primesLE ⌊X⌋₊, f p) ≤
    (∑ p ∈ S, f p) + (∑ p ∈ I, f p) + (∑ p ∈ B, f p) + Real.log (2 * (q : ℝ))
  change (∑ p ∈ D, f p) ≤ _ at hd
  linarith

/-- The purely arithmetic implication `(2.1) → (2.2)`, with an absolute
Mertens constant and an explicit finite contribution depending only on `H`. -/
theorem exists_inert_lower_from_split_constant :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsQuadratic → ∀ (H : ℕ) (X : ℝ), 3 ≤ X →
      Real.log X - splitPrimeSum χ X - Real.log q -
        (C₀ + ∑ p ∈ Nat.primesLE H, Real.log p / p) ≤ inertPrimeSum χ H X := by
  obtain ⟨C, hC, hM⟩ := exists_mertens_lower_constant
  refine ⟨C + Real.log 2, by positivity, ?_⟩
  intro q _ χ hχ H X hX
  have h := prime_partition_bound χ hχ H X
  have hm := hM X hX
  rw [Real.log_mul (by norm_num) (by exact_mod_cast (NeZero.ne q))] at h
  linarith

end Siegel
