import Siegel.MertensLower
import Siegel.Estimates
import Mathlib.NumberTheory.Chebyshev

/-! The two-sided Mertens estimate displayed in the proof of Lemma 2. -/

namespace Siegel

/-- The first term of Legendre's formula gives a lower factorial valuation. -/
theorem div_le_factorial_factorization (N p : ℕ) (hp : p.Prime) :
    N / p ≤ N.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (show Nat.log p N < Nat.log p N + 2 by omega)]
  have hmem : 1 ∈ Finset.Ico 1 (Nat.log p N + 2) := by simp
  simpa using (Finset.single_le_sum (fun i _ => Nat.zero_le (N / p ^ i)) hmem)

/-- The upper half of Mertens' estimate follows from the factorial and Chebyshev. -/
theorem mertens_upper_nat (N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ Nat.primesLE N, Real.log p / p) ≤ Real.log N + Real.log 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfac : Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
    have h := Real.log_le_log (show (0 : ℝ) < N.factorial by positivity)
      (show (N.factorial : ℝ) ≤ (N : ℝ) ^ N by exact_mod_cast N.factorial_le_pow)
    simpa only [Real.log_pow] using h
  have hlower : (N : ℝ) * (∑ p ∈ Nat.primesLE N, Real.log p / p) -
      (∑ p ∈ Nat.primesLE N, Real.log p) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_prime_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hprime := Nat.prime_of_mem_primesLE hp
    have hval : (N : ℝ) / p - 1 ≤ (N.factorial.factorization p : ℝ) :=
      (nat_div_lower N p hprime.pos).trans (by exact_mod_cast div_le_factorial_factorization N p hprime)
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    have h := mul_le_mul_of_nonneg_right hval hlog
    convert h using 1
    ring
  have htheta : (∑ p ∈ Nat.primesLE N, Real.log p) ≤ Real.log 4 * N := by
    simpa only [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast] using
      Chebyshev.theta_le_log4_mul_x hN0.le
  nlinarith

/-- The complete estimate `sum_{p≤X} log(p)/p = log X + O(1)`, with an absolute
constant and a real cutoff, as displayed in the proof of Lemma 2. -/
theorem exists_mertens_absolute_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 3 ≤ X →
      |(∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p / p) - Real.log X| ≤ C := by
  obtain ⟨C, hC, hlower⟩ := exists_mertens_lower_constant
  refine ⟨max C (Real.log 4), hC.trans (le_max_left _ _), ?_⟩
  intro X hX
  have hN : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ X)).mpr (by norm_num; linarith)
  have hNp : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast (show 0 < ⌊X⌋₊ by omega)
  have hlog : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X :=
    Real.log_le_log hNp (Nat.floor_le (by linarith))
  have hu := mertens_upper_nat ⌊X⌋₊ hN
  have hl := hlower X hX
  rw [abs_le]
  constructor <;> linarith [le_max_left C (Real.log 4), le_max_right C (Real.log 4)]

end Siegel
