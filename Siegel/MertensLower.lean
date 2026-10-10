import Mathlib

/-! The one-sided Mertens estimate required by (2.2), from factorials. -/

namespace Siegel

open scoped BigOperators

/-- Factorization of the factorial, after taking real logarithms. -/
theorem log_factorial_eq_prime_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, (N.factorial.factorization p : ℝ) * Real.log p := by
  have hfac : N.factorial.primeFactors = Nat.primesLE N := by
    ext p
    rw [Nat.mem_primeFactors, Nat.mem_primesLE]
    constructor
    · rintro ⟨hp, hd, _⟩
      exact ⟨hp.dvd_factorial.mp hd, hp⟩
    · rintro ⟨hle, hp⟩
      exact ⟨hp, hp.dvd_factorial.mpr hle, Nat.factorial_ne_zero N⟩
  have hprod : N.factorial = ∏ p ∈ Nat.primesLE N, p ^ N.factorial.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero N)]
    rw [Nat.prod_factorization_eq_prod_primeFactors, hfac]
  conv_lhs => rw [hprod]
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by
    exact_mod_cast pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero)]
  simp only [Nat.cast_pow, Real.log_pow]

/-- A real-valued consequence of Legendre's formula. -/
theorem factorial_factorization_le (N p : ℕ) (hp : p.Prime) :
    (N.factorial.factorization p : ℝ) ≤ (N : ℝ) / (p - 1 : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Nat.factorization_def _ hp]
  apply (le_div_iff₀ (by linarith)).mpr
  by_cases hN : N = 0
  · subst N
    simp
  · have h := (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hN).le
    have hreal : ((p - 1 : ℕ) : ℝ) * (padicValNat p N.factorial : ℝ) ≤ N := by
      exact_mod_cast h
    rw [Nat.cast_sub hp.one_le, Nat.cast_one] at hreal
    nlinarith

/-- A convergent majorant for the contribution of higher prime powers. -/
theorem prime_power_correction_le (p : ℕ) (hp : 2 ≤ p) :
    Real.log p / ((p : ℝ) * (p - 1)) ≤ 4 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hl := Real.log_natCast_le_rpow_div p (show (0 : ℝ) < 1 / 2 by norm_num)
  have hpow : (p : ℝ) ^ (-3 / 2 : ℝ) * (p : ℝ) ^ 2 = (p : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
    norm_num
  have hden : 0 < (p : ℝ) * (p - 1) := mul_pos hp0 (by linarith)
  apply (div_le_iff₀ hden).mpr
  have hr : 0 ≤ (p : ℝ) ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hp0.le _
  nlinarith [mul_nonneg hr (show (0 : ℝ) ≤ p * (p - 2) by positivity)]

/-- An absolute convergent constant bounds all higher-prime-power errors. -/
theorem prime_power_correction_sum_le (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * (p - 1))) ≤
      4 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, 4 * (p : ℝ) ^ (-3 / 2 : ℝ) :=
      Finset.sum_le_sum fun p hp => prime_power_correction_le p (Nat.prime_of_mem_primesLE hp).two_le
    _ = 4 * ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (-3 / 2 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by norm_num)

/-- A lower Mertens bound at integer cutoffs; the constant is absolute. -/
theorem mertens_lower_nat (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - (1 + 4 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogfac : (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    have h := Stirling.le_log_factorial_stirling (show N ≠ 0 by omega)
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
    have hlogpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    linarith
  have hupper : Real.log (N.factorial : ℝ) ≤
      (N : ℝ) * (∑ p ∈ Nat.primesLE N, (Real.log p / p +
        Real.log p / ((p : ℝ) * (p - 1)))) := by
    rw [log_factorial_eq_prime_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpprime := Nat.prime_of_mem_primesLE hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    calc
      _ ≤ ((N : ℝ) / (p - 1 : ℝ)) * Real.log p :=
        mul_le_mul_of_nonneg_right (factorial_factorization_le N p hpprime)
          (Real.log_nonneg hp1.le)
      _ = _ := by
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp1ne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp
        ring
  rw [Finset.sum_add_distrib] at hupper
  have hc := prime_power_correction_sum_le N
  have hbound := mul_le_mul_of_nonneg_left hc hN0.le
  nlinarith

/-- The real-cutoff estimate used to pass from split primes to inert primes.
Only this lower half of Mertens' estimate is required in the paper. -/
theorem exists_mertens_lower_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 3 ≤ X →
      Real.log X - C ≤ ∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p / p := by
  let C : ℝ := 1 + 4 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C + Real.log 2, by positivity, ?_⟩
  intro X hX
  have hN : 1 ≤ ⌊X⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ X)).mpr (by norm_num; linarith)
  have hNp : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast (show 0 < ⌊X⌋₊ by omega)
  have hx2 : X ≤ 2 * (⌊X⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one X
    have h1 : (1 : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hN
    linarith
  have hlog := Real.log_le_log (show 0 < X by linarith) hx2
  rw [Real.log_mul (by norm_num) hNp.ne'] at hlog
  have hn := mertens_lower_nat ⌊X⌋₊ hN
  dsimp [C] at *
  linarith

end Siegel
