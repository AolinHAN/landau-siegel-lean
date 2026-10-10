import Siegel.AnalyticBridge
import Siegel.Estimates

/-! Passing from the convergent Euler series to the split-prime sum. -/

namespace Siegel

open scoped BigOperators ComplexOrder

/-- The exponential loss at the choice `s = 1 + 1 / log X`. -/
theorem prime_rpow_log_scale_le (p : ℕ) (X : ℝ) (hp : 0 < p)
    (hX : 1 < X) (hpX : (p : ℝ) ≤ X) :
    (p : ℝ) ^ (1 + 1 / Real.log X) ≤ (p : ℝ) * Real.exp 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [Real.rpow_add hp0, Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hp0.le
  rw [Real.rpow_def_of_pos hp0, Real.exp_le_exp]
  have h := Real.log_le_log hp0 hpX
  rw [mul_one_div]
  apply (div_le_iff₀ hlog).mpr
  simpa only [one_mul] using h

/-- A split prime contributes exactly `2 log p / p^s` to the real Euler series. -/
theorem split_prime_term_re {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : ℕ) (hp : p.Prime) (hχ : χ (p : ZMod q) = 1) (s : ℝ) :
    (LSeries.term (mangoldtCombination χ) (s : ℂ) p).re =
      2 * Real.log p / (p : ℝ) ^ s := by
  rw [LSeries.term_of_ne_zero hp.ne_zero]
  simp only [mangoldtCombination, ArithmeticFunction.vonMangoldt_apply_prime hp, hχ]
  rw [← Complex.ofReal_natCast p, ← Complex.ofReal_cpow (Nat.cast_nonneg p) s]
  norm_num [← Complex.ofReal_mul, ← Complex.ofReal_div]
  simp only [Complex.log_re, Complex.norm_natCast]
  ring

/-- The explicit `2/e` lower bound in the proof of Lemma 2. -/
theorem splitPrimeSum_le_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (X : ℝ) (hX : 1 < X) :
    (2 / Real.exp 1) * splitPrimeSum χ X ≤
      (logDerivativeCombination χ ((1 + 1 / Real.log X : ℝ) : ℂ)).re := by
  classical
  let s : ℝ := 1 + 1 / Real.log X
  let P := (Finset.range (⌊X⌋₊ + 1)).filter
    (fun p => Nat.Prime p ∧ χ (p : ZMod q) = 1)
  have hs : 1 < s := by
    dsimp [s]
    exact lt_add_of_pos_right _ (one_div_pos.mpr (Real.log_pos hX))
  have hsum := mangoldtCombination_summable χ (s := (s : ℂ)) (by simpa using hs)
  have hreal := (Complex.hasSum_re hsum.hasSum).summable
  have hnonneg (n : ℕ) : 0 ≤ (LSeries.term (mangoldtCombination χ) (s : ℂ) n).re :=
    (Complex.nonneg_iff.mp (LSeries.term_nonneg (mangoldtCombination_nonneg χ hχ n) s)).1
  have hfinite : (∑ p ∈ P, (LSeries.term (mangoldtCombination χ) (s : ℂ) p).re) ≤
      (logDerivativeCombination χ (s : ℂ)).re := by
    rw [← mangoldtCombination_LSeries_eq χ (by simpa using hs), LSeries, Complex.re_tsum hsum]
    exact hreal.sum_le_tsum P (fun n _ => hnonneg n)
  apply le_trans _ hfinite
  change (2 / Real.exp 1) * (∑ p ∈ P, Real.log p / p) ≤ _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hdata := Finset.mem_filter.mp hp
  have hpprime : p.Prime := hdata.2.1
  have hpFloor : (p : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hdata.1)
  have hpX : (p : ℝ) ≤ X := hpFloor.trans (Nat.floor_le (by linarith : 0 ≤ X))
  rw [split_prime_term_re χ p hpprime hdata.2.2]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
  calc
    _ = 2 * Real.log p / ((p : ℝ) * Real.exp 1) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hp0 s)
      (prime_rpow_log_scale_le p X hpprime.pos hX hpX)

end Siegel
