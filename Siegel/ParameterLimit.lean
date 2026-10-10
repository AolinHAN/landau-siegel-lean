import Siegel.Estimates

/-! Section 6 with an integer power `N = q^k`, an allowed choice of the
paper's fixed exponent. No ceiling errors are needed for this choice. -/

namespace Siegel

open Filter

noncomputable def powerCutoff (q k : ℕ) : ℝ := ((q ^ k : ℕ) : ℝ) ^ (4 / 3 : ℝ)

theorem powerCutoff_log (q k : ℕ) (hq : 0 < q) :
    Real.log (powerCutoff q k) = (4 * (k : ℝ) / 3) * Real.log q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [powerCutoff, Nat.cast_pow, Real.log_rpow (pow_pos hq0 k), Real.log_pow]
  ring

theorem powerCutoff_tendsto (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (k : ℕ) (hk : 0 < k) : Tendsto (fun n => powerCutoff (q n) k) atTop atTop := by
  have hqR : Tendsto (fun n => (q n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hq
  have hN := (tendsto_pow_atTop (show k ≠ 0 by omega)).comp hqR
  simpa only [powerCutoff, Nat.cast_pow] using
    (tendsto_rpow_atTop (show (0 : ℝ) < 4 / 3 by norm_num)).comp hN

/-- The exponent can be fixed using only the absolute analytic constant. -/
theorem exists_power_exponent (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ, 0 < k ∧ (C + 13 / 24) * 3 / (4 * (k : ℝ)) ≤ 1 / 16 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (12 * (C + 13 / 24))
  have hk0 : (0 : ℝ) < k := by linarith
  refine ⟨k, by exact_mod_cast hk0, ?_⟩
  apply (div_le_iff₀ (mul_pos (by norm_num) hk0)).mpr
  linarith

/-- All errors in the normalized determinant comparison tend to zero
for the counterexample sequence, with the chosen exponent held fixed. -/
theorem power_comparison_impossible (q : ℕ → ℕ) (δ : ℕ → ℝ)
    (hq : Tendsto q atTop atTop) (hδ : Tendsto δ atTop (nhds 0))
    (C C_H K : ℝ) (k : ℕ) (hk : 0 < k)
    (hkbound : (C + 13 / 24) * 3 / (4 * (k : ℝ)) ≤ 1 / 16)
    (hcompare : ∀ᶠ n in atTop,
      1 ≤ (13 / 16 : ℝ) + (C + 13 / 24) * Real.log (q n) / Real.log (powerCutoff (q n) k) +
        C * δ n * Real.log (powerCutoff (q n) k) / Real.log (q n) +
        (C_H + (13 / 12) * Real.log 8 + K * Real.log 4) / Real.log (powerCutoff (q n) k) +
        (3 * K / 2) / powerCutoff (q n) k) : False := by
  have hU := powerCutoff_tendsto q hq k hk
  have hu := Real.tendsto_log_atTop.comp hU
  let E : ℕ → ℝ := fun n => (4 * C * (k : ℝ) / 3) * δ n +
    (C_H + (13 / 12) * Real.log 8 + K * Real.log 4) / Real.log (powerCutoff (q n) k) +
    (3 * K / 2) / powerCutoff (q n) k
  have hE : Tendsto E atTop (nhds 0) := by
    have h := ((hδ.const_mul (4 * C * (k : ℝ) / 3)).add
      (hu.const_div_atTop (C_H + (13 / 12) * Real.log 8 + K * Real.log 4))).add
      (hU.const_div_atTop (3 * K / 2))
    simpa only [mul_zero, zero_add, E] using h
  have hbound : ∀ᶠ n in atTop, (1 : ℝ) ≤ 7 / 8 + E n := by
    filter_upwards [hcompare, hq.eventually (eventually_ge_atTop 3)] with n hn hqn
    have hq0 : 0 < q n := by omega
    have hlogq : 0 < Real.log (q n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q n by omega))
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [powerCutoff_log (q n) k hq0] at hn
    have h1 : (C + 13 / 24) * Real.log (q n) / ((4 * (k : ℝ) / 3) * Real.log (q n)) =
        (C + 13 / 24) * 3 / (4 * (k : ℝ)) := by field_simp
    have h2 : C * δ n * ((4 * (k : ℝ) / 3) * Real.log (q n)) / Real.log (q n) =
        (4 * C * (k : ℝ) / 3) * δ n := by field_simp
    rw [h1, h2, ← powerCutoff_log (q n) k hq0] at hn
    dsimp [E]
    linarith
  have hlimit : Tendsto (fun n => (7 / 8 : ℝ) + E n) atTop (nhds (7 / 8 + 0)) :=
    tendsto_const_nhds.add hE
  have h := ge_of_tendsto hlimit hbound
  norm_num at h

end Siegel
