import Siegel.ParameterLimit

/-! The real-power cutoff `N = ⌈q^γ⌉` used in Section 6 of the paper. -/

namespace Siegel

open Filter

/-- The integer box size for an arbitrary fixed positive real exponent. -/
noncomputable def ceilingPower (q : ℕ) (γ : ℝ) : ℕ := ⌈(q : ℝ) ^ γ⌉₊

/-- The associated natural degree scale `U = N^(4/3)`. -/
noncomputable def ceilingCutoff (q : ℕ) (γ : ℝ) : ℝ :=
  (ceilingPower q γ : ℝ) ^ (4 / 3 : ℝ)

theorem ceilingPower_tendsto (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n => ceilingPower (q n) γ) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    ((tendsto_rpow_atTop hγ).comp (tendsto_natCast_atTop_atTop.comp hq))

/-- Rounding a growing positive real power changes it by a relative error tending to zero. -/
theorem ceilingPower_ratio_tendsto (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n => (ceilingPower (q n) γ : ℝ) / (q n : ℝ) ^ γ)
      atTop (nhds 1) := by
  exact tendsto_nat_ceil_div_atTop.comp
    ((tendsto_rpow_atTop hγ).comp (tendsto_natCast_atTop_atTop.comp hq))

/-- The ceiling error has no effect on the limiting logarithmic exponent. -/
theorem ceilingPower_log_ratio_tendsto (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n => Real.log (ceilingPower (q n) γ : ℝ) / Real.log (q n))
      atTop (nhds γ) := by
  have hqR : Tendsto (fun n => (q n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hq
  have hlogq := Real.tendsto_log_atTop.comp hqR
  have hratio := (ceilingPower_ratio_tendsto q hq γ hγ).log (by norm_num : (1 : ℝ) ≠ 0)
  have herror : Tendsto
      (fun n => Real.log ((ceilingPower (q n) γ : ℝ) / (q n : ℝ) ^ γ) /
        Real.log (q n)) atTop (nhds 0) := by
    simpa using hratio.mul (hlogq.const_div_atTop 1)
  have ht := herror.const_add γ
  have heq : (fun n => Real.log (ceilingPower (q n) γ : ℝ) / Real.log (q n)) =ᶠ[atTop]
      (fun n => γ + Real.log ((ceilingPower (q n) γ : ℝ) / (q n : ℝ) ^ γ) /
        Real.log (q n)) := by
    filter_upwards [hq.eventually (eventually_ge_atTop 2)] with n hn
    have hq0 : (0 : ℝ) < q n := by exact_mod_cast (show 0 < q n by omega)
    have hq1 : (1 : ℝ) < q n := by exact_mod_cast (show 1 < q n by omega)
    have hpow : 0 < (q n : ℝ) ^ γ := Real.rpow_pos_of_pos hq0 γ
    have hN : 0 < (ceilingPower (q n) γ : ℝ) := by
      exact_mod_cast (Nat.ceil_pos.mpr hpow)
    rw [Real.log_div hN.ne' hpow.ne', Real.log_rpow hq0]
    have hl : Real.log (q n : ℝ) ≠ 0 := (Real.log_pos hq1).ne'
    field_simp
    ring
  simpa using ht.congr' heq.symm

theorem ceilingCutoff_tendsto (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n => ceilingCutoff (q n) γ) atTop atTop := by
  exact (tendsto_rpow_atTop (show (0 : ℝ) < 4 / 3 by norm_num)).comp
    (tendsto_natCast_atTop_atTop.comp (ceilingPower_tendsto q hq γ hγ))

/-- The exact asymptotic displayed in Section 6: `log U / log q → 4γ/3`. -/
theorem ceilingCutoff_log_ratio_tendsto (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n => Real.log (ceilingCutoff (q n) γ) / Real.log (q n))
      atTop (nhds (4 * γ / 3)) := by
  have h := (ceilingPower_log_ratio_tendsto q hq γ hγ).const_mul (4 / 3 : ℝ)
  have heq : (fun n => Real.log (ceilingCutoff (q n) γ) / Real.log (q n)) =ᶠ[atTop]
      (fun n => (4 / 3 : ℝ) *
        (Real.log (ceilingPower (q n) γ : ℝ) / Real.log (q n))) := by
    filter_upwards [(ceilingPower_tendsto q hq γ hγ).eventually (eventually_ge_atTop 1)] with n hn
    have hN : (0 : ℝ) < ceilingPower (q n) γ := by
      exact_mod_cast (show 0 < ceilingPower (q n) γ by omega)
    rw [ceilingCutoff, Real.log_rpow hN]
    ring
  simpa only [div_mul_eq_mul_div] using h.congr' heq.symm

/-- The zero-gap term still tends to zero with a fixed real exponent and ceiling. -/
theorem ceilingCutoff_zero_term_tendsto (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (nhds 0)) (C γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun n => C * δ n * Real.log (ceilingCutoff (q n) γ) / Real.log (q n))
      atTop (nhds 0) := by
  have h := (hδ.const_mul C).mul (ceilingCutoff_log_ratio_tendsto q hq γ hγ)
  simpa only [mul_zero, zero_mul, zero_div, ← mul_div_assoc] using h

/-- The final limiting contradiction also holds for the paper's arbitrary
fixed real exponent with its ceiling, including all the normalized errors. -/
theorem ceiling_comparison_impossible (q : ℕ → ℕ) (δ : ℕ → ℝ)
    (hq : Tendsto q atTop atTop) (hδ : Tendsto δ atTop (nhds 0))
    (C C_H K γ : ℝ) (hγ : 0 < γ)
    (hγbound : (C + 13 / 24) * 3 / (4 * γ) ≤ 1 / 16)
    (hcompare : ∀ᶠ n in atTop,
      1 ≤ (13 / 16 : ℝ) + (C + 13 / 24) * Real.log (q n) / Real.log (ceilingCutoff (q n) γ) +
        C * δ n * Real.log (ceilingCutoff (q n) γ) / Real.log (q n) +
        (C_H + (13 / 12) * Real.log 8 + K * Real.log 4) / Real.log (ceilingCutoff (q n) γ) +
        (3 * K / 2) / ceilingCutoff (q n) γ) : False := by
  have hU := ceilingCutoff_tendsto q hq γ hγ
  have hu := Real.tendsto_log_atTop.comp hU
  have hratio : Tendsto (fun n => Real.log (q n) / Real.log (ceilingCutoff (q n) γ))
      atTop (nhds (3 / (4 * γ))) := by
    simpa only [inv_div] using
      (ceilingCutoff_log_ratio_tendsto q hq γ hγ).inv₀ (by positivity)
  have hzero := ceilingCutoff_zero_term_tendsto q hq δ hδ C γ hγ
  have hfixed := hu.const_div_atTop (C_H + (13 / 12) * Real.log 8 + K * Real.log 4)
  have htail := hU.const_div_atTop (3 * K / 2)
  have hlimit := (((hratio.const_mul (C + 13 / 24)).const_add (13 / 16)).add hzero).add
    hfixed |>.add htail
  have hbound := ge_of_tendsto hlimit (by
    simpa only [← mul_div_assoc] using hcompare)
  simp only [add_zero, ← mul_div_assoc] at hbound
  linarith

end Siegel
