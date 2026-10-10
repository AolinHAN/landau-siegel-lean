import Siegel.LFunctionGrowth
import Siegel.LFunctionCenter

namespace Siegel

open Metric

/-- Jensen's formula gives an absolute logarithmic bound for the total
multiplicity of the zeros in the fixed disk around two. -/
theorem exists_LFunction_disk_zero_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      3 ≤ q → χ ≠ 1 →
      ((∑ᶠ z, MeromorphicOn.divisor χ.LFunction (closedBall (2 : ℂ) (7 / 4 : ℝ)) z : ℤ) : ℝ)
        ≤ C * Real.log q := by
  obtain ⟨c, hc, hcenter⟩ := exists_LFunction_two_norm_lower_bound
  let K : ℝ := max (Real.log (32 / c)) 0
  let a : ℝ := Real.log (15 / 14 : ℝ)
  have hK : 0 ≤ K := le_max_right _ _
  have ha : 0 < a := Real.log_pos (by norm_num)
  refine ⟨(K + 1) / a, by positivity, ?_⟩
  intro q _ χ hq hχ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 1 ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq3
    linarith [Real.log_three_gt_d9]
  have hcent := hcenter χ
  have hnorm : 0 < ‖χ.LFunction 2‖ := hc.trans_le hcent
  have hj := AnalyticOnNhd.sum_divisor_le (f := χ.LFunction) (c := (2 : ℂ))
    (r := (7 / 4 : ℝ)) (R := (15 / 8 : ℝ)) (M := 32 * q)
    (by norm_num) (by norm_num) (by nlinarith)
    (fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
    (norm_pos_iff.mp hnorm) (fun z hz =>
      norm_LFunction_disk_le χ (by omega) hχ z (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 15 / 8)] using sphere_subset_closedBall hz))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] at hj
  norm_num at hj
  have hdiv : (32 * (q : ℝ)) / ‖χ.LFunction 2‖ ≤ 32 * q / c :=
    div_le_div_of_nonneg_left (by positivity) hc hcent
  have hlog := Real.log_le_log (by positivity : 0 < 32 * (q : ℝ) / ‖χ.LFunction 2‖) hdiv
  have hid : Real.log (32 * (q : ℝ) / c) = Real.log q + Real.log (32 / c) := by
    rw [Real.log_div (by positivity) hc.ne', Real.log_mul (by norm_num) hqp.ne',
      Real.log_div (by norm_num) hc.ne']
    ring
  have hupper : Real.log (32 * (q : ℝ) / ‖χ.LFunction 2‖) ≤ (K + 1) * Real.log q := by
    rw [hid] at hlog
    have hklog : K ≤ K * Real.log q := by nlinarith
    nlinarith [le_max_left (Real.log (32 / c)) 0]
  apply hj.trans
  change Real.log (32 * (q : ℝ) / ‖χ.LFunction 2‖) / a ≤ (K + 1) / a * Real.log q
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hupper ha.le

end Siegel
