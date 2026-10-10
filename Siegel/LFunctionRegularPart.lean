import Siegel.DiskRegularPart
import Siegel.DivisorTranslation
import Siegel.LFunctionZeroCount

namespace Siegel

open Metric Filter
open scoped Topology

/-- Uniform local zero removal for the actual Dirichlet L-function, including
the full error term needed in its logarithmic derivative estimate. -/
theorem exists_LFunction_regular_part_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      3 ≤ q → χ ≠ 1 →
      ∃ (S : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
        (∀ w ∈ S, w ∈ ball 0 (7 / 4 : ℝ) ∧ χ.LFunction (w + 2) = 0 ∧ 0 < m w) ∧
        AnalyticOnNhd ℂ g (closedBall 0 (7 / 4 : ℝ)) ∧
        (∀ z ∈ ball 0 (7 / 4 : ℝ), g z ≠ 0) ∧
        (∀ z ∈ closedBall 0 (7 / 4 : ℝ),
          g =ᶠ[𝓝[≠] z] (fun w => χ.LFunction (w + 2) * canonicalProduct (7 / 4) S m w)) ∧
        (∀ z : ℂ, ‖z‖ ≤ 1 →
          ‖logDeriv g z‖ + (4 / 3 : ℝ) * ∑ w ∈ S, (m w : ℝ) + 2 ≤ C * Real.log q) := by
  obtain ⟨c, hc, hcenter⟩ := exists_LFunction_two_norm_lower_bound
  obtain ⟨C₀, hC₀, hcount⟩ := exists_LFunction_disk_zero_count_bound
  let K : ℝ := max (Real.log (32 / c) + 1) 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨160 * (K + 1) + (4 / 3) * C₀ + 2, by positivity, ?_⟩
  intro q _ χ hq hχ
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogq : 1 ≤ Real.log (q : ℝ) := by
    have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq3
    linarith [Real.log_three_gt_d9]
  let f : ℂ → ℂ := fun z => χ.LFunction (z + 2)
  have hf : AnalyticOnNhd ℂ f (closedBall 0 (7 / 4 : ℝ)) := by
    intro z hz
    exact ((DirichletCharacter.differentiable_LFunction hχ).analyticAt (z + 2)).comp
      (f := fun w : ℂ => w + 2) (by fun_prop)
  have hf0 : f 0 ≠ 0 := by
    simpa [f] using χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by norm_num : 1 ≤ (2 : ℂ).re)
  have hbound : ∀ z ∈ sphere 0 (7 / 4 : ℝ), ‖f z‖ ≤ 32 * q := by
    intro z hz
    apply norm_LFunction_disk_le χ (by omega) hχ
    have hz' : ‖z‖ = (7 / 4 : ℝ) := by simpa [mem_sphere, dist_eq_norm] using hz
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
    rw [hz']
    norm_num
  obtain ⟨S, m, g, hS, h0, hg, hgnz, heq, hderiv, hN⟩ :=
    exists_disk_regular_part f hf hf0 (32 * q) (by positivity) hbound
  have htrans := divisor_sum_translate χ.LFunction (2 : ℂ) (7 / 4 : ℝ)
    (fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
  change ((∑ w ∈ S, m w : ℕ) : ℤ) ≤
    ∑ᶠ z, MeromorphicOn.divisor (fun w => χ.LFunction (w + 2)) (closedBall 0 (7 / 4 : ℝ)) z at hN
  rw [htrans] at hN
  have hNR : (∑ w ∈ S, (m w : ℝ)) ≤
      ((∑ᶠ z, MeromorphicOn.divisor χ.LFunction (closedBall (2 : ℂ) (7 / 4 : ℝ)) z : ℤ) : ℝ) := by
    exact_mod_cast hN
  have hNbound := hNR.trans (hcount χ hq hχ)
  have hcent : c ≤ ‖f 0‖ := by simpa [f] using hcenter χ
  have hlogcent := Real.log_le_log hc hcent
  have hlogid : Real.log (32 * (q : ℝ)) - Real.log c + 1 =
      Real.log q + (Real.log (32 / c) + 1) := by
    rw [Real.log_mul (by norm_num) hqp.ne', Real.log_div (by norm_num) hc.ne']
    ring
  have hlogbound : Real.log (32 * (q : ℝ)) - Real.log ‖f 0‖ + 1 ≤
      (K + 1) * Real.log q := by
    have hklog : K ≤ K * Real.log q := by nlinarith
    have hconst : Real.log (32 / c) + 1 ≤ K := le_max_left _ _
    nlinarith [hlogid]
  refine ⟨S, m, g, hS, hg, hgnz, heq, ?_⟩
  intro z hz
  have hd := hderiv z hz
  nlinarith

end Siegel
