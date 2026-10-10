import Siegel.CharacterSums
import Siegel.AbelMellin

namespace Siegel

open MeasureTheory Set Filter
open scoped Topology

/-- Abel summation represents the actual analytic continuation throughout
Re(s)>0, using the bounded partial sums of a nonprincipal character. -/
theorem LFunction_eq_mellin_partialSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    χ.LFunction s = s * mellin (partialSumStep (fun n : ℕ => χ n)) (-s) := by
  let f : ℕ → ℂ := fun n => χ n
  let G : ℂ → ℂ := fun z => z * mellin (partialSumStep f) (-z)
  have hB : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ (q : ℝ) :=
    norm_character_sum_Icc_le χ hq hχ
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.re} := by
    intro z hz
    exact (differentiableAt_id.mul
      (mellin_partialSumStep_differentiableAt f q hB z hz)).differentiableWithinAt
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
    (hG.analyticOnNhd hU) (convex_halfSpace_re_gt 0).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | 0 < z.re} by norm_num) (z₀ := 2) ?_ hs
  have ho : IsOpen {z : ℂ | 1 < z.re} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by norm_num)] with z hz
  rw [χ.LFunction_eq_LSeries hz]
  change LSeries f z = z * mellin (partialSumStep f) (-z)
  rw [mellin_partialSumStep_eq_integral]
  apply LSeries_eq_mul_integral f (r := 0) le_rfl (lt_trans zero_lt_one hz)
    (χ.LSeriesSummable_of_one_lt_re hz)
  apply Asymptotics.IsBigO.of_bound (q : ℝ)
  filter_upwards [] with n
  simpa using hB n

/-- A polynomial conductor bound on the positive half-plane. -/
theorem norm_LFunction_le_conductor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) : ‖χ.LFunction s‖ ≤ ‖s‖ * q / s.re := by
  rw [LFunction_eq_mellin_partialSum χ hq hχ s hs, norm_mul]
  have h := norm_mellin_partialSumStep_le (fun n : ℕ => χ n) q
    (norm_character_sum_Icc_le χ hq hχ) s hs
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left h (norm_nonneg s)

/-- Uniform growth on the fixed disk used to extract zeros near one. -/
theorem norm_LFunction_disk_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : s ∈ Metric.closedBall (2 : ℂ) (15 / 8 : ℝ)) :
    ‖χ.LFunction s‖ ≤ 32 * q := by
  have hdist : ‖s - 2‖ ≤ 15 / 8 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hre : 1 / 8 ≤ s.re := by
    have ha := Complex.abs_re_le_norm (s - 2)
    simp only [Complex.sub_re, Complex.re_ofNat] at ha
    linarith [neg_abs_le (s.re - 2)]
  have hn : ‖s‖ ≤ 4 := by
    have ht := norm_le_norm_sub_add s (2 : ℂ)
    norm_num at ht
    linarith
  apply (norm_LFunction_le_conductor χ hq hχ s (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < s.re)).mpr
  nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]

end Siegel
