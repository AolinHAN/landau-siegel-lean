import Mathlib

namespace Siegel

open MeasureTheory Set Filter
open scoped Topology

noncomputable def partialSumStep (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

theorem partialSumStep_eq_zero (f : ℕ → ℂ) {t : ℝ} (ht : t < 1) :
    partialSumStep f t = 0 := by
  simp [partialSumStep, Nat.floor_eq_zero.mpr ht]

theorem partialSumStep_locallyIntegrable (f : ℕ → ℂ) :
    LocallyIntegrableOn (partialSumStep f) (Ioi 0) := by
  have h : LocallyIntegrableOn (partialSumStep f) (Ici 0) := by
    simpa [partialSumStep] using locallyIntegrableOn_mul_sum_Icc f
      (m := 1) (a := (0 : ℝ)) le_rfl (locallyIntegrableOn_const (1 : ℂ))
  exact h.mono_set Ioi_subset_Ici_self

theorem partialSumStep_isBigO_top (f : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ B) :
    partialSumStep f =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound B
  filter_upwards [] with t
  simpa [partialSumStep] using hB ⌊t⌋₊

theorem partialSumStep_isBigO_zero (f : ℕ → ℂ) (b : ℝ) :
    partialSumStep f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with t ht
  simp [partialSumStep_eq_zero f ht]

theorem mellin_partialSumStep_differentiableAt (f : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ B)
    (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (partialSumStep f) (-z)) s := by
  have hm : DifferentiableAt ℂ (mellin (partialSumStep f)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (partialSumStep_locallyIntegrable f)
      (partialSumStep_isBigO_top f B hB) (by simpa using neg_neg_of_pos hs)
      (partialSumStep_isBigO_zero f (-s.re - 1)) (by simp only [Complex.neg_re]; linarith)
  exact hm.comp s differentiableAt_id.neg

theorem mellin_partialSumStep_eq_integral (f : ℕ → ℂ) (s : ℂ) :
    mellin (partialSumStep f) (-s) =
      ∫ t in Ioi (1 : ℝ), partialSumStep f t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (show Ici (1 : ℝ) ⊆ Ioi 0 from fun t ht => show 0 < t from lt_of_lt_of_le zero_lt_one (show 1 ≤ t from ht))]
  · rw [integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    rw [show -s - 1 = -(s + 1) by ring]
    exact mul_comm _ _
  · intro t ht
    rw [partialSumStep_eq_zero f (lt_of_not_ge ht.2), smul_zero]

theorem norm_mellin_partialSumStep_le (f : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ B)
    (s : ℂ) (hs : 0 < s.re) :
    ‖mellin (partialSumStep f) (-s)‖ ≤ B / s.re := by
  rw [mellin_partialSumStep_eq_integral]
  have hi : IntegrableOn (fun t : ℝ => B * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one).const_mul B
  have hb : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1),
      ‖partialSumStep f t * (t : ℂ) ^ (-(s + 1))‖ ≤ B * t ^ (-s.re - 1) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht1 : 1 < t := ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < t)]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    have he : -(s.re + 1) = -s.re - 1 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (hB ⌊t⌋₊) (Real.rpow_nonneg (by linarith) _)
  apply (norm_integral_le_of_norm_le hi hb).trans_eq
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) zero_lt_one]
  simp
  ring

end Siegel
