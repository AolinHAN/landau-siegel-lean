import Siegel.AnalyticBridge

/-! The absolute zeta-function error in equation (2.4). -/

namespace Siegel

open DirichletCharacter

/-- Removing the zeta pole gives the entire function already constructed
in Mathlib for the trivial character of conductor one. -/
theorem zeta_pole_removed_value (s : ℂ) (hs : s ≠ 1) :
    LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  rw [LFunctionTrivChar₁, Function.update_of_ne hs]
  simp only [LFunctionTrivChar, LFunction_modOne_eq]

theorem zeta_pole_removed_deriv (s : ℂ) (hs : s ≠ 1) :
    deriv (LFunctionTrivChar₁ 1) s = (s - 1) * deriv riemannZeta s + riemannZeta s := by
  simpa only [LFunctionTrivChar, LFunction_modOne_eq] using
    deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs

/-- The term left after subtracting `1/(s-1)` is bounded on `1 < s ≤ 2`.
This proves the zeta-function part of (2.4) without using a zero-sum identity. -/
theorem exists_zeta_logDerivative_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re ≤ 1 / (s - 1) + C := by
  let F : ℂ → ℂ := fun z => -deriv (LFunctionTrivChar₁ 1) z / LFunctionTrivChar₁ 1 z
  have hc : ContinuousOn (fun s : ℝ => (F (s : ℂ)).re) (Set.Icc 1 2) := by
    apply Complex.continuous_re.comp_continuousOn
    apply (continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).comp Complex.continuous_ofReal.continuousOn
    intro s hs
    by_cases h1 : s = 1
    · left
      simp [h1]
    · right
      simp only [LFunctionTrivChar, LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_lt_re (by simp only [Complex.ofReal_re]; exact lt_of_le_of_ne hs.1 (Ne.symm h1))
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs hs2
  have hFs : (F (s : ℂ)).re ≤ C := hC (Set.mem_image_of_mem _ ⟨hs.le, hs2⟩)
  have hsne : (s : ℂ) ≠ 1 := by exact_mod_cast hs.ne'
  have hz : riemannZeta (s : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  have hid : -deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) =
      (1 / ((s : ℂ) - 1)) + F (s : ℂ) := by
    dsimp [F]
    rw [zeta_pole_removed_value _ hsne, zeta_pole_removed_deriv _ hsne]
    have hs0 : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hsne
    field_simp
    ring
  rw [hid, Complex.add_re]
  have hinv : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    norm_cast
  rw [hinv]
  linarith [le_max_left C 0]

end Siegel
