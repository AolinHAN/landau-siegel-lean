import Siegel.ZetaPoleBound

/-! A two-sided error bound for the logarithmic derivative at the zeta pole. -/

namespace Siegel

open DirichletCharacter

/-- The complete uniform `O(1)` assertion used on page 3 of the paper:
after subtracting the pole, the real negative logarithmic derivative stays
bounded in absolute value throughout `1 < s ≤ 2`. -/
theorem exists_zeta_logDerivative_absolute_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      |(-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re - 1 / (s - 1)| ≤ C := by
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
      exact riemannZeta_ne_zero_of_one_lt_re (by
        simp only [Complex.ofReal_re]
        exact lt_of_le_of_ne hs.1 (Ne.symm h1))
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc.abs).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro s hs hs2
  have hFs : |(F (s : ℂ)).re| ≤ C := hC (Set.mem_image_of_mem _ ⟨hs.le, hs2⟩)
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
  have hinv : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by norm_cast
  rw [hinv, add_sub_cancel_left]
  exact hFs.trans (le_max_left _ _)

end Siegel
