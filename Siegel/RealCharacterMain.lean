import Siegel.Main
import Siegel.RealCharacter

namespace Siegel

/-- The main theorem with real-valuedness expressed directly, instead of
the equivalent `IsQuadratic` predicate. -/
theorem uniform_exclusion_for_real_characters :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
        3 ≤ q → χ.IsPrimitive → χ ≠ 1 → (∀ x : ZMod q, (χ x).im = 0) →
        0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  obtain ⟨c, hc, h⟩ := uniform_exclusion_of_landau_siegel_zeros
  refine ⟨c, hc, ?_⟩
  intro q _ χ β hq hprim hnontriv hreal hβ0 hβ1 hzero
  exact h q χ β hq hprim hnontriv ((isQuadratic_iff_im_eq_zero χ).mpr hreal) hβ0 hβ1 hzero

end Siegel
