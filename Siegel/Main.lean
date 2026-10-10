import Siegel.QuadraticModel
import Siegel.LogDerivativeUpper
import Siegel.SingleZeroBound

/-! The paper's main theorem for Mathlib's actual Dirichlet L-function. -/

namespace Siegel

/-- Theorem 1: an absolute positive lower bound for the logarithmically
normalized real zero gap of every primitive nonprincipal real character. -/
theorem uniformExclusion : UniformExclusion :=
  uniformExclusion_of_logDerivative_upper logDerivativeUpper_from_global_zeros

/-- Fully expanded form of Theorem 1, making the order of quantifiers and
the standard Dirichlet L-function explicit. -/
theorem uniform_exclusion_of_landau_siegel_zeros :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
        3 ≤ q → χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
        0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  obtain ⟨c, hc, h⟩ := uniformExclusion
  refine ⟨c, hc, ?_⟩
  intro q _ χ β hq hprim hnontriv hreal hβ0 hβ1 hzero
  exact h q χ β ⟨hq, hprim, hnontriv, hreal, hβ0, hβ1, hzero⟩

end Siegel
