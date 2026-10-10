import Siegel.CompletedZeroMultiplicity

namespace Siegel

open scoped Classical

/-- The multiplicity of an actual nontrivial zero of the analytically
continued Dirichlet L-function; it is zero outside the open critical strip. -/
noncomputable def nontrivialZeroMultiplicity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℤ :=
  if ρ.re ∈ Set.Ioo (0 : ℝ) 1 then MeromorphicOn.divisor χ.LFunction Set.univ ρ else 0

/-- Completing the L-function removes its trivial zeros and leaves exactly
the nontrivial zeros with the same analytic multiplicities. -/
theorem completed_divisor_eq_nontrivialZeroMultiplicity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) (ρ : ℂ) :
    MeromorphicOn.divisor (completedDirichlet χ) Set.univ ρ =
      nontrivialZeroMultiplicity χ ρ := by
  by_cases hρ : ρ.re ∈ Set.Ioo (0 : ℝ) 1
  · rw [nontrivialZeroMultiplicity, if_pos hρ]
    exact divisor_completedDirichlet_eq_of_re_pos χ hχ hρ.1
  · rw [nontrivialZeroMultiplicity, if_neg hρ]
    by_contra hn
    have hz := (divisor_completedDirichlet_ne_zero_iff χ hχ ρ).mp hn
    exact hρ (completedDirichlet_zero_re_mem_Ioo χ hp hχ hquad hz)

/-- The multiplicity is nonzero exactly at nontrivial zeros. -/
theorem nontrivialZeroMultiplicity_ne_zero_iff {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) (ρ : ℂ) :
    nontrivialZeroMultiplicity χ ρ ≠ 0 ↔
      ρ.re ∈ Set.Ioo (0 : ℝ) 1 ∧ χ.LFunction ρ = 0 := by
  rw [← completed_divisor_eq_nontrivialZeroMultiplicity χ hp hχ hquad,
    divisor_completedDirichlet_ne_zero_iff χ hχ]
  constructor
  · intro hz
    have hs := completedDirichlet_zero_re_mem_Ioo χ hp hχ hquad hz
    exact ⟨hs, (completedDirichlet_eq_zero_iff_of_re_pos χ hs.1).mp hz⟩
  · rintro ⟨hs, hz⟩
    exact (completedDirichlet_eq_zero_iff_of_re_pos χ hs.1).mpr hz

/-- Actual nontrivial-zero multiplicities are nonnegative integers. -/
theorem nontrivialZeroMultiplicity_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) (ρ : ℂ) : 0 ≤ nontrivialZeroMultiplicity χ ρ := by
  rw [← completed_divisor_eq_nontrivialZeroMultiplicity χ hp hχ hquad]
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
    (fun z _ => (differentiable_completedDirichlet χ hχ).analyticAt z) ρ

end Siegel
