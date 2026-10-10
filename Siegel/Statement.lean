import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The paper's analytic target and established local facts

`UniformExclusion` is the exact quantifier pattern of Theorem 1, stated using
mathlib's analytically continued Dirichlet L-function. Its proof is
`Siegel.uniformExclusion` in `Siegel.Main`.

`MulChar.IsQuadratic` means that character values belong to `{0, 1, -1}`;
for the nonprincipal characters here this expresses the real-character
condition. No uniformity in the conductor is asserted by the local theorems.
-/

namespace Siegel

/-- The logarithmically normalized real zero gap, equation (1.1). -/
noncomputable def logGap (q : ℕ) (β : ℝ) : ℝ :=
  (1 - β) * Real.log (q : ℝ)

/-- The hypotheses imposed on a zero in Theorem 1. -/
def AdmissibleZero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ) : Prop :=
  3 ≤ q ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.IsQuadratic ∧
    0 < β ∧ β < 1 ∧ χ.LFunction (β : ℂ) = 0

/-- The paper's Theorem 1, proved by `Siegel.uniformExclusion` in `Siegel.Main`. -/
def UniformExclusion : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
      AdmissibleZero χ β → c ≤ logGap q β

/-- Positivity of each individual gap does not give a uniform lower bound. -/
theorem logGap_pos {q : ℕ} {β : ℝ} (hq : 3 ≤ q) (hβ : β < 1) :
    0 < logGap q β := by
  unfold logGap
  apply mul_pos (sub_pos.mpr hβ)
  apply Real.log_pos
  exact_mod_cast (by omega : 1 < q)

/-- Nonprincipal Dirichlet L-functions are nonzero on some complex ball about 1.
The radius depends on the character. -/
theorem nonvanishing_near_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ⦃s : ℂ⦄, dist s 1 < ε → χ.LFunction s ≠ 0 := by
  exact Metric.eventually_nhds_iff.mp
    ((DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt.eventually_ne
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ))

/-- The real interval version of character-dependent nonvanishing near 1. -/
theorem real_nonvanishing_near_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, 1 - ε < β → β < 1 → χ.LFunction (β : ℂ) ≠ 0 := by
  obtain ⟨ε, hε, h⟩ := nonvanishing_near_one χ hχ
  refine ⟨ε, hε, fun β hβ₁ hβ₂ ↦ h ?_⟩
  rw [dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hβ₂)]
  linarith

/-- All real zeros below 1 of one fixed nonprincipal character have a positive
normalized gap. The lower bound is allowed to depend on the character. -/
theorem fixed_character_gap_lower_bound {q : ℕ} [NeZero q]
    (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ,
      β < 1 → χ.LFunction (β : ℂ) = 0 → c ≤ logGap q β := by
  obtain ⟨ε, hε, hnonzero⟩ := real_nonvanishing_near_one χ hχ
  have hlog : 0 < Real.log (q : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < q)
  refine ⟨ε * Real.log (q : ℝ), mul_pos hε hlog, ?_⟩
  intro β hβ hzero
  have hβ' : β ≤ 1 - ε := by
    by_contra! h
    exact hnonzero β h hβ hzero
  exact mul_le_mul_of_nonneg_right (by linarith : ε ≤ 1 - β) hlog.le

/-- A finite family of positive real numbers has a common positive lower bound. -/
theorem finite_positive_lower_bound {ι : Type*} [Finite ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ d : ℝ, 0 < d ∧ ∀ i, d ≤ c i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hfinite : ∀ s : Finset ι, ∃ d : ℝ, 0 < d ∧ ∀ i ∈ s, d ≤ c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨d, hd, hs⟩ := ih
      refine ⟨min d (c i), lt_min hd (hc i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hs j hj)
  obtain ⟨d, hd, hs⟩ := hfinite Finset.univ
  exact ⟨d, hd, fun i ↦ hs i (Finset.mem_univ i)⟩

/-- A finite family of nonprincipal characters admits a common positive lower
bound for normalized real zero gaps. This is not uniform over unbounded conductors. -/
theorem finite_family_gap_lower_bound {ι : Type*} [Finite ι]
    (q : ι → ℕ) [∀ i, NeZero (q i)]
    (χ : (i : ι) → DirichletCharacter ℂ (q i))
    (hq : ∀ i, 3 ≤ q i) (hχ : ∀ i, χ i ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : ι) (β : ℝ),
      β < 1 → (χ i).LFunction (β : ℂ) = 0 → c ≤ logGap (q i) β := by
  classical
  have hlocal := fun i ↦ fixed_character_gap_lower_bound (hq i) (χ i) (hχ i)
  choose c hc hbound using hlocal
  obtain ⟨d, hd, hdc⟩ := finite_positive_lower_bound c hc
  exact ⟨d, hd, fun i β hβ hzero ↦ (hdc i).trans (hbound i β hβ hzero)⟩

end Siegel
