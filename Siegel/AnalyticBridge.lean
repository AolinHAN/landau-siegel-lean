import Siegel.Statement
import Siegel.PrimeBias
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Verified analytic links and bounded-conductor reduction

This file proves the Euler/logarithmic-derivative identity used in Section 2
and its positivity for real characters. It does not assume or assert the
zero-sum identity (2.3), whose Hadamard-product proof is not in mathlib.
The final theorems make the finite-conductor step of Section 6 explicit.
-/

namespace Siegel

open scoped BigOperators ComplexOrder

/-- The nonnegative Dirichlet-series coefficients in the proof of Lemma 2. -/
noncomputable def mangoldtCombination {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * (1 + χ (n : ZMod q))

/-- The sum of negative logarithmic derivatives occurring in (2.4). -/
noncomputable def logDerivativeCombination {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s - deriv χ.LFunction s / χ.LFunction s

/-- The Dirichlet series with coefficients `Λ(n)(1 + χ(n))` converges for `Re s > 1`. -/
theorem mangoldtCombination_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (mangoldtCombination χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).add
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)
  convert h using 1
  ext n
  simp only [mangoldtCombination, Pi.add_apply, Pi.mul_apply]
  ring

/-- The actual Euler-series equality from Section 2, on its convergence half-plane. -/
theorem mangoldtCombination_LSeries_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (mangoldtCombination χ) s = logDerivativeCombination χ s := by
  have hcoeff : mangoldtCombination χ =
      (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) +
        (fun n : ℕ ↦ χ (n : ZMod q)) *
          (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    ext n
    simp only [mangoldtCombination, Pi.add_apply, Pi.mul_apply]
    ring
  rw [hcoeff, LSeries_add (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs),
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs]
  rw [logDerivativeCombination, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring

/-- For a real character all coefficients in the combined Euler series are nonnegative. -/
theorem mangoldtCombination_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (n : ℕ) : 0 ≤ mangoldtCombination χ n := by
  have hΛ : (0 : ℂ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ) := by
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
  rcases hχ (n : ZMod q) with h | h | h
  · simpa only [mangoldtCombination, h, add_zero, mul_one] using hΛ
  · simpa only [mangoldtCombination, h, mul_add, mul_one] using add_nonneg hΛ hΛ
  · simp [mangoldtCombination, h]

/-- The combined logarithmic derivative is real and nonnegative for real `s > 1`. -/
theorem logDerivativeCombination_nonneg {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) {s : ℝ} (hs : 1 < s) :
    0 ≤ logDerivativeCombination χ (s : ℂ) := by
  rw [← mangoldtCombination_LSeries_eq χ (by simpa using hs), LSeries]
  exact tsum_nonneg fun n ↦ LSeries.term_nonneg (mangoldtCombination_nonneg χ hχ n) s

/-- Every bounded range of conductors has a positive normalized zero gap.
This constant may depend on `Q`; no bound uniform in `Q` is claimed. -/
theorem bounded_conductor_gap_lower_bound (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
        3 ≤ q → q ≤ Q → χ ≠ 1 → β < 1 → χ.LFunction (β : ℂ) = 0 →
          c ≤ logGap q β := by
  classical
  let I := {q : Fin (Q + 1) // 3 ≤ q.val}
  letI : Fintype I := inferInstance
  let J := (q : I) × {χ : DirichletCharacter ℂ q.val.val // χ ≠ 1}
  letI : Fintype J := inferInstance
  let qfun : J → ℕ := fun i ↦ i.1.val.val
  let χfun : (i : J) → DirichletCharacter ℂ (qfun i) := fun i ↦ i.2.val
  have hq : ∀ i : J, 3 ≤ qfun i := fun i ↦ i.1.property
  letI : ∀ i : J, NeZero (qfun i) := fun i ↦ ⟨by have := hq i; omega⟩
  obtain ⟨c, hc, hbound⟩ := finite_family_gap_lower_bound qfun χfun hq
    (fun i ↦ i.2.property)
  refine ⟨c, hc, ?_⟩
  intro q _ χ β hq₃ hqQ hχ hβ hzero
  exact hbound ⟨⟨⟨q, by omega⟩, hq₃⟩, ⟨χ, hχ⟩⟩ β hβ hzero

/-- Failure of the target produces arbitrarily small normalized gaps at
arbitrarily large conductors. This is the exact compactness reduction
needed for (6.1), without an unproved finiteness assumption. -/
theorem arbitrarily_small_gap_large_conductor (h : ¬ UniformExclusion)
    (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (β : ℝ),
      Q < q ∧ AdmissibleZero χ β ∧ logGap q β < ε := by
  obtain ⟨c, hc, hbounded⟩ := bounded_conductor_gap_lower_bound Q
  have hnot : ¬ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
      AdmissibleZero χ β → min c ε ≤ logGap q β := by
    intro hall
    exact h ⟨min c ε, lt_min hc hε, hall⟩
  push Not at hnot
  obtain ⟨q, hq, χ, β, hzero, hsmall⟩ := hnot
  letI := hq
  refine ⟨q, hq, χ, β, ?_, hzero, hsmall.trans_le (min_le_right _ _)⟩
  by_contra! hqQ
  have hbound := hbounded q χ β hzero.1 hqQ hzero.2.2.1
    hzero.2.2.2.2.2.1 hzero.2.2.2.2.2.2
  exact (not_lt_of_ge hbound) (hsmall.trans_le (min_le_left _ _))

/-- The counterexample sequence (6.1), derived from failure of Theorem 1.
Both the conductors tending to infinity and the gaps tending to zero are proved. -/
theorem counterexample_sequence_of_not_uniform (h : ¬ UniformExclusion) :
    ∃ (q : ℕ → ℕ) (hq : ∀ n, NeZero (q n))
      (χ : (n : ℕ) → DirichletCharacter ℂ (q n)) (β : ℕ → ℝ),
      (∀ n, @AdmissibleZero (q n) (hq n) (χ n) (β n)) ∧
      Filter.Tendsto q Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n => logGap (q n) (β n)) Filter.atTop (nhds 0) := by
  classical
  have hex (n : ℕ) := arbitrarily_small_gap_large_conductor h n (1 / ((n : ℝ) + 1))
    (by positivity)
  choose q hq χ β hlarge hadm hsmall using hex
  refine ⟨q, hq, χ, β, hadm, ?_, ?_⟩
  · exact Filter.tendsto_atTop_mono (fun n => (hlarge n).le) Filter.tendsto_id
  · apply squeeze_zero (fun n => (logGap_pos (hadm n).1 (hadm n).2.2.2.2.2.1).le)
      (fun n => (hsmall n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat

end Siegel
