import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The prime sums and analytic statement of Section 2

`PrimeBiasStatement` is proved by `Siegel.primeBias` in
`Siegel.LogDerivativeUpper`. Its prime sums use the actual Mathlib Dirichlet
character. The proof combines the logarithmic derivative bound, Euler
products, and a Mertens lower estimate.
-/

namespace Siegel

open scoped BigOperators

/-- The prime sum in (2.1), for a real cutoff `X`. -/
noncomputable def splitPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ χ (p : ZMod q) = 1), Real.log p / p

/-- The admissible primes used in (2.2) and Section 5. -/
noncomputable def admissiblePrimes {q : ℕ} (χ : DirichletCharacter ℂ q)
    (H : ℕ) (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊X⌋₊ + 1)).filter
    (fun p => Nat.Prime p ∧ H < p ∧ ¬ p ∣ 2 * q ∧ χ (p : ZMod q) = -1)

/-- The sum in (2.2). -/
noncomputable def inertPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (H : ℕ) (X : ℝ) : ℝ :=
  ∑ p ∈ admissiblePrimes χ H X, Real.log p / p

/-- Lemma 2, with all implicit constants and their dependencies exposed.
The common constant `C` is absolute; `C_H` is chosen before the conductor,
character, zero and cutoff. The proof is `Siegel.primeBias`. -/
def PrimeBiasStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ C_H : ℝ, 0 ≤ C_H ∧
    ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      3 ≤ q → χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
      ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 →
      ∀ X : ℝ, 3 ≤ X →
        splitPrimeSum χ X ≤
          C * Real.log q + C * ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q ∧
        Real.log X - C * Real.log q -
          C * ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q - C_H ≤
          inertPrimeSum χ H X

end Siegel
