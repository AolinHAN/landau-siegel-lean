import Siegel.AnalyticBridge
import Mathlib.NumberTheory.MulChar.Lemmas

/-! Real-valued characters and their logarithmic derivatives on the real axis. -/

namespace Siegel

/-- For a complex Dirichlet character, the quadratic condition is exactly
real-valuedness, including its zero values at nonunits. -/
theorem isQuadratic_iff_im_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    χ.IsQuadratic ↔ ∀ x : ZMod q, (χ x).im = 0 := by
  constructor
  · intro hχ x
    rcases hχ x with h | h | h <;> simp [h]
  · intro hreal
    have hstar : star χ = χ := by
      apply MulChar.ext
      intro x
      change star (χ x) = χ x
      exact Complex.conj_eq_iff_im.mpr (hreal x)
    rw [MulChar.star_eq_inv] at hstar
    apply MulChar.isQuadratic_iff_sq_eq_one.mpr
    rw [pow_two]
    calc
      χ * χ = χ⁻¹ * χ := congrArg (fun ψ => ψ * χ) hstar.symm
      _ = 1 := inv_mul_cancel χ

/-- A convergent Dirichlet series with real coefficients is real on the real axis. -/
theorem LSeries_im_eq_zero_of_real (f : ℕ → ℂ) (hf : ∀ n, (f n).im = 0)
    (s : ℝ) (hs : LSeriesSummable f (s : ℂ)) :
    (LSeries f (s : ℂ)).im = 0 := by
  rw [LSeries, Complex.im_tsum hs]
  trans ∑' _ : ℕ, (0 : ℝ)
  · apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp [hn]
    rw [LSeries.term_of_ne_zero hn]
    have hfcast : ((f n).re : ℂ) = f n := Complex.ext rfl (by simp [hf])
    have hpow : (n : ℂ) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm
    rw [hpow, ← hfcast, ← Complex.ofReal_div]
    rfl
  · simp

/-- The logarithmic derivative of the actual L-function is real for real `s>1`
when the character is real. This follows from the convergent von Mangoldt series. -/
theorem logDeriv_LFunction_im_eq_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) :
    (logDeriv χ.LFunction (s : ℂ)).im = 0 := by
  have hsC : 1 < (s : ℂ).re := by simpa using hs
  have hreal := (isQuadratic_iff_im_eq_zero χ).mp hχ
  have h := LSeries_im_eq_zero_of_real
    ((fun n : ℕ => χ (n : ZMod q)) * (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)))
    (by intro n; simp [Complex.mul_im, hreal]) s
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsC)
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hsC,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hsC,
    ← DirichletCharacter.LFunction_eq_LSeries χ hsC] at h
  simpa only [logDeriv_apply, neg_div, Complex.neg_im, neg_eq_zero] using h

/-- The real-axis logarithmic derivative equals the complex inclusion of its real part. -/
theorem logDeriv_LFunction_eq_ofReal_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (s : ℝ) (hs : 1 < s) :
    logDeriv χ.LFunction (s : ℂ) = ((logDeriv χ.LFunction (s : ℂ)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using logDeriv_LFunction_im_eq_zero χ hχ s hs

end Siegel
