import Mathlib

namespace Siegel

open scoped ArithmeticFunction.Moebius LSeries.notation

/-- The Euler inverse at two gives a conductor-independent lower bound. -/
theorem exists_LFunction_two_norm_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      c ≤ ‖χ.LFunction 2‖ := by
  let A : ℝ := ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖) :=
    (LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun _ _ => by simp)
      (by norm_num : 1 < (2 : ℂ).re)).norm
  have hA : 0 ≤ A := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨1 / (A + 1), by positivity, ?_⟩
  intro q _ χ
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ (by norm_num : 1 < (2 : ℂ).re)
  have hnorm : ‖LSeries (↗χ * ↗μ) 2‖ ≤ A := by
    have hb (n : ℕ) : ‖(↗χ * ↗μ) n‖ ≤ ‖(1 : ℂ)‖ := by
      simp only [Pi.mul_apply, norm_mul, norm_one]
      have hm : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
        simpa using (show ((|μ n| : ℤ) : ℝ) ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n))
      exact mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) hm
    have hterms := fun n => LSeries.norm_term_le (f := ↗χ * ↗μ)
      (g := fun _ => (1 : ℂ)) (2 : ℂ) (hb n)
    have hs : Summable (fun n => ‖LSeries.term (↗χ * ↗μ) 2 n‖) :=
      hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterms
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hterms hsum)
  have hprod : 1 ≤ ‖χ.LFunction 2‖ * (A + 1) := by
    have he := congrArg norm hmul
    rw [norm_mul, norm_one, ← χ.LFunction_eq_LSeries (by norm_num)] at he
    have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg (χ.LFunction 2))
    nlinarith [norm_nonneg (χ.LFunction 2)]
  exact (div_le_iff₀ (by positivity : 0 < A + 1)).mpr hprod

end Siegel
