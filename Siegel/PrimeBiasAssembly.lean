import Siegel.EulerPrimeComparison
import Siegel.PrimePartition

/-! Reduction of Lemma 2 to the logarithmic-derivative estimate. -/

namespace Siegel

/-- Equation (2.4), proved by `Siegel.logDerivativeUpper` in `Siegel.LogDerivativeUpper`. -/
def LogDerivativeUpperStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (β : ℝ), AdmissibleZero χ β → ∀ s : ℝ, 1 < s → s ≤ 2 →
      (logDerivativeCombination χ (s : ℂ)).re ≤
        C * Real.log q + 1 / (s - 1) - 1 / (s - β)

/-- All arithmetic and Euler-series steps from (2.4) to Lemma 2.
The only analytic hypothesis of this reduction is explicitly displayed. -/
theorem primeBias_of_logDerivative_upper (hld : LogDerivativeUpperStatement) :
    PrimeBiasStatement := by
  obtain ⟨C, hC, hbound⟩ := hld
  obtain ⟨C₀, hC₀, hpartition⟩ := exists_inert_lower_from_split_constant
  let A : ℝ := Real.exp 1 / 2 * (C + 1)
  have he : 0 < Real.exp 1 / 2 := by positivity
  have hA : 0 < A := mul_pos he (by linarith)
  refine ⟨A + 1, by positivity, ?_⟩
  intro H hH
  refine ⟨C₀ + ∑ p ∈ Nat.primesLE H, Real.log p / p, by positivity, ?_⟩
  intro q _ χ hq hprim hnontriv hreal β hβ0 hβ1 hzero X hX
  have hlogX : 1 < Real.log X := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hX
    linarith [Real.log_three_gt_d9]
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  let s : ℝ := 1 + 1 / Real.log X
  have hs : 1 < s := by dsimp [s]; exact lt_add_of_pos_right _ (by positivity)
  have hs2 : s ≤ 2 := by
    have hinv : 1 / Real.log X ≤ 1 := (div_le_one (by linarith)).mpr hlogX.le
    dsimp [s]
    linarith
  have hupper := hbound χ β ⟨hq, hprim, hnontriv, hreal, hβ0, hβ1, hzero⟩ s hs hs2
  have hrec := reciprocal_at_log_scale (Real.log X) β (by linarith) hβ1
  have hlower := splitPrimeSum_le_euler χ hreal X (by linarith)
  have hsplit0 : splitPrimeSum χ X ≤
      (Real.exp 1 / 2) * (C * Real.log q + (1 - β) * (Real.log X) ^ 2) := by
    have hepos : 0 < Real.exp 1 := Real.exp_pos _
    have hid : (Real.exp 1 / 2) * (2 / Real.exp 1) = 1 := by field_simp
    have h := mul_le_mul_of_nonneg_left
      (show (2 / Real.exp 1) * splitPrimeSum χ X ≤
        C * Real.log q + (1 - β) * (Real.log X) ^ 2 by
          dsimp [s] at hupper
          linarith) he.le
    rwa [← mul_assoc, hid, one_mul] at h
  let E : ℝ := (1 - β) * (Real.log X) ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsplit : splitPrimeSum χ X ≤ A * Real.log q + A * E := by
    have h1 : (Real.exp 1 / 2) * C ≤ A := by dsimp [A]; nlinarith
    have h2 : Real.exp 1 / 2 ≤ A := by dsimp [A]; nlinarith
    have hm1 := mul_le_mul_of_nonneg_right h1 hlogq.le
    have hm2 := mul_le_mul_of_nonneg_right h2 hE
    dsimp [E] at *
    nlinarith
  have hcancel : ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q = E := by
    dsimp [E]
    field_simp
  have hcancel' : (A + 1) * ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q =
      (A + 1) * E := by rw [mul_assoc, mul_div_assoc, hcancel]
  rw [hcancel']
  refine ⟨?_, ?_⟩
  · nlinarith
  · have hp := hpartition χ hreal H X hX
    nlinarith

end Siegel
