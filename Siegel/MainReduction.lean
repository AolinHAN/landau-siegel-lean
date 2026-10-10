import Siegel.PrimeBiasAssembly
import Siegel.ScalarComparison
import Siegel.ParameterLimit

/-! The full reduction of Theorem 1 to two explicit inputs:
the logarithmic-derivative bound and the quadratic character realization. -/

namespace Siegel

open Filter

/-- The arithmetic realization used in Section 4, allowing finitely many
exceptional conductors. This proposition is proved in `Siegel.QuadraticModel`, not assumed as an axiom. -/
def QuadraticModelStatement : Prop :=
  ∃ Q : ℕ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
    Q ≤ q → 3 ≤ q → χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
    ∃ (d : ℤ) (a b : ℂ), a ^ 2 = (d : ℂ) ∧ b ^ 2 = 2 ∧
      LinearIndependent ℚ ![1, a, b, a * b] ∧ |(d : ℝ)| ≤ q ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q →
        χ (p : ZMod q) = (legendreSym p d : ℂ)

/-- With Lemma 2 and the quadratic realization, all of the determinant
construction, parameter choices, finite-conductor removal and limiting
contradiction have proofs. The two hypotheses are not hidden assumptions. -/
theorem uniformExclusion_of_primeBias_and_models
    (hprime : PrimeBiasStatement) (hmodels : QuadraticModelStatement) : UniformExclusion := by
  by_contra hnot
  obtain ⟨q, hq, χ, β, hadm, hqtop, hδ⟩ := counterexample_sequence_of_not_uniform hnot
  letI : ∀ n, NeZero (q n) := hq
  obtain ⟨C, hC, hprime⟩ := hprime
  let H : ℕ := 86713344
  obtain ⟨C_H, _, hprime⟩ := hprime H (by norm_num [H])
  obtain ⟨Q, hmodel⟩ := hmodels
  obtain ⟨k, hk, hkbound⟩ := exists_power_exponent C hC
  let K : ℝ := (4 * 97 ^ 2) / (H : ℝ) ^ (2 / 3 : ℝ)
  have hNtop : Tendsto (fun n => q n ^ k) atTop atTop :=
    (tendsto_pow_atTop (show k ≠ 0 by omega)).comp hqtop
  have hUtop := powerCutoff_tendsto q hqtop k hk
  have hYtop : Tendsto (fun n => (H : ℝ) ^ (2 / 3 : ℝ) * powerCutoff (q n) k)
      atTop atTop := hUtop.const_mul_atTop (by dsimp [H]; positivity)
  apply power_comparison_impossible q (fun n => logGap (q n) (β n)) hqtop hδ C C_H K k hk hkbound
  filter_upwards [hqtop.eventually (eventually_ge_atTop Q),
    hNtop.eventually (eventually_ge_atTop H), hUtop.eventually (eventually_ge_atTop 3),
    hYtop.eventually (eventually_ge_atTop (2 * 97 ^ 2))] with n hqn hNn hUn hYn
  obtain ⟨hq3, hprim, hnontriv, hreal, hβ0, hβ1, hzero⟩ := hadm n
  obtain ⟨d, a, b, ha, hb, hlin, hd, hchar⟩ :=
    hmodel (χ n) hqn hq3 hprim hnontriv hreal
  have hN0 : (0 : ℝ) < ((q n ^ k : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (show 0 < q n by omega) k
  have hℓ : 0 < Real.log (q n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q n by omega))
  have hU : 0 < powerCutoff (q n) k := by linarith
  have hu : 0 < Real.log (powerCutoff (q n) k) := Real.log_pos (by linarith)
  have hlogN : Real.log ((q n ^ k : ℕ) : ℝ) = (3 / 4 : ℝ) * Real.log (powerCutoff (q n) k) := by
    rw [powerCutoff, Real.log_rpow hN0]
    ring
  have hlower := (hprime (χ n) hq3 hprim hnontriv hreal (β n) hβ0 hβ1 hzero
    (powerCutoff (q n) k) hUn).2
  have hupper := inertPrimeSum_upper_of_model d (q n ^ k) H (q n) a b ha hb hlin (χ n)
    hchar (by omega) hd (by rfl) hNn hYn
  change inertPrimeSum (χ n) H (powerCutoff (q n) k) ≤
    (13 / 12 : ℝ) * (Real.log ((q n ^ k : ℕ) : ℝ) + Real.log (q n) / 2 + Real.log 8) +
      K * (Real.log 4 + 2 * Real.log ((q n ^ k : ℕ) : ℝ) / powerCutoff (q n) k) at hupper
  rw [hlogN] at hupper
  apply scalar_comparison_normalization _ _ _ _ _ _ _ _ hU hu hℓ
  · exact hlower
  · convert hupper using 1 <;> ring

/-- Theorem 1 reduced to exactly the analytic and arithmetic inputs
used by this reduction. The arithmetic input is discharged in `Siegel.QuadraticModel`. -/
theorem uniformExclusion_of_logDerivative_upper_and_models
    (hld : LogDerivativeUpperStatement) (hmodels : QuadraticModelStatement) : UniformExclusion :=
  uniformExclusion_of_primeBias_and_models (primeBias_of_logDerivative_upper hld) hmodels

end Siegel
