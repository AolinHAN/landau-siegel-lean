import Siegel.CompletedLFunction
import Siegel.LFunctionGrowth
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

namespace Siegel

open MeasureTheory Set

/-- Euler's integral bounds the complex gamma function by the real gamma
function at the real part. -/
theorem norm_Gamma_le_realGamma (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  calc
    ‖∫ x : ℝ in Ioi 0, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖
      ≤ ∫ x : ℝ in Ioi 0, ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s.re - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul, Complex.norm_of_nonneg (le_of_lt (Real.exp_pos (-x))),
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

/-- A coarse logarithmic gamma bound, obtained from convexity and factorials. -/
theorem log_realGamma_le_factorial_bound (n : ℕ) (x : ℝ)
    (hx : 1 / 4 ≤ x) (hxn : x ≤ (n : ℝ) + 4) :
    Real.log (Real.Gamma x) ≤ |Real.log (Real.Gamma (1 / 4))| +
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) := by
  have hconv := Real.convexOn_log_Gamma.le_max_of_mem_Icc
    (show (1 / 4 : ℝ) ∈ Ioi 0 by norm_num)
    (show (n : ℝ) + 4 ∈ Ioi 0 by change 0 < (n : ℝ) + 4; positivity) ⟨hx, hxn⟩
  simp only [Function.comp_apply] at hconv
  have hfac : Real.log (Real.Gamma ((n : ℝ) + 4)) ≤
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) := by
    have hid : (n : ℝ) + 4 = ((n + 3 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hid, Real.Gamma_nat_eq_factorial]
    have hle : (((n + 3).factorial : ℕ) : ℝ) ≤ (((n + 3 : ℕ) : ℝ) ^ (n + 3)) := by
      exact_mod_cast Nat.factorial_le_pow (n + 3)
    apply (Real.log_le_log (by positivity) hle).trans
    rw [Real.log_pow]
    norm_num [Nat.cast_add, Nat.cast_ofNat]
  apply hconv.trans
  apply max_le
  · exact (le_abs_self _).trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith))))
  · exact hfac.trans (le_add_of_nonneg_left (abs_nonneg _))

/-- The normalized real gamma factor has the same coarse growth bound. -/
theorem log_norm_GammaReal_le_factorial_bound (n : ℕ) (s : ℂ)
    (hs : 1 / 2 ≤ s.re) (hsn : s.re ≤ 2 * ((n : ℝ) + 4)) :
    Real.log ‖Complex.Gammaℝ s‖ ≤ |Real.log (Real.Gamma (1 / 4))| +
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) := by
  have hspos : 0 < s.re := by linarith
  have hhalf : 0 < (s / 2).re := by simp only [Complex.div_ofNat_re]; linarith
  have hnorm : ‖Complex.Gammaℝ s‖ ≤ Real.Gamma (s.re / 2) := by
    rw [Complex.Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hpow : Real.pi ^ (-s / 2).re ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
      simp only [Complex.div_ofNat_re, Complex.neg_re]
      linarith
    calc
      Real.pi ^ (-s / 2).re * ‖Complex.Gamma (s / 2)‖ ≤
          1 * ‖Complex.Gamma (s / 2)‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ Real.Gamma (s.re / 2) := by
        simpa only [one_mul, Complex.div_ofNat_re] using norm_Gamma_le_realGamma (s / 2) hhalf
  apply (Real.log_le_log (norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos hspos)) hnorm).trans
  exact log_realGamma_le_factorial_bound n _ (by linarith) (by linarith)

/-- Both parity choices obey one common gamma-factor bound. -/
theorem log_norm_gammaFactor_le_factorial_bound {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) (s : ℂ)
    (hs : 1 / 2 ≤ s.re) (hsn : ‖s‖ ≤ (n : ℝ) + 3) :
    Real.log ‖χ.gammaFactor s‖ ≤ |Real.log (Real.Gamma (1 / 4))| +
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) := by
  have hre : s.re ≤ (n : ℝ) + 3 :=
    (Complex.re_le_norm s).trans hsn
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact log_norm_GammaReal_le_factorial_bound n s hs (by linarith [Nat.cast_nonneg (α := ℝ) n])
  · rw [ho.gammaFactor_def]
    apply log_norm_GammaReal_le_factorial_bound n (s + 1)
    · simp only [Complex.add_re, Complex.one_re]; linarith
    · simp only [Complex.add_re, Complex.one_re]; linarith [Nat.cast_nonneg (α := ℝ) n]

/-- Product expression on the positive half-plane. -/
theorem completedDirichlet_eq_product {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    completedDirichlet χ s = (q : ℂ) ^ (s / 2) * χ.gammaFactor s * χ.LFunction s := by
  unfold completedDirichlet
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl (by
    intro h; simp [h] at hs))]
  field_simp [gammaFactor_ne_zero_of_re_pos χ hs]

/-- Explicit coarse growth on the right half-plane. -/
theorem log_norm_completedDirichlet_right_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hχ : χ ≠ 1)
    (n : ℕ) (s : ℂ) (hs : 1 / 2 ≤ s.re) (hsn : ‖s‖ ≤ (n : ℝ) + 3)
    (hne : completedDirichlet χ s ≠ 0) :
    Real.log ‖completedDirichlet χ s‖ ≤
      ((n : ℝ) + 3) * Real.log (q : ℝ) + Real.log (2 * (q : ℝ)) +
      Real.log ((n : ℝ) + 3) + |Real.log (Real.Gamma (1 / 4))| +
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) := by
  have hqp : 0 < (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  have hsp : 0 < s.re := by linarith
  have hnormL : ‖χ.LFunction s‖ ≤ 2 * (q : ℝ) * ((n : ℝ) + 3) := by
    apply (norm_LFunction_le_conductor χ hq hχ s hsp).trans
    apply (div_le_iff₀ hsp).mpr
    calc
      ‖s‖ * (q : ℝ) ≤ ((n : ℝ) + 3) * q := by gcongr
      _ ≤ 2 * (q : ℝ) * ((n : ℝ) + 3) * s.re := by
        have hh := mul_le_mul_of_nonneg_left hs
          (show 0 ≤ 2 * (q : ℝ) * ((n : ℝ) + 3) by positivity)
        nlinarith
  have hLne : χ.LFunction s ≠ 0 := by
    intro hz
    apply hne
    rw [completedDirichlet_eq_product χ hsp, hz, mul_zero]
  have hlogL := Real.log_le_log (norm_pos_iff.mpr hLne) hnormL
  rw [Real.log_mul (by positivity : (2 * (q : ℝ)) ≠ 0) (by positivity)] at hlogL
  have hgamma := log_norm_gammaFactor_le_factorial_bound χ n s hs hsn
  have hpow : Real.log ‖(q : ℂ) ^ (s / 2)‖ ≤
      ((n : ℝ) + 3) * Real.log (q : ℝ) := by
    rw [show (q : ℂ) = ((q : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hqp, Real.log_rpow hqp]
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg q)
    simp only [Complex.div_ofNat_re]
    have hre := (Complex.re_le_norm s).trans hsn
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [completedDirichlet_eq_product χ hsp, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))) )
      (norm_ne_zero_iff.mpr (gammaFactor_ne_zero_of_re_pos χ hsp)))
      (norm_ne_zero_iff.mpr hLne),
    Real.log_mul (norm_ne_zero_iff.mpr
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))))
      (norm_ne_zero_iff.mpr (gammaFactor_ne_zero_of_re_pos χ hsp))]
  linarith

/-- A global order-one growth bound sufficient for the large-disk zero
expansion.  The constant may depend on the fixed character. -/
theorem exists_completedDirichlet_log_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hquad : χ.IsQuadratic) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ), 1 ≤ n → ∀ z : ℂ,
      ‖z - 2‖ ≤ (n : ℝ) →
      Real.log ‖completedDirichlet χ z‖ ≤
        A * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2) := by
  let C : ℝ := |Real.log ‖χ.rootNumber‖| + |Real.log (2 * (q : ℝ))| +
    |Real.log (Real.Gamma (1 / 4))|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  refine ⟨3 * Real.log (q : ℝ) + C + 9, by positivity, ?_⟩
  intro n hn z hz
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let T : ℝ := ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2)
  have hlog : 1 ≤ Real.log ((n : ℝ) + 2) := by
    have he := Real.log_le_log (by norm_num : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ (n : ℝ) + 2 by linarith)
    linarith [Real.log_three_gt_d9]
  have hT : (n : ℝ) + 1 ≤ T := by
    dsimp [T]
    nlinarith
  have hT1 : 1 ≤ T := by linarith
  by_cases hzero : completedDirichlet χ z = 0
  · simp only [hzero, norm_zero, Real.log_zero]
    positivity
  have hz_norm : ‖z‖ ≤ (n : ℝ) + 2 := by
    have h := norm_le_norm_sub_add z (2 : ℂ)
    norm_num at h
    linarith
  have hraw : Real.log ‖completedDirichlet χ z‖ ≤
      ((n : ℝ) + 3) * Real.log (q : ℝ) + Real.log ((n : ℝ) + 3) +
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) + C := by
    by_cases hright : 1 / 2 ≤ z.re
    · have h := log_norm_completedDirichlet_right_bound χ hq hχ n z hright
        (by linarith) hzero
      dsimp [C]
      linarith [le_abs_self (Real.log (2 * (q : ℝ))), abs_nonneg (Real.log ‖χ.rootNumber‖)]
    · have hrr : 1 / 2 ≤ (1 - z).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have hrn : ‖1 - z‖ ≤ (n : ℝ) + 3 := by
        have h := norm_sub_le (1 : ℂ) z
        norm_num at h
        linarith
      have hrne := rootNumber_ne_zero_of_quadratic χ hp hχ hquad
      have hzne : completedDirichlet χ (1 - z) ≠ 0 := by
        rw [completedDirichlet_reflection χ hp hquad]
        exact mul_ne_zero hrne hzero
      have h := log_norm_completedDirichlet_right_bound χ hq hχ n (1 - z) hrr hrn hzne
      have he := completedDirichlet_reflection χ hp hquad (1 - z)
      rw [show 1 - (1 - z) = z by ring] at he
      rw [he, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hrne)
        (norm_ne_zero_iff.mpr hzne)]
      dsimp [C]
      linarith [le_abs_self (Real.log (2 * (q : ℝ))), le_abs_self (Real.log ‖χ.rootNumber‖)]
  have hklog : Real.log ((n : ℝ) + 3) ≤ 2 * Real.log ((n : ℝ) + 2) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 3)
      (show (n : ℝ) + 3 ≤ ((n : ℝ) + 2) ^ 2 by nlinarith)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have h1 : ((n : ℝ) + 3) * Real.log (q : ℝ) ≤
      3 * Real.log (q : ℝ) * T := by nlinarith
  have h2 : Real.log ((n : ℝ) + 3) ≤ 2 * T := by
    have htlog : Real.log ((n : ℝ) + 2) ≤ T := by
      dsimp [T]
      nlinarith
    linarith
  have h3 : ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) ≤ 6 * T := by
    calc
      ((n : ℝ) + 3) * Real.log ((n : ℝ) + 3) ≤
          (3 * ((n : ℝ) + 1)) * (2 * Real.log ((n : ℝ) + 2)) := by
        apply mul_le_mul (by linarith) hklog (Real.log_nonneg (by linarith)) (by positivity)
      _ = 6 * T := by dsimp [T]; ring
  have h4 : C ≤ C * T := by nlinarith
  change Real.log ‖completedDirichlet χ z‖ ≤
    (3 * Real.log (q : ℝ) + C + 9) * ((n : ℝ) + 1) * Real.log ((n : ℝ) + 2)
  have hout : Real.log ‖completedDirichlet χ z‖ ≤
      (3 * Real.log (q : ℝ) + C + 9) * T := by nlinarith
  simpa only [T, mul_assoc] using hout

end Siegel
