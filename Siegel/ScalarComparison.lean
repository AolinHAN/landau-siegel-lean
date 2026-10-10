import Siegel.SelectedIntegral

/-! A scalar upper estimate obtained from the actual integral determinant. -/

namespace Siegel

open Siegel.Interpolation

/-- Lemma 6 bounds the ratio of the two row moments uniformly in the field. -/
theorem moment_ratio_le (S₁ S₂ M X Y H : ℝ)
    (hS : 0 < S₁) (hH : 0 < H) (hscale : H * X = Y)
    (hlower : M * Y / (4 * 97 ^ 2) ≤ S₁) (hupper : S₂ ≤ 192 * M * X) :
    S₂ / S₁ ≤ (192 * (4 * 97 ^ 2)) / H := by
  apply (div_le_div_iff₀ hS hH).mpr
  have h := mul_le_mul_of_nonneg_right hupper hH.le
  rw [mul_assoc (192 * M) X H, mul_comm X H, hscale] at h
  nlinarith

/-- The normalized row-count error, again with the original constants. -/
theorem row_count_div_moment_le (S₁ M Y : ℝ) (hS : 0 < S₁) (hY : 0 < Y)
    (hlower : M * Y / (4 * 97 ^ 2) ≤ S₁) :
    M / S₁ ≤ (4 * 97 ^ 2) / Y := by
  apply (div_le_div_iff₀ hS hY).mpr
  nlinarith

/-- A field-uniform upper estimate for inert primes, derived entirely from
Sections 3--5. The large weight is fixed before `q` or `N`. -/
theorem inertPrimeSum_upper_of_model (d : ℤ) (N H q : ℕ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b])
    (χ : DirichletCharacter ℂ q)
    (hchar : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q →
      χ (p : ZMod q) = (legendreSym p d : ℂ))
    (hq : 1 ≤ q) (hd : |(d : ℝ)| ≤ q) (hH : 86713344 ≤ H) (hHN : H ≤ N)
    (hlarge : 2 * 97 ^ 2 ≤ (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    let U := (N : ℝ) ^ (4 / 3 : ℝ)
    let K := (4 * 97 ^ 2) / (H : ℝ) ^ (2 / 3 : ℝ)
    inertPrimeSum χ H U ≤
      (13 / 12 : ℝ) * (Real.log N + Real.log q / 2 + Real.log 8) +
        K * (Real.log 4 + 2 * Real.log N / U) := by
  dsimp
  obtain ⟨S₁, S₂, hS, _, hlower, hupper, hcompare⟩ :=
    Biquadratic.exists_determinant_comparison d N H q a b ha hb hlin χ hchar hq hd
      (by omega) hHN hlarge
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hU : 0 < (N : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hHp : 0 < (H : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hH0 _
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hL : 0 ≤ Real.log (N : ℝ) + Real.log q / 2 + Real.log 8 := by positivity
  obtain ⟨_, hscale, _⟩ := WeightedRows.row_scale_identities N H (by omega) hHN
  have hratio := moment_ratio_le S₁ S₂ ((N : ℝ) ^ 4) _ _ H hS hH0 hscale hlower hupper
  have hratio' : S₂ / S₁ ≤ 1 / 12 := hratio.trans (by
    have hw := explicit_weight_choice H hH
    norm_num at hw ⊢
    exact hw)
  have hcount := row_count_div_moment_le S₁ ((N : ℝ) ^ 4) _ hS (mul_pos hHp hU) hlower
  have hc := hcompare ((N : ℝ) ^ (4 / 3 : ℝ)) hU.le
  rw [Real.log_pow] at hc
  have hpre : inertPrimeSum χ H ((N : ℝ) ^ (4 / 3 : ℝ)) ≤
      (1 + S₂ / S₁) * (Real.log N + Real.log q / 2 + Real.log 8) +
        ((N : ℝ) ^ 4 / S₁) * (2 * Real.log N + Real.log 4 * (N : ℝ) ^ (4 / 3 : ℝ)) := by
    apply (le_of_mul_le_mul_right ?_ hS)
    have hid : ((1 + S₂ / S₁) * (Real.log N + Real.log q / 2 + Real.log 8) +
        ((N : ℝ) ^ 4 / S₁) * (2 * Real.log N + Real.log 4 * (N : ℝ) ^ (4 / 3 : ℝ))) * S₁ =
        (S₁ + S₂) * (Real.log N + Real.log q / 2 + Real.log 8) +
          (N : ℝ) ^ 4 * (2 * Real.log N + Real.log 4 * (N : ℝ) ^ (4 / 3 : ℝ)) := by
      field_simp
    rw [hid]
    norm_num only [Nat.cast_ofNat] at hc
    nlinarith
  have hlead := mul_le_mul_of_nonneg_right (show 1 + S₂ / S₁ ≤ (13 / 12 : ℝ) by linarith) hL
  have herr := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ 2 * Real.log N + Real.log 4 * (N : ℝ) ^ (4 / 3 : ℝ) by positivity)
  have heq : (4 * 97 ^ 2 / ((H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ))) *
      (2 * Real.log N + Real.log 4 * (N : ℝ) ^ (4 / 3 : ℝ)) =
      (4 * 97 ^ 2 / (H : ℝ) ^ (2 / 3 : ℝ)) *
        (Real.log 4 + 2 * Real.log N / (N : ℝ) ^ (4 / 3 : ℝ)) := by
    field_simp
    ring
  rw [heq] at herr
  linarith

/-- Exact normalization of the scalar determinant comparison.
All denominator assumptions are stated explicitly. -/
theorem scalar_comparison_normalization (I U u ℓ δ C C_H K : ℝ)
    (hU : 0 < U) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hlower : u - C * ℓ - C * δ * u ^ 2 / ℓ - C_H ≤ I)
    (hupper : I ≤ (13 / 12 : ℝ) * (3 / 4 * u + ℓ / 2 + Real.log 8) +
      K * (Real.log 4 + 3 / 2 * u / U)) :
    1 ≤ (13 / 16 : ℝ) + (C + 13 / 24) * ℓ / u + C * δ * u / ℓ +
      (C_H + (13 / 12) * Real.log 8 + K * Real.log 4) / u + (3 * K / 2) / U := by
  let R := (13 / 16 : ℝ) + (C + 13 / 24) * ℓ / u + C * δ * u / ℓ +
    (C_H + (13 / 12) * Real.log 8 + K * Real.log 4) / u + (3 * K / 2) / U
  have hid : (R - 1) * u =
      ((13 / 12 : ℝ) * (3 / 4 * u + ℓ / 2 + Real.log 8) +
        K * (Real.log 4 + 3 / 2 * u / U)) -
      (u - C * ℓ - C * δ * u ^ 2 / ℓ - C_H) := by
    dsimp [R]
    field_simp
    ring
  have hnonneg : 0 ≤ (R - 1) * u := by rw [hid]; linarith
  change 1 ≤ R
  nlinarith

end Siegel
