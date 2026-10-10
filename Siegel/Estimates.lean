import Mathlib

/-!
# Verified numerical steps from Sections 2, 5 and 6

All analytic estimates used as inputs below are explicit hypotheses. In
particular this file does not prove the prime bias or the determinant bounds.
-/

namespace Siegel

open scoped BigOperators
open Filter

/-- The rational identity in the proof of Lemma 2. -/
theorem reciprocal_difference (s β : ℝ) (hs : 1 < s) (hβ : β < 1) :
    1 / (s - 1) - 1 / (s - β) = (1 - β) / ((s - 1) * (s - β)) := by
  have h₁ : s - 1 ≠ 0 := ne_of_gt (by linarith)
  have h₂ : s - β ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The following bound is the algebraic step of Lemma 2, not the
logarithmic-derivative estimate (2.4). -/
theorem reciprocal_difference_le (s β : ℝ) (hs : 1 < s) (hβ : β < 1) :
    1 / (s - 1) - 1 / (s - β) ≤ (1 - β) / (s - 1) ^ 2 := by
  rw [reciprocal_difference s β hs hβ]
  apply div_le_div_of_nonneg_left (by linarith) (sq_pos_of_pos (by linarith))
  nlinarith

/-- Specialization to `s = 1 + 1 / log X`, used in (2.1). -/
theorem reciprocal_at_log_scale (L β : ℝ) (hL : 0 < L) (hβ : β < 1) :
    1 / ((1 + 1 / L) - 1) - 1 / ((1 + 1 / L) - β) ≤ (1 - β) * L ^ 2 := by
  have hs : 1 < 1 + 1 / L := by
    have := one_div_pos.mpr hL
    linarith
  calc
    _ ≤ (1 - β) / ((1 + 1 / L) - 1) ^ 2 := reciprocal_difference_le _ _ hs hβ
    _ = _ := by field_simp; ring

/-- The floor error for a single row in (5.6). -/
theorem nat_div_lower (a p : ℕ) (hp : 0 < p) :
    (a : ℝ) / (p : ℝ) - 1 ≤ ((a / p : ℕ) : ℝ) := by
  have hrem : ((a % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt a hp
  have hsplit : (p : ℝ) * ((a / p : ℕ) : ℝ) + ((a % p : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast Nat.div_add_mod a p
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ hp').2
  nlinarith

/-- Sum of the rowwise floor errors: `E_p ≥ S₁ / p - M`. -/
theorem sum_nat_div_lower {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (p : ℕ) (hp : 0 < p) :
    (∑ i ∈ s, (a i : ℝ)) / p - s.card ≤ ∑ i ∈ s, ((a i / p : ℕ) : ℝ) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ s) => nat_div_lower (a i) p hp)
  simpa [Finset.sum_sub_distrib, Finset.sum_div] using h

/-- The weighted summation of the floor error in equation (5.6).
The finite set `primes` can be any set of positive integers; primality is
needed for the preceding norm divisibility argument, not this inequality. -/
theorem weighted_floor_lower {ι : Type*} (rows : Finset ι) (a : ι → ℕ)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, 0 < p) :
    (∑ i ∈ rows, (a i : ℝ)) * (∑ p ∈ primes, Real.log p / p) -
      rows.card * (∑ p ∈ primes, Real.log p) ≤
        ∑ p ∈ primes, (∑ i ∈ rows, ((a i / p : ℕ) : ℝ)) * Real.log p := by
  calc
    _ = ∑ p ∈ primes,
        ((∑ i ∈ rows, (a i : ℝ)) / p - rows.card) * Real.log p := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right (sum_nat_div_lower rows a p (hprimes p hp))
        (Real.log_nonneg (by exact_mod_cast hprimes p hp))

/-- The purely numerical last inequality in the proof of Lemma 6. -/
theorem sum_lower_of_capacity (M Q S : ℝ) (hQ : 0 < Q) (hM : 2 * Q ≤ M)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) :
    M ^ 2 / (4 * Q) ≤ S := by
  have hM0 : 0 ≤ M := by linarith
  have h : M ^ 2 / (4 * Q) ≤ M ^ 2 / (2 * Q) - M / 2 := by
    apply (le_sub_iff_add_le).2
    field_simp
    nlinarith [mul_nonneg hM0 (sub_nonneg.mpr hM)]
  exact h.trans hS

/-- The first term of (6.2) after choosing `H`. -/
theorem leading_term_le (r : ℝ) (hr : r ≤ 1 / 12) :
    (3 / 4 : ℝ) * (1 + r) ≤ 13 / 16 := by linarith

/-- The exact rearrangement from (5.1) and (5.7) to (6.2).
Here `u = log U`, `m = log M`, and `d = log |Norm Δ| / 4`.
The two determinant bounds are explicit inputs, not asserted theorems. -/
theorem comparison_normalization (S₁ S₂ M U ℓ δ C C_H u m d : ℝ)
    (hS : 0 < S₁) (hu : 0 < u) (hℓ : 0 < ℓ)
    (hlower : S₁ * (u - C * ℓ - C * δ * u ^ 2 / ℓ - C_H) - C * M * U ≤ d)
    (hupper : d ≤ M / 2 * m + (S₁ + S₂) * (3 / 4 * u + 1 / 2 * ℓ + Real.log 8)) :
    1 ≤ (3 / 4 : ℝ) * (1 + S₂ / S₁) +
      (C + 1 / 2 * (1 + S₂ / S₁)) * ℓ / u + C * δ * u / ℓ +
      (C_H + (1 + S₂ / S₁) * Real.log 8) / u +
      (C * M * U + 1 / 2 * M * m) / (S₁ * u) := by
  let rhs := (3 / 4 : ℝ) * (1 + S₂ / S₁) +
      (C + 1 / 2 * (1 + S₂ / S₁)) * ℓ / u + C * δ * u / ℓ +
      (C_H + (1 + S₂ / S₁) * Real.log 8) / u +
      (C * M * U + 1 / 2 * M * m) / (S₁ * u)
  have hid : (rhs - 1) * (S₁ * u) =
      (M / 2 * m + (S₁ + S₂) * (3 / 4 * u + 1 / 2 * ℓ + Real.log 8)) -
      (S₁ * (u - C * ℓ - C * δ * u ^ 2 / ℓ - C_H) - C * M * U) := by
    dsimp [rhs]
    field_simp
    ring
  have hnonneg : 0 ≤ (rhs - 1) * (S₁ * u) := by
    rw [hid]
    exact sub_nonneg.mpr (hlower.trans hupper)
  have hden := mul_pos hS hu
  change 1 ≤ rhs
  nlinarith

/-- One explicit integer value large enough for the paper's choice of `H`,
using exactly `c₀ = (4*97²)⁻¹` and `C₀ = 192` from Lemma 6. -/
theorem explicit_weight_choice (H : ℕ) (hH : 86713344 ≤ H) :
    ((192 : ℝ) / (1 / (4 * 97 ^ 2))) / H ≤ 1 / 12 := by
  have hH' : (86713344 : ℝ) ≤ H := by exact_mod_cast hH
  have hpos : (0 : ℝ) < H := by linarith
  apply (div_le_iff₀ hpos).2
  norm_num
  linarith

/-- A finite, quantitative version of the last contradiction. -/
theorem comparison_impossible (r conductorTerm zeroTerm fixedTerm tailTerm : ℝ)
    (hr : r ≤ 1 / 12) (hc : conductorTerm ≤ 1 / 16)
    (he : zeroTerm + fixedTerm + tailTerm < 1 / 8)
    (hcomparison : 1 ≤ (3 / 4 : ℝ) * (1 + r) + conductorTerm +
      zeroTerm + fixedTerm + tailTerm) : False := by
  have := leading_term_le r hr
  linarith

/-- A limit argument using a convergent upper bound for the conductor term.
The raw expression involving `S₂ / S₁` need not converge. Obtaining a
majorant and the hypotheses from Dirichlet characters is a separate task. -/
theorem limit_comparison_impossible
    (r conductorTerm error : ℕ → ℝ) (c : ℝ)
    (hr : ∀ᶠ n in atTop, r n ≤ 1 / 12)
    (hc : Tendsto conductorTerm atTop (nhds c)) (hcBound : c ≤ 1 / 16)
    (he : Tendsto error atTop (nhds 0))
    (hcomparison : ∀ᶠ n in atTop,
      1 ≤ (3 / 4 : ℝ) * (1 + r n) + conductorTerm n + error n) : False := by
  have hbound : ∀ᶠ n in atTop, (1 : ℝ) ≤ 13 / 16 + conductorTerm n + error n := by
    filter_upwards [hr, hcomparison] with n hrn hn
    have := leading_term_le (r n) hrn
    linarith
  have hlimit : Tendsto (fun n => (13 / 16 : ℝ) + conductorTerm n + error n)
      atTop (nhds (13 / 16 + c + 0)) := (tendsto_const_nhds.add hc).add he
  have h := ge_of_tendsto hlimit hbound
  linarith

/-- The form used directly in Section 6: the conductor term is eventually
at most `1/16`; no convergence of `S₂ / S₁` is required. The error is the
sum of the remaining three terms of (6.2). -/
theorem eventual_comparison_impossible
    (r conductorTerm error : ℕ → ℝ)
    (hr : ∀ᶠ n in atTop, r n ≤ 1 / 12)
    (hc : ∀ᶠ n in atTop, conductorTerm n ≤ 1 / 16)
    (he : Tendsto error atTop (nhds 0))
    (hcomparison : ∀ᶠ n in atTop,
      1 ≤ (3 / 4 : ℝ) * (1 + r n) + conductorTerm n + error n) : False := by
  have hbound : ∀ᶠ n in atTop, (1 : ℝ) ≤ 7 / 8 + error n := by
    filter_upwards [hr, hc, hcomparison] with n hrn hcn hn
    have := leading_term_le (r n) hrn
    linarith
  have hlimit : Tendsto (fun n => (7 / 8 : ℝ) + error n)
      atTop (nhds (7 / 8 + 0)) := tendsto_const_nhds.add he
  have h := ge_of_tendsto hlimit hbound
  norm_num at h

end Siegel
