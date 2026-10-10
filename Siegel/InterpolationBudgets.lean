import Siegel.InterpolationTheorem

/-! Uniform degree budgets and Corollary 4. -/

namespace Siegel.Interpolation

open scoped BigOperators

/-- The degree budgets in Corollary 4. -/
noncomputable def degreeBudget (N H : ℕ) : Fin 3 → ℝ :=
  ![32 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ),
    32 * (H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ),
    32 * (H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)]

theorem degreeBudget_lower (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) (j : Fin 3) :
    32 * (N : ℝ) ≤ degreeBudget N H j := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hH.trans hHN
  have hHpos : (0 : ℝ) < H := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hpow1 : 1 ≤ (H : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow hH1 (by norm_num)
  have hpowN : (N : ℝ) ≤ (N : ℝ) ^ (4 / 3 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have hpow2 : (N : ℝ) ^ (-1 / 3 : ℝ) ≤ (H : ℝ) ^ (-1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hHpos (by exact_mod_cast hHN) (by norm_num)
  have hproduct : (N : ℝ) ≤ (H : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (-1 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_add hNpos]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow2 (Real.rpow_nonneg (by positivity) _)
  fin_cases j <;> dsimp [degreeBudget]
  · nlinarith [mul_le_mul_of_nonneg_right hpow1 (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) (4 / 3))]
  · nlinarith
  · nlinarith

theorem degreeBudget_product (N H : ℕ) (hH : 1 ≤ H) (hN : 1 ≤ N) :
    (∏ j, degreeBudget N H j) = 32 ^ 3 * (N : ℝ) ^ 4 := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hHpow : (H : ℝ) ^ (2 / 3 : ℝ) * (H : ℝ) ^ (-1 / 3 : ℝ) *
      (H : ℝ) ^ (-1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hHpos, ← Real.rpow_add hHpos]
    norm_num
  have hNpow : (N : ℝ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) *
      (N : ℝ) ^ (4 / 3 : ℝ) = (N : ℝ) ^ 4 := by
    rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    norm_num
  rw [Fin.prod_univ_three]
  dsimp [degreeBudget]
  calc
    _ = 32 ^ 3 * ((H : ℝ) ^ (2 / 3 : ℝ) * (H : ℝ) ^ (-1 / 3 : ℝ) *
        (H : ℝ) ^ (-1 / 3 : ℝ)) *
        ((N : ℝ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) := by ring
    _ = _ := by rw [hHpow, hNpow]; ring

/-- Flooring real budgets of the indicated size still meets Lemma 3's
strict dimension inequality. -/
theorem floor_budget_hypotheses (N : ℕ) (hN : 1 ≤ N) (T : Fin 3 → ℝ)
    (hT : ∀ j, 32 * (N : ℝ) ≤ T j)
    (hprod : (∏ j, T j) = 32 ^ 3 * (N : ℝ) ^ 4) :
    (∀ j, 3 * (N - 1) ≤ ⌊T j⌋₊) ∧
      (4 * N - 3) ^ 4 < ∏ j, (⌊T j⌋₊ - 3 * (N - 1) + 1) := by
  have hNj : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hTpos (j) : 0 < T j := lt_of_lt_of_le (by positivity) (hT j)
  have hsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN]; norm_num
  have ht (j) : 3 * (N - 1) ≤ ⌊T j⌋₊ := by
    apply (Nat.le_floor_iff (hTpos j).le).mpr
    push_cast
    rw [hsub]
    linarith [hT j]
  refine ⟨ht, ?_⟩
  have hhalf (j) : T j / 2 ≤ ((⌊T j⌋₊ - 3 * (N - 1) + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (ht j)]
    push_cast
    rw [hsub]
    linarith [Nat.lt_floor_add_one (T j), hT j]
  have hmul := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3)))
    (f := fun j => T j / 2)
    (g := fun j => ((⌊T j⌋₊ - 3 * (N - 1) + 1 : ℕ) : ℝ))
    (fun j _ => (div_pos (hTpos j) (by norm_num)).le) (fun j _ => hhalf j)
  have hprodhalf : (∏ j, T j / 2) = 4096 * (N : ℝ) ^ 4 := by
    rw [Finset.prod_div_distrib, hprod]
    norm_num
    ring
  rw [hprodhalf, ← Nat.cast_prod] at hmul
  have hbound : ((4 * N - 3 : ℕ) : ℝ) < 4 * (N : ℝ) := by
    rw [Nat.cast_sub (by omega : 3 ≤ 4 * N)]
    push_cast
    linarith
  have hpow : (((4 * N - 3 : ℕ) : ℝ)) ^ 4 < (4 * (N : ℝ)) ^ 4 := by
    exact pow_lt_pow_left₀ hbound (by positivity) (by norm_num)
  have hstrict : (((4 * N - 3 : ℕ) : ℝ)) ^ 4 <
      ((∏ j, (⌊T j⌋₊ - 3 * (N - 1) + 1) : ℕ) : ℝ) := by
    nlinarith [pow_pos hNj 4]
  exact_mod_cast hstrict

/-- Corollary 4: the source's three explicit degree budgets give a
surjective evaluation map, uniformly in the projection and in `H`. -/
theorem uniform_budget_interpolation
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ)
    (hA : Function.Surjective A) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hc : LinearIndependent ℚ c) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    Function.Surjective (evaluationMap A N (fun j => ⌊degreeBudget N H j⌋₊)) := by
  have hN := hH.trans hHN
  obtain ⟨ht, hsize⟩ := floor_budget_hypotheses N hN (degreeBudget N H)
    (degreeBudget_lower N H hH hHN) (degreeBudget_product N H hH hN)
  exact rectangular_interpolation A c hA hker hc N _ hN ht hsize

end Siegel.Interpolation
