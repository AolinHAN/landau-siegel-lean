import Mathlib

namespace Siegel
open Finset

theorem character_sum_range_period {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ k ∈ range q, χ (k : ZMod q) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  have he : ∑ k : Fin q, χ (k.val : ZMod q) = ∑ k : ZMod q, χ k := by
    apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
    intro k
    congr 1
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
      apply Fin.ext
      change k.val % (q + 1) = k.val
      exact Nat.mod_eq_of_lt k.isLt
  rw [he]
  exact MulChar.sum_eq_zero_of_ne_one hχ

theorem character_sum_range_add_period {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ range (q + n), χ (k : ZMod q) = ∑ k ∈ range n, χ (k : ZMod q) := by
  rw [sum_range_add, character_sum_range_period χ hχ, zero_add]
  apply sum_congr rfl
  intro k _
  simp

theorem character_sum_range_eq_remainder {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, χ (k : ZMod q) = ∑ k ∈ range (n % q), χ (k : ZMod q) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < q
    · rw [Nat.mod_eq_of_lt hn]
    · have hnq : q ≤ n := by omega
      have heq : n = q + (n - q) := by omega
      calc
        _ = ∑ k ∈ range (n - q), χ (k : ZMod q) := by
          conv_lhs => rw [heq]
          exact character_sum_range_add_period χ hχ _
        _ = ∑ k ∈ range ((n - q) % q), χ (k : ZMod q) := ih _ (by have := NeZero.pos q; omega)
        _ = ∑ k ∈ range (n % q), χ (k : ZMod q) := by
          congr 2
          exact (Nat.sub_modulus_modEq_iff hnq).mpr rfl

theorem norm_character_sum_range_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, χ (k : ZMod q)‖ ≤ q := by
  rw [character_sum_range_eq_remainder χ hχ]
  calc
    _ ≤ ∑ k ∈ range (n % q), ‖χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (n % q), (1 : ℝ) := sum_le_sum fun _ _ => χ.norm_le_one _
    _ = ((n % q : ℕ) : ℝ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt n (NeZero.pos q)).le


theorem norm_character_sum_Icc_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Icc 1 n, χ (k : ZMod q)‖ ≤ q := by
  letI : Fact (1 < q) := ⟨by omega⟩
  have heq : ∑ k ∈ Icc 1 n, χ (k : ZMod q) =
      ∑ k ∈ range (n + 1), χ (k : ZMod q) := by
    have hset : Icc 1 n = Ico 1 (n + 1) := by ext k; simp
    rw [hset, sum_Ico_eq_sub _ (by omega : 1 ≤ n + 1)]
    simp only [sum_range_one, Nat.cast_zero, MulChar.map_zero, sub_zero]
  rw [heq]
  exact norm_character_sum_range_le χ hχ _

end Siegel
