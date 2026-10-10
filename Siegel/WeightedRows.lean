import Mathlib
import Siegel.Algebra

/-!
# Counting weighted row indices

This file proves the finite-set counting step of Lemma 6. In particular the
lower bound on the sum of first coordinates is deduced from the cardinality
of the fibers, rather than taken as a hypothesis.
-/

namespace Siegel
namespace WeightedRows

open scoped BigOperators

private theorem threshold_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, ((k : ℝ) - j)) = (k : ℝ) * (k + 1) / 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have heq (j : ℕ) : ((k + 1 : ℕ) : ℝ) - j = ((k : ℝ) - j) + 1 := by
        push_cast
        ring
      simp_rw [heq]
      rw [Finset.sum_range_succ, Finset.sum_add_distrib, ih]
      simp
      ring

/-- If every fiber of an integer-valued function has at most `Q` elements,
then the deficit below any threshold `k` has the stated upper bound. -/
theorem threshold_deficit_bound {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (a : ι → ℕ) (Q k : ℕ)
    (hcapacity : ∀ j, (P.filter fun x => a x = j).card ≤ Q) :
    (k : ℝ) * P.card - ∑ x ∈ P, (a x : ℝ) ≤
      (Q : ℝ) * k * (k + 1) / 2 := by
  have hpoint (x : ι) :
      (k : ℝ) - a x ≤ ∑ j ∈ Finset.range k,
        if a x = j then (k : ℝ) - j else 0 := by
    by_cases hx : a x < k
    · rw [Finset.sum_eq_single (a x)]
      · simp
      · intro j hj hne
        simp [Ne.symm hne]
      · simp [Finset.mem_range, hx]
    · have hk : (k : ℝ) ≤ a x := by exact_mod_cast Nat.le_of_not_gt hx
      have hz : (∑ j ∈ Finset.range k,
          if a x = j then (k : ℝ) - j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hne : a x ≠ j := by
          intro he
          subst j
          exact hx (Finset.mem_range.mp hj)
        simp [hne]
      rw [hz]
      linarith
  calc
    _ = ∑ x ∈ P, ((k : ℝ) - a x) := by
      simp [Finset.sum_sub_distrib]
      ring
    _ ≤ ∑ x ∈ P, ∑ j ∈ Finset.range k,
        if a x = j then (k : ℝ) - j else 0 :=
      Finset.sum_le_sum fun x _ => hpoint x
    _ = ∑ j ∈ Finset.range k,
        ((k : ℝ) - j) * (P.filter fun x => a x = j).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp [mul_comm]
      ring
    _ ≤ ∑ j ∈ Finset.range k, ((k : ℝ) - j) * Q := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left (by exact_mod_cast hcapacity j)
      have : (j : ℝ) < k := by exact_mod_cast Finset.mem_range.mp hj
      linarith
    _ = (Q : ℝ) * k * (k + 1) / 2 := by
      rw [← Finset.sum_mul, threshold_sum]
      ring

/-- The precise lower bound in Lemma 6 from the fiber-capacity assumption.
No ordering or pre-existing bound on the sum is assumed. -/
theorem first_moment_lower_of_fiber_capacity {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (a : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (hcapacity : ∀ j, (P.filter fun x => a x = j).card ≤ Q) :
    (P.card : ℝ) ^ 2 / (2 * Q) - P.card / 2 ≤ ∑ x ∈ P, (a x : ℝ) := by
  let k := P.card / Q
  let r := P.card % Q
  have hsplit : (P.card : ℝ) = (Q : ℝ) * k + r := by
    exact_mod_cast (Nat.div_add_mod P.card Q).symm
  have hr : (r : ℝ) < Q := by exact_mod_cast Nat.mod_lt P.card hQ
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hb := threshold_deficit_bound P a Q k hcapacity
  have hbound : (k : ℝ) * P.card - (Q : ℝ) * k * (k + 1) / 2 ≤
      ∑ x ∈ P, (a x : ℝ) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ 2 * Q)
  have hid : (P.card : ℝ) ^ 2 - (Q : ℝ) * P.card -
      2 * Q * ((k : ℝ) * P.card - (Q : ℝ) * k * (k + 1) / 2) =
      (r : ℝ) * (r - Q) := by
    rw [hsplit]
    ring
  have hrem : (r : ℝ) * (r - Q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 (by linarith)
  have hpoly : (P.card : ℝ) ^ 2 ≤
      2 * Q * (∑ x ∈ P, (a x : ℝ)) + Q * P.card := by linarith
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Q)).2
  nlinarith

/-- A fixed first coordinate leaves at most `(B+1)^2` possibilities when the
second and third coordinates are bounded by `B`. -/
theorem first_coordinate_fiber_card (P : Finset (Fin 3 → ℕ)) (B j : ℕ)
    (hB : ∀ α ∈ P, α 1 ≤ B ∧ α 2 ≤ B) :
    (P.filter fun α => α 0 = j).card ≤ (B + 1) ^ 2 := by
  let target := Finset.range (B + 1) ×ˢ Finset.range (B + 1)
  have hmap : Set.MapsTo (fun α : Fin 3 → ℕ => (α 1, α 2))
      (P.filter fun α => α 0 = j) target := by
    intro α hα
    have h := hB α (Finset.mem_filter.mp hα).1
    simp only [target, Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    omega
  have hinj : Set.InjOn (fun α : Fin 3 → ℕ => (α 1, α 2))
      (P.filter fun α => α 0 = j) := by
    intro α hα β hβ he
    have hα0 := (Finset.mem_filter.mp hα).2
    have hβ0 := (Finset.mem_filter.mp hβ).2
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    ext i
    fin_cases i <;> simp_all
  simpa [target, pow_two] using Finset.card_le_card_of_injOn _ hmap hinj

/-- The first inequality for `S₁` on page 6, with a natural coordinate cap. -/
theorem first_coordinate_sum_lower (P : Finset (Fin 3 → ℕ)) (B : ℕ)
    (hB : ∀ α ∈ P, α 1 ≤ B ∧ α 2 ≤ B) :
    (P.card : ℝ) ^ 2 / (2 * (B + 1) ^ 2) - P.card / 2 ≤
      ∑ α ∈ P, (α 0 : ℝ) := by
  have h := first_moment_lower_of_fiber_capacity P (fun α => α 0) ((B + 1) ^ 2)
    (by positivity) (first_coordinate_fiber_card P B · hB)
  exact_mod_cast h

/-- The companion upper bound `S₂ ≤ 2 M B` in Lemma 6. -/
theorem other_coordinates_sum_upper (P : Finset (Fin 3 → ℕ)) (B : ℝ)
    (hB : ∀ α ∈ P, (α 1 : ℝ) ≤ B ∧ (α 2 : ℝ) ≤ B) :
    (∑ α ∈ P, ((α 1 : ℝ) + α 2)) ≤ 2 * P.card * B := by
  calc
    _ ≤ ∑ _α ∈ P, (2 * B) := by
      apply Finset.sum_le_sum
      intro α hα
      have h := hB α hα
      linarith
    _ = _ := by simp; ring

end WeightedRows
end Siegel
