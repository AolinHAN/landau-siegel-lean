import Mathlib

/-! Finite greedy selection with a priority bound on every spanning relation. -/

namespace Siegel.WeightedRows

open Submodule Set

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ι]

/-- A finite family has an independent spanning subfamily such that each
input vector is spanned by selected vectors of no larger weight. This is
the precise greedy-selection property used in Lemma 7. -/
theorem exists_weighted_basis (s : Finset ι) (w : ι → ℕ) (v : ι → V) :
    ∃ P : Finset ι, P ⊆ s ∧ LinearIndepOn K v (P : Set ι) ∧
      span K (v '' (P : Set ι)) = span K (v '' (s : Set ι)) ∧
      ∀ a ∈ s, v a ∈ span K (v '' {i | i ∈ P ∧ w i ≤ w a}) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      exact ⟨∅, by simp, by simp, rfl, by simp⟩
    obtain ⟨a, ha, hmax⟩ := s.exists_max_image w (Finset.nonempty_iff_ne_empty.mpr hs)
    obtain ⟨P, hP, hlin, hspan, hpriority⟩ := ih (s.erase a) (Finset.erase_ssubset ha)
    have hPs : P ⊆ s := fun i hi => Finset.mem_of_mem_erase (hP hi)
    have hane : a ∉ P := fun hi => (Finset.mem_erase.mp (hP hi)).1 rfl
    have hPweight : {i | i ∈ P ∧ w i ≤ w a} = (P : Set ι) := by
      ext i
      exact ⟨fun h => h.1, fun hi => ⟨hi, hmax i (hPs hi)⟩⟩
    have hspan_s : span K (v '' (s : Set ι)) = span K (insert (v a) (v '' (P : Set ι))) := by
      have heq : (s : Set ι) = insert a ((s.erase a : Finset ι) : Set ι) := by
        rw [← Finset.coe_insert, Finset.insert_erase ha]
      rw [heq, Set.image_insert_eq, span_insert, span_insert, hspan]
    by_cases hmem : v a ∈ span K (v '' (P : Set ι))
    · refine ⟨P, hPs, hlin, ?_, ?_⟩
      · rw [hspan_s, span_insert_eq_span hmem]
      · intro b hb
        by_cases hba : b = a
        · subst b
          rwa [hPweight]
        · exact hpriority b (Finset.mem_erase.mpr ⟨hba, hb⟩)
    · refine ⟨insert a P, ?_, ?_, ?_, ?_⟩
      · exact Finset.insert_subset ha hPs
      · rw [Finset.coe_insert, linearIndepOn_insert hane]
        exact ⟨hlin, hmem⟩
      · rw [Finset.coe_insert, Set.image_insert_eq, hspan_s]
      · intro b hb
        by_cases hba : b = a
        · subst b
          exact subset_span ⟨a, ⟨Finset.mem_insert_self _ _, le_rfl⟩, rfl⟩
        · apply span_mono (Set.image_mono ?_) (hpriority b (Finset.mem_erase.mpr ⟨hba, hb⟩))
          intro i hi
          exact ⟨Finset.mem_insert_of_mem hi.1, hi.2⟩

/-- In particular, every row of strictly smaller weight is a combination
of selected rows whose weights are strictly smaller than the current row. -/
theorem weighted_basis_earlier_span (s : Finset ι) (w : ι → ℕ) (v : ι → V) :
    ∃ P : Finset ι, P ⊆ s ∧ LinearIndepOn K v (P : Set ι) ∧
      span K (v '' (P : Set ι)) = span K (v '' (s : Set ι)) ∧
      ∀ a ∈ s, ∀ b, w a < w b → v a ∈ span K (v '' {i | i ∈ P ∧ w i < w b}) := by
  obtain ⟨P, hP, hlin, hspan, hpriority⟩ := exists_weighted_basis (K := K) s w v
  refine ⟨P, hP, hlin, hspan, ?_⟩
  intro a ha b hab
  apply span_mono (Set.image_mono ?_) (hpriority a ha)
  intro i hi
  exact ⟨hi.1, hi.2.trans_lt hab⟩

end Siegel.WeightedRows
