import Mathlib

namespace Siegel

open Metric Function

/-- List the zeros in an open disk with their multiplicities, obtaining both
the exact local orders and the comparison with the closed-disk divisor count. -/
theorem exists_disk_zero_data (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    ∃ (S : Finset ℂ) (m : ℂ → ℕ),
      (∀ w ∈ S, w ∈ ball 0 R ∧ f w = 0 ∧ 0 < m w) ∧ (0 : ℂ) ∉ S ∧
      (∀ z ∈ closedBall 0 R,
        (((if z ∈ S then m z else 0 : ℕ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z) ∧
      (∀ z ∈ ball 0 R,
        meromorphicOrderAt f z = (((if z ∈ S then m z else 0 : ℕ) : ℤ) : WithTop ℤ)) ∧
      ((∑ w ∈ S, m w : ℕ) : ℤ) ≤ ∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z := by
  classical
  let D := MeromorphicOn.divisor f (ball 0 R)
  let E := MeromorphicOn.divisor f (closedBall 0 R)
  have hfopen := hf.mono ball_subset_closedBall
  have hD0 : ∀ z, 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfopen
  have hE0 : ∀ z, 0 ≤ E z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hDE (z : ℂ) (hz : z ∈ ball 0 R) : D z = E z := by
    simp only [D, E, hfopen.meromorphicOn.divisor_apply hz,
      hf.meromorphicOn.divisor_apply (ball_subset_closedBall hz)]
  have hsupp : D.support ⊆ E.support := by
    intro z hz
    have hzb := D.supportWithinDomain hz
    change D z ≠ 0 at hz
    change E z ≠ 0
    rwa [← hDE z hzb]
  have hEfin := E.finiteSupport (isCompact_closedBall 0 R)
  have hDfin : D.support.Finite := hEfin.subset hsupp
  let S : Finset ℂ := hDfin.toFinset
  let m : ℂ → ℕ := fun z => (D z).toNat
  have hmem (z : ℂ) : z ∈ S ↔ D z ≠ 0 := by simp [S, Function.mem_support]
  have hweight (z : ℂ) : ((if z ∈ S then m z else 0 : ℕ) : ℤ) = D z := by
    by_cases hz : z ∈ S
    · simp [hz, m, Int.toNat_of_nonneg (hD0 z)]
    · have hDz : D z = 0 := by simpa only [hmem, not_not] using hz
      simp [hz, hDz]
  have hfzero : meromorphicOrderAt f (0 : ℂ) = 0 :=
    ((hf 0 (mem_closedBall_self hR.le)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr hf0
  have hfinite (z : ℂ) (hz : z ∈ closedBall 0 R) : meromorphicOrderAt f z ≠ ⊤ :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall (0 : ℂ) R).isPreconnected (mem_closedBall_self hR.le) hz (by simp [hfzero])
  have hzeros := hfopen.meromorphicNFOn.zero_set_eq_divisor_support
    (fun z => hfinite z (ball_subset_closedBall z.property))
  have hSdata (w : ℂ) (hw : w ∈ S) : w ∈ ball 0 R ∧ f w = 0 ∧ 0 < m w := by
    have hs : w ∈ D.support := by simpa [S] using hw
    have hwz : w ∈ ball 0 R ∩ f ⁻¹' {0} := hzeros ▸ hs
    refine ⟨hwz.1, hwz.2, ?_⟩
    have hp := lt_of_le_of_ne (hD0 w) (Ne.symm ((hmem w).mp hw))
    dsimp [m]
    omega
  refine ⟨S, m, hSdata, ?_, ?_, ?_, ?_⟩
  · intro h0
    exact hf0 (hSdata 0 h0).2.1
  · intro z hz
    rw [hweight]
    by_cases hzb : z ∈ ball 0 R
    · rw [show D z = (meromorphicOrderAt f z).untop₀ from hfopen.meromorphicOn.divisor_apply hzb,
        WithTop.coe_untop₀_of_ne_top (hfinite z hz)]
    · have hDz : D z = 0 := by simp [D, hzb]
      rw [hDz, WithTop.coe_zero]
      exact (hf z hz).meromorphicOrderAt_nonneg
  · intro z hz
    rw [hweight]
    rw [show D z = (meromorphicOrderAt f z).untop₀ from hfopen.meromorphicOn.divisor_apply hz,
      WithTop.coe_untop₀_of_ne_top (hfinite z (ball_subset_closedBall hz))]
  · have heq : ((∑ w ∈ S, m w : ℕ) : ℤ) = ∑ᶠ z, D z := by
      rw [Nat.cast_sum, finsum_eq_sum_of_support_subset _ (s := S) (by simp [S])]
      apply Finset.sum_congr rfl
      intro z hz
      exact Int.toNat_of_nonneg (hD0 z)
    rw [heq]
    apply finsum_le_finsum' hDfin hEfin
    intro z
    by_cases hz : z ∈ ball 0 R
    · exact (hDE z hz).le
    · have hDz : D z = 0 := by simp [D, hz]
      rw [hDz]
      exact hE0 z

end Siegel
