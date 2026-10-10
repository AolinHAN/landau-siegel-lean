import Mathlib

/-! # Recovering a nonnegative zero sum from radial finite sums

A finite limit of nonnegative radial sums proves summability, rather than
assuming it. This is used to pass from disk zero formulas to global sums.
-/

namespace Siegel

open Filter Topology Metric Function

/-- The part of a function inside the open disk of radius `n+1`. -/
noncomputable def radialCut (a : ℂ → ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  if ‖z‖ < (n : ℝ) + 1 then a z else 0

theorem radialCut_nonneg (a : ℂ → ℝ) (ha : ∀ z, 0 ≤ a z) (n : ℕ) (z : ℂ) :
    0 ≤ radialCut a n z := by
  unfold radialCut
  split_ifs
  · exact ha z
  · exact le_rfl

theorem radialCut_le (a : ℂ → ℝ) (ha : ∀ z, 0 ≤ a z) (n : ℕ) (z : ℂ) :
    radialCut a n z ≤ a z := by
  unfold radialCut
  split_ifs <;> simp_all

/-- Every fixed finite subset eventually lies in the radial disks. -/
theorem eventually_finset_mem_radial_ball (S : Finset ℂ) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ S, ‖z‖ < (n : ℝ) + 1 := by
  rw [Filter.eventually_all_finset]
  intro z hz
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- A finite limit of locally finite, nonnegative radial sums determines the
unconditional sum. In particular, summability is derived from the limit. -/
theorem summable_tsum_eq_of_radial_finsum_tendsto
    (a : ℂ → ℝ) (ha : ∀ z, 0 ≤ a z)
    (hfinite : ∀ n, (support (radialCut a n)).Finite)
    (L : ℝ) (hlimit : Tendsto (fun n => ∑ᶠ z, radialCut a n z) atTop (𝓝 L)) :
    Summable a ∧ (∑' z, a z) = L := by
  classical
  have hcut (n : ℕ) : Summable (radialCut a n) :=
    summable_of_hasFiniteSupport (hfinite n)
  have hbound (S : Finset ℂ) : ∑ z ∈ S, a z ≤ L := by
    apply ge_of_tendsto hlimit
    filter_upwards [eventually_finset_mem_radial_ball S] with n hn
    calc
      ∑ z ∈ S, a z = ∑ z ∈ S, radialCut a n z := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [radialCut, hn z hz]
      _ ≤ ∑' z, radialCut a n z :=
        (hcut n).sum_le_tsum S (fun z hz => radialCut_nonneg a ha n z)
      _ = ∑ᶠ z, radialCut a n z := tsum_eq_finsum (hfinite n)
  have hsum : Summable a := summable_of_sum_le ha hbound
  refine ⟨hsum, le_antisymm (hsum.tsum_le_of_sum_le hbound) ?_⟩
  apply le_of_tendsto' hlimit
  intro n
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) (hfinite n)]
  exact (hcut n).tsum_le_tsum (radialCut_le a ha n) hsum

/-- Open-disk divisors have finite support when the function is meromorphic
on the whole plane. The proof uses compactness of the closed disk. -/
theorem finiteSupport_divisor_ball (f : ℂ → ℂ)
    (hf : MeromorphicOn f Set.univ) (R : ℝ) :
    (support (MeromorphicOn.divisor f (ball 0 R))).Finite := by
  let D := MeromorphicOn.divisor f (closedBall 0 R)
  apply (D.finiteSupport (isCompact_closedBall 0 R)).subset
  intro z hz
  have hzb : z ∈ ball 0 R :=
    (MeromorphicOn.divisor f (ball 0 R)).supportWithinDomain hz
  have hd : MeromorphicOn.divisor f (ball 0 R) z = D z := by
    rw [(hf.mono_set (Set.subset_univ _)).divisor_apply hzb,
      (hf.mono_set (Set.subset_univ _)).divisor_apply (ball_subset_closedBall hzb)]
  change D z ≠ 0
  rwa [← hd]

/-- The global divisor cut down by the disk is the disk divisor. -/
theorem radialCut_divisor_mul (f : ℂ → ℂ)
    (hf : MeromorphicOn f Set.univ) (k : ℂ → ℝ) (n : ℕ) (z : ℂ) :
    radialCut (fun w => (MeromorphicOn.divisor f Set.univ w : ℝ) * k w) n z =
      (MeromorphicOn.divisor f (ball 0 ((n : ℝ) + 1)) z : ℝ) * k z := by
  by_cases hz : ‖z‖ < (n : ℝ) + 1
  · have hzb : z ∈ ball 0 ((n : ℝ) + 1) := by simpa using hz
    simp only [radialCut, hz, if_true, hf.divisor_apply (Set.mem_univ z),
      (hf.mono_set (Set.subset_univ _)).divisor_apply hzb]
  · have hzb : z ∉ ball 0 ((n : ℝ) + 1) := by simpa using hz
    simp [radialCut, hz, hzb]

/-- Global weighted divisor summation from convergent radial sums. This
applies in particular to any entire function and nonnegative zero kernel. -/
theorem summable_divisor_mul_of_radial_limit (f : ℂ → ℂ)
    (hf : MeromorphicOn f Set.univ) (k : ℂ → ℝ)
    (hpos : ∀ z, 0 ≤ (MeromorphicOn.divisor f Set.univ z : ℝ) * k z)
    (L : ℝ)
    (hlimit : Tendsto
      (fun n : ℕ => ∑ᶠ z, (MeromorphicOn.divisor f (ball 0 ((n : ℝ) + 1)) z : ℝ) * k z)
      atTop (𝓝 L)) :
    Summable (fun z => (MeromorphicOn.divisor f Set.univ z : ℝ) * k z) ∧
      (∑' z, (MeromorphicOn.divisor f Set.univ z : ℝ) * k z) = L := by
  refine summable_tsum_eq_of_radial_finsum_tendsto _ hpos ?_ L ?_
  · intro n
    rw [funext (radialCut_divisor_mul f hf k n)]
    apply (finiteSupport_divisor_ball f hf ((n : ℝ) + 1)).subset
    intro z hz
    change MeromorphicOn.divisor f (ball 0 ((n : ℝ) + 1)) z ≠ 0
    intro hzero
    exact hz (by simp [hzero])
  · simpa only [radialCut_divisor_mul f hf k] using hlimit

end Siegel
