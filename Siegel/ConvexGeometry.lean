import Siegel.Interpolation

/-!
# The nearest-point construction in Lemma 3

This file supplies actual existence and supporting inequalities for the
nearest pair used on page 4, and the convex-combination argument (3.4).
-/

namespace Siegel.Interpolation

open Set Metric Topology
open scoped InnerProductSpace

section NearestPair

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A nonempty closed set and a nonempty compact set have a closest pair.
The closed set will be the lattice points where the polynomial is nonzero. -/
theorem exists_closest_pair {S K : Set E} (hS : IsClosed S) (hSn : S.Nonempty)
    (hK : IsCompact K) (hKn : K.Nonempty) :
    ∃ m ∈ S, ∃ y ∈ K,
      ∀ m' ∈ S, ∀ y' ∈ K, ‖m - y‖ ≤ ‖m' - y'‖ := by
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKn
    (continuous_infDist_pt S).continuousOn
  obtain ⟨m, hm, hdist⟩ := hS.exists_infDist_eq_dist hSn y
  refine ⟨m, hm, y, hy, ?_⟩
  intro m' hm' y' hy'
  calc
    ‖m - y‖ = infDist y S := by rw [hdist, dist_eq_norm, norm_sub_rev]
    _ ≤ infDist y' S := hmin hy'
    _ ≤ dist y' m' := infDist_le_dist_of_mem hm'
    _ = ‖m' - y'‖ := by rw [dist_eq_norm, norm_sub_rev]

end NearestPair

section SupportingInequality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A closest point to `m` in a convex set gives the supporting inequality
used immediately before (3.4). -/
theorem closest_point_supporting {K : Set E} (hK : Convex ℝ K) (m y : E)
    (hy : y ∈ K) (hmin : ∀ z ∈ K, ‖m - y‖ ≤ ‖m - z‖) :
    ∀ z ∈ K, ⟪m - y, z - y⟫_ℝ ≤ 0 := by
  intro z hz
  by_contra! hpos
  obtain ⟨η, hη, hη1, hdecrease⟩ := exists_small_step_norm_decrease (m - y) (z - y) hpos
  have hpoint : y + η • (z - y) ∈ K := by
    have hc := hK hy hz (sub_nonneg.mpr hη1.le) hη.le (by ring : 1 - η + η = 1)
    convert hc using 1
    module
  have hnorm := hmin (y + η • (z - y)) hpoint
  have heq : m - (y + η • (z - y)) = (m - y) - η • (z - y) := by abel
  rw [heq] at hnorm
  nlinarith [norm_nonneg (m - y), norm_nonneg ((m - y) - η • (z - y))]

/-- The translated lattice point in (3.6) must be a zero whenever `u` is
on the supporting face and `n` is strictly below it. The minimality is
taken over the actual nonzero locus of an arbitrary function `F`. -/
theorem translated_value_eq_zero {K S : Set E} (hK : Convex ℝ K)
    (F : E → ℂ) (m y n u : E)
    (hy : y ∈ K) (hy' : y + n - u ∈ K)
    (htranslated : m + n - u ∈ S)
    (hmin : ∀ m' ∈ S, F m' ≠ 0 → ∀ z ∈ K, ‖m - y‖ ≤ ‖m' - z‖)
    (hpos : 0 < ⟪m - y, u - n⟫_ℝ) :
    F (m + n - u) = 0 := by
  by_contra hne
  obtain ⟨η, hη, hη1, hdecrease⟩ := translated_distance_decrease m y n u hpos
  have hpoint : (y + n - u) + η • (y - (y + n - u)) ∈ K := by
    have hc := hK hy' hy (sub_nonneg.mpr hη1.le) hη.le (by ring : 1 - η + η = 1)
    convert hc using 1
    module
  have hn := hmin (m + n - u) htranslated hne _ hpoint
  nlinarith [norm_nonneg (m - y),
    norm_nonneg ((m + n - u) - ((y + n - u) + η • (y - (y + n - u))))]

end SupportingInequality

/-- The integer lattice in the Euclidean space used in the geometric proof. -/
noncomputable def latticePoint (m : Fin 4 → ℤ) : EuclideanSpace ℝ (Fin 4) :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm (fun i => (m i : ℝ))

/-- Every subset of the integer lattice is closed. This is what permits
minimizing over the nonzero values of the auxiliary polynomial. -/
theorem isClosed_lattice_image (s : Set (Fin 4 → ℤ)) :
    IsClosed (latticePoint '' s) := by
  have hcast : IsClosedEmbedding (fun m : Fin 4 → ℤ => fun i => (m i : ℝ)) :=
    IsClosedEmbedding.piMap (fun _ => Real.isClosedEmbedding_intCast)
  have hmap : IsClosedEmbedding latticePoint :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.toHomeomorph.isClosedEmbedding.comp hcast
  exact hmap.isClosedMap s (isClosed_discrete s)

/-- The nearest lattice point where `F` is nonzero exists, and has a
nearest point in `K`. This discharges the minimum-existence step on page 4. -/
theorem exists_closest_nonzero_lattice_point
    (F : (Fin 4 → ℤ) → ℂ) (hF : ∃ m, F m ≠ 0)
    {K : Set (EuclideanSpace ℝ (Fin 4))} (hK : IsCompact K) (hKn : K.Nonempty) :
    ∃ m : Fin 4 → ℤ, F m ≠ 0 ∧ ∃ y ∈ K,
      ∀ m', F m' ≠ 0 → ∀ y' ∈ K,
        ‖latticePoint m - y‖ ≤ ‖latticePoint m' - y'‖ := by
  let S := latticePoint '' {m | F m ≠ 0}
  have hSn : S.Nonempty := by
    obtain ⟨m, hm⟩ := hF
    exact ⟨latticePoint m, m, hm, rfl⟩
  obtain ⟨x, ⟨m, hm, rfl⟩, y, hy, hmin⟩ :=
    exists_closest_pair (isClosed_lattice_image {m | F m ≠ 0}) hSn hK hKn
  refine ⟨m, hm, y, hy, ?_⟩
  intro m' hm' y' hy'
  exact hmin (latticePoint m') ⟨m', hm', rfl⟩ y' hy'

section ConvexCombination

variable {E : Type*}

/-- The large coefficient in a convex combination of at most four points. -/
theorem exists_quarter_le_weight (t : Finset E) (w : E → ℝ)
    (hcard : t.card ≤ 4) (hsum : ∑ z ∈ t, w z = 1) :
    ∃ u ∈ t, (1 / 4 : ℝ) ≤ w u := by
  have ht : t.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    norm_num at hsum
  by_contra! hn
  have hh := Finset.sum_lt_sum_of_nonempty ht hn
  have hc : (t.card : ℝ) ≤ 4 := by exact_mod_cast hcard
  simp only [hsum, Finset.sum_const, nsmul_eq_mul] at hh
  linarith

variable [AddCommGroup E] [Module ℝ E]

/-- The exact convex-combination calculation yielding (3.4): for one of
at most four vertices, `4*x - u` lies in three times the convex hull. -/
theorem exists_vertex_sub_mem_three_hull {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (z : ι → E) (w : ι → ℝ) (x : E)
    (hcard : t.card ≤ 4) (hw : ∀ i ∈ t, 0 ≤ w i)
    (hsum : ∑ i ∈ t, w i = 1) (hx : ∑ i ∈ t, w i • z i = x) :
    ∃ u ∈ t, ∃ v ∈ convexHull ℝ (z '' (t : Set ι)),
      (3 : ℝ) • v = (4 : ℝ) • x - z u := by
  obtain ⟨u, hu, hwu⟩ := exists_quarter_le_weight t w hcard hsum
  let w' : ι → ℝ := fun i => (4 * w i - if i = u then 1 else 0) / 3
  have hw' : ∀ z ∈ t, 0 ≤ w' z := by
    intro z hz
    by_cases hzu : z = u
    · subst z
      dsimp [w']
      simp only [ite_true]
      linarith
    · simp only [w', if_neg hzu, sub_zero]
      have := hw z hz
      positivity
  have hsum' : ∑ z ∈ t, w' z = 1 := by
    dsimp [w']
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    norm_num [hu]
  let v : E := ∑ i ∈ t, w' i • z i
  have hv : v ∈ convexHull ℝ (z '' (t : Set ι)) := by
    apply (convex_convexHull ℝ _).sum_mem hw' hsum'
    intro i hi
    exact subset_convexHull ℝ _ ⟨i, hi, rfl⟩
  refine ⟨u, hu, v, hv, ?_⟩
  calc
    (3 : ℝ) • v = ∑ i ∈ t, (4 * w i - if i = u then 1 else 0) • z i := by
      simp only [v, Finset.smul_sum, smul_smul, w']
      apply Finset.sum_congr rfl
      intro z hz
      congr 1
      ring
    _ = (4 : ℝ) • (∑ i ∈ t, w i • z i) - z u := by
      simp [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hu]
    _ = _ := by rw [hx]

end ConvexCombination

/-- An affinely independent family in a proper affine hyperplane of real
four-space has at most four members. -/
theorem affineIndependent_card_le_four {ι : Type*} [Fintype ι]
    (z : ι → EuclideanSpace ℝ (Fin 4))
    (l : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℝ) (hl : l ≠ 0) (k : ℝ)
    (hz : ∀ i, l (z i) = k) (hind : AffineIndependent ℝ z) :
    Fintype.card ι ≤ 4 := by
  have hspan : vectorSpan ℝ (Set.range z) ≤ LinearMap.ker l := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    change l (z i - z j) = 0
    rw [map_sub, hz, hz, sub_self]
  have hker : LinearMap.ker l ≠ ⊤ := by
    intro h
    apply hl
    ext x
    have hx : x ∈ LinearMap.ker l := by rw [h]; trivial
    exact hx
  have hrank := Submodule.finrank_lt hker
  have hle := Submodule.finrank_mono hspan
  have hcard := hind.card_le_finrank_succ
  simp only [finrank_euclideanSpace_fin] at hrank
  omega

/-- A positive convex combination which maximizes a linear functional uses
only points on the supporting hyperplane. -/
theorem positive_combination_on_supporting_hyperplane {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (z : ι → E) (w : ι → ℝ) (x : E)
    (l : E →ₗ[ℝ] ℝ) (hw : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) (hx : ∑ i, w i • z i = x)
    (hsupport : ∀ i, l (z i) ≤ l x) : ∀ i, l (z i) = l x := by
  have hzero : ∑ i, w i * (l x - l (z i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    have hmap := congrArg l hx
    simpa only [map_sum, map_smul, smul_eq_mul] using sub_eq_zero.mpr hmap.symm
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * (l x - l (z i)) := by
    intro i hi
    exact mul_nonneg (hw i).le (sub_nonneg.mpr (hsupport i))
  have hpoint := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
  intro i
  have hprod := hpoint i (Finset.mem_univ i)
  have hdiff := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (hw i))
  linarith

/-- The supporting-face selection step (3.4), assembled from Carathéodory
and the large-coefficient argument. -/
theorem supporting_vertex_sub_mem_three_hull
    (S : Set (EuclideanSpace ℝ (Fin 4))) (x : EuclideanSpace ℝ (Fin 4))
    (hx : x ∈ convexHull ℝ S)
    (l : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℝ) (hl : l ≠ 0)
    (hsupport : ∀ z ∈ S, l z ≤ l x) :
    ∃ u ∈ S, l u = l x ∧ ∃ v ∈ convexHull ℝ S,
      (3 : ℝ) • v = (4 : ℝ) • x - u := by
  classical
  obtain ⟨ι, hι, z, w, hzS, hind, hw, hsum, hcombo⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI := hι
  have hface := positive_combination_on_supporting_hyperplane z w x l hw hsum hcombo
    (fun i => hsupport (z i) (hzS ⟨i, rfl⟩))
  have hcard := affineIndependent_card_le_four z l hl (l x) hface hind
  obtain ⟨i, hi, v, hv, hcalc⟩ := exists_vertex_sub_mem_three_hull
    Finset.univ z w x (by simpa using hcard) (fun i _ => (hw i).le) hsum hcombo
  refine ⟨z i, hzS ⟨i, rfl⟩, hface i, v, ?_, hcalc⟩
  exact convexHull_mono (by simpa using hzS) hv

end Siegel.Interpolation
