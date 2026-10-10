import Mathlib

/-!
# Exact setup and checked pieces of Lemma 3

`interpolationStatement` states the projected-box interpolation claim of the
paper. Its proof is `Siegel.Interpolation.interpolation` in
`Siegel/InterpolationTheorem.lean`.

The lemmas below verify the supporting-hyperplane algebra, the strict distance
decrease in (3.5), and the final finite-sum isolation argument. The convex
construction and the complete interpolation theorem are in the subsequent
geometry and polynomial modules.
-/

namespace Siegel

open scoped BigOperators InnerProductSpace

namespace Interpolation

/-- The source box `E_N = {0, ..., N-1}^4`. -/
abbrev IntegerBox (N : ℕ) := Fin 4 → Fin N

/-- Inclusion of the integer box in complex four-space. -/
def boxPoint {N : ℕ} (n : IntegerBox N) : Fin 4 → ℂ := fun i => (n i : ℕ)

/-- Monomial indices with separate degree bounds `t`. -/
abbrev MonomialRectangle (t : Fin 3 → ℕ) := (j : Fin 3) → Fin (t j + 1)

/-- Evaluation of a polynomial given by its coefficients in the finite
monomial rectangle. This is the coefficient model of the paper's `P_t`. -/
noncomputable def evaluate (t : Fin 3 → ℕ)
    (coeff : MonomialRectangle t → ℂ) (z : Fin 3 → ℂ) : ℂ :=
  ∑ α, coeff α * ∏ j, z j ^ (α j : ℕ)

/-- Evaluation at an arbitrary finite family of points in complex three-space. -/
noncomputable def finiteEvaluationMap {ι : Type*} [Fintype ι]
    (t : Fin 3 → ℕ) (z : ι → Fin 3 → ℂ) :
    (MonomialRectangle t → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun coeff i := evaluate t coeff (z i)
  map_add' x y := by
    ext i
    simp [evaluate, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [evaluate, Finset.mul_sum, mul_assoc]

/-- The finite evaluation map appearing in Lemma 3. -/
noncomputable def evaluationMap
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (N : ℕ) (t : Fin 3 → ℕ) :
    (MonomialRectangle t → ℂ) →ₗ[ℂ] (IntegerBox N → ℂ) where
  toFun coeff n := evaluate t coeff (A (boxPoint n))
  map_add' x y := by
    ext n
    simp [evaluate, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext n
    simp [evaluate, Finset.mul_sum, mul_assoc]

/-- The exact hypotheses and conclusion of Lemma 3, proved in
`InterpolationTheorem.lean`. -/
def interpolationStatement : Prop :=
  ∀ (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ),
    Function.Surjective A →
    LinearMap.ker A = Submodule.span ℂ {c} →
    LinearIndependent ℚ c →
    ∀ (N : ℕ) (t : Fin 3 → ℕ),
      1 ≤ N →
      (∀ j, 3 * (N - 1) ≤ t j) →
      (4 * N - 3) ^ 4 < ∏ j, (t j - 3 * (N - 1) + 1) →
      Function.Surjective (evaluationMap A N t)

/-- The number of available monomials is the dimension count in (3.1). -/
theorem monomialRectangle_card (t : Fin 3 → ℕ) :
    Fintype.card (MonomialRectangle t) = ∏ j, (t j + 1) := by
  simp [MonomialRectangle, Fintype.card_pi]

/-- The finite-dimensional kernel argument producing (3.3): if the number
of prescribed evaluations is smaller than the number of monomials, there
is a nonzero coefficient vector vanishing at every prescribed point. -/
theorem exists_nonzero_vanishing_coefficients {ι : Type*} [Fintype ι]
    (t : Fin 3 → ℕ) (z : ι → Fin 3 → ℂ)
    (hcard : Fintype.card ι < ∏ j, (t j + 1)) :
    ∃ coeff : MonomialRectangle t → ℂ,
      coeff ≠ 0 ∧ ∀ i, evaluate t coeff (z i) = 0 := by
  let L := finiteEvaluationMap t z
  have hnot : ¬Function.Injective L := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdim : (∏ j, (t j + 1)) ≤ Fintype.card ι := by
      simpa only [Module.finrank_pi, monomialRectangle_card] using hle
    exact (not_le_of_gt hcard) hdim
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hnot
  refine ⟨a - b, sub_ne_zero.mpr hne, ?_⟩
  have hzero : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
  intro i
  exact congrFun hzero i

/-- Rational independence makes every nonzero rational normal transverse
to the kernel line, as used on pages 4--5. -/
theorem rational_normal_transverse (c : Fin 4 → ℂ)
    (hc : LinearIndependent ℚ c) (r : Fin 4 → ℚ) (hr : r ≠ 0) :
    (∑ i, (r i : ℂ) * c i) ≠ 0 := by
  intro h
  apply hr
  ext i
  apply (Fintype.linearIndependent_iff.mp hc r) _ i
  simpa only [Rat.smul_def, Rat.cast_def] using h

section Hyperplane

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Correct a point along the kernel direction to put it on `r(x) = k`. -/
def hyperplaneCorrection (r : V →ₗ[K] K) (c : V) (k : K) (x : V) : V :=
  x + ((k - r x) / r c) • c

theorem hyperplaneCorrection_mem (r : V →ₗ[K] K) (c : V) (k : K) (x : V)
    (hr : r c ≠ 0) :
    r (hyperplaneCorrection r c k x) = k := by
  simp only [hyperplaneCorrection, map_add, map_smul, smul_eq_mul]
  field_simp
  ring

theorem hyperplaneCorrection_image (A : V →ₗ[K] W) (r : V →ₗ[K] K)
    (c : V) (k : K) (x : V) (hc : A c = 0) :
    A (hyperplaneCorrection r c k x) = A x := by
  simp [hyperplaneCorrection, hc]

/-- Surjectivity of a projection is retained on a hyperplane transverse
to its kernel direction. -/
theorem hyperplane_preimage_exists (A : V →ₗ[K] W) (r : V →ₗ[K] K)
    (c : V) (k : K) (hA : Function.Surjective A)
    (hc : A c = 0) (hr : r c ≠ 0) (z : W) :
    ∃ x : V, r x = k ∧ A x = z := by
  obtain ⟨x, hx⟩ := hA z
  refine ⟨hyperplaneCorrection r c k x, hyperplaneCorrection_mem r c k x hr, ?_⟩
  rw [hyperplaneCorrection_image A r c k x hc, hx]

/-- Injectivity on a transverse hyperplane, completing the affine-bijection
argument on page 5. -/
theorem hyperplane_preimage_unique (A : V →ₗ[K] W) (r : V →ₗ[K] K)
    (c : V) (k : K) (hker : LinearMap.ker A = Submodule.span K {c})
    (hr : r c ≠ 0) (x y : V) (hx : r x = k) (hy : r y = k)
    (hxy : A x = A y) : x = y := by
  have hmem : x - y ∈ Submodule.span K {c} := by
    rw [← hker]
    change A (x - y) = 0
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have har : a * r c = 0 := by
    have h := congrArg r ha
    simpa [map_sub, hx, hy] using h
  have ha0 : a = 0 := (mul_eq_zero.mp har).resolve_right hr
  apply sub_eq_zero.mp
  simpa [ha0] using ha.symm

/-- Every image point has exactly one preimage on the chosen hyperplane. -/
theorem hyperplane_preimage_existsUnique (A : V →ₗ[K] W) (r : V →ₗ[K] K)
    (c : V) (k : K) (hA : Function.Surjective A)
    (hker : LinearMap.ker A = Submodule.span K {c})
    (hr : r c ≠ 0) (z : W) :
    ∃! x : V, r x = k ∧ A x = z := by
  have hc : A c = 0 := by
    change c ∈ LinearMap.ker A
    rw [hker]
    exact Submodule.mem_span_singleton_self c
  obtain ⟨x, hx, hAx⟩ := hyperplane_preimage_exists A r c k hA hc hr z
  refine ⟨x, ⟨hx, hAx⟩, ?_⟩
  intro y hy
  exact hyperplane_preimage_unique A r c k hker hr y x hy.1 hx (hy.2.trans hAx.symm)

end Hyperplane

section DistanceDecrease

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Algebraic form of the strict decrease in (3.5). -/
theorem norm_sub_smul_sq_lt (h v : E) (η : ℝ) (hη : 0 < η)
    (hstep : η * ‖v‖ ^ 2 < 2 * ⟪h, v⟫_ℝ) :
    ‖h - η • v‖ ^ 2 < ‖h‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hη]
  have hprod := mul_pos hη (sub_pos.mpr hstep)
  nlinarith

/-- Positive inner product supplies a segment parameter strictly between
zero and one giving the decrease required in (3.5). Applies in particular
to `EuclideanSpace ℝ (Fin 4)`, with `v = u - n`. -/
theorem exists_small_step_norm_decrease (h v : E) (hv : 0 < ⟪h, v⟫_ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ‖h - η • v‖ ^ 2 < ‖h‖ ^ 2 := by
  let η : ℝ := min (1 / 2) (⟪h, v⟫_ℝ / (‖v‖ ^ 2 + 1))
  have hden : 0 < ‖v‖ ^ 2 + 1 := by positivity
  have hη : 0 < η := lt_min (by norm_num) (div_pos hv hden)
  have hηhalf : η ≤ 1 / 2 := min_le_left _ _
  have hηbound : η * (‖v‖ ^ 2 + 1) ≤ ⟪h, v⟫_ℝ :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨η, hη, lt_of_le_of_lt hηhalf (by norm_num), ?_⟩
  apply norm_sub_smul_sq_lt h v η hη
  nlinarith

/-- Equation (3.5) with `m' = m+n-u`, `y' = y+n-u`, and `h = m-y`
written without abbreviations. The step lies on the segment from `y'` to
`y` because its parameter is strictly between zero and one. -/
theorem translated_distance_decrease (m y n u : E)
    (hpositive : 0 < ⟪m - y, u - n⟫_ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      ‖(m + n - u) - ((y + n - u) + η • (y - (y + n - u)))‖ ^ 2 <
        ‖m - y‖ ^ 2 := by
  obtain ⟨η, hη, hη1, hdecrease⟩ :=
    exists_small_step_norm_decrease (m - y) (u - n) hpositive
  refine ⟨η, hη, hη1, ?_⟩
  have hdir : y - (y + n - u) = u - n := by abel
  have hvec : (m + n - u) - ((y + n - u) + η • (u - n)) =
      (m - y) - η • (u - n) := by abel
  rw [hdir, hvec]
  exact hdecrease

end DistanceDecrease

/-- The final isolation step of Lemma 3: one surviving nonzero summand
contradicts the putative annihilating relation (3.2). -/
theorem isolated_sum_ne_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v Q R : ι → ℂ) (u : ι) (hu : u ∈ s)
    (hvu : v u ≠ 0) (hQu : Q u = 1) (hRu : R u ≠ 0)
    (hisolate : ∀ n ∈ s, n ≠ u → Q n = 0 ∨ R n = 0) :
    (∑ n ∈ s, v n * Q n * R n) ≠ 0 := by
  have hsum : (∑ n ∈ s, v n * Q n * R n) = v u * Q u * R u := by
    apply Finset.sum_eq_single_of_mem u hu
    intro n hn hnu
    rcases hisolate n hn hnu with h | h <;> simp [h]
  rw [hsum, hQu, mul_one]
  exact mul_ne_zero hvu hRu

end Interpolation

end Siegel
