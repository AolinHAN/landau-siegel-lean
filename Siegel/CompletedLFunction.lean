import Siegel.Statement
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Meromorphic.Order

namespace Siegel

/-- The entire completion with conductor normalization.  Multiplication by
`q^(epsilon/2)` gives the paper's normalization and does not change its
logarithmic derivative. -/
noncomputable def completedDirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * χ.completedLFunction s

/-- Nonprincipal completed Dirichlet functions are entire. -/
theorem differentiable_completedDirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Differentiable ℂ (completedDirichlet χ) := by
  exact ((differentiable_id.div_const (2 : ℂ)).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))).mul
    (DirichletCharacter.differentiable_completedLFunction hχ)

/-- The gamma factor has no zeros on the positive half-plane. -/
theorem gammaFactor_ne_zero_of_re_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [ho.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simpa using (show 0 < s.re + 1 by linarith)

/-- Nonvanishing of the completed function to the right of the critical strip. -/
theorem completedDirichlet_ne_zero_of_one_le_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    completedDirichlet χ s ≠ 0 := by
  apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
  have hL := χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hs
  rw [χ.LFunction_eq_completed_div_gammaFactor s (Or.inl (by
    intro h; norm_num [h] at hs))] at hL
  exact (div_ne_zero_iff.mp hL).1

/-- A fixed nonzero value used for Jensen's formula. -/
theorem completedDirichlet_two_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : completedDirichlet χ 2 ≠ 0 :=
  completedDirichlet_ne_zero_of_one_le_re χ hχ (by norm_num)

/-- The conductor normalization turns the primitive functional equation into
reflection about the critical line. -/
theorem completedDirichlet_reflection {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (s : ℂ) : completedDirichlet χ (1 - s) = χ.rootNumber * completedDirichlet χ s := by
  unfold completedDirichlet
  rw [hp.completedLFunction_one_sub, hquad.inv]
  calc
    (q : ℂ) ^ ((1 - s) / 2) *
        ((q : ℂ) ^ (s - 1 / 2) * χ.rootNumber * χ.completedLFunction s) =
      ((q : ℂ) ^ ((1 - s) / 2) * (q : ℂ) ^ (s - 1 / 2)) *
        χ.rootNumber * χ.completedLFunction s := by ring
    _ = (q : ℂ) ^ (s / 2) * χ.rootNumber * χ.completedLFunction s := by
      rw [← Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (NeZero.ne q))]
      congr 2
      ring
    _ = χ.rootNumber * ((q : ℂ) ^ (s / 2) * χ.completedLFunction s) := by ring

/-- The constant in the primitive functional equation is nonzero. -/
theorem rootNumber_ne_zero_of_quadratic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) : χ.rootNumber ≠ 0 := by
  intro hzero
  have h := completedDirichlet_reflection χ hp hquad (-1)
  norm_num [hzero] at h
  exact completedDirichlet_two_ne_zero χ hχ h

/-- The logarithmic derivative changes sign under reflection. -/
theorem logDeriv_completedDirichlet_reflection {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) (s : ℂ) :
    logDeriv (completedDirichlet χ) (1 - s) = -logDeriv (completedDirichlet χ) s := by
  have heq : completedDirichlet χ ∘ (fun z : ℂ => 1 - z) =
      (fun z => χ.rootNumber * completedDirichlet χ z) := by
    funext z
    exact completedDirichlet_reflection χ hp hquad z
  have hd := logDeriv_comp ((differentiable_completedDirichlet χ hχ) (1 - s))
    (show DifferentiableAt ℂ (fun z : ℂ => 1 - z) s by fun_prop)
  rw [heq, logDeriv_const_mul s χ.rootNumber
    (rootNumber_ne_zero_of_quadratic χ hp hχ hquad)] at hd
  have hder : deriv (fun z : ℂ => 1 - z) s = -1 := by simpa using
    ((hasDerivAt_id s).const_sub (1 : ℂ)).deriv
  rw [hder, mul_neg_one] at hd
  simpa using (congrArg Neg.neg hd).symm

/-- Completed zeros lie in the critical strip; in fact both boundary lines
are zero-free for a nonprincipal primitive real character. -/
theorem completedDirichlet_zero_re_mem_Ioo {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) {z : ℂ} (hz : completedDirichlet χ z = 0) :
    z.re ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · by_contra! hre
    have hn := completedDirichlet_ne_zero_of_one_le_re χ hχ
      (s := 1 - z) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    apply hn
    rw [completedDirichlet_reflection χ hp hquad, hz, mul_zero]
  · by_contra! hre
    exact completedDirichlet_ne_zero_of_one_le_re χ hχ hre hz

/-- Closed-strip version convenient in estimates for nonnegative zero terms. -/
theorem completedDirichlet_zero_re_mem_Icc {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hp : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hquad : χ.IsQuadratic) {z : ℂ} (hz : completedDirichlet χ z = 0) :
    z.re ∈ Set.Icc (0 : ℝ) 1 :=
  Set.Ioo_subset_Icc_self (completedDirichlet_zero_re_mem_Ioo χ hp hχ hquad hz)

end Siegel
