import Siegel.CompletedLogDerivative

namespace Siegel

/-- The entire completed L-function with exactly the conductor and parity
normalization displayed before equation (2.3). -/
noncomputable def paperCompletedDirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ ((dirichletParity χ : ℂ) / 2) * completedDirichlet χ s

/-- The change of completion normalization is a nonzero constant. -/
theorem paper_completion_factor_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (q : ℂ) ^ ((dirichletParity χ : ℂ) / 2) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))

/-- The paper's completion is entire for a nonprincipal character. -/
theorem differentiable_paperCompletedDirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Differentiable ℂ (paperCompletedDirichlet χ) :=
  (differentiable_completedDirichlet χ hχ).const_mul _

/-- The paper's displayed gamma-times-L expression on the positive half-plane. -/
theorem paperCompletedDirichlet_eq_formula {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    paperCompletedDirichlet χ s =
      ((q : ℂ) / (Real.pi : ℂ)) ^ ((s + (dirichletParity χ : ℂ)) / 2) *
        Complex.Gamma ((s + (dirichletParity χ : ℂ)) / 2) * χ.LFunction s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hdiv (t : ℂ) : ((q : ℂ) / (Real.pi : ℂ)) ^ t =
      (q : ℂ) ^ t * (Real.pi : ℂ) ^ (-t) := by
    have h := Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg q)
      (inv_nonneg.mpr Real.pi_pos.le) t
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg] at h
    simpa only [Complex.ofReal_natCast, div_eq_mul_inv, Complex.cpow_neg] using h
  have hqpow : (q : ℂ) ^ ((dirichletParity χ : ℂ) / 2) * (q : ℂ) ^ (s / 2) =
      (q : ℂ) ^ ((s + (dirichletParity χ : ℂ)) / 2) := by
    rw [← Complex.cpow_add _ _ hq,
      show (dirichletParity χ : ℂ) / 2 + s / 2 = (s + (dirichletParity χ : ℂ)) / 2 by ring]
  rw [paperCompletedDirichlet, completedDirichlet_eq_product χ hs,
    gammaFactor_eq_parity, Complex.Gammaℝ_def, hdiv]
  rw [show -(s + (dirichletParity χ : ℂ)) / 2 =
    -((s + (dirichletParity χ : ℂ)) / 2) by ring]
  calc
    _ = ((q : ℂ) ^ ((dirichletParity χ : ℂ) / 2) * (q : ℂ) ^ (s / 2)) *
        (Real.pi : ℂ) ^ (-((s + (dirichletParity χ : ℂ)) / 2)) *
        Complex.Gamma ((s + (dirichletParity χ : ℂ)) / 2) * χ.LFunction s := by ring
    _ = _ := by rw [hqpow]

/-- The displayed normalization gives the same logarithmic derivative. -/
theorem logDeriv_paperCompletedDirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    logDeriv (paperCompletedDirichlet χ) s = logDeriv (completedDirichlet χ) s :=
  logDeriv_const_mul s _ (paper_completion_factor_ne_zero χ)

/-- The displayed normalization gives exactly the same zero multiplicities. -/
theorem divisor_paperCompletedDirichlet {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    MeromorphicOn.divisor (paperCompletedDirichlet χ) Set.univ s =
      MeromorphicOn.divisor (completedDirichlet χ) Set.univ s := by
  have hp : AnalyticOnNhd ℂ (paperCompletedDirichlet χ) Set.univ :=
    fun z _ => (differentiable_paperCompletedDirichlet χ hχ).analyticAt z
  have hc : AnalyticOnNhd ℂ (completedDirichlet χ) Set.univ :=
    fun z _ => (differentiable_completedDirichlet χ hχ).analyticAt z
  rw [hp.meromorphicOn.divisor_apply (Set.mem_univ s),
    hc.meromorphicOn.divisor_apply (Set.mem_univ s)]
  congr 1
  exact meromorphicOrderAt_mul_of_ne_zero (by fun_prop)
    (paper_completion_factor_ne_zero χ)

end Siegel
