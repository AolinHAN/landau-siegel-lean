import Mathlib

/-! Elementary independence of the four biquadratic generators. -/

namespace Siegel

/-- A square root of two has no nontrivial rational linear relation with one. -/
theorem sqrt_two_rational_relation (b : ℂ) (hb : b ^ 2 = 2)
    (x y : ℚ) (h : (x : ℂ) + (y : ℂ) * b = 0) : x = 0 ∧ y = 0 := by
  have htwo : ¬ IsSquare (2 : ℚ) := by norm_num
  by_cases hy : y = 0
  · constructor
    · have hx : (x : ℂ) = 0 := by simpa [hy] using h
      exact_mod_cast hx
    · exact hy
  · have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    have heq : b = ((-x / y : ℚ) : ℂ) := by
      push_cast
      apply (eq_div_iff hyC).mpr
      linear_combination h
    have hs : (-x / y : ℚ) ^ 2 = 2 := by
      have hc : (((-x / y : ℚ) : ℂ)) ^ 2 = 2 := heq ▸ hb
      exact_mod_cast hc
    exact (htwo ⟨-x / y, by nlinarith [hs]⟩).elim

/-- A rational square in the quadratic span of `1, sqrt 2` is either a
rational square or twice one. -/
theorem radical_not_in_sqrt_two_span (d : ℚ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hd : ¬ IsSquare d) (h2d : ¬ IsSquare (2 * d)) (x y : ℚ) :
    a ≠ (x : ℂ) + (y : ℂ) * b := by
  intro heq
  have hrel : ((x ^ 2 + 2 * y ^ 2 - d : ℚ) : ℂ) +
      ((2 * x * y : ℚ) : ℂ) * b = 0 := by
    push_cast
    rw [heq] at ha
    linear_combination ha - (y : ℂ) ^ 2 * hb
  obtain ⟨hconst, hcross⟩ := sqrt_two_rational_relation b hb _ _ hrel
  have hxy : x = 0 ∨ y = 0 := by
    rcases mul_eq_zero.mp hcross with h | h
    · left; nlinarith
    · exact Or.inr h
  rcases hxy with hx | hy
  · apply h2d
    refine ⟨2 * y, ?_⟩
    nlinarith [hconst]
  · apply hd
    refine ⟨x, ?_⟩
    nlinarith [hconst]

/-- The four generators of a biquadratic extension are rationally independent
when neither `d` nor `2d` is a rational square. -/
theorem biquadratic_generators_linearIndependent (d : ℚ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hd : ¬ IsSquare d) (h2d : ¬ IsSquare (2 * d)) :
    LinearIndependent ℚ ![1, a, b, a * b] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hrel : (c 0 : ℂ) + (c 1 : ℂ) * a + (c 2 : ℂ) * b +
      (c 3 : ℂ) * (a * b) = 0 := by
    simpa [Fin.sum_univ_succ, smul_eq_mul, add_assoc] using hc
  have hcoeff : c 1 = 0 ∧ c 3 = 0 := by
    by_contra hne
    let t : ℚ := (c 1) ^ 2 - 2 * (c 3) ^ 2
    have ht : t ≠ 0 := by
      intro ht
      by_cases h3 : c 3 = 0
      · apply hne
        constructor
        · dsimp [t] at ht
          nlinarith
        · exact h3
      · have htwo : ¬ IsSquare (2 : ℚ) := by norm_num
        apply htwo
        refine ⟨c 1 / c 3, ?_⟩
        dsimp [t] at ht
        field_simp
        nlinarith
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    let x : ℚ := -(c 0 * c 1 - 2 * c 2 * c 3) / t
    let y : ℚ := -(c 2 * c 1 - c 0 * c 3) / t
    apply radical_not_in_sqrt_two_span d a b ha hb hd h2d x y
    dsimp [x, y]
    push_cast
    field_simp
    change a * (t : ℂ) = _
    dsimp [t]
    push_cast
    linear_combination ((c 1 : ℂ) - (c 3 : ℂ) * b) * hrel +
      ((c 2 : ℂ) * (c 3 : ℂ) + a * (c 3 : ℂ) ^ 2) * hb
  have hrest : c 0 = 0 ∧ c 2 = 0 := by
    apply sqrt_two_rational_relation b hb
    simpa [hcoeff.1, hcoeff.2] using hrel
  intro i
  fin_cases i
  · exact hrest.1
  · exact hcoeff.1
  · exact hrest.2
  · exact hcoeff.2

end Siegel
