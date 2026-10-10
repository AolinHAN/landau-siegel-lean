import Siegel.QuadraticModel

/-! Removing square factors from the signed conductor in the quadratic model. -/

namespace Siegel

/-- Every nonzero integer has a squarefree part of no larger absolute value. -/
theorem exists_squarefree_part (D : ℤ) (hD : D ≠ 0) :
    ∃ (d : ℤ) (k : ℕ), 0 < k ∧ Squarefree d ∧
      (k : ℤ) ^ 2 * d = D ∧ |(d : ℝ)| ≤ |(D : ℝ)| := by
  obtain ⟨n, k, hn, hk, hkn, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hD)
  have hnle : n ≤ D.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hD)
    ⟨k ^ 2, by simpa [mul_comm] using hkn.symm⟩
  have hknZ : (k : ℤ) ^ 2 * (n : ℤ) = |D| := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs] using
      congrArg (fun m : ℕ => (m : ℤ)) hkn
  have hnleR : (n : ℝ) ≤ |(D : ℝ)| := by
    have h : (n : ℝ) ≤ (D.natAbs : ℝ) := by exact_mod_cast hnle
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  by_cases hpos : 0 ≤ D
  · refine ⟨n, k, hk, Int.squarefree_natCast.mpr hsq, ?_, ?_⟩
    · simpa [abs_of_nonneg hpos] using hknZ
    · simpa using hnleR
  · refine ⟨-(n : ℤ), k, hk, ?_, ?_, ?_⟩
    · apply Int.squarefree_natAbs.mp
      simpa using hsq
    · rw [abs_of_neg (lt_of_not_ge hpos)] at hknZ
      nlinarith
    · simpa using hnleR

/-- Dividing the first radical by a nonzero rational scalar preserves the
four-generator independence required by the projected-box argument. -/
theorem biquadratic_linearIndependent_div (a b : ℂ) (k : ℕ) (hk : 0 < k)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) :
    LinearIndependent ℚ ![1, a / k, b, (a / k) * b] := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  let u : ℚˣ := Units.mk0 (k : ℚ) hkQ
  have h := hlin.units_smul (![1, u⁻¹, 1, u⁻¹] : Fin 4 → ℚˣ)
  convert h using 1
  ext i
  fin_cases i <;> simp [u, Units.smul_def, Algebra.smul_def, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

/-- Stripping the square factor does not change the generated quadratic field. -/
theorem adjoin_singleton_div_nat (a : ℂ) (k : ℕ) (hk : 0 < k) :
    IntermediateField.adjoin ℚ ({a / k} : Set ℂ) =
      IntermediateField.adjoin ℚ ({a} : Set ℂ) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  apply le_antisymm <;> rw [IntermediateField.adjoin_le_iff]
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact IntermediateField.div_mem _
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton a))
      (IntermediateField.natCast_mem _ k)
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have ha : a / k ∈ IntermediateField.adjoin ℚ ({a / k} : Set ℂ) :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    have h := IntermediateField.mul_mem _ ha (IntermediateField.natCast_mem _ k)
    simpa only [div_mul_cancel₀ _ hkC] using h

/-- The squarefree radicand can be used in the actual character realization.
All field, size and Legendre-symbol properties remain valid. -/
theorem squarefreeQuadraticModel :
    ∃ Q : ℕ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      Q ≤ q → 3 ≤ q → χ.IsPrimitive → χ ≠ 1 → χ.IsQuadratic →
      ∃ (d : ℤ) (a b : ℂ), Squarefree d ∧ a ^ 2 = (d : ℂ) ∧ b ^ 2 = 2 ∧
        LinearIndependent ℚ ![1, a, b, a * b] ∧ |(d : ℝ)| ≤ q ∧
        ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q →
          χ (p : ZMod q) = (legendreSym p d : ℂ) := by
  obtain ⟨Q, hmodel⟩ := quadraticModel
  refine ⟨Q, ?_⟩
  intro q _ χ hQ hq hprim hnontriv hquad
  obtain ⟨D, a, b, ha, hb, hlin, hsize, hchar⟩ :=
    hmodel χ hQ hq hprim hnontriv hquad
  have ha0 : a ≠ 0 := by simpa using hlin.ne_zero (1 : Fin 4)
  have hD0 : D ≠ 0 := by
    intro hz
    have h : a ^ 2 = 0 := by simpa [hz] using ha
    exact ha0 (eq_zero_of_pow_eq_zero h)
  obtain ⟨d, k, hk, hsq, hdecomp, hdsize⟩ := exists_squarefree_part D hD0
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdecompC : (k : ℂ) ^ 2 * (d : ℂ) = (D : ℂ) := by exact_mod_cast hdecomp
  refine ⟨d, a / k, b, hsq, ?_, hb, biquadratic_linearIndependent_div a b k hk hlin,
    hdsize.trans hsize, ?_⟩
  · rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hkC)).mpr
    rw [ha]
    exact hdecompC.symm.trans (mul_comm _ _)
  · intro p _ hp
    have hpq : ¬ p ∣ q := fun h => hp (dvd_mul_of_dvd_right h 2)
    have hu : χ (p : ZMod q) ≠ 0 :=
      (IsUnit.map χ (ZMod.isUnit_prime_of_not_dvd (Fact.out : p.Prime) hpq)).ne_zero
    have hDmod : (D : ZMod p) ≠ 0 := by
      intro hz
      apply hu
      rw [hchar p hp, (legendreSym.eq_zero_iff p D).mpr hz]
      simp
    have hkmod : ((k : ℤ) : ZMod p) ≠ 0 := by
      intro hz
      apply hDmod
      rw [← hdecomp]
      simp only [Int.cast_mul, Int.cast_pow, hz]
      norm_num
    rw [hchar p hp, ← hdecomp, legendreSym.mul, legendreSym.sq_one' p hkmod, one_mul]

end Siegel
