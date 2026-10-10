import Siegel.RadicalIndependence
import Mathlib.Algebra.Squarefree.Basic

namespace Siegel

/-- A squarefree integer which is a rational square is necessarily one. -/
theorem squarefree_not_isSquare_rat {d : ℤ} (hd : Squarefree d) (hd1 : d ≠ 1) :
    ¬ IsSquare (d : ℚ) := by
  intro hs
  obtain ⟨k, hk⟩ := Rat.isSquare_intCast_iff.mp hs
  have hu : IsUnit k := hd k (by rw [hk])
  rcases Int.isUnit_iff.mp hu with h | h <;> apply hd1 <;> simpa [h] using hk

/-- For squarefree d, twice d is a rational square only in the excluded case d=2. -/
theorem squarefree_twice_not_isSquare_rat {d : ℤ} (hd : Squarefree d) (hd2 : d ≠ 2) :
    ¬ IsSquare (2 * (d : ℚ)) := by
  intro hs
  have hsZ : IsSquare (2 * d) := Rat.isSquare_intCast_iff.mp (by simpa using hs)
  obtain ⟨k, hk⟩ := hsZ
  have hkd : k ∣ (2 : ℤ) :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_left hd (by rw [hk])
  have hbound := Int.natAbs_le_of_dvd_ne_zero hkd (by norm_num : (2 : ℤ) ≠ 0)
  have habs : |k| ≤ (2 : ℤ) := by
    have h : (k.natAbs : ℤ) ≤ 2 := by exact_mod_cast hbound
    simpa only [Int.natCast_natAbs] using h
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hd0 := hd.ne_zero
  interval_cases k <;> norm_num at hk <;> omega

/-- The four basis elements in §4 are independent for every squarefree
radicand except exactly 1 and 2; there is no conductor threshold. -/
theorem biquadratic_linearIndependent_of_squarefree {d : ℤ}
    (hd : Squarefree d) (hd1 : d ≠ 1) (hd2 : d ≠ 2) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) :
    LinearIndependent ℚ ![1, a, b, a * b] := by
  exact biquadratic_generators_linearIndependent (d : ℚ) a b (by simpa using ha) hb
    (squarefree_not_isSquare_rat hd hd1) (squarefree_twice_not_isSquare_rat hd hd2)

end Siegel
