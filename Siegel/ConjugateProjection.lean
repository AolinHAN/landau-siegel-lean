import Siegel.Algebra
import Siegel.InterpolationBudgets
import Siegel.Archimedean

/-! Connecting the explicit matrix (4.1) with Lemma 3 and Corollary 4. -/

namespace Siegel

open Siegel.Interpolation

noncomputable def conjugateProjection (a b : ℂ) :
    (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) := (conjugateMatrix a b).mulVecLin

theorem conjugateProjection_surjective (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Surjective (conjugateProjection a b) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have h := conjugateMatrix_rank a b ha hb
  simpa [Matrix.rank, conjugateProjection, Module.finrank_pi] using h

theorem conjugateProjection_ker (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearMap.ker (conjugateProjection a b) = Submodule.span ℂ {conjugateKernel a b} := by
  ext x
  change (conjugateMatrix a b).mulVec x = 0 ↔ _
  rw [conjugateMatrix_mulVec_eq_zero_iff a b ha hb, Submodule.mem_span_singleton]
  exact exists_congr fun t => eq_comm

theorem conjugateKernel_linearIndependent (a b : ℂ)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) :
    LinearIndependent ℚ (conjugateKernel a b) := by
  have hrev := hlin.comp Fin.rev Fin.rev_injective
  let w : Fin 4 → ℚˣ := ![1, 1, -1, -1]
  have hs := hrev.units_smul w
  convert hs using 1
  ext i
  fin_cases i <;> norm_num [conjugateKernel, w, Pi.smul_apply, Function.comp_def,
    Fin.rev, Units.smul_def]

/-- Corollary 4 applies to the exact three conjugates in (4.1). -/
theorem conjugateProjection_uniform_interpolation (a b : ℂ)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b])
    (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    Function.Surjective (evaluationMap (conjugateProjection a b) N
      (fun j => ⌊degreeBudget N H j⌋₊)) := by
  have ha : a ≠ 0 := by simpa using hlin.ne_zero (1 : Fin 4)
  have hb : b ≠ 0 := by simpa using hlin.ne_zero (2 : Fin 4)
  exact uniform_budget_interpolation (conjugateProjection a b) (conjugateKernel a b)
    (conjugateProjection_surjective a b ha hb) (conjugateProjection_ker a b ha hb)
    (conjugateKernel_linearIndependent a b hlin) N H hH hHN

/-- The projection sends the integer box to the three specified conjugates. -/
theorem conjugateProjection_boxPoint {N : ℕ} (a b : ℂ) (n : IntegerBox N) :
    conjugateProjection a b (boxPoint n) =
      ![thetaPoint a b n, thetaPoint (-a) b n, thetaPoint (-a) (-b) n] := by
  ext i
  fin_cases i <;>
    simp [conjugateProjection, conjugateMatrix, boxPoint, thetaPoint,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

end Siegel
