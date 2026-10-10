import Siegel.BoxHull
import Siegel.LagrangeFace

/-! The full rectangular interpolation theorem (Lemma 3). -/

namespace Siegel.Interpolation

open MvPolynomial

theorem dual_eq_coordinate_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ℂ) →ₗ[ℂ] ℂ) (x : ι → ℂ) :
    φ x = ∑ i, φ (Pi.single i 1) * x i := by
  have hx : (∑ i, x i • Pi.single i (1 : ℂ)) = x := by
    ext i
    simp [Pi.single_apply]
  calc
    φ x = φ (∑ i, x i • Pi.single i (1 : ℂ)) := congrArg φ hx.symm
    _ = _ := by simp [map_sum, mul_comm]

theorem exists_nonzero_coordinate_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : (ι → ℂ) →ₗ[ℂ] ℂ) (hφ : φ ≠ 0) :
    ∃ i, φ (Pi.single i 1) ≠ 0 := by
  by_contra! h
  apply hφ
  apply LinearMap.ext
  intro x
  change φ x = 0
  rw [dual_eq_coordinate_sum]
  simp [h]

/-- Lemma 3, with exactly the hypotheses stated in the source. -/
theorem rectangular_interpolation
    (A : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (c : Fin 4 → ℂ)
    (hA : Function.Surjective A) (hker : LinearMap.ker A = Submodule.span ℂ {c})
    (hc : LinearIndependent ℚ c) (N : ℕ) (t : Fin 3 → ℕ)
    (hN : 1 ≤ N) (ht : ∀ j, 3 * (N - 1) ≤ t j)
    (hsize : (4 * N - 3) ^ 4 < ∏ j, (t j - 3 * (N - 1) + 1)) :
    Function.Surjective (evaluationMap A N t) := by
  classical
  by_contra hsurj
  have hproper : LinearMap.range (evaluationMap A N t) < ⊤ := by
    exact lt_top_iff_ne_top.mpr (fun h => hsurj (LinearMap.range_eq_top.mp h))
  obtain ⟨φ, hφ, hφrange⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hproper inferInstance
  let v : IntegerBox N → ℂ := fun n => φ (Pi.single n 1)
  have hann (P : MvPolynomial (Fin 3) ℂ) (hP : ∀ j, P.degreeOf j ≤ t j) :
      (∑ n : IntegerBox N, v n * eval (A (boxPoint n)) P) = 0 := by
    have hmem := polynomial_evaluation_mem_range A N t P hP
    have hzero := Submodule.mem_map_of_mem (f := φ) hmem
    rw [hφrange, Submodule.mem_bot] at hzero
    change φ (fun n => eval (A (boxPoint n)) P) = 0 at hzero
    rw [dual_eq_coordinate_sum φ] at hzero
    exact hzero
  let S : Finset (Fin 4 → ℤ) := (Finset.univ.filter (fun n => v n ≠ 0)).image boxInt
  have hS : S.Nonempty := by
    obtain ⟨n, hn⟩ := exists_nonzero_coordinate_of_dual φ hφ
    exact ⟨boxInt n, Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩⟩
  have hSbox : ∀ s ∈ S, ∃ n : IntegerBox N, boxInt n = s := by
    intro s hs
    obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hs
    exact ⟨n, heq⟩
  let b : Fin 3 → ℕ := fun j => t j - 3 * (N - 1)
  have hcard : Fintype.card (IntegerBox (4 * N - 3)) < ∏ j, (b j + 1) := by
    simpa [IntegerBox, b, Fintype.card_pi] using hsize
  obtain ⟨R, hR, hRdeg, hRzero⟩ := exists_nonzero_vanishing_polynomial b
    (fun n : IntegerBox (4 * N - 3) => A (boxPoint n)) hcard
  let F : (Fin 4 → ℤ) → ℂ := fun m => eval (A (fun i => (m i : ℂ))) R
  have hF : ∃ m, F m ≠ 0 := exists_integer_nonzero_of_surjective A hA R hR
  have hvanish : ∀ m, latticePoint m ∈ fourHull S → F m = 0 := by
    intro m hm
    obtain ⟨n, rfl⟩ := fourHull_integer_mem_box N hN S hSbox m hm
    simpa [F] using hRzero n
  obtain ⟨m, uu, r, hm, huu, hr, hface⟩ := rational_face_reduction S hS F hF hvanish
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp huu
  have hvu : v u ≠ 0 := (Finset.mem_filter.mp hu).2
  let rC := complexifyNormal r
  have hrc : rC c ≠ 0 := complexifyNormal_transverse r hr c hc
  have hrC : rC ≠ 0 := by intro h; apply hrc; rw [h]; rfl
  obtain ⟨i₀, hi₀⟩ := exists_nonzero_coordinate_of_dual rC hrC
  obtain ⟨Q, hQdeg, hQu, hQzero⟩ := exists_face_selector A c rC (rC (boxPoint u))
    hA hker hrc i₀ hi₀ N u rfl
  let d : Fin 3 → ℂ := A (fun i => (m i : ℂ) - (boxInt u i : ℂ))
  let B : MvPolynomial (Fin 3) ℂ := Q * translatePolynomial d R
  have hBdeg : ∀ j, B.degreeOf j ≤ t j := by
    intro j
    apply (degreeOf_mul_le j Q (translatePolynomial d R)).trans
    have hQj := (degreeOf_le_totalDegree Q j).trans hQdeg
    have hRj := (degreeOf_translatePolynomial_le d R j).trans (hRdeg j)
    have htj := ht j
    dsimp [b] at hRj
    omega
  have hBeval (n : IntegerBox N) :
      eval (A (boxPoint n)) B = eval (A (boxPoint n)) Q * F (m + boxInt n - boxInt u) := by
    rw [show B = _ from rfl, map_mul, eval_translatePolynomial]
    congr 1
    change eval (A (boxPoint n) + d) R = eval (A _) R
    congr 2
    rw [show d = A _ from rfl, ← map_add]
    congr 1
    ext i
    simp [boxPoint, boxInt]
    ring
  have hzero (n : IntegerBox N) (hnu : n ≠ u) :
      v n * eval (A (boxPoint n)) B = 0 := by
    by_cases hvn : v n = 0
    · simp [hvn]
    rw [hBeval]
    by_cases hFn : F (m + boxInt n - boxInt u) = 0
    · simp [hFn]
    have hnS : boxInt n ∈ S :=
      Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvn⟩, rfl⟩
    have hrat := hface (boxInt n) hnS hFn
    have hplane : rC (boxPoint n) = rC (boxPoint u) := by
      apply sub_eq_zero.mp
      rw [← map_sub]
      have heq : boxPoint n - boxPoint u =
          fun i => (((boxInt n i : ℚ) - (boxInt u i : ℚ) : ℚ) : ℂ) := by
        ext i
        simp [boxPoint, boxInt]
      rw [heq, show rC = complexifyNormal r from rfl, complexifyNormal_rat, hrat]
      simp
    rw [hQzero n hplane hnu]
    simp
  have hsum : (∑ n : IntegerBox N, v n * eval (A (boxPoint n)) B) = v u * F m := by
    rw [Finset.sum_eq_single u]
    · rw [hBeval, hQu, one_mul]
      congr 2
      abel
    · intro n hn hnu
      exact hzero n hnu
    · simp
  have hcontr := hann B hBdeg
  rw [hsum] at hcontr
  exact (mul_ne_zero hvu hm) hcontr

/-- The proposition recording the source's full Lemma 3 is now proved. -/
theorem interpolation : interpolationStatement := rectangular_interpolation

end Siegel.Interpolation
