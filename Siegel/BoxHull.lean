import Siegel.FaceReduction

/-! Coordinate bounds for the convex hull in Lemma 3. -/

namespace Siegel.Interpolation

/-- Integer coordinates of a point in the finite box. -/
def boxInt {N : ℕ} (n : IntegerBox N) : Fin 4 → ℤ := fun i => (n i : ℕ)

theorem boxInt_injective (N : ℕ) : Function.Injective (@boxInt N) := by
  intro a b h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  simp only [boxInt] at hi
  exact_mod_cast hi

@[simp] theorem boxInt_complex {N : ℕ} (n : IntegerBox N) :
    (fun i => (boxInt n i : ℂ)) = boxPoint n := by
  ext i
  simp [boxInt, boxPoint]

/-- Every integer point of `4 conv(S)` lies in the box of side `4N-3`
whenever `S` is contained in the box of side `N`. -/
theorem fourHull_integer_mem_box (N : ℕ) (hN : 1 ≤ N)
    (S : Finset (Fin 4 → ℤ))
    (hS : ∀ s ∈ S, ∃ n : IntegerBox N, boxInt n = s)
    (m : Fin 4 → ℤ) (hm : latticePoint m ∈ fourHull S) :
    ∃ n : IntegerBox (4 * N - 3), boxInt n = m := by
  classical
  obtain ⟨x, hx, hxm⟩ := hm
  have hbound (i : Fin 4) : 0 ≤ m i ∧ m i < (4 * N - 3 : ℕ) := by
    let π : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℝ :=
      (LinearMap.proj i).comp (EuclideanSpace.equiv (Fin 4) ℝ).toLinearMap
    have hxcoord : π x ∈ Set.Icc (0 : ℝ) (N - 1 : ℕ) := by
      apply convexHull_min (t := π ⁻¹' Set.Icc (0 : ℝ) (N - 1 : ℕ)) ?_
        ((convex_Icc _ _).linear_preimage π) hx
      rintro z ⟨s, hs, rfl⟩
      obtain ⟨n, rfl⟩ := hS s hs
      change (0 : ℝ) ≤ (n i : ℕ) ∧ ((n i : ℕ) : ℝ) ≤ (N - 1 : ℕ)
      exact ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.le_sub_one_of_lt (n i).isLt⟩
    have hmi : (m i : ℝ) = 4 * π x := by
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin 4) => z i) hxm
      simpa [latticePoint, π] using hi.symm
    have hnid : 4 * N - 3 = 4 * (N - 1) + 1 := by omega
    constructor
    · have h : (0 : ℝ) ≤ (m i : ℝ) := by rw [hmi]; exact mul_nonneg (by norm_num) hxcoord.1
      exact_mod_cast h
    · have h : (m i : ℝ) < (4 * N - 3 : ℕ) := by
        rw [hnid]
        push_cast
        linarith [hxcoord.2]
      exact_mod_cast h
  let n : IntegerBox (4 * N - 3) := fun i =>
    ⟨(m i).toNat, by
      have hi := (hbound i).2
      omega⟩
  refine ⟨n, ?_⟩
  funext i
  exact Int.toNat_of_nonneg (hbound i).1

end Siegel.Interpolation
