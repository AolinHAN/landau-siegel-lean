import Mathlib

/-! Quadratic Gauss sums over a general conductor, including composite levels. -/

namespace Siegel

open scoped BigOperators
open AddChar

noncomputable def finiteFourier {q : ℕ} [NeZero q] {R : Type*} [CommRing R]
    (ψ : AddChar (ZMod q) R) (f : ZMod q → R) (k : ZMod q) : R :=
  ∑ j, ψ (-(j * k)) * f j

/-- Finite Fourier inversion with a primitive additive character over any
integral domain, so it applies in both characteristic zero and odd characteristic. -/
theorem finiteFourier_twice {q : ℕ} [NeZero q] {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (ZMod q) R) (hψ : ψ.IsPrimitive) (f : ZMod q → R) (k : ZMod q) :
    finiteFourier ψ (finiteFourier ψ f) k = (q : R) * f (-k) := by
  classical
  have hsum (t : ZMod q) : (∑ i, ψ (t * i)) = if t = 0 then (q : R) else 0 := by
    split_ifs with ht
    · simp [ht]
    · exact AddChar.sum_eq_zero_of_ne_one (hψ ht)
  calc
    _ = ∑ j, (∑ i, ψ ((-(k + j)) * i)) * f j := by
      simp only [finiteFourier, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_assoc, ← map_add_eq_mul]
      congr 2
      ring
    _ = (q : R) * f (-k) := by
      simp only [hsum, neg_eq_zero, add_eq_zero_iff_eq_neg, ite_mul, zero_mul]
      have hneg (j : ZMod q) : k = -j ↔ j = -k := by
        constructor <;> intro h <;> simpa using congrArg Neg.neg h.symm
      simp only [hneg, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The primitive multiplicative character is an eigenvector of this
Fourier transform when it is quadratic. -/
theorem primitive_quadratic_fourier {q : ℕ} [NeZero q] {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R q) (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (ψ : AddChar (ZMod q) R) (k : ZMod q) :
    finiteFourier ψ χ k = χ (-k) * gaussSum χ ψ := by
  have heq : finiteFourier ψ χ k = gaussSum χ (ψ.mulShift (-k)) := by
    simp only [finiteFourier, gaussSum, mulShift_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm (χ j)]
    congr 2
    ring
  rw [heq, gaussSum_mulShift_of_isPrimitive ψ hχ, hquad.inv]

/-- The quadratic Gauss-sum identity for every primitive Dirichlet
character. The conductor is not assumed prime. -/
theorem primitive_quadratic_gaussSum_sq {q : ℕ} [NeZero q]
    {R : Type*} [CommRing R] [IsDomain R]
    (χ : DirichletCharacter R q) (hχ : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (ψ : AddChar (ZMod q) R) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 2 = χ (-1) * (q : R) := by
  have hneg : χ (-1) ^ 2 = 1 := by
    rw [← map_pow]
    norm_num
  have heigen : finiteFourier ψ χ = fun j => (χ (-1) * gaussSum χ ψ) * χ j := by
    ext j
    rw [primitive_quadratic_fourier χ hχ hquad ψ, ← neg_one_mul j, map_mul]
    ring
  have hdouble := finiteFourier_twice ψ hψ (fun j => χ j) 1
  rw [heigen] at hdouble
  have hconst (c : R) (f : ZMod q → R) (k : ZMod q) :
      finiteFourier ψ (fun j => c * f j) k = c * finiteFourier ψ f k := by
    simp only [finiteFourier, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hconst, primitive_quadratic_fourier χ hχ hquad ψ] at hdouble
  have heq : (χ (-1) * gaussSum χ ψ) * (χ (-1) * gaussSum χ ψ) = gaussSum χ ψ ^ 2 := by
    calc
      _ = χ (-1) ^ 2 * gaussSum χ ψ ^ 2 := by ring
      _ = _ := by rw [hneg, one_mul]
  rw [heq] at hdouble
  simpa only [mul_comm] using hdouble

end Siegel
