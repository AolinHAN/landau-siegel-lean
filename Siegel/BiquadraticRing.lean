import Siegel.Algebra

namespace Siegel.Biquadratic

open scoped QuadraticAlgebra

abbrev Base (d : ℤ) := QuadraticAlgebra ℤ d 0
abbrev Ring (d : ℤ) := QuadraticAlgebra (Base d) 2 0

/-- Evaluation of a quadratic algebra along a ring homomorphism. -/
def quadraticEval {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d e : R) (a : S) (ha : a ^ 2 = f d + f e * a) :
    QuadraticAlgebra R d e →+* S where
  toFun z := f z.re + f z.im * a
  map_zero' := by simp
  map_one' := by change f 1 + f 0 * a = 1; simp
  map_add' z w := by simp [add_mul]; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul]
    linear_combination -(f z.im * f w.im) * ha

noncomputable def embed (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) : Ring d →+* ℂ :=
  quadraticEval (quadraticEval (Int.castRingHom ℂ) d 0 a (by simpa using ha))
    2 0 b (by simpa [quadraticEval] using hb)

@[simp] theorem embed_apply (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (z : Ring d) :
    embed d a b ha hb z = (z.re.re : ℂ) + z.re.im * a + z.im.re * b + z.im.im * a * b := by
  simp [embed, quadraticEval]
  ring

theorem embed_injective (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) :
    Function.Injective (embed d a b ha hb) := by
  have hzero (z : Ring d) (hz : embed d a b ha hb z = 0) : z = 0 := by
    let c : Fin 4 → ℚ := ![z.re.re, z.re.im, z.im.re, z.im.im]
    have hsum : ∑ i, c i • (![1, a, b, a * b] : Fin 4 → ℂ) i = 0 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      dsimp [c]
      simpa [Rat.smul_def, embed_apply, mul_assoc, add_assoc] using hz
    have hc := Fintype.linearIndependent_iff.mp hlin c hsum
    have h0 : z.re.re = 0 := by have := hc 0; dsimp [c] at this; exact_mod_cast this
    have h1 : z.re.im = 0 := by have := hc 1; dsimp [c] at this; exact_mod_cast this
    have h2 : z.im.re = 0 := by have := hc 2; dsimp [c] at this; exact_mod_cast this
    have h3 : z.im.im = 0 := by have := hc 3; dsimp [c] at this; exact_mod_cast this
    ext <;> simp [h0, h1, h2, h3]
  intro z w h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, h, sub_self]

/-- The relative norm followed by the quadratic norm to the integers. -/
def norm (d : ℤ) : Ring d →* ℤ :=
  (QuadraticAlgebra.norm : Base d →* ℤ).comp QuadraticAlgebra.norm

@[simp] theorem norm_intCast (d n : ℤ) : norm d (n : Ring d) = n ^ 4 := by
  norm_num [norm, ← pow_mul]

theorem norm_ne_zero (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (hlin : LinearIndependent ℚ ![1, a, b, a * b]) (z : Ring d) (hz : z ≠ 0) :
    norm d z ≠ 0 := by
  letI : IsDomain (Ring d) := (embed_injective d a b ha hb hlin).isDomain (embed d a b ha hb)
  have h1 := QuadraticAlgebra.norm_mem_nonZeroDivisors_iff.mpr
    (mem_nonZeroDivisors_of_ne_zero hz)
  have h2 := QuadraticAlgebra.norm_mem_nonZeroDivisors_iff.mpr h1
  exact nonZeroDivisors.ne_zero h2

theorem norm_divisibility (d : ℤ) (z : Ring d) (p E : ℕ)
    (h : (p : Ring d) ^ E ∣ z) : (p : ℤ) ^ (4 * E) ∣ norm d z := by
  have hm := map_dvd (norm d) h
  have hp : norm d (p : Ring d) = (p : ℤ) ^ 4 := by
    simpa using norm_intCast d (p : ℤ)
  simpa only [map_pow, hp, ← pow_mul] using hm

/-- The composite norm is the explicit integer polynomial from Section 5. -/
theorem norm_eq_polynomial (d : ℤ) (z : Ring d) :
    norm d z = biquadraticNorm d 2 z.re.re z.re.im z.im.re z.im.im := by
  simp [norm, QuadraticAlgebra.norm_def, biquadraticNorm]
  ring

/-- The four complex embeddings, ordered by the two choices of signs. -/
noncomputable def embeddings (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) : Fin 4 → (Ring d →+* ℂ) :=
  ![embed d a b ha hb,
    embed d (-a) b (by simpa using ha) hb,
    embed d a (-b) ha (by simpa using hb),
    embed d (-a) (-b) (by simpa using ha) (by simpa using hb)]

/-- The integer norm really is the product of the four conjugates. -/
theorem norm_eq_embeddings_product (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) (z : Ring d) :
    (norm d z : ℂ) = ∏ ν, embeddings d a b ha hb ν z := by
  rw [norm_eq_polynomial, Fin.prod_univ_four]
  dsimp [embeddings]
  simp only [embed_apply, mul_neg, neg_mul, neg_neg]
  have h := four_conjugates_eq_integer a b d 2 z.re.re z.re.im z.im.re z.im.im ha
    (by simpa using hb)
  simpa only [sub_eq_add_neg] using h.symm

/-- Applying this to a determinant identifies exactly the same norm in
the Archimedean and prime-divisibility bounds. -/
theorem determinant_norm_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℤ) (a b : ℂ) (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2)
    (A : Matrix ι ι (Ring d)) :
    (norm d A.det : ℂ) = ∏ ν, (A.map (embeddings d a b ha hb ν)).det := by
  rw [norm_eq_embeddings_product d a b ha hb A.det]
  apply Finset.prod_congr rfl
  intro ν hν
  exact (embeddings d a b ha hb ν).map_det A

/-- The two square-root generators of the concrete integral ring. -/
def genA (d : ℤ) : Ring d := algebraMap (Base d) (Ring d) QuadraticAlgebra.omega
def genB (d : ℤ) : Ring d := QuadraticAlgebra.omega

theorem genA_sq (d : ℤ) : genA d ^ 2 = (d : Ring d) := by
  ext <;> simp [genA, pow_two, QuadraticAlgebra.omega]

theorem genB_sq (d : ℤ) : genB d ^ 2 = 2 := by
  ext <;> simp [genB, pow_two, QuadraticAlgebra.omega]

theorem coordinate_expression (d : ℤ) (z : Ring d) :
    z = (z.re.re : Ring d) + z.re.im * genA d + z.im.re * genB d +
      z.im.im * genA d * genB d := by
  ext <;> simp [genA, genB, QuadraticAlgebra.omega]

@[simp] theorem embed_genA (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) : embed d a b ha hb (genA d) = a := by
  simp [embed_apply, genA, QuadraticAlgebra.omega]

@[simp] theorem embed_genB (d : ℤ) (a b : ℂ)
    (ha : a ^ 2 = (d : ℂ)) (hb : b ^ 2 = 2) : embed d a b ha hb (genB d) = b := by
  simp [embed_apply, genB, QuadraticAlgebra.omega]

end Siegel.Biquadratic
