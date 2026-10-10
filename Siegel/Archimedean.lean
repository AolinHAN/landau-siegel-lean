import Siegel.Hadamard
import Siegel.RowReplacement
import Siegel.Interpolation

/-! Entry bounds and the logarithmic Hadamard estimate in Section 5. -/

namespace Siegel

open Siegel.Interpolation

/-- The biquadratic evaluation point in the original embedding. -/
def thetaPoint {N : ℕ} (a b : ℂ) (n : IntegerBox N) : ℂ :=
  (n 0 : ℕ) + (n 1 : ℕ) * a + (n 2 : ℕ) * b + (n 3 : ℕ) * a * b

theorem thetaPoint_norm_le {N : ℕ} (a b : ℂ) (n : IntegerBox N) :
    ‖thetaPoint a b n‖ ≤ (N - 1 : ℕ) * (1 + ‖a‖) * (1 + ‖b‖) := by
  have hn (i) : (n i : ℕ) ≤ N - 1 := Nat.le_sub_one_of_lt (n i).isLt
  calc
    _ ≤ ‖((n 0 : ℕ) : ℂ)‖ + ‖((n 1 : ℕ) : ℂ) * a‖ +
        ‖((n 2 : ℕ) : ℂ) * b‖ + ‖((n 3 : ℕ) : ℂ) * a * b‖ := by
      dsimp [thetaPoint]
      have h1 := norm_add_le (((n 0 : ℕ) : ℂ)) (((n 1 : ℕ) : ℂ) * a)
      have h2 := norm_add_le ((((n 0 : ℕ) : ℂ)) + ((n 1 : ℕ) : ℂ) * a)
        (((n 2 : ℕ) : ℂ) * b)
      have h3 := norm_add_le ((((n 0 : ℕ) : ℂ)) + ((n 1 : ℕ) : ℂ) * a +
        ((n 2 : ℕ) : ℂ) * b) (((n 3 : ℕ) : ℂ) * a * b)
      linarith
    _ ≤ (N - 1 : ℕ) + (N - 1 : ℕ) * ‖a‖ + (N - 1 : ℕ) * ‖b‖ +
        (N - 1 : ℕ) * ‖a‖ * ‖b‖ := by
      simp only [norm_mul, Complex.norm_natCast]
      gcongr <;> exact hn _
    _ = _ := by ring

/-- The uniform `8 N sqrt(q)` entry bound in Section 5. -/
theorem thetaPoint_norm_le_conductor {N : ℕ} (a b : ℂ) (n : IntegerBox N)
    (q : ℝ) (hq : 1 ≤ q) (ha : ‖a‖ ≤ Real.sqrt q) (hb : ‖b‖ ≤ 2) :
    ‖thetaPoint a b n‖ ≤ 8 * N * Real.sqrt q := by
  have hq0 : 0 ≤ q := by linarith
  have hs : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq
  have hN : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  calc
    _ ≤ (N - 1 : ℕ) * (1 + ‖a‖) * (1 + ‖b‖) := thetaPoint_norm_le a b n
    _ ≤ (N : ℝ) * (1 + Real.sqrt q) * (1 + 2) := by gcongr
    _ ≤ 8 * N * Real.sqrt q := by
      nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (by linarith : 0 ≤ Real.sqrt q - 1)]

theorem rawRow_norm_le {ι : Type*} (x y z : ι → ℂ) (α : Fin 3 → ℕ)
    (B : ℝ) (hB : 0 ≤ B) (hx : ∀ n, ‖x n‖ ≤ B)
    (hy : ∀ n, ‖y n‖ ≤ B) (hz : ∀ n, ‖z n‖ ≤ B) (n : ι) :
    ‖rawRow x y z α n‖ ≤ B ^ (α 0 + α 1 + α 2) := by
  simp only [rawRow, norm_mul, norm_pow, pow_add]
  gcongr
  · exact hx n
  · exact hy n
  · exact hz n

/-- The logarithmic form of Hadamard's inequality, including the exact
`(M/2) log M` term of (5.1). -/
theorem log_det_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (A : Matrix ι ι ℂ) (e : ι → ℕ) (B : ℝ) (hB : 0 < B)
    (hdet : A.det ≠ 0) (hentry : ∀ i j, ‖A i j‖ ≤ B ^ e i) :
    Real.log ‖A.det‖ ≤ (Fintype.card ι : ℝ) / 2 * Real.log (Fintype.card ι) +
      (∑ i, (e i : ℝ)) * Real.log B := by
  have hM : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsqrt : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.mpr hM
  have hb := det_norm_le_row_bounds A (fun i => B ^ e i) (fun i => (pow_pos hB _).le) hentry
  have hl := Real.log_le_log (norm_pos_iff.mpr hdet) hb
  have heq : Real.log (∏ i, (Real.sqrt (Fintype.card ι) * B ^ e i)) =
      (Fintype.card ι : ℝ) / 2 * Real.log (Fintype.card ι) +
        (∑ i, (e i : ℝ)) * Real.log B := by
    rw [Real.log_prod (fun i _ => mul_ne_zero hsqrt.ne' (pow_pos hB _).ne')]
    simp_rw [Real.log_mul hsqrt.ne' (pow_pos hB _).ne', Real.log_pow,
      Real.log_sqrt hM.le]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    simp
    ring
  rwa [heq] at hl

/-- The size of a complex square root is controlled by the absolute value
of its integer radicand, for either sign of that radicand. -/
theorem norm_square_root_le (a : ℂ) (d : ℤ) (q : ℝ)
    (ha : a ^ 2 = (d : ℂ)) (hd : |(d : ℝ)| ≤ q) : ‖a‖ ≤ Real.sqrt q := by
  calc
    ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg a)).symm
    _ = Real.sqrt |(d : ℝ)| := by rw [← norm_pow, ha, Complex.norm_intCast]
    _ ≤ _ := Real.sqrt_le_sqrt hd

/-- The factor `1/4` in (5.1), obtained from all four conjugate
determinants rather than assumed as an Archimedean estimate. -/
theorem four_determinants_log_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (A : Fin 4 → Matrix ι ι ℂ) (e : ι → ℕ) (B : ℝ) (hB : 0 < B)
    (hdet : ∀ ν, (A ν).det ≠ 0) (hentry : ∀ ν i j, ‖A ν i j‖ ≤ B ^ e i) :
    Real.log ‖∏ ν, (A ν).det‖ / 4 ≤
      (Fintype.card ι : ℝ) / 2 * Real.log (Fintype.card ι) +
        (∑ i, (e i : ℝ)) * Real.log B := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
    (fun ν _ => log_det_norm_le (A ν) e B hB (hdet ν) (hentry ν))
  rw [norm_prod, Real.log_prod (fun ν _ => norm_ne_zero_iff.mpr (hdet ν))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

/-- The complete four-embedding upper estimate from Section 5, given
the evaluation-point bounds at those embeddings. -/
theorem four_conjugate_archimedean_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (x y z : Fin 4 → ι → ℂ) (α : ι → Fin 3 → ℕ) (N q : ℕ)
    (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hpoints : ∀ ν n, ‖x ν n‖ ≤ 8 * N * Real.sqrt q ∧
      ‖y ν n‖ ≤ 8 * N * Real.sqrt q ∧ ‖z ν n‖ ≤ 8 * N * Real.sqrt q)
    (hdet : ∀ ν, (Matrix.of (fun i n => rawRow (x ν) (y ν) (z ν) (α i) n)).det ≠ 0) :
    Real.log ‖∏ ν, (Matrix.of (fun i n => rawRow (x ν) (y ν) (z ν) (α i) n)).det‖ / 4 ≤
      (Fintype.card ι : ℝ) / 2 * Real.log (Fintype.card ι) +
        (∑ i, ((α i 0 : ℝ) + α i 1 + α i 2)) *
          (Real.log N + Real.log q / 2 + Real.log 8) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hB : 0 < 8 * (N : ℝ) * Real.sqrt q := by positivity
  have h := four_determinants_log_bound
    (fun ν => Matrix.of (fun i n => rawRow (x ν) (y ν) (z ν) (α i) n))
    (fun i => α i 0 + α i 1 + α i 2) (8 * N * Real.sqrt q) hB hdet
    (fun ν i n => rawRow_norm_le (x ν) (y ν) (z ν) (α i) _ hB.le
      (fun n => (hpoints ν n).1) (fun n => (hpoints ν n).2.1)
      (fun n => (hpoints ν n).2.2) n)
  have hlog : Real.log (8 * (N : ℝ) * Real.sqrt q) =
      Real.log N + Real.log q / 2 + Real.log 8 := by
    rw [Real.log_mul (mul_pos (by norm_num) hNp).ne' (Real.sqrt_pos.mpr hqp).ne',
      Real.log_mul (by norm_num) hNp.ne', Real.log_sqrt hqp.le]
    ring
  simpa only [hlog, Nat.cast_add] using h

end Siegel
