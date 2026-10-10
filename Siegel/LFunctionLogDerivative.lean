import Siegel.LFunctionRegularPart
import Siegel.CanonicalProductLogDeriv
import Siegel.ZeroPoleLower
import Siegel.Statement

namespace Siegel

open Metric Filter
open scoped Topology

/-- The logarithmic derivative retains the exceptional real zero, with an
absolute conductor-logarithmic error. -/
theorem exists_LFunction_logDeriv_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      (β : ℝ), AdmissibleZero χ β → ∀ s : ℝ, 1 < s → s ≤ 2 →
      1 / (s - β) - C * Real.log q ≤ (logDeriv χ.LFunction (s : ℂ)).re := by
  obtain ⟨C, hC, hregular⟩ := exists_LFunction_regular_part_bound
  refine ⟨C, hC, ?_⟩
  intro q _ χ β hβ s hs hs2
  rcases hβ with ⟨hq, hprim, hχ, hquad, hβ0, hβ1, hβzero⟩
  obtain ⟨S, m, g, hS, hg, hgnz, heq, herror⟩ := hregular χ hq hχ
  let f : ℂ → ℂ := fun w => χ.LFunction (w + 2)
  have hf (w : ℂ) : AnalyticAt ℂ f w :=
    ((DirichletCharacter.differentiable_LFunction hχ).analyticAt (w + 2)).comp
      (f := fun u : ℂ => u + 2) (by fun_prop)
  have hSre (w : ℂ) (hw : w ∈ S) : w.re ≤ -1 ∧ 0 < m w := by
    refine ⟨?_, (hS w hw).2.2⟩
    by_contra hn
    have hlarge : 1 ≤ (w + 2).re := by simp only [Complex.add_re, Complex.re_ofNat]; linarith
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hχ) hlarge (hS w hw).2.1
  have hmem (hb : 1 / 2 < β) : ((β - 2 : ℝ) : ℂ) ∈ S := by
    let w : ℂ := ((β - 2 : ℝ) : ℂ)
    have hwb : w ∈ ball 0 (7 / 4 : ℝ) := by
      rw [mem_ball_zero_iff]
      dsimp [w]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : β - 2 < 0)]
      linarith
    have hwcl := ball_subset_closedBall hwb
    apply zero_mem_of_regular_part (7 / 4) S m f g w (hf w).continuousAt
      (hg w hwcl).continuousAt (hgnz w hwb) (heq w hwcl)
    simpa [f, w, Complex.ofReal_sub] using hβzero
  let z : ℂ := ((s - 2 : ℝ) : ℂ)
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hzcl : z ∈ closedBall 0 (7 / 4 : ℝ) := by rw [mem_closedBall_zero_iff]; linarith
  have hfz : f z ≠ 0 := by
    have h := χ.LFunction_ne_zero_of_one_le_re (.inl hχ)
      (by simpa using hs.le : 1 ≤ (s : ℂ).re)
    simpa [f, z, Complex.ofReal_sub] using h
  have hzn : z ∉ S := fun h => hfz (hS z h).2.1
  have hlower := real_logDeriv_lower_from_regular_part S m (fun w hw => (hS w hw).1)
    f g z hz hzn hfz (hf z).differentiableAt (hg z hzcl).differentiableAt (heq z hzcl)
  have hpoles := real_zero_pole_sum_lower S m hSre s β hs hβ1 hmem
  have herr := herror z hz
  have hid : logDeriv f z = logDeriv χ.LFunction (s : ℂ) := by
    change logDeriv (χ.LFunction ∘ (fun w : ℂ => w + 2)) z = _
    rw [logDeriv_comp (g := fun w : ℂ => w + 2) (DirichletCharacter.differentiable_LFunction hχ (z + 2)) (by fun_prop)]
    simp [z, Complex.ofReal_sub]
  rw [hid] at hlower
  change 1 / (s - β) - 2 ≤ ∑ w ∈ S, (m w : ℝ) * (1 / (z - w)).re at hpoles
  linarith

end Siegel
