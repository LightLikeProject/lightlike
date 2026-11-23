import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PhiRange
import Lightlike.Lorentz.SL2RPlancherel.PhiRangeAux

/-!
# `Φ h` is in the range of `sphericalL2` for real even compactly supported `h`

If `h` is a Schwartz function that is the complexification of a real smooth even function
vanishing for `|t| > T₀`, then `phiL2 h` lies in the range of the spherical Plancherel isometry
`sphericalL2` of `SL(2,ℝ)` (milestone HA3).  The proof approximates `h` by `P ∘ cosh`
(`exists_cosh_cutoff_approx`) in `H¹` and uses the closure step `phiL2_mem_range_of_approx`.
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

theorem phiL2_mem_range_of_real (h : SchwartzMap ℝ ℂ) (h0 : ℝ → ℝ)
    (hh : ∀ t, h t = (h0 t : ℂ)) (hs : ContDiff ℝ ∞ h0) (he : ∀ t, h0 (-t) = h0 t)
    (T0 : ℝ) (hsup : ∀ t, T0 < |t| → h0 t = 0) :
    phiL2 h ∈ Set.range sphericalL2 := by
  obtain ⟨T, C, hT, hC, hex⟩ := exists_cosh_cutoff_approx h0 hs he T0 hsup
  apply phiL2_mem_range_of_approx
  intro δ hδ
  set K : ℝ := 4 * T * C ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set ε : ℝ := min 1 (δ / (K + 1)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ δ / (K + 1) := min_le_right _ _
  obtain ⟨P, hP, hPc, hPp⟩ := hex ε hε0
  have hgs : ContDiff ℝ ∞ (fun t : ℝ => ((P (Real.cosh t) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hP.comp Real.contDiff_cosh)
  have hgc : HasCompactSupport (fun t : ℝ => ((P (Real.cosh t) : ℝ) : ℂ)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(max T T0)) (b := max T T0))
      fun t ht => ?_
    have hlt : max T T0 < |t| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith [le_max_left T T0])]
        linarith
      · exact lt_of_lt_of_le h (le_abs_self t)
    have h1 := (hPp t).1 (lt_of_le_of_lt (le_max_left _ _) hlt)
    have h2 := hsup t (lt_of_le_of_lt (le_max_right _ _) hlt)
    have h3 : P (Real.cosh t) = 0 := by linarith
    simp [h3]
  set g : SchwartzMap ℝ ℂ := hgc.toSchwartzMap hgs with hg
  have hsq : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  refine ⟨g, ?_, ?_⟩
  · refine phiL2_mem_range_of_cosh g (fun v => ((P v / √2 : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hP.div_const _)) ?_ fun t => ?_
    · exact hPc.comp_left (g := fun x : ℝ => ((x / √2 : ℝ) : ℂ)) (by simp)
    · have h1 : g t = ((P (Real.cosh t) : ℝ) : ℂ) := rfl
      rw [h1]
      push_cast
      field_simp
  · have hdiff : ∀ x, (h - g) x = ((h0 x - P (Real.cosh x) : ℝ) : ℂ) := by
      intro x
      simp [hg, hh]
    have hfun : ⇑(h - g) = fun t => ((h0 t - P (Real.cosh t) : ℝ) : ℂ) := funext hdiff
    have hd0 : Differentiable ℝ h0 := hs.differentiable (by simp)
    have hd1 : Differentiable ℝ (fun s => P (Real.cosh s)) :=
      (hP.comp Real.contDiff_cosh).differentiable (by simp)
    have hder : ∀ x, deriv ⇑(h - g) x
        = ((deriv h0 x - deriv (fun s => P (Real.cosh s)) x : ℝ) : ℂ) := by
      intro x
      rw [hfun]
      exact (((hd0 x).hasDerivAt.sub (hd1 x).hasDerivAt).ofReal_comp).deriv
    have hz : ∀ x, T < |x| → deriv ⇑(h - g) x = 0 := by
      intro x hx
      have hev : (⇑(h - g)) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
        rw [hdiff]
        simp [(hPp y).1 hy]
      rw [hev.deriv_eq]
      simp
    have I1 := integral_norm_sq_le_of_support (⇑(h - g)) T (C * ε) hT
      (fun t ht => by rw [hdiff]; simp [(hPp t).1 ht])
      (fun t => by
        rw [hdiff, Complex.norm_real, Real.norm_eq_abs]; exact (hPp t).2.1)
    have I2 := integral_norm_sq_le_of_support (fun x => deriv ⇑(h - g) x) T (C * ε) hT
      (fun t ht => hz t ht)
      (fun t => by
        rw [hder, Complex.norm_real, Real.norm_eq_abs]; exact (hPp t).2.2)
    have hεK : ε * (K + 1) ≤ δ := by
      rwa [le_div_iff₀ (by positivity)] at hε2
    have hε3 : ε ^ 2 ≤ ε := by nlinarith
    have hfin : 2 * T * (C * ε) ^ 2 + 2 * T * (C * ε) ^ 2 ≤ δ := by
      have : 2 * T * (C * ε) ^ 2 + 2 * T * (C * ε) ^ 2 = K * ε ^ 2 := by rw [hK]; ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hε3 hK0]
    linarith

end Lightlike.Lorentz.SL2RPlancherel
