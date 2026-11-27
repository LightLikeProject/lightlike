import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KKCoeffSmooth
import Lightlike.Lorentz.SL2RPlancherel.PrincipalSpherical
import Lightlike.Lorentz.SL2RPlancherel.KTypeBlockL2

/-!
# The `K × K` components of a smooth function vanishing near `K` are ladder chains

The entries of `k_α a_ξ k_θ` have `Σ g_ij² = 2 cosh ξ` (`sumSq_polar`). So if `f = F(g_ij)` with `F`
smooth, `f` has compact support and `f` vanishes where `Σ g_ij² < 2 + ε`, every component
`kkCoeff f m` is smooth (`contDiff_kkCoeff`), vanishes for `|ξ|` small and for `|ξ|` large, and its
restriction to `ξ > 0` is a test function supported in `(0, ∞)`; by the surjectivity of the ladder
chains it is `Hc_{r,l} G` for a test function `G`, for every `r, l` (`exists_Hc_eq_kkCoeff`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (a dense class of test functions), milestone HA3.
-/

open MeasureTheory Set Filter Topology Lightlike.Lorentz.SL2R
open scoped ContDiff Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The sum of the squared entries. -/
def sumSq (g : SL2R) : ℝ := g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2

lemma continuous_sumSq : Continuous sumSq := by
  unfold sumSq
  have h : ∀ i j : Fin 2, Continuous fun g : SL2R => g i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  fun_prop

/-- `Σ (k_α a_ξ k_θ)_ij² = 2 cosh ξ`. -/
lemma sumSq_polar (a ξ b : ℝ) : sumSq (rot a * aR ξ * rot b) = 2 * Real.cosh ξ := by
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  have h1 : Real.exp (ξ / 2) ^ 2 = Real.exp ξ := by rw [sq, ← Real.exp_add]; ring_nf
  have h2 : Real.exp (-(ξ / 2)) ^ 2 = Real.exp (-ξ) := by rw [sq, ← Real.exp_add]; ring_nf
  simp only [sumSq]
  simp [Matrix.mul_apply, Fin.sum_univ_two, aR, diagSL, ← Real.exp_neg, Real.cosh_eq]
  linear_combination (Real.exp (ξ / 2) ^ 2 + Real.exp (-(ξ / 2)) ^ 2) *
    ((Real.sin b ^ 2 + Real.cos b ^ 2) * ha + hb) + h1 + h2

/-- `kkCoeff f m ξ = 0` when `f` vanishes on `{Σ g_ij² = 2 cosh ξ}`. -/
lemma kkCoeff_eq_zero_of_vanish {f : SL2R → ℂ} {ξ : ℝ}
    (h : ∀ g : SL2R, sumSq g = 2 * Real.cosh ξ → f g = 0) (m : Fin 2 → ℤ) :
    kkCoeff f m ξ = 0 := by
  rw [kkCoeff]
  have e : ∀ x : Fin 2 → ℝ,
      Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) * kkProfile f ξ x = 0 :=
    fun x => by rw [kkProfile, h _ (sumSq_polar _ _ _), mul_zero]
  simp only [e, integral_zero]

/-- **Every component of a smooth function vanishing near `K` is a ladder chain.** -/
theorem exists_Hc_eq_kkCoeff {f : SL2R → ℂ} {F : (Fin 2 → Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hfF : ∀ g : SL2R, f g = F fun i j => g i j)
    (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ g : SL2R, sumSq g < 2 + ε → f g = 0) (m : Fin 2 → ℤ) (r l : ℕ) :
    ∃ G : smoothCS, ∀ ξ ∈ Ioi (0 : ℝ), kkCoeff f m ξ = Hc r G l ξ := by
  have hk := contDiff_kkCoeff hF hfF m
  -- vanishing near `0`
  set δ := Real.arcosh (1 + ε / 2) with hδ
  have h1e : 1 ≤ 1 + ε / 2 := by linarith
  have hδ0 : 0 < δ := by
    rw [hδ]
    have hne : Real.arcosh (1 + ε / 2) ≠ 0 := by
      rw [Ne, Real.arcosh_eq_zero_iff h1e]; linarith
    exact lt_of_le_of_ne (Real.arcosh_nonneg h1e) (Ne.symm hne)
  have hsmall : ∀ ξ, |ξ| < δ → kkCoeff f m ξ = 0 := fun ξ hξ => by
    refine kkCoeff_eq_zero_of_vanish (fun g hg => h0 g ?_) m
    have : Real.cosh ξ < 1 + ε / 2 := by
      rw [← Real.cosh_arcosh h1e, Real.cosh_lt_cosh, abs_of_nonneg (Real.arcosh_nonneg h1e)]
      exact hξ
    linarith
  -- vanishing far out
  obtain ⟨R, hR⟩ := (hc.isCompact.image continuous_sumSq).isBounded.bddAbove
  have hlarge : ∀ ξ, |R| < |ξ| → kkCoeff f m ξ = 0 := fun ξ hξ => by
    refine kkCoeff_eq_zero_of_vanish (fun g hg => ?_) m
    by_contra hne
    have hle := hR ⟨g, subset_tsupport f hne, rfl⟩
    have hcosh := cosh_ge_half_abs ξ
    have := le_abs_self R
    linarith
  -- the cut to `ξ > 0`
  set H : ℝ → ℂ := fun ξ => if 0 < ξ then kkCoeff f m ξ else 0 with hH
  have hHsmooth : ContDiff ℝ ∞ H := by
    rw [contDiff_iff_contDiffAt]
    intro ξ₀
    by_cases hξ₀ : -δ < ξ₀
    · refine (hk.contDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hξ₀] with ξ hξ
      by_cases hp : 0 < ξ
      · simp [hH, hp]
      · have hlt : |ξ| < δ := by
          rw [abs_lt]; exact ⟨hξ, by push Not at hp; linarith⟩
        simp [hH, hp, hsmall ξ hlt]
    · push Not at hξ₀
      refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℂ)) ξ₀).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds (show ξ₀ < δ by linarith)] with ξ hξ
      by_cases hp : 0 < ξ
      · have hlt : |ξ| < δ := by rw [abs_of_pos hp]; exact hξ
        simp [hH, hp, hsmall ξ hlt]
      · simp [hH, hp]
  have hHc : HasCompactSupport H := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -|R|) (b := |R|)) fun ξ hξ => ?_
    have : |R| < |ξ| := by
      by_contra h
      push Not at h
      exact hξ (abs_le.1 h)
    by_cases hp : 0 < ξ
    · simp [hH, hp, hlarge ξ this]
    · simp [hH, hp]
  have hHsub : tsupport H ⊆ Ioi 0 := by
    refine (closure_minimal (fun ξ hξ => ?_) isClosed_Ici).trans (Ici_subset_Ioi.2 hδ0)
    by_contra hlt
    simp only [mem_Ici, not_le] at hlt
    apply hξ
    by_cases hp : 0 < ξ
    · have : |ξ| < δ := by rw [abs_of_pos hp]; exact hlt
      simp [hH, hp, hsmall ξ this]
    · simp [hH, hp]
  obtain ⟨G, hG, hGc, hGeq⟩ := exists_hLR_eq r l hHsmooth hHc hHsub
  refine ⟨⟨G, hG, hGc⟩, fun ξ hξ => ?_⟩
  have hp : (0 : ℝ) < ξ := hξ
  rw [show ((⟨G, hG, hGc⟩ : smoothCS) : ℝ → ℂ) = G from rfl, Hc_eq_hLR r hG l hp, hGeq ξ hp]
  simp [hH, hp]

end Lightlike.Lorentz.SL2RPlancherel
