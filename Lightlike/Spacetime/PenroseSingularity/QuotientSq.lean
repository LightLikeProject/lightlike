import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The quotient `h (s) / s²` of a function with vanishing value and derivative (G1-012, step D4)

If `h (0) = 0`, `h' (0) = 0` and `h'` has derivative `c` at `0`, then `h (s) / s² → c / 2` as `s → 0`; the
vector-valued version follows componentwise.
-/

open Set Filter Topology

namespace Lightlike.Penrose

/-- **Second-order quotient (scalar).** -/
theorem tendsto_div_sq {f f' : ℝ → ℝ} {c : ℝ} (hf : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt f (f' x) x)
    (hf0 : f 0 = 0) (hf'0 : f' 0 = 0) (hc : HasDerivAt f' c 0) :
    Tendsto (fun x => f x / x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (c / 2)) := by
  have hcont : ContinuousAt f 0 := (hf.self_of_nhds).continuousAt
  have hfa : Tendsto f (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := hcont.tendsto
    rw [hf0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun x : ℝ => x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have : Continuous (fun x : ℝ => x ^ 2) := by fun_prop
    have h := this.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hgg' : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x :=
    Filter.Eventually.of_forall fun x => by simpa using hasDerivAt_pow 2 x
  have hg' : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 2 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero two_ne_zero hx
  have hdiv : Tendsto (fun x => f' x / (2 * x)) (𝓝[≠] (0 : ℝ)) (𝓝 (c / 2)) := by
    have hs := (hasDerivAt_iff_tendsto_slope.1 hc)
    have h2 : Tendsto (fun x => (1 / 2 : ℝ) * slope f' 0 x) (𝓝[≠] (0 : ℝ)) (𝓝 ((1 / 2) * c)) :=
      hs.const_mul _
    have h3 : (1 / 2 : ℝ) * c = c / 2 := by ring
    rw [h3] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x ≠ 0 := hx
    simp only [slope_def_field, hf'0, sub_zero]
    field_simp
  exact HasDerivAt.lhopital_zero_nhdsNE (hf.filter_mono nhdsWithin_le_nhds) hgg' hg' hfa hga hdiv

/-- **Second-order quotient (vector valued).** If `h (0) = 0`, `h' (0) = 0` and `h'` has derivative `c` at `0`,
then `h s = s² d s` for a function `d` that is continuous at `0` with `d 0 = c / 2`. -/
theorem exists_continuousAt_quot_sq {n : ℕ} {h h' : ℝ → Fin n → ℝ} {c : Fin n → ℝ}
    (hh : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt h (h' x) x) (h0 : h 0 = 0) (h'0 : h' 0 = 0)
    (hc : HasDerivAt h' c 0) :
    ∃ d : ℝ → Fin n → ℝ, (∀ s, h s = s ^ 2 • d s) ∧ ContinuousAt d 0 ∧ d 0 = (1 / 2 : ℝ) • c := by
  classical
  refine ⟨fun s => if s = 0 then (1 / 2 : ℝ) • c else (s ^ 2)⁻¹ • h s, fun s => ?_, ?_, by simp⟩
  · by_cases hs : s = 0
    · subst hs; simp [h0]
    · simp [hs]
  · rw [ContinuousAt, tendsto_pi_nhds]
    intro i
    have hi : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (fun x => h x i) (h' x i) x :=
      hh.mono fun x hx => (hasDerivAt_pi.1 hx) i
    have hc' : HasDerivAt (fun x => h' x i) (c i) 0 := (hasDerivAt_pi.1 hc) i
    have hq := tendsto_div_sq hi (by simp [h0]) (by simp [h'0]) hc'
    have hq' : Tendsto (fun x => (if x = 0 then (1 / 2 : ℝ) • c else (x ^ 2)⁻¹ • h x) i) (𝓝[≠] (0 : ℝ))
        (𝓝 (c i / 2)) := by
      refine hq.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x ≠ 0 := hx
      simp [hx', div_eq_inv_mul]
    have hval : (if (0 : ℝ) = 0 then (1 / 2 : ℝ) • c else ((0 : ℝ) ^ 2)⁻¹ • h 0) i = c i / 2 := by
      simp; ring
    rw [hval]
    rw [← nhdsNE_sup_pure (0 : ℝ), tendsto_sup]
    refine ⟨hq', ?_⟩
    rw [tendsto_pure_left]
    intro x hx
    have hmem := mem_of_mem_nhds hx
    rw [hval]
    exact hmem

end Lightlike.Penrose
