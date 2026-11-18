import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A function with zero weak derivative on `(0, 1)` is constant

The du Bois-Reymond lemma on the interval `(0, 1)`: if `v` is integrable on `(0, 1)` and
`∫ ψ' v = 0` for every real smooth `ψ` with compact support inside `(0, 1)`, then `v` is almost everywhere
equal to a constant on `(0, 1)`. Proof: for a fixed bump `φ₀` with `∫ φ₀ = 1`, every such `ψ` gives
`χ = ψ - (∫ ψ) φ₀`, whose primitive `θ` is smooth with compact support inside `(0, 1)`, so
`0 = ∫ θ' v = ∫ ψ v - (∫ ψ) ∫ φ₀ v`, and the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) finishes.
-/

open MeasureTheory Set
open scoped ContDiff

namespace Lightlike.OperatorAlgebras

/-- The primitive `x ↦ ∫₀ˣ χ` of a smooth function `χ` is smooth, with derivative `χ`. -/
lemma primitive_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun x => ∫ t in (0 : ℝ)..x, χ t) := by
  have hd : ∀ x, HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, χ t) (χ x) x := fun x =>
    (hχ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  have : deriv (fun x => ∫ t in (0 : ℝ)..x, χ t) = χ := funext fun x => (hd x).deriv
  rw [this]; exact hχ

/-- The primitive of a function supported in `[a, b] ⊆ (0, ∞)` with zero total integral vanishes outside
`(a, b)`. -/
lemma primitive_zero_outside {χ : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ t, χ t ≠ 0 → t ∈ Icc a b) (hint : ∫ t, χ t = 0) (x : ℝ) (hx : x < a ∨ b < x) :
    ∫ t in (0 : ℝ)..x, χ t = 0 := by
  rcases hx with hx | hx
  · have : ∀ t ∈ Set.uIcc (0 : ℝ) x, χ t = 0 := by
      intro t ht
      by_contra hne
      have h1 := (hs t hne).1
      have h2 : t ≤ max 0 x := by
        rcases Set.mem_uIcc.1 ht with ⟨_, h⟩ | ⟨_, h⟩
        · exact h.trans (le_max_right _ _)
        · exact h.trans (le_max_left _ _)
      have : max 0 x < a := max_lt ha hx
      linarith
    rw [intervalIntegral.integral_congr this]; simp
  · have hb0 : 0 ≤ x := by linarith
    rw [intervalIntegral.integral_of_le hb0, ← hint]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    by_contra hne
    have := hs t hne
    exact ht ⟨by linarith [this.1], by linarith [this.2]⟩

/-- The bump function centred at `1/2` with outer radius `1/4`. -/
noncomputable def bumpB : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The normalized bump function used as `φ₀`: smooth, supported in `[1/4, 3/4]`, total integral one. -/
noncomputable def bump0 : ℝ → ℝ := bumpB.normed volume

lemma bump0_contDiff : ContDiff ℝ ∞ bump0 := bumpB.contDiff_normed

lemma bump0_compact : HasCompactSupport bump0 := bumpB.hasCompactSupport_normed

lemma bump0_integral : ∫ x, bump0 x = 1 := bumpB.integral_normed

lemma bump0_support : Function.support bump0 = Metric.ball (1 / 2 : ℝ) (1 / 4) :=
  bumpB.support_normed_eq

lemma bump0_tsupport : tsupport bump0 ⊆ Ioo (0 : ℝ) 1 := by
  have h : tsupport bump0 ⊆ Metric.closedBall (1 / 2 : ℝ) (1 / 4) := by
    unfold tsupport
    rw [bump0_support]
    exact Metric.closure_ball_subset_closedBall
  refine h.trans fun x hx => ?_
  have := abs_le.1 (by simpa [Real.dist_eq] using Metric.mem_closedBall.1 hx)
  constructor <;> linarith [this.1, this.2]

lemma bump0_mem : (1 / 2 : ℝ) ∈ tsupport bump0 :=
  subset_closure (by rw [bump0_support]; simp [Metric.mem_ball])

/-- A compact subset of `(0, 1)` lies in `[δ, 1 - δ]` for some `δ > 0`. -/
lemma exists_margin {K : Set ℝ} (hK : IsCompact K) (hs : K ⊆ Ioo (0 : ℝ) 1) :
    ∃ δ > 0, ∀ t ∈ K, δ ≤ t ∧ t ≤ 1 - δ := by
  obtain ⟨δ, hδ, hth⟩ := hK.exists_cthickening_subset_open isOpen_Ioo hs
  refine ⟨δ, hδ, fun t ht => ⟨?_, ?_⟩⟩
  · have h1 : t - δ ∈ Ioo (0 : ℝ) 1 := hth (Metric.mem_cthickening_of_dist_le (t - δ) t δ K ht (by
      rw [Real.dist_eq]; simp [abs_of_nonneg hδ.le]))
    linarith [h1.1]
  · have h1 : t + δ ∈ Ioo (0 : ℝ) 1 := hth (Metric.mem_cthickening_of_dist_le (t + δ) t δ K ht (by
      rw [Real.dist_eq]; simp [abs_of_nonneg hδ.le]))
    linarith [h1.2]

/-- **Zero weak derivative on `(0, 1)` implies constant.** -/
theorem weak_const {v : ℝ → ℂ} (hv : IntegrableOn v (Ioo (0 : ℝ) 1))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo (0 : ℝ) 1 →
      ∫ x in Ioo (0 : ℝ) 1, deriv ψ x • v x = 0) :
    ∃ c : ℂ, ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), v x = c := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1) with hμ
  set c : ℂ := ∫ x, bump0 x • v x ∂μ with hc
  refine ⟨c, ?_⟩
  have hvμ : Integrable v μ := hv
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ioo (0 : ℝ) 1 →
      ∫ x, ψ x • (v x - c) ∂μ = 0 := by
    intro ψ hψ hψc hψs
    -- the margin of the compact set `tsupport ψ ∪ tsupport bump0`
    have hK : IsCompact (tsupport ψ ∪ tsupport bump0) := hψc.union bump0_compact
    obtain ⟨δ, hδ, hmar⟩ := exists_margin hK (union_subset hψs bump0_tsupport)
    have hmid := hmar _ (Or.inr bump0_mem)
    have hδ2 : δ ≤ 1 - δ := by linarith [hmid.1, hmid.2]
    set I : ℝ := ∫ x, ψ x with hI
    let χ : ℝ → ℝ := fun x => ψ x - I * bump0 x
    have hχ : ContDiff ℝ ∞ χ := hψ.sub (contDiff_const.mul bump0_contDiff)
    have hψi : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hbi : Integrable bump0 := bump0_contDiff.continuous.integrable_of_hasCompactSupport bump0_compact
    have hint : ∫ t, χ t = 0 := by
      simp only [χ]
      rw [integral_sub hψi (hbi.const_mul I), integral_const_mul, bump0_integral]; simp [hI]
    have hs : ∀ t, χ t ≠ 0 → t ∈ Icc δ (1 - δ) := by
      intro t ht
      by_cases h1 : ψ t = 0
      · have h2 : bump0 t ≠ 0 := fun h2 => ht (by simp [χ, h1, h2])
        exact ⟨(hmar t (Or.inr (subset_tsupport _ h2))).1, (hmar t (Or.inr (subset_tsupport _ h2))).2⟩
      · exact ⟨(hmar t (Or.inl (subset_tsupport _ h1))).1, (hmar t (Or.inl (subset_tsupport _ h1))).2⟩
    let θ : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, χ t
    have hθ : ContDiff ℝ ∞ θ := primitive_contDiff hχ
    have hθ0 : ∀ x, x ∉ Icc δ (1 - δ) → θ x = 0 := fun x hx =>
      primitive_zero_outside hδ hδ2 hs hint x (by
        by_contra hcon
        exact hx ⟨not_lt.1 fun h => hcon (Or.inl h), not_lt.1 fun h => hcon (Or.inr h)⟩)
    have hθsub : tsupport θ ⊆ Icc δ (1 - δ) :=
      closure_minimal (fun x hx => by
        by_contra hxn; exact hx (hθ0 x hxn)) isClosed_Icc
    have hθc : HasCompactSupport θ := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun x hx => by by_contra hxn; exact hx (hθ0 x hxn))
    have hθs : tsupport θ ⊆ Ioo (0 : ℝ) 1 := hθsub.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hderiv : deriv θ = χ := funext fun x => (hχ.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.deriv
    have h0 := h θ hθ hθc hθs
    rw [hderiv] at h0
    have hψv : Integrable (fun x => ψ x • v x) μ := by
      obtain ⟨C, hC⟩ := hψ.continuous.bounded_above_of_compact_support hψc
      exact hvμ.bdd_smul C hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    have hbv : Integrable (fun x => bump0 x • v x) μ := by
      obtain ⟨C, hC⟩ := bump0_contDiff.continuous.bounded_above_of_compact_support bump0_compact
      exact hvμ.bdd_smul C bump0_contDiff.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
    have hsplit : ∫ x, χ x • v x ∂μ = ∫ x, ψ x • v x ∂μ - I • c := by
      have : (fun x => χ x • v x) = fun x => ψ x • v x - I • (bump0 x • v x) := by
        funext x; simp only [χ, sub_smul, mul_smul]
      rw [this]
      exact (integral_sub hψv (hbv.smul I)).trans (by simp only [Pi.smul_apply, integral_smul, hc])
    have hIμ : ∫ x, ψ x ∂μ = I := by
      rw [hμ, hI]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      by_contra hne
      exact hx (hψs (subset_tsupport _ hne))
    have hψc' : Integrable (fun x => ψ x • c) μ := (hψi.restrict).smul_const c
    have hfin : ∫ x, ψ x • (v x - c) ∂μ = ∫ x, ψ x • v x ∂μ - I • c := by
      have : (fun x => ψ x • (v x - c)) = fun x => ψ x • v x - ψ x • c := by
        funext x; exact smul_sub _ _ _
      rw [this, integral_sub hψv hψc', integral_smul_const, hIμ]
    rw [hfin, ← hsplit]; exact h0
  have hf : LocallyIntegrableOn (fun x => v x - c) (Ioo (0 : ℝ) 1) μ :=
    (hvμ.sub (integrable_const c)).locallyIntegrable.locallyIntegrableOn _
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf
    (fun g hg hc hs => key g hg hc hs)
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxU
  exact sub_eq_zero.1 (hx hxU)

end Lightlike.OperatorAlgebras
