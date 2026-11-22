import Mathlib

/-!
# The double primitive in null coordinates

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For `g : ℝ × ℝ → ℝ` continuous with compact support put
`quadPrim g (a, b) = ∫_{a' ≤ a, b' ≤ b} g (a', b')`.  This is the building block of the retarded
Green operator of the massless wave equation on `1+1` Minkowski space (in null coordinates
`a = t - x`, `b = t + x` the operator `-∂ₜ² + ∂ₓ²` is `-4 ∂ₐ ∂_b`).

Main results: `quadPrim_contDiff` (smoothness, via convolution with the indicator of a quadrant),
`fderiv_quadPrim_fst` (`∂ₐ` of the primitive is `∫_{b' ≤ b} g(a, b') db'`),
`fderiv_fderiv_quadPrim` (`∂_b ∂ₐ` of the primitive is `g`), and `quadPrim_eq_zero`.

This is a supporting result; no catalogue entry.
-/

open Set MeasureTheory
open scoped Convolution

namespace Lightlike.GreenOperators

/-- The double primitive `∫_{q ≤ p} g q` over the lower-left quadrant of `p`. -/
noncomputable def quadPrim (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := ∫ q in Iic p, g q

/-- The primitive vanishes if `g` vanishes on the lower-left quadrant of `p`. -/
lemma quadPrim_eq_zero {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : ∀ q, q ≤ p → g q = 0) :
    quadPrim g p = 0 :=
  setIntegral_eq_zero_of_forall_eq_zero fun q hq => h q hq

/-- The indicator of the closed upper-right quadrant. -/
noncomputable def quadKernel : ℝ × ℝ → ℝ := (Ici (0 : ℝ × ℝ)).indicator fun _ => (1 : ℝ)

lemma quadPrim_eq_convolution (g : ℝ × ℝ → ℝ) :
    quadPrim g = quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
  funext p
  rw [convolution_def]
  unfold quadPrim
  have h1 : ∀ t : ℝ × ℝ, (ContinuousLinearMap.lsmul ℝ ℝ) (quadKernel t) (g (p - t))
      = (Iic p).indicator g (p - t) := by
    intro t
    by_cases ht : (0 : ℝ × ℝ) ≤ t
    · have : p - t ≤ p := sub_le_self _ ht
      simp [quadKernel, ht, this, indicator_of_mem]
    · have : ¬ p - t ≤ p := fun h => ht (by simpa using h)
      simp [quadKernel, ht, this]
  simp_rw [h1]
  rw [integral_sub_left_eq_self (fun q => (Iic p).indicator g q) volume p,
    integral_indicator measurableSet_Iic]

lemma quadKernel_locallyIntegrable : LocallyIntegrable quadKernel (volume : Measure (ℝ × ℝ)) :=
  (locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Ici

/-- The double primitive of a `Cⁿ` function with compact support is `Cⁿ`. -/
theorem quadPrim_contDiff {n : ℕ∞} {g : ℝ × ℝ → ℝ} (hcg : HasCompactSupport g)
    (hg : ContDiff ℝ n g) : ContDiff ℝ n (quadPrim g) := by
  rw [quadPrim_eq_convolution]
  exact hcg.contDiff_convolution_right _ quadKernel_locallyIntegrable hg

/-- A compactly supported function vanishes outside a box. -/
lemma exists_box {g : ℝ × ℝ → ℝ} (hcg : HasCompactSupport g) :
    ∃ R : ℝ, ∀ q : ℝ × ℝ, g q ≠ 0 → |q.1| < R ∧ |q.2| < R := by
  obtain ⟨r, hr⟩ := hcg.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨r + 1, fun q hq => ?_⟩
  have hq' : q ∈ tsupport g := subset_tsupport g hq
  have := hr hq'
  rw [mem_closedBall_zero_iff] at this
  have h1 : |q.1| ≤ ‖q‖ := by simpa using norm_fst_le q
  have h2 : |q.2| ≤ ‖q‖ := by simpa using norm_snd_le q
  constructor <;> linarith

/-- A function vanishing on `(-∞, -R]` has the same integral over `(-∞, b]` as over `[-R, b]`
(oriented). -/
lemma integral_Iic_eq_intervalIntegral {h : ℝ → ℝ} {R : ℝ} (hz : ∀ x, x ≤ -R → h x = 0) (b : ℝ) :
    ∫ x in Iic b, h x = ∫ x in (-R)..b, h x := by
  rcases le_or_gt (-R) b with hb | hb
  · rw [intervalIntegral.integral_of_le hb]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic Ioc_subset_Iic_self
      (fun x hx => hz x ?_)
    by_contra hc
    exact hx.2 ⟨not_le.mp hc, hx.1⟩
  · have e1 : ∫ x in Iic b, h x = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hz x (le_trans hx hb.le))
    have e2 : ∫ x in Ioc b (-R), h x = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hz x hx.2)
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hb.le, e1, e2]
    simp

/-- Iterated-integral form of the double primitive, for `g` supported in the box `|q₁|,|q₂| < R`. -/
lemma quadPrim_eq_iterated {g : ℝ × ℝ → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    {R : ℝ} (hR : ∀ q : ℝ × ℝ, g q ≠ 0 → |q.1| < R ∧ |q.2| < R) (p : ℝ × ℝ) :
    quadPrim g p = ∫ a in (-R)..p.1, ∫ b in (-R)..p.2, g (a, b) := by
  have hset : Iic p = Iic p.1 ×ˢ Iic p.2 := by
    ext q; simp [Prod.le_def]
  have hint : IntegrableOn g (Iic p.1 ×ˢ Iic p.2) (volume : Measure (ℝ × ℝ)) :=
    (hg.integrable_of_hasCompactSupport hcg).integrableOn
  rw [Measure.volume_eq_prod] at hint
  unfold quadPrim
  rw [hset, Measure.volume_eq_prod, setIntegral_prod _ hint]
  have h1 : ∀ a, ∫ b in Iic p.2, g (a, b) = ∫ b in (-R)..p.2, g (a, b) := by
    intro a
    refine integral_Iic_eq_intervalIntegral (fun b hb => ?_) p.2
    by_contra hc
    have := (hR _ hc).2
    simp only at this
    rw [abs_lt] at this
    linarith [this.1]
  simp_rw [h1]
  refine integral_Iic_eq_intervalIntegral (fun a ha => ?_) p.1
  have h0 : ∀ b, g (a, b) = 0 := by
    intro b
    by_contra hc
    have := (hR _ hc).1
    simp only at this
    rw [abs_lt] at this
    linarith [this.1]
  simp [h0]

/-- `∂ₐ` of the double primitive is the single primitive `∫_{b' ≤ b} g(a, b') db'`. -/
theorem fderiv_quadPrim_fst {g : ℝ × ℝ → ℝ} (hcg : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {R : ℝ} (hR : ∀ q : ℝ × ℝ, g q ≠ 0 → |q.1| < R ∧ |q.2| < R) (p : ℝ × ℝ) :
    fderiv ℝ (quadPrim g) p ((1 : ℝ), (0 : ℝ)) = ∫ b in (-R)..p.2, g (p.1, b) := by
  have hc : Continuous g := hg.continuous
  have hu : ContDiff ℝ 2 (quadPrim g) := by
    have := quadPrim_contDiff (n := 2) hcg (by exact_mod_cast hg)
    exact_mod_cast this
  have hd : Differentiable ℝ (quadPrim g) := hu.differentiable (by norm_num)
  have h1 : HasDerivAt (fun a => quadPrim g (a, p.2)) (fderiv ℝ (quadPrim g) p ((1 : ℝ), (0 : ℝ)))
      p.1 := by
    have hl : HasFDerivAt (quadPrim g) (fderiv ℝ (quadPrim g) p) (p.1, p.2) := (hd p).hasFDerivAt
    have hf : HasDerivAt (fun a : ℝ => (a, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const _ _)
    exact hl.comp_hasDerivAt p.1 hf
  have hV : Continuous (fun a : ℝ => ∫ b in (-R)..p.2, g (a, b)) :=
    (intervalIntegral.continuous_parametric_primitive_of_continuous (a₀ := -R) (f := fun a b => g (a, b))
      (hc.comp (by fun_prop))).comp (by fun_prop : Continuous fun a : ℝ => (a, p.2))
  have h2 : HasDerivAt (fun a => ∫ a' in (-R)..a, ∫ b in (-R)..p.2, g (a', b))
      (∫ b in (-R)..p.2, g (p.1, b)) p.1 :=
    (hV.integral_hasStrictDerivAt (-R) p.1).hasDerivAt
  have h3 : (fun a => quadPrim g (a, p.2))
      = fun a => ∫ a' in (-R)..a, ∫ b in (-R)..p.2, g (a', b) :=
    funext fun a => quadPrim_eq_iterated hc hcg hR (a, p.2)
  rw [h3] at h1
  exact h1.unique h2

/-- `∂_b ∂ₐ` of the double primitive is `g`: `D²u (0,1) (1,0) = g`. -/
theorem fderiv_fderiv_quadPrim {g : ℝ × ℝ → ℝ} (hcg : HasCompactSupport g) (hg : ContDiff ℝ 2 g)
    {R : ℝ} (hR : ∀ q : ℝ × ℝ, g q ≠ 0 → |q.1| < R ∧ |q.2| < R) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (quadPrim g)) p ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) = g p := by
  have hc : Continuous g := hg.continuous
  have hu : ContDiff ℝ 2 (quadPrim g) := by
    have := quadPrim_contDiff (n := 2) hcg (by exact_mod_cast hg)
    exact_mod_cast this
  have hG : Differentiable ℝ (fderiv ℝ (quadPrim g)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hl : HasFDerivAt (fderiv ℝ (quadPrim g)) (fderiv ℝ (fderiv ℝ (quadPrim g)) p) (p.1, p.2) :=
    (hG p).hasFDerivAt
  have hf : HasDerivAt (fun b : ℝ => (p.1, b)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id p.2)
  have h3 := hl.comp_hasDerivAt p.2 hf
  have h4 := (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))
    : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt p.2 h3
  have h5 : HasDerivAt (fun b => ∫ b' in (-R)..b, g (p.1, b')) (g p) p.2 := by
    have := (Continuous.integral_hasStrictDerivAt (hc.comp (by fun_prop : Continuous
      fun b : ℝ => (p.1, b))) (-R) p.2).hasDerivAt
    simpa using this
  have h6 : (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ)) : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ)
      ∘ (fderiv ℝ (quadPrim g)) ∘ (fun b : ℝ => (p.1, b))
      = fun b => ∫ b' in (-R)..b, g (p.1, b') := by
    funext b
    simp only [Function.comp, ContinuousLinearMap.apply_apply]
    exact fderiv_quadPrim_fst hcg hg hR (p.1, b)
  rw [h6] at h4
  exact h4.unique h5

end Lightlike.GreenOperators
