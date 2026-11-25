module

public import Lightlike.Lorentz.SL2RPlancherel.AbelTransformDeriv

/-!
# The Abel transform intertwines the radial Laplacian

For `F` smooth with compact support, the half-order Abel operator `H = halfAbel F` satisfies
`halfAbel (Q F) = (1/4) H - ((x² - 1) H'' + x H')` with `Q F = -((v² - 1) F')'` the radial Laplacian in the variable
`v = cosh ξ` (Helgason, *Groups and Geometric Analysis*, Ch. III): in the variable `x = cosh t` the bracket is `∂_t²`, so
`𝒜 (Q F) = (1/4 - ∂_t²) 𝒜 F`. The proof integrates by parts in the Abel variable `w`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology Metric

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- A power times a compactly supported continuous function is integrable on `(0, ∞)` when the exponent exceeds `-1`. -/
lemma integrableOn_rpow_mul_compact {s : ℝ} (hs : -1 < s) {g : ℝ → ℂ} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    IntegrableOn (fun w : ℝ => ((w ^ s : ℝ) : ℂ) * g w) (Ioi (0 : ℝ)) := by
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hsupp : ∀ w : ℝ, g w ≠ 0 → |w| ≤ R := by
    intro w hw
    have hmem : w ∈ tsupport g := subset_tsupport g hw
    have := hR₀ hmem
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hzero : ∀ w ∈ Ioi R, ((w ^ s : ℝ) : ℂ) * g w = 0 := by
    intro w hw
    have hw' : R < w := hw
    have : g w = 0 := by
      by_contra hne
      have := hsupp w hne
      rw [abs_of_pos (lt_of_le_of_lt hR0 hw')] at this
      linarith
    simp [this]
  have h1 : IntegrableOn (fun w : ℝ => ((w ^ s : ℝ) : ℂ) * g w) (Icc 0 R) := by
    have hrp : IntegrableOn (fun w : ℝ => w ^ s) (Ioc 0 R) := by
      have := (intervalIntegral.intervalIntegrable_rpow' hs (a := 0) (b := R)).1
      simpa [intervalIntegrable_iff_integrableOn_Ioc_of_le hR0] using this
    have hrp' : IntegrableOn (fun w : ℝ => w ^ s) (Icc 0 R) := by
      rwa [integrableOn_Icc_iff_integrableOn_Ioc]
    have hrc : IntegrableOn (fun w : ℝ => ((w ^ s : ℝ) : ℂ)) (Icc 0 R) := hrp'.ofReal
    exact hrc.mul_continuousOn hg.continuousOn isCompact_Icc
  have h2 : IntegrableOn (fun w : ℝ => ((w ^ s : ℝ) : ℂ) * g w) (Ioc 0 R) := h1.mono_set Ioc_subset_Icc_self
  have h3 : IntegrableOn (fun w : ℝ => ((w ^ s : ℝ) : ℂ) * g w) (Ioi R) :=
    (integrableOn_zero).congr_fun (fun w hw => (hzero w hw).symm) measurableSet_Ioi
  have : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := by
    ext w; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hw; by_cases h : w ≤ R
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr (not_le.1 h)
    · rintro (⟨h, -⟩ | h)
      · exact h
      · exact lt_of_le_of_lt hR0 h
  rw [this]
  exact h2.union h3

/-- A translate of a compactly supported function vanishes for large `w`. -/
lemma eventually_zero_translate {f : ℝ → ℂ} (hc : HasCompactSupport f) (x : ℝ) :
    ∀ᶠ w in atTop, f (x + w) = 0 := by
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
  filter_upwards [eventually_gt_atTop (|R₀| + |x|)] with w hw
  by_contra hne
  have hmem : x + w ∈ tsupport f := subset_tsupport f hne
  have := hR₀ hmem
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have h1 : w - |x| ≤ |x + w| := by
    have := abs_sub_abs_le_abs_sub w (-x)
    rw [abs_neg] at this
    have h2 : |w| - |x| ≤ |w - -x| := this
    rw [sub_neg_eq_add, add_comm] at h2
    have : w ≤ |w| := le_abs_self w
    linarith
  linarith [le_abs_self R₀]

/-- **Integration by parts against `w^p`**: for `f` of class `C¹` with compact support and `p > 0`,
`∫_{w>0} w^p f'(x+w) dw = -p ∫_{w>0} w^{p-1} f(x+w) dw`. -/
theorem integral_rpow_mul_deriv {p : ℝ} (hp : 0 < p) {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (x : ℝ) :
    ∫ w in Ioi (0 : ℝ), ((w ^ p : ℝ) : ℂ) * deriv f (x + w) =
      -(p : ℂ) * ∫ w in Ioi (0 : ℝ), ((w ^ (p - 1) : ℝ) : ℂ) * f (x + w) := by
  have hfd : ∀ y, HasDerivAt f (deriv f y) y := fun y => (hf.differentiable one_ne_zero y).hasDerivAt
  have hu : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt (fun w : ℝ => ((w ^ p : ℝ) : ℂ)) (((p * w ^ (p - 1) : ℝ)) : ℂ) w :=
    fun w hw => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hw))).ofReal_comp
  have hv : ∀ w ∈ Ioi (0 : ℝ), HasDerivAt (fun w : ℝ => f (x + w)) (deriv f (x + w)) w := fun w _ => by
    exact HasDerivAt.comp_const_add x w (hfd (x + w))
  have hf'c : Continuous (fun w : ℝ => deriv f (x + w)) :=
    (hf.continuous_deriv le_rfl).comp (continuous_const.add continuous_id)
  have hfc : Continuous (fun w : ℝ => f (x + w)) := hf.continuous.comp (continuous_const.add continuous_id)
  have hcomp1 : HasCompactSupport (fun w : ℝ => deriv f (x + w)) := by
    have := (hc.deriv).comp_homeomorph (Homeomorph.addLeft x)
    exact this
  have hcomp0 : HasCompactSupport (fun w : ℝ => f (x + w)) := hc.comp_homeomorph (Homeomorph.addLeft x)
  have huv' : IntegrableOn ((fun w : ℝ => ((w ^ p : ℝ) : ℂ)) * fun w => deriv f (x + w)) (Ioi 0) :=
    integrableOn_rpow_mul_compact (by linarith) hf'c hcomp1
  have hu'v : IntegrableOn ((fun w : ℝ => (((p * w ^ (p - 1) : ℝ)) : ℂ)) * fun w => f (x + w)) (Ioi 0) := by
    have h0 := integrableOn_rpow_mul_compact (s := p - 1) (by linarith) hfc hcomp0
    have h1 : IntegrableOn (fun w : ℝ => (p : ℂ) * (((w ^ (p - 1) : ℝ) : ℂ) * f (x + w))) (Ioi (0 : ℝ)) :=
      MeasureTheory.Integrable.const_mul h0 (p : ℂ)
    exact MeasureTheory.IntegrableOn.congr_fun h1 (fun w _ => by simp only [Pi.mul_apply]; push_cast; ring)
      measurableSet_Ioi
  have hzero : Tendsto ((fun w : ℝ => ((w ^ p : ℝ) : ℂ)) * fun w => f (x + w)) (𝓝[>] 0) (𝓝 0) := by
    have hu0 : ContinuousAt (fun w : ℝ => ((w ^ p : ℝ) : ℂ)) 0 :=
      (Complex.continuous_ofReal.continuousAt).comp (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
    have := (hu0.mul hfc.continuousAt).tendsto
    simp only [Pi.mul_apply, Real.zero_rpow hp.ne', Complex.ofReal_zero, zero_mul] at this ⊢
    exact this.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun w : ℝ => ((w ^ p : ℝ) : ℂ)) * fun w => f (x + w)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_zero_translate hc x] with w hw
    simp [Pi.mul_apply, hw]
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
  have h2 : ∫ w in Ioi (0 : ℝ), (((p * w ^ (p - 1) : ℝ)) : ℂ) * f (x + w) =
      (p : ℂ) * ∫ w in Ioi (0 : ℝ), ((w ^ (p - 1) : ℝ) : ℂ) * f (x + w) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    push_cast; ring
  rw [key, sub_self, zero_sub, h2, neg_mul]

/-- The basic integrals `J s g = ∫_{w>0} w^s g(x + w) dw` of the Abel calculus. -/
def absJ (s : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ := ∫ w in Ioi (0 : ℝ), ((w ^ s : ℝ) : ℂ) * g (x + w)

/-- Integrability of the basic integrals. -/
lemma integrableOn_absJ {s : ℝ} (hs : -1 < s) {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) (x : ℝ) :
    IntegrableOn (fun w : ℝ => ((w ^ s : ℝ) : ℂ) * g (x + w)) (Ioi (0 : ℝ)) :=
  integrableOn_rpow_mul_compact hs (hg.comp (continuous_const.add continuous_id))
    (hc.comp_homeomorph (Homeomorph.addLeft x))

/-- `halfAbel f x = J (-1/2) f x`. -/
lemma halfAbel_eq_absJ (f : ℝ → ℂ) (x : ℝ) : halfAbel f x = absJ (-(1 / 2)) f x := by
  unfold halfAbel absJ
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [Complex.real_smul]

/-- **The half-order Abel operator intertwines the radial Laplacian**: for `F` of class `C²` with compact support and
`Q F = -((v² - 1) F'' + 2 v F')`,
`halfAbel (Q F) x = (1/4) halfAbel F x - ((x² - 1) halfAbel F'' x + x halfAbel F' x)`. -/
theorem halfAbel_casimir {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) (x : ℝ) :
    halfAbel (fun v : ℝ => -((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv F) v + ((2 * v : ℝ) : ℂ) * deriv F v)) x =
      (1 / 4 : ℂ) * halfAbel F x -
        ((((x ^ 2 - 1 : ℝ)) : ℂ) * halfAbel (deriv (deriv F)) x + (x : ℂ) * halfAbel (deriv F) x) := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hF1d : ContDiff ℝ 1 (deriv F) := by
    have h : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) F := by simpa using hF
    exact ((contDiff_succ_iff_deriv (n := 1)).1 h).2.2
  have hFc : Continuous F := hF.continuous
  have hF1c : Continuous (deriv F) := hF1.continuous_deriv le_rfl
  have hF2c : Continuous (deriv (deriv F)) := hF1d.continuous_deriv le_rfl
  have hc1 : HasCompactSupport (deriv F) := hc.deriv
  have hc2 : HasCompactSupport (deriv (deriv F)) := hc1.deriv
  -- integration by parts
  have hb : absJ (1 / 2) (deriv (deriv F)) x = -(1 / 2 : ℂ) * absJ (-(1 / 2)) (deriv F) x := by
    have := integral_rpow_mul_deriv (p := 1 / 2) (by norm_num) hF1d hc1 x
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at this
    simpa only [absJ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using this
  have hc3 : absJ (3 / 2) (deriv (deriv F)) x = -(3 / 2 : ℂ) * absJ (1 / 2) (deriv F) x := by
    have := integral_rpow_mul_deriv (p := 3 / 2) (by norm_num) hF1d hc1 x
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num] at this
    simpa only [absJ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using this
  have he : absJ (1 / 2) (deriv F) x = -(1 / 2 : ℂ) * absJ (-(1 / 2)) F x := by
    have := integral_rpow_mul_deriv (p := 1 / 2) (by norm_num) hF1 hc x
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num] at this
    simpa only [absJ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using this
  -- the five basic integrals of the left-hand side
  have i1 := integrableOn_absJ (s := -(1 / 2)) (by norm_num) hF2c hc2 x
  have i2 := integrableOn_absJ (s := 1 / 2) (by norm_num) hF2c hc2 x
  have i3 := integrableOn_absJ (s := 3 / 2) (by norm_num) hF2c hc2 x
  have i4 := integrableOn_absJ (s := -(1 / 2)) (by norm_num) hF1c hc1 x
  have i5 := integrableOn_absJ (s := 1 / 2) (by norm_num) hF1c hc1 x
  have hLHS : halfAbel (fun v : ℝ => -((((v ^ 2 - 1 : ℝ)) : ℂ) * deriv (deriv F) v + ((2 * v : ℝ) : ℂ) * deriv F v)) x =
      (-(((x ^ 2 - 1 : ℝ)) : ℂ)) * absJ (-(1 / 2)) (deriv (deriv F)) x
        + (-(2 * x : ℂ)) * absJ (1 / 2) (deriv (deriv F)) x
        + (-1 : ℂ) * absJ (3 / 2) (deriv (deriv F)) x
        + (-(2 * x : ℂ)) * absJ (-(1 / 2)) (deriv F) x
        + (-2 : ℂ) * absJ (1 / 2) (deriv F) x := by
    rw [halfAbel_eq_absJ]
    have key : ∀ a b c d e : ℂ,
        ∫ w in Ioi (0 : ℝ), (a * (((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * deriv (deriv F) (x + w))
          + b * (((w ^ (1 / 2 : ℝ)) : ℝ) * deriv (deriv F) (x + w))
          + c * (((w ^ (3 / 2 : ℝ)) : ℝ) * deriv (deriv F) (x + w))
          + d * (((w ^ (-(1 / 2 : ℝ))) : ℝ) * deriv F (x + w))
          + e * (((w ^ (1 / 2 : ℝ)) : ℝ) * deriv F (x + w)))
        = a * absJ (-(1 / 2)) (deriv (deriv F)) x + b * absJ (1 / 2) (deriv (deriv F)) x
          + c * absJ (3 / 2) (deriv (deriv F)) x + d * absJ (-(1 / 2)) (deriv F) x
          + e * absJ (1 / 2) (deriv F) x := by
      intro a b c d e
      have s12 : IntegrableOn (fun w : ℝ => a * (((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * deriv (deriv F) (x + w))
          + b * (((w ^ (1 / 2 : ℝ)) : ℝ) * deriv (deriv F) (x + w))) (Ioi (0 : ℝ)) :=
        (i1.const_mul a).add (i2.const_mul b)
      have s123 : IntegrableOn (fun w : ℝ => a * (((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * deriv (deriv F) (x + w))
          + b * (((w ^ (1 / 2 : ℝ)) : ℝ) * deriv (deriv F) (x + w))
          + c * (((w ^ (3 / 2 : ℝ)) : ℝ) * deriv (deriv F) (x + w))) (Ioi (0 : ℝ)) :=
        s12.add (i3.const_mul c)
      have s1234 : IntegrableOn (fun w : ℝ => a * (((w ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * deriv (deriv F) (x + w))
          + b * (((w ^ (1 / 2 : ℝ)) : ℝ) * deriv (deriv F) (x + w))
          + c * (((w ^ (3 / 2 : ℝ)) : ℝ) * deriv (deriv F) (x + w))
          + d * (((w ^ (-(1 / 2 : ℝ))) : ℝ) * deriv F (x + w))) (Ioi (0 : ℝ)) :=
        s123.add (i4.const_mul d)
      rw [integral_add s1234 (i5.const_mul e), integral_add s123 (i4.const_mul d),
        integral_add s12 (i3.const_mul c), integral_add (i1.const_mul a) (i2.const_mul b)]
      simp only [integral_const_mul, absJ]
    rw [← key]
    unfold absJ
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    have hw0 : 0 < w := hw
    have e1 : (w ^ (1 / 2 : ℝ) : ℝ) = w * w ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_one_add' hw0.le (by norm_num)]; norm_num
    have e2 : (w ^ (3 / 2 : ℝ) : ℝ) = w * w ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_one_add' hw0.le (by norm_num)]; norm_num
    simp only [e2, e1]
    push_cast
    ring
  rw [hLHS, hb, hc3, he, halfAbel_eq_absJ, halfAbel_eq_absJ, halfAbel_eq_absJ]
  push_cast
  ring

end Lightlike.Lorentz.SL2RPlancherel
