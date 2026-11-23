import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PhiRangeComplex

/-!
# Cutoff approximation of an even Schwartz function in `H¹`

For an even Schwartz function `h` and `δ > 0` there is an even, compactly supported Schwartz
function `g` with `‖h - g‖² + ‖(h - g)'‖² ≤ δ` (`exists_cutoff_approx`): take `g = χ(t/R) h`
for a smooth even bump `χ` and `R` large (step S6 of the surjectivity programme for
`sphericalL2`, milestone HA3).
-/

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

theorem integrable_norm_sq_schwartz (S : SchwartzMap ℝ ℂ) :
    Integrable (fun x => ‖S x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm S.continuous.aestronglyMeasurable).1 (S.memLp 2)

/-- Tails of an integrable function tend to zero. -/
theorem tendsto_tail_integral (w : ℝ → ℝ) (hw : Integrable w) :
    Tendsto (fun R : ℝ => ∫ t, {t : ℝ | R ≤ |t|}.indicator w t) atTop (𝓝 0) := by
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun (R : ℝ) t => {t : ℝ | R ≤ |t|}.indicator w t) (f := fun _ => (0 : ℝ))
    (fun t => ‖w t‖) ?_ ?_ hw.norm ?_
  · simpa using key
  · refine Eventually.of_forall fun R => ?_
    exact hw.1.indicator (measurableSet_le measurable_const measurable_id.abs)
  · exact Eventually.of_forall fun R => Eventually.of_forall fun t =>
      norm_indicator_le_norm_self _ _
  · refine Eventually.of_forall fun t => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop |t|] with R hR
    rw [indicator_of_notMem]
    intro hm
    exact absurd hm (not_le.2 hR)

/-- The cutoff function `t ↦ χ(t/R)`, with `χ` a smooth even bump equal to `1` on `[-1,1]` and
supported in `[-2,2]`. -/
def chi : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

theorem chi_even (t : ℝ) : chi (-t) = chi t := ContDiffBump.neg chi t

theorem chi_eq_one {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ R) : chi (R⁻¹ * s) = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hR,
    ← div_eq_inv_mul]
  show |s| / R ≤ 1
  rw [div_le_one hR]
  exact hs

theorem chi_eq_zero {R s : ℝ} (hR : 0 < R) (hs : 2 * R ≤ |s|) : chi (R⁻¹ * s) = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hR, ← div_eq_inv_mul,
    le_div_iff₀ hR]
  show 2 * R ≤ |s|
  exact hs

/-- The cutoff product `t ↦ χ(t/R) h(t)`. -/
def cutFun (h : SchwartzMap ℝ ℂ) (R : ℝ) (t : ℝ) : ℂ := ((chi (R⁻¹ * t) : ℝ) : ℂ) * h t

theorem contDiff_cutFun (h : SchwartzMap ℝ ℂ) (R : ℝ) : ContDiff ℝ ∞ (cutFun h R) := by
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => chi (R⁻¹ * t)) :=
    chi.contDiff.comp (contDiff_const.mul contDiff_id)
  exact (Complex.ofRealCLM.contDiff.comp h1).mul (h.smooth (⊤ : ℕ∞))

theorem hasCompactSupport_cutFun (h : SchwartzMap ℝ ℂ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (cutFun h R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * R)) fun t ht => ?_
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, not_le] at ht
  simp [cutFun, chi_eq_zero hR ht.le]

theorem cutFun_even (h : SchwartzMap ℝ ℂ) (he : ∀ t, h (-t) = h t) (R : ℝ) (t : ℝ) :
    cutFun h R (-t) = cutFun h R t := by
  simp [cutFun, he t, chi_even]

theorem cutFun_eq_of_abs_le (h : SchwartzMap ℝ ℂ) {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ R) :
    cutFun h R s = h s := by
  simp [cutFun, chi_eq_one hR hs]

theorem hasDerivAt_sub_cutFun (h : SchwartzMap ℝ ℂ) (R : ℝ) (t : ℝ) :
    HasDerivAt (fun t => h t - cutFun h R t)
      ((1 - ((chi (R⁻¹ * t) : ℝ) : ℂ)) * deriv h t
        - (((R⁻¹ * deriv chi (R⁻¹ * t) : ℝ)) : ℂ) * h t) t := by
  have h1 : HasDerivAt (fun t : ℝ => R⁻¹ * t) R⁻¹ t := by
    simpa using (hasDerivAt_id t).const_mul R⁻¹
  have hc : HasDerivAt (fun t : ℝ => chi (R⁻¹ * t)) (deriv chi (R⁻¹ * t) * R⁻¹) t :=
    HasDerivAt.comp (h₂ := (chi : ℝ → ℝ)) t
      (((chi.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt.hasDerivAt) h1
  have hc' := hc.ofReal_comp
  have hh : HasDerivAt h (deriv h t) t := h.differentiableAt.hasDerivAt
  have := hh.sub (hc'.mul hh)
  refine this.congr_deriv ?_
  push_cast
  ring

/-- **Cutoff approximation (S6)**: an even Schwartz function is approximated in `H¹` by even
compactly supported Schwartz functions. -/
theorem exists_cutoff_approx (h : SchwartzMap ℝ ℂ) (he : ∀ t, h (-t) = h t) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ g : SchwartzMap ℝ ℂ, (∀ t, g (-t) = g t) ∧ HasCompactSupport g ∧
      (∫ x, ‖(h - g) x‖ ^ 2) + ∫ x, ‖deriv (⇑(h - g)) x‖ ^ 2 ≤ δ := by
  obtain ⟨M, hM⟩ := ((chi.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
    chi.hasCompactSupport.deriv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set w : ℝ → ℝ := fun t => ‖h t‖ ^ 2 + ‖deriv h t‖ ^ 2 with hwdef
  have hdint : Integrable (fun x => ‖deriv h x‖ ^ 2) := by
    have := integrable_norm_sq_schwartz (SchwartzMap.derivCLM ℂ ℂ h)
    simpa only [SchwartzMap.derivCLM_apply] using this
  have hw : Integrable w := (integrable_norm_sq_schwartz h).add hdint
  set K : ℝ := 2 + 2 * M ^ 2 with hK
  have hK0 : 0 < 1 + K := by positivity
  have key := (tendsto_order.1 (tendsto_tail_integral w hw)).2 (δ / (1 + K)) (by positivity)
  obtain ⟨R, hR1, hRI⟩ := ((eventually_ge_atTop (1 : ℝ)).and key).exists
  have hR : 0 < R := by linarith
  set I : ℝ := ∫ t, {t : ℝ | R ≤ |t|}.indicator w t with hI
  have hind : Integrable ({t : ℝ | R ≤ |t|}.indicator w) :=
    hw.indicator (measurableSet_le measurable_const measurable_id.abs)
  set g : SchwartzMap ℝ ℂ :=
    (hasCompactSupport_cutFun h hR).toSchwartzMap (contDiff_cutFun h R) with hg
  have hgt : ∀ t, g t = cutFun h R t := fun t => rfl
  have hfun : (⇑(h - g)) = fun t => h t - cutFun h R t := by
    funext t
    rw [sub_apply, hgt]
  have hder0 : ∀ t, |t| < R → deriv (⇑(h - g)) t = 0 := by
    intro t ht
    have hev : (⇑(h - g)) =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with s hs
      rw [hfun]
      simp only [cutFun_eq_of_abs_le h hR (le_of_lt (show |s| < R from hs)), sub_self]
    rw [hev.deriv_eq]
    simp
  have hD : ∀ t, ‖(h - g) t‖ ^ 2 ≤ {t : ℝ | R ≤ |t|}.indicator w t := by
    intro t
    by_cases hc : R ≤ |t|
    · rw [indicator_of_mem (show t ∈ {t : ℝ | R ≤ |t|} from hc)]
      have h1 : ‖(h - g) t‖ ≤ ‖h t‖ := by
        rw [sub_apply, hgt]
        have : h t - cutFun h R t = (1 - ((chi (R⁻¹ * t) : ℝ) : ℂ)) * h t := by
          simp [cutFun]; ring
        rw [this, norm_mul]
        have h2 : ‖(1 : ℂ) - ((chi (R⁻¹ * t) : ℝ) : ℂ)‖ ≤ 1 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.2 chi.le_one)]
          linarith [chi.nonneg (x := R⁻¹ * t)]
        calc _ ≤ 1 * ‖h t‖ := by gcongr
          _ = _ := one_mul _
      have h3 : ‖(h - g) t‖ ^ 2 ≤ ‖h t‖ ^ 2 := by gcongr
      simp only [hwdef]
      nlinarith [sq_nonneg ‖deriv h t‖]
    · rw [indicator_of_notMem (show t ∉ {t : ℝ | R ≤ |t|} from hc)]
      rw [not_le] at hc
      rw [sub_apply, hgt, cutFun_eq_of_abs_le h hR hc.le]
      simp
  have hD' : ∀ t, ‖deriv (⇑(h - g)) t‖ ^ 2 ≤ K * {t : ℝ | R ≤ |t|}.indicator w t := by
    intro t
    by_cases hc : R ≤ |t|
    · rw [indicator_of_mem (show t ∈ {t : ℝ | R ≤ |t|} from hc)]
      rw [hfun, (hasDerivAt_sub_cutFun h R t).deriv]
      set a : ℝ := chi (R⁻¹ * t) with ha
      set u : ℝ := R⁻¹ * deriv chi (R⁻¹ * t) with hu
      have ha0 : 0 ≤ a := chi.nonneg
      have ha1 : a ≤ 1 := chi.le_one
      have h2 : ‖(1 : ℂ) - (a : ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.2 ha1)]
        linarith
      have hu1 : ‖(u : ℂ)‖ ≤ M := by
        rw [Complex.norm_real, Real.norm_eq_abs, hu, abs_mul, abs_inv]
        have : |R|⁻¹ ≤ 1 := by
          rw [abs_of_pos hR]; exact inv_le_one_of_one_le₀ hR1
        calc |R|⁻¹ * |deriv chi (R⁻¹ * t)| ≤ 1 * M := by
              apply mul_le_mul this _ (abs_nonneg _) zero_le_one
              simpa using hM (R⁻¹ * t)
          _ = M := one_mul _
      set A := ‖h t‖ with hA
      set B := ‖deriv h t‖ with hB
      have hnorm : ‖(1 - (a : ℂ)) * deriv h t - (u : ℂ) * h t‖ ≤ B + M * A := by
        calc _ ≤ ‖(1 - (a : ℂ)) * deriv h t‖ + ‖(u : ℂ) * h t‖ := norm_sub_le _ _
          _ ≤ 1 * B + M * A := by
              rw [norm_mul, norm_mul]
              gcongr
          _ = _ := by ring
      have hA0 : 0 ≤ A := norm_nonneg _
      have hB0 : 0 ≤ B := norm_nonneg _
      have h4 : ‖(1 - (a : ℂ)) * deriv h t - (u : ℂ) * h t‖ ^ 2 ≤ (B + M * A) ^ 2 := by
        gcongr
      simp only [hwdef, hK]
      nlinarith [sq_nonneg (B - M * A), sq_nonneg A, sq_nonneg B, mul_nonneg (sq_nonneg M) (sq_nonneg A),
        mul_nonneg (sq_nonneg M) (sq_nonneg B)]
    · rw [indicator_of_notMem (show t ∉ {t : ℝ | R ≤ |t|} from hc), mul_zero]
      rw [not_le] at hc
      rw [hder0 t hc]
      simp
  have e1 : ∫ x, ‖(h - g) x‖ ^ 2 ≤ I :=
    integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) hind
      (Eventually.of_forall hD)
  have e2 : ∫ x, ‖deriv (⇑(h - g)) x‖ ^ 2 ≤ K * I := by
    rw [hI, ← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity) (hind.const_mul K)
      (Eventually.of_forall hD')
  refine ⟨g, fun t => ?_, hasCompactSupport_cutFun h hR, ?_⟩
  · rw [hgt, hgt, cutFun_even h he]
  · have := (le_div_iff₀ hK0).1 hRI.le
    nlinarith

/-- **S6**: `Φ h` lies in the range of `sphericalL2` for every even Schwartz function `h`. -/
theorem phiL2_mem_range_of_even (h : SchwartzMap ℝ ℂ) (he : ∀ t, h (-t) = h t) :
    phiL2 h ∈ Set.range sphericalL2 := by
  refine phiL2_mem_range_of_approx h fun δ hδ => ?_
  obtain ⟨g, hge, hgc, hg⟩ := exists_cutoff_approx h he hδ
  exact ⟨g, phiL2_mem_range_of_compact g hge hgc, hg⟩

end Lightlike.Lorentz.SL2RPlancherel
