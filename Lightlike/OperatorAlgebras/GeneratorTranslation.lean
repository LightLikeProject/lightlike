import Lightlike.OperatorAlgebras.Translation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The generator of the translation group on `L²(ℝ)` is `-i d/dx`

For `ψ` twice continuously differentiable with compact support, `t ↦ U t ψ` is differentiable at `0` in
`L²(ℝ)` with derivative `ψ'` (`translationGroup_hasDerivAt`): the error `ψ(· + t) - ψ - t ψ'` is bounded
pointwise by `M t²` (`taylor_bound`, `M` a bound of `ψ''`) and supported in a fixed interval, so its `L²`
norm is at most `M t² √(2 (R + 1))` (`norm_toLp_le`). Hence the generator of `translationGroup` maps such a
`ψ` to `-i ψ'` (`translationGroup_generator_ofCS`), which is the momentum operator `-i d/dx`; the sign is
tested by `translationGroup_generator_ne`, and `exists_core_ne_zero` shows the test is not vacuous.

Not proved here: that these functions form a core of the generator (the closure of `-i d/dx` on them is
the generator, so that it is essentially self-adjoint there); that is `T-OP1-P4`.
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras

/-- A function bounded by `B` and supported in `[-a, a]` has `L²` norm at most `B * sqrt (2 a)`. -/
lemma norm_toLp_le {h : ℝ → ℂ} (hh : MemLp h 2 volume) {B a : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hb : ∀ x, ‖h x‖ ≤ B) (hs : ∀ x, a < |x| → h x = 0) :
    ‖hh.toLp h‖ ≤ B * Real.sqrt (2 * a) := by
  rw [Lp.norm_toLp]
  have h1 : eLpNorm h 2 volume ≤ eLpNorm ((Set.Icc (-a) a).indicator (fun _ => (B : ℝ))) 2 volume := by
    refine eLpNorm_mono hh.aestronglyMeasurable ?_
    intro x
    by_cases hx : x ∈ Set.Icc (-a) a
    · simpa [hx, Real.norm_eq_abs, abs_of_nonneg hB] using hb x
    · have : a < |x| := by
        rw [Set.mem_Icc] at hx; rw [lt_abs]; push Not at hx
        by_cases h0 : -a ≤ x
        · left; exact hx h0
        · right; linarith
      simp [hx, hs x this]
  have h2 := eLpNorm_indicator_const (μ := (volume : Measure ℝ)) (p := 2) (c := (B : ℝ))
    (s := Set.Icc (-a) a) measurableSet_Icc.nullMeasurableSet (by norm_num) (by norm_num)
  rw [h2, Real.volume_Icc] at h1
  have hfin : (‖(B : ℝ)‖ₑ * ENNReal.ofReal (a - -a) ^ (1 / (2 : ENNReal).toReal)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have h3 := ENNReal.toReal_mono hfin h1
  refine h3.trans (le_of_eq ?_)
  have e : (1 / ENNReal.toReal 2 : ℝ) = 1 / 2 := by norm_num
  rw [e, ENNReal.toReal_mul, ENNReal.ofReal_rpow_of_nonneg (by linarith) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (by linarith) _)]
  simp [Real.sqrt_eq_rpow, abs_of_nonneg hB, show a - -a = 2 * a by ring]

/-- **Taylor bound**: for `f` twice continuously differentiable with `‖f''‖ ≤ M`,
`‖f (x + t) - f x - t f' x‖ ≤ M t²`. -/
lemma taylor_bound {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ x, ‖deriv (deriv f) x‖ ≤ M) (x t : ℝ) :
    ‖f (x + t) - f x - t • deriv f x‖ ≤ M * t ^ 2 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : ContDiff ℝ 1 (deriv f) := by
    have := (contDiff_succ_iff_deriv (n := 1) (𝕜 := ℝ) (f := f)).mp (by
      have h2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
      rw [h2]; exact hf)
    exact this.2.2
  have hdd : Differentiable ℝ (deriv f) := hd2.differentiable (by norm_num)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have lip : ∀ y z : ℝ, ‖deriv f y - deriv f z‖ ≤ M * ‖y - z‖ := fun y z =>
    Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun w _ => hdd w) (fun w _ => hM w)
      convex_univ (Set.mem_univ z) (Set.mem_univ y)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => f (x + s) - s • deriv f x)
    (f' := fun s : ℝ => deriv f (x + s) - deriv f x) (s := Set.uIcc 0 t) (C := M * |t|)
    (fun s _ => by
      have h1 : HasDerivAt (fun s : ℝ => f (x + s)) (deriv f (x + s)) s := by
        have hfd : HasDerivAt f (deriv f (x + s)) (x + s) := (hd (x + s)).hasDerivAt
        have := HasDerivAt.scomp s hfd ((hasDerivAt_id' s).const_add x)
        simp only [one_smul] at this
        exact this
      have h2 : HasDerivAt (fun s : ℝ => s • deriv f x) (deriv f x) s := by
        simpa using (hasDerivAt_id s).smul_const (deriv f x)
      exact (h1.sub h2).hasDerivWithinAt)
    (fun s hs => by
      have := lip (x + s) x
      simp only [add_sub_cancel_left] at this
      refine this.trans ?_
      have hs' : |s| ≤ |t| := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
        · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
      rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hs' hM0)
    (convex_uIcc 0 t) Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [zero_smul, sub_zero, add_zero, sub_sub] at key
  have : ‖f (x + t) - f x - t • deriv f x‖ = ‖f (x + t) - (t • deriv f x + f x)‖ := by
    congr 1; abel
  rw [this]
  refine key.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, mul_assoc, ← sq, sq_abs]

/-- The `L²(ℝ)` class of a continuous function with compact support. -/
noncomputable def ofCS {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) : L2R :=
  (hf.memLp_of_hasCompactSupport (p := 2) (μ := (volume : Measure ℝ)) hc).toLp f

/-- The translate of a class of a continuous compactly supported function is the class of the
translated function. -/
lemma translate_ofCS {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) (t : ℝ)
    {hf' : Continuous fun x => f (x + t)} {hc' : HasCompactSupport fun x => f (x + t)} :
    translationGroup t (ofCS hf hc) = ofCS hf' hc' := rfl

/-- The derivative of a `C²` function with compact support is continuous. -/
lemma continuous_deriv_of_two {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) : Continuous (deriv f) :=
  hf.continuous_deriv (by norm_num)

/-- The error `ψ(· + t) - ψ - t ψ'` of the difference quotient, as the class of a function. -/
lemma error_eq {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (t : ℝ)
    (hg : MemLp (fun x => f (x + t) - f x - t • deriv f x) 2 (volume : Measure ℝ)) :
    translationGroup t (ofCS hf.continuous hc) - ofCS hf.continuous hc -
        t • ofCS (continuous_deriv_of_two hf) hc.deriv = hg.toLp _ := by
  have h0 : MemLp f 2 (volume : Measure ℝ) := hf.continuous.memLp_of_hasCompactSupport hc
  have h1 : MemLp (fun x => f (x + t)) 2 (volume : Measure ℝ) :=
    h0.comp_measurePreserving (measurePreserving_shift t)
  have h2 : MemLp (deriv f) 2 (volume : Measure ℝ) :=
    (continuous_deriv_of_two hf).memLp_of_hasCompactSupport hc.deriv
  have e1 : translationGroup t (ofCS hf.continuous hc) = h1.toLp _ := rfl
  have e2 : ofCS hf.continuous hc = h0.toLp _ := rfl
  have e3 : ofCS (continuous_deriv_of_two hf) hc.deriv = h2.toLp _ := rfl
  rw [e1, e2, e3, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub, ← MemLp.toLp_sub]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => rfl)

/-- **The derivative of the translation group on a `C²` function with compact support**: for such `ψ`,
`t ↦ U t ψ` is differentiable at `0` in `L²(ℝ)` with derivative `ψ'`. -/
theorem translationGroup_hasDerivAt {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    HasDerivAt (fun t : ℝ => translationGroup t (ofCS hf.continuous hc))
      (ofCS (continuous_deriv_of_two hf) hc.deriv) 0 := by
  have hd2 : ContDiff ℝ 1 (deriv f) := by
    have := (contDiff_succ_iff_deriv (n := 1) (𝕜 := ℝ) (f := f)).mp (by
      have h2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
      rw [h2]; exact hf)
    exact this.2.2
  have hcc : Continuous (deriv (deriv f)) := hd2.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hcc.bounded_above_of_compact_support hc.deriv.deriv
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hf0 : ∀ x, |R| < |x| → f x = 0 := fun x hx => by
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact absurd (this.trans (le_abs_self R)) (not_le.mpr hx)
  have hf1 : ∀ x, |R| < |x| → deriv f x = 0 := fun x hx => by
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hR (tsupport_deriv_subset hmem)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact absurd (this.trans (le_abs_self R)) (not_le.mpr hx)
  have h0 : MemLp f 2 (volume : Measure ℝ) := hf.continuous.memLp_of_hasCompactSupport hc
  have h2 : MemLp (deriv f) 2 (volume : Measure ℝ) :=
    (continuous_deriv_of_two hf).memLp_of_hasCompactSupport hc.deriv
  have hmem : ∀ t : ℝ, MemLp (fun x => f (x + t) - f x - t • deriv f x) 2 (volume : Measure ℝ) :=
    fun t => ((h0.comp_measurePreserving (measurePreserving_shift t)).sub h0).sub (h2.const_smul t)
  have bound : ∀ t : ℝ, |t| ≤ 1 →
      ‖translationGroup t (ofCS hf.continuous hc) - ofCS hf.continuous hc -
        t • ofCS (continuous_deriv_of_two hf) hc.deriv‖ ≤ (M * Real.sqrt (2 * (|R| + 1))) * t ^ 2 := by
    intro t ht
    rw [error_eq hf hc t (hmem t)]
    have := norm_toLp_le (hmem t) (B := M * t ^ 2) (a := |R| + 1) (by positivity) (by positivity)
      (fun x => taylor_bound hf hM x t)
      (fun x hx => by
        have e1 : f (x + t) = 0 := hf0 _ (by
          have : |x| - |t| ≤ |x + t| := by
            have := abs_sub_abs_le_abs_sub x (-t); simpa using this
          linarith)
        have e2 : f x = 0 := hf0 x (by linarith [abs_nonneg R])
        have e3 : deriv f x = 0 := hf1 x (by linarith [abs_nonneg R])
        simp [e1, e2, e3])
    calc _ ≤ _ := this
      _ = _ := by ring
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hz : translationGroup 0 (ofCS hf.continuous hc) = ofCS hf.continuous hc := by
    rw [translationGroup.map_zero']; rfl
  have hbig : (fun h : ℝ => translationGroup (0 + h) (ofCS hf.continuous hc) -
      translationGroup 0 (ofCS hf.continuous hc) -
      h • ofCS (continuous_deriv_of_two hf) hc.deriv) =O[nhds 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound (M * Real.sqrt (2 * (|R| + 1))) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with h hh
    rw [zero_add, hz]
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
    refine (bound h hh.le).trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg h)]
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

/-- **Trust check, `L²(ℝ)`: the generator of translation is `-i d/dx` on `C²` functions with compact
support.** The class of `ψ` is in the domain of the generator of `translationGroup`, and the generator maps
it to `-i ψ'`. -/
theorem translationGroup_generator_ofCS {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ h : ofCS hf.continuous hc ∈ translationGroup.generatorDomain,
      translationGroup.generator ⟨ofCS hf.continuous hc, h⟩ =
        (-Complex.I) • ofCS (continuous_deriv_of_two hf) hc.deriv := by
  have hd := translationGroup_hasDerivAt hf hc
  refine ⟨hd.differentiableAt, ?_⟩
  show (-Complex.I) • deriv (fun t => translationGroup t (ofCS hf.continuous hc)) 0 = _
  rw [hd.deriv]

/-- **Negative control**: the generator of translation is not `+i d/dx`: whenever `ψ' ≠ 0` in `L²(ℝ)`, it
differs from `i ψ'`, so the sign of the convention `U t = exp (i t A)` is tested. -/
theorem translationGroup_generator_ne {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hne : ofCS (continuous_deriv_of_two hf) hc.deriv ≠ 0) :
    ∀ h : ofCS hf.continuous hc ∈ translationGroup.generatorDomain,
      translationGroup.generator ⟨ofCS hf.continuous hc, h⟩ ≠
        Complex.I • ofCS (continuous_deriv_of_two hf) hc.deriv := by
  intro h heq
  obtain ⟨h', hgen⟩ := translationGroup_generator_ofCS hf hc
  rw [hgen] at heq
  generalize ofCS (continuous_deriv_of_two hf) hc.deriv = v at heq hne
  rw [neg_smul, neg_eq_iff_add_eq_zero, ← add_smul] at heq
  rcases smul_eq_zero.mp heq with h0 | h0
  · have := congrArg Complex.im h0
    simp at this
  · exact hne h0

/-- **Non-vacuity**: a smooth bump function `ψ` (complex valued, with compact support) has `ψ' ≠ 0` in
`L²(ℝ)`, so the core of the generator is not trivial and the negative control applies. -/
theorem exists_core_ne_zero : ∃ (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f),
    ofCS (continuous_deriv_of_two hf) hc.deriv ≠ 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let f : ℝ → ℂ := fun x => (b x : ℂ)
  have hf : ContDiff ℝ 2 f := Complex.ofRealCLM.contDiff.comp (b.contDiff)
  have hc : HasCompactSupport f := b.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) (by simp)
  refine ⟨f, hf, hc, fun h0 => ?_⟩
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hae : deriv f =ᵐ[volume] 0 := by
    have := (Lp.eq_zero_iff_ae_eq_zero (f := ofCS (continuous_deriv_of_two hf) hc.deriv)).mp h0
    refine (MemLp.coeFn_toLp _).symm.trans (this.trans ?_)
    exact Filter.EventuallyEq.rfl
  have hz : deriv f = 0 :=
    (continuous_deriv_of_two hf).ae_eq_iff_eq volume continuous_const |>.mp hae
  have hconst : ∀ x, f x = f 0 := fun x => is_const_of_deriv_eq_zero hdiff (fun y => by simp [hz]) x 0
  have hb1 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hb2 : b 2 = 0 := b.zero_of_le_dist (by
    change (2 : ℝ) ≤ dist (2 : ℝ) 0
    simp)
  have h1 : f 0 = 1 := by simp [f, hb1]
  have h2 : f 2 = 0 := by simp [f, hb2]
  have := hconst 2
  rw [h1, h2] at this
  exact zero_ne_one this

end Lightlike.OperatorAlgebras
