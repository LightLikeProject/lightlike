import Lightlike.OperatorAlgebras.MomentumDeficiency
import Lightlike.OperatorAlgebras.WeakConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The adjoint of the momentum on `L²(0, 1)`: the maximal domain

Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Appendix A.3 (read): for the momentum `P = -i d/dx` on `(0, L)` with the minimal domain,
`D(P†) = D_max(0, L)`, the absolutely continuous `ψ` with `ψ, ψ' ∈ L²`. Here, with `L = 1` and `momentumMin` (`-i d/dx` on the `C²` functions with
compact support in `(0, 1)`), `D_max` is written through primitives: `y ∈ L²(0, 1)` lies in the domain of the adjoint iff `y = c + ∫₀ˣ g` almost
everywhere for a constant `c` and `g ∈ L²(0, 1)`, and then `A† y = -i g` (`mem_adjoint_iff_primitive`). The absolutely continuous functions with
`L²` derivative are exactly these primitives (`Mathlib`'s fundamental theorem of calculus for absolutely continuous functions).
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

/-- A continuous `ℝ`-linear map preserves interval integrability. -/
lemma intervalIntegrable_clm_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => L (f x)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

lemma intervalIntegrable_re_part {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (f x).re) volume a b := by
  simpa using intervalIntegrable_clm_comp Complex.reCLM hf

lemma intervalIntegrable_im_part {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (f x).im) volume a b := by
  simpa using intervalIntegrable_clm_comp Complex.imCLM hf

lemma intervalIntegrable_ofReal_comp {f : ℝ → ℝ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (f x : ℂ)) volume a b := by
  simpa using intervalIntegrable_clm_comp Complex.ofRealCLM hf

lemma intervalIntegrable_conj_comp {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun x => (starRingEnd ℂ) (f x)) volume a b := by
  simpa using intervalIntegrable_clm_comp Complex.conjCLE.toContinuousLinearMap hf

lemma integrable_conj_comp {f : ℝ → ℂ} {μ : Measure ℝ} (hf : Integrable f μ) :
    Integrable (fun x => (starRingEnd ℂ) (f x)) μ := by
  simpa using Complex.conjCLE.toContinuousLinearMap.integrable_comp hf

/-- **Integration by parts against a primitive, real case**: for `ψ` of class `C¹` vanishing at `0` and `1` and `r` integrable on `[0, 1]`,
`∫₀¹ ψ' (∫₀ˣ r) = -∫₀¹ ψ r`. -/
lemma integral_deriv_mul_primitive_real {ψ r : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (h0 : ψ 0 = 0) (h1 : ψ 1 = 0)
    (hr : IntervalIntegrable r volume 0 1) :
    ∫ x in (0 : ℝ)..1, deriv ψ x * (∫ t in (0 : ℝ)..x, r t) = -∫ x in (0 : ℝ)..1, ψ x * r x := by
  have hAψ : AbsolutelyContinuousOnInterval ψ 0 1 := hψ.contDiffOn.absolutelyContinuousOnInterval
  have hAP : AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, r t) 0 1 :=
    hr.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hibp := hAP.integral_mul_deriv_eq_deriv_mul hAψ
  simp only [h0, h1, mul_zero, sub_zero, integral_same, zero_mul, sub_self] at hibp
  have hder : ∫ x in (0 : ℝ)..1, deriv (fun x => ∫ t in (0 : ℝ)..x, r t) x * ψ x = ∫ x in (0 : ℝ)..1, ψ x * r x := by
    refine integral_congr_ae ?_
    filter_upwards [hr.ae_hasDerivAt_integral] with x hx hxI
    have hx' := hx (uIoc_subset_uIcc hxI) 0 (by simp)
    rw [hx'.deriv, mul_comm]
  rw [hder, zero_sub] at hibp
  rw [← hibp]
  exact integral_congr fun x _ => mul_comm _ _

/-- **Integration by parts against a primitive, complex primitive**: for real `ψ` of class `C¹` vanishing at `0` and `1` and `h` integrable on
`[0, 1]`, `∫₀¹ ψ' • (∫₀ˣ h) = -∫₀¹ ψ • h`. -/
lemma integral_deriv_smul_primitive {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (h0 : ψ 0 = 0) (h1 : ψ 1 = 0) {h : ℝ → ℂ}
    (hh : IntervalIntegrable h volume 0 1) :
    ∫ x in (0 : ℝ)..1, deriv ψ x • (∫ t in (0 : ℝ)..x, h t) = -∫ x in (0 : ℝ)..1, ψ x • h x := by
  have hPc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, h t) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hh left_mem_uIcc
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hI1 : IntervalIntegrable (fun x => deriv ψ x • (∫ t in (0 : ℝ)..x, h t)) volume 0 1 :=
    ((hψ'.continuousOn.smul hPc)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun x => ψ x • h x) volume 0 1 :=
    hh.continuousOn_smul hψ.continuous.continuousOn
  have hsub : ∀ x ∈ uIcc (0 : ℝ) 1, IntervalIntegrable h volume 0 x := fun x hx =>
    hh.mono_set (uIcc_subset_uIcc (left_mem_uIcc) hx)
  have hre : ∀ x ∈ uIcc (0 : ℝ) 1, (∫ t in (0 : ℝ)..x, h t).re = ∫ t in (0 : ℝ)..x, (h t).re := fun x hx =>
    (intervalIntegral_re (hsub x hx)).symm
  have him : ∀ x ∈ uIcc (0 : ℝ) 1, (∫ t in (0 : ℝ)..x, h t).im = ∫ t in (0 : ℝ)..x, (h t).im := fun x hx =>
    (intervalIntegral_im (hsub x hx)).symm
  apply Complex.ext
  · rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, ← intervalIntegral_re hI1, map_neg, ← intervalIntegral_re hI2]
    have e1 : ∫ x in (0 : ℝ)..1, RCLike.re (deriv ψ x • (∫ t in (0 : ℝ)..x, h t)) =
        ∫ x in (0 : ℝ)..1, deriv ψ x * (∫ t in (0 : ℝ)..x, (h t).re) := by
      refine integral_congr fun x hx => ?_
      simp only [Complex.real_smul, RCLike.re_to_complex, Complex.re_ofReal_mul]
      rw [hre x hx]
    have e2 : ∫ x in (0 : ℝ)..1, RCLike.re (ψ x • h x) = ∫ x in (0 : ℝ)..1, ψ x * (h x).re := by
      refine integral_congr fun x _ => ?_
      simp [Complex.real_smul]
    rw [e1, e2]
    exact integral_deriv_mul_primitive_real hψ h0 h1 (intervalIntegrable_re_part hh)
  · rw [← RCLike.im_to_complex, ← RCLike.im_to_complex, ← intervalIntegral_im hI1, map_neg, ← intervalIntegral_im hI2]
    have e1 : ∫ x in (0 : ℝ)..1, RCLike.im (deriv ψ x • (∫ t in (0 : ℝ)..x, h t)) =
        ∫ x in (0 : ℝ)..1, deriv ψ x * (∫ t in (0 : ℝ)..x, (h t).im) := by
      refine integral_congr fun x hx => ?_
      simp only [Complex.real_smul, RCLike.im_to_complex, Complex.im_ofReal_mul]
      rw [him x hx]
    have e2 : ∫ x in (0 : ℝ)..1, RCLike.im (ψ x • h x) = ∫ x in (0 : ℝ)..1, ψ x * (h x).im := by
      refine integral_congr fun x _ => ?_
      simp [Complex.real_smul]
    rw [e1, e2]
    exact integral_deriv_mul_primitive_real hψ h0 h1 (intervalIntegrable_im_part hh)

/-- **The adjoint of `momentumMin` through test functions**: `A† y = w` iff `∫ φ conj w = -i ∫ φ' conj y` for every test function `φ`. -/
lemma adjoint_momentumMin_iff (y w : L2I) :
    (∃ h : y ∈ (momentumMin†).domain, (momentumMin† ⟨y, h⟩ : L2I) = w) ↔ ∀ f : testFunctions,
      ∫ x in Ioo (0 : ℝ) 1, f.1 x * (starRingEnd ℂ) (w x) =
        (-Complex.I) * ∫ x in Ioo (0 : ℝ) 1, deriv f.1 x * (starRingEnd ℂ) (y x) := by
  have hform : ∀ f : testFunctions, ∀ hx : (momentumPair f).1 ∈ momentumMin.domain,
      (⟪w, ((⟨(momentumPair f).1, hx⟩ : momentumMin.domain) : L2I)⟫_ℂ = ⟪y, momentumMin ⟨(momentumPair f).1, hx⟩⟫_ℂ) ↔
      ∫ x in Ioo (0 : ℝ) 1, f.1 x * (starRingEnd ℂ) (w x) =
        (-Complex.I) * ∫ x in Ioo (0 : ℝ) 1, deriv f.1 x * (starRingEnd ℂ) (y x) := by
    intro f hx
    rw [momentumMin_apply f hx]
    show ⟪w, classI f.1 f.2.1.continuous f.2.2⟫_ℂ = ⟪y, (-Complex.I) • classI (deriv f.1) _ _⟫_ℂ ↔ _
    rw [inner_smul_right, inner_classI_right, inner_classI_right]
  have hall : (∀ x : momentumMin.domain, ⟪w, (x : L2I)⟫_ℂ = ⟪y, momentumMin x⟫_ℂ) ↔ ∀ f : testFunctions,
      ∫ x in Ioo (0 : ℝ) 1, f.1 x * (starRingEnd ℂ) (w x) =
        (-Complex.I) * ∫ x in Ioo (0 : ℝ) 1, deriv f.1 x * (starRingEnd ℂ) (y x) := by
    constructor
    · intro h f
      have hx : (momentumPair f).1 ∈ momentumMin.domain := mem_momentumMin_domain.2 ⟨f, rfl⟩
      exact (hform f hx).1 (h ⟨_, hx⟩)
    · intro h x
      obtain ⟨f, hf⟩ := mem_momentumMin_domain.1 x.2
      have hx : (momentumPair f).1 ∈ momentumMin.domain := mem_momentumMin_domain.2 ⟨f, rfl⟩
      have hx' : x = ⟨(momentumPair f).1, hx⟩ := Subtype.ext hf.symm
      rw [hx']
      exact (hform f hx).2 (h f)
  rw [← hall]
  constructor
  · rintro ⟨hy, rfl⟩ x
    exact LinearPMap.adjoint_isFormalAdjoint dense_momentumMin_domain ⟨y, hy⟩ x
  · intro h
    have hy := LinearPMap.mem_adjoint_domain_of_exists y ⟨w, h⟩
    exact ⟨hy, LinearPMap.adjoint_apply_eq dense_momentumMin_domain ⟨y, hy⟩ h⟩

/-- The measure of `L²(0, 1)` is finite. -/
instance : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr (by simp)

lemma integrable_L2I (y : L2I) : Integrable (y : ℝ → ℂ) ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) :=
  (Lp.memLp y).integrable one_le_two

lemma integral_Ioo_eq (F : ℝ → ℂ) : ∫ x in Ioo (0 : ℝ) 1, F x = ∫ x in (0 : ℝ)..1, F x := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

lemma intervalIntegrable_of_integrableOn {F : ℝ → ℂ} (h : IntegrableOn F (Ioo (0 : ℝ) 1)) :
    IntervalIntegrable F volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr h

lemma integrableOn_cont_mul {g F : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 1)) (hF : IntegrableOn F (Ioo (0 : ℝ) 1)) :
    IntegrableOn (fun x => g x * F x) (Ioo (0 : ℝ) 1) := by
  have hF' : IntegrableOn F (Icc (0 : ℝ) 1) := by rw [integrableOn_Icc_iff_integrableOn_Ioo]; exact hF
  exact (hF'.continuousOn_mul hg isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- **The domain of the adjoint lies in the primitives** (one half of Bonneau-Faraut-Valent, Appendix A.3, `D(P†) = D_max`): every `y ∈ D(A†)` is
`c + ∫₀ˣ i (A† y)` almost everywhere on `(0, 1)`. -/
theorem adjoint_eq_primitive (y : L2I) (hy : y ∈ (momentumMin†).domain) :
    ∃ c : ℂ, ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      y x = c + ∫ t in (0 : ℝ)..x, Complex.I * (momentumMin† ⟨y, hy⟩ : L2I) t := by
  set w : L2I := momentumMin† ⟨y, hy⟩ with hw
  have hcond := (adjoint_momentumMin_iff y w).mp ⟨hy, rfl⟩
  have hwc : IntegrableOn (fun t => (-Complex.I) * (starRingEnd ℂ) (w t)) (Ioo (0 : ℝ) 1) :=
    (integrable_conj_comp (integrable_L2I w)).const_mul _
  have hwi : IntervalIntegrable (fun t => (-Complex.I) * (starRingEnd ℂ) (w t)) volume 0 1 :=
    intervalIntegrable_of_integrableOn hwc
  set P : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, (-Complex.I) * (starRingEnd ℂ) (w t) with hP
  have hPc : ContinuousOn P (Icc 0 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hwi (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
    rw [uIcc_of_le zero_le_one] at h
    exact h
  have hPi : IntegrableOn P (Ioo (0 : ℝ) 1) := (hPc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hyc : IntegrableOn (fun x => (starRingEnd ℂ) (y x)) (Ioo (0 : ℝ) 1) := integrable_conj_comp (integrable_L2I y)
  set v : ℝ → ℂ := fun x => (starRingEnd ℂ) (y x) - P x with hv
  have hvi : IntegrableOn v (Ioo (0 : ℝ) 1) := hyc.sub hPi
  obtain ⟨c, hc⟩ := weak_const hvi fun ψ hψ hcs hts => by
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
    have h0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (hts h).1
    have h1 : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (hts h).2
    let f : testFunctions := ⟨fun x => (ψ x : ℂ), realTest_mem hψ hcs hts⟩
    have hderiv : ∀ x, deriv f.1 x = ((deriv ψ x : ℝ) : ℂ) := fun x =>
      ((hψ1.differentiable one_ne_zero x).hasDerivAt.ofReal_comp).deriv
    have hc1 := hcond f
    simp only [hderiv] at hc1
    have hg : ContinuousOn (fun x => ((deriv ψ x : ℝ) : ℂ)) (Icc 0 1) :=
      (Complex.continuous_ofReal.comp (hψ1.continuous_deriv le_rfl)).continuousOn
    have hibp := integral_deriv_smul_primitive hψ1 h0 h1 hwi
    have e1 : ∫ x in Ioo (0 : ℝ) 1, deriv ψ x • v x =
        (∫ x in Ioo (0 : ℝ) 1, ((deriv ψ x : ℝ) : ℂ) * (starRingEnd ℂ) (y x)) -
          ∫ x in Ioo (0 : ℝ) 1, ((deriv ψ x : ℝ) : ℂ) * P x := by
      rw [← integral_sub (integrableOn_cont_mul hg hyc) (integrableOn_cont_mul hg hPi)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [hv, Complex.real_smul, mul_sub]
    have e2 : ∫ x in Ioo (0 : ℝ) 1, ((deriv ψ x : ℝ) : ℂ) * P x =
        Complex.I * ∫ x in Ioo (0 : ℝ) 1, (ψ x : ℂ) * (starRingEnd ℂ) (w x) := by
      rw [integral_Ioo_eq, integral_Ioo_eq]
      have h3 : ∫ x in (0 : ℝ)..1, ((deriv ψ x : ℝ) : ℂ) * P x = ∫ x in (0 : ℝ)..1, deriv ψ x • P x := by
        simp [Complex.real_smul]
      rw [h3, hibp]
      have h4 : ∫ x in (0 : ℝ)..1, ψ x • ((-Complex.I) * (starRingEnd ℂ) (w x)) =
          (-Complex.I) * ∫ x in (0 : ℝ)..1, (ψ x : ℂ) * (starRingEnd ℂ) (w x) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp [Complex.real_smul]; ring
      rw [h4]; ring
    rw [e1, e2]
    have : ∫ x in Ioo (0 : ℝ) 1, ((deriv ψ x : ℝ) : ℂ) * (starRingEnd ℂ) (y x) =
        Complex.I * ∫ x in Ioo (0 : ℝ) 1, (ψ x : ℂ) * (starRingEnd ℂ) (w x) := by
      rw [hc1]; ring_nf; simp [Complex.I_sq]
    rw [this, sub_self]
  refine ⟨(starRingEnd ℂ) c, ?_⟩
  filter_upwards [hc] with x hx
  have hyx : (starRingEnd ℂ) (y x) = c + P x := by rw [← hx]; simp [hv]
  have := congrArg (starRingEnd ℂ) hyx
  rw [Complex.conj_conj, map_add] at this
  rw [this, hP]
  congr 1
  rw [← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp

/-- **Integration by parts against a primitive, complex test function**: for `f` of class `C¹` vanishing at `0` and `1` and `h` integrable on
`[0, 1]`, `∫₀¹ f' (∫₀ˣ h) = -∫₀¹ f h`. -/
lemma integral_deriv_mul_primitive_complex {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (h0 : f 0 = 0) (h1 : f 1 = 0) {h : ℝ → ℂ}
    (hh : IntervalIntegrable h volume 0 1) :
    ∫ x in (0 : ℝ)..1, deriv f x * (∫ t in (0 : ℝ)..x, h t) = -∫ x in (0 : ℝ)..1, f x * h x := by
  set fr : ℝ → ℝ := fun x => (f x).re
  set fi : ℝ → ℝ := fun x => (f x).im
  have hfr : ContDiff ℝ 1 fr := Complex.reCLM.contDiff.comp hf
  have hfi : ContDiff ℝ 1 fi := Complex.imCLM.contDiff.comp hf
  have hdr : ∀ x, deriv fr x = (deriv f x).re := fun x =>
    ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf.differentiable one_ne_zero x).hasDerivAt)).deriv
  have hdi : ∀ x, deriv fi x = (deriv f x).im := fun x =>
    ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf.differentiable one_ne_zero x).hasDerivAt)).deriv
  have hr := integral_deriv_smul_primitive hfr (by simp [fr, h0]) (by simp [fr, h1]) hh
  have hi := integral_deriv_smul_primitive hfi (by simp [fi, h0]) (by simp [fi, h1]) hh
  have hPc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, h t) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hh left_mem_uIcc
  have hfr' : Continuous (deriv fr) := hfr.continuous_deriv le_rfl
  have hfi' : Continuous (deriv fi) := hfi.continuous_deriv le_rfl
  have iA : IntervalIntegrable (fun x => deriv fr x • (∫ t in (0 : ℝ)..x, h t)) volume 0 1 :=
    (hfr'.continuousOn.smul hPc).intervalIntegrable
  have iB : IntervalIntegrable (fun x => Complex.I * (deriv fi x • (∫ t in (0 : ℝ)..x, h t))) volume 0 1 :=
    ((continuousOn_const.mul (hfi'.continuousOn.smul hPc))).intervalIntegrable
  have iC : IntervalIntegrable (fun x => fr x • h x) volume 0 1 := hh.continuousOn_smul hfr.continuous.continuousOn
  have iD : IntervalIntegrable (fun x => Complex.I * (fi x • h x)) volume 0 1 :=
    (hh.continuousOn_smul hfi.continuous.continuousOn).const_mul _
  have eL : ∫ x in (0 : ℝ)..1, deriv f x * (∫ t in (0 : ℝ)..x, h t) =
      ∫ x in (0 : ℝ)..1, (deriv fr x • (∫ t in (0 : ℝ)..x, h t) + Complex.I * (deriv fi x • (∫ t in (0 : ℝ)..x, h t))) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [hdr, hdi]
    simp only [Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im (deriv f x)]
    ring
  have eR : ∫ x in (0 : ℝ)..1, f x * h x = ∫ x in (0 : ℝ)..1, (fr x • h x + Complex.I * (fi x • h x)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [Complex.real_smul, fr, fi]
    conv_lhs => rw [← Complex.re_add_im (f x)]
    ring
  rw [eL, eR, intervalIntegral.integral_add iA iB, intervalIntegral.integral_add iC iD,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hr, hi]
  ring

/-- **The primitives lie in the domain of the adjoint** (the other half of `D(P†) = D_max`): if `y = c + ∫₀ˣ g` almost everywhere on `(0, 1)` with
`g ∈ L²(0, 1)`, then `y ∈ D(A†)` and `A† y = -i g`. -/
theorem mem_adjoint_of_primitive (y g : L2I) (c : ℂ)
    (hy : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), y x = c + ∫ t in (0 : ℝ)..x, g t) :
    ∃ h : y ∈ (momentumMin†).domain, (momentumMin† ⟨y, h⟩ : L2I) = (-Complex.I) • g := by
  rw [adjoint_momentumMin_iff]
  intro f
  have hf1 : ContDiff ℝ 1 f.1 := f.2.1.of_le (by norm_num)
  have h0 : f.1 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (f.2.2 h).1
  have h1 : f.1 1 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (f.2.2 h).2
  have hgi : IntervalIntegrable (fun t => (starRingEnd ℂ) (g t)) volume 0 1 :=
    intervalIntegrable_of_integrableOn (integrable_conj_comp (integrable_L2I g))
  have hgi' : IntervalIntegrable (fun t => g t) volume 0 1 := intervalIntegrable_of_integrableOn (integrable_L2I g)
  have hsmul : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), ((-Complex.I) • g : L2I) x = (-Complex.I) * g x := by
    filter_upwards [Lp.coeFn_smul (-Complex.I) g] with x hx
    rw [hx]; rfl
  have eL : ∫ x in Ioo (0 : ℝ) 1, f.1 x * (starRingEnd ℂ) (((-Complex.I) • g : L2I) x) =
      Complex.I * ∫ x in (0 : ℝ)..1, f.1 x * (starRingEnd ℂ) (g x) := by
    rw [← intervalIntegral.integral_const_mul, ← integral_Ioo_eq]
    refine integral_congr_ae ?_
    filter_upwards [hsmul] with x hx
    rw [hx, map_mul]; simp; ring
  have eR : ∫ x in Ioo (0 : ℝ) 1, deriv f.1 x * (starRingEnd ℂ) (y x) =
      ∫ x in (0 : ℝ)..1, (deriv f.1 x * (starRingEnd ℂ) c + deriv f.1 x * ∫ t in (0 : ℝ)..x, (starRingEnd ℂ) (g t)) := by
    rw [← integral_Ioo_eq]
    refine integral_congr_ae ?_
    filter_upwards [hy] with x hx
    rw [hx, map_add, intervalIntegral_conj, mul_add]
  have hderiv_int : IntervalIntegrable (fun x => deriv f.1 x * (starRingEnd ℂ) c) volume 0 1 :=
    ((hf1.continuous_deriv le_rfl).mul continuous_const).intervalIntegrable 0 1
  have hPc : ContinuousOn (fun x => ∫ t in (0 : ℝ)..x, (starRingEnd ℂ) (g t)) (uIcc 0 1) :=
    intervalIntegral.continuousOn_primitive_interval' hgi left_mem_uIcc
  have hsecond_int : IntervalIntegrable (fun x => deriv f.1 x * ∫ t in (0 : ℝ)..x, (starRingEnd ℂ) (g t)) volume 0 1 :=
    ((hf1.continuous_deriv le_rfl).continuousOn.mul hPc).intervalIntegrable
  have hftc : ∫ x in (0 : ℝ)..1, deriv f.1 x = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hf1.differentiable one_ne_zero x)
      ((hf1.continuous_deriv le_rfl).intervalIntegrable 0 1), h0, h1, sub_zero]
  rw [eL, eR, intervalIntegral.integral_add hderiv_int hsecond_int, intervalIntegral.integral_mul_const, hftc,
    zero_mul, zero_add, integral_deriv_mul_primitive_complex hf1 h0 h1 hgi]
  ring

/-- **The domain of the adjoint of the momentum is the space of primitives of `L²` functions** (Bonneau-Faraut-Valent, Appendix A.3, read:
`D(P†) = D_max(0, L)`, with `L = 1` and `D_max` written through primitives): `y ∈ D(A†)` iff `y = c + ∫₀ˣ g` almost everywhere for some `c` and
`g ∈ L²(0, 1)`; then `A† y = -i g`. -/
theorem mem_adjoint_iff_primitive (y : L2I) :
    y ∈ (momentumMin†).domain ↔ ∃ (c : ℂ) (g : L2I),
      ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), y x = c + ∫ t in (0 : ℝ)..x, g t := by
  constructor
  · intro hy
    obtain ⟨c, hc⟩ := adjoint_eq_primitive y hy
    refine ⟨c, Complex.I • (momentumMin† ⟨y, hy⟩ : L2I), ?_⟩
    have hs := (ae_restrict_iff' measurableSet_Ioo).mp (Lp.coeFn_smul Complex.I (momentumMin† ⟨y, hy⟩ : L2I))
    filter_upwards [hc, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hs] with t ht htI
    rw [uIoc_of_le hxI.1.le] at htI
    rw [ht ⟨htI.1, lt_of_le_of_lt htI.2 hxI.2⟩]
    rfl
  · rintro ⟨c, g, hg⟩
    exact (mem_adjoint_of_primitive y g c hg).1

end Lightlike.OperatorAlgebras
