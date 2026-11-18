import Lightlike.OperatorAlgebras.MomentumSmooth
import Lightlike.OperatorAlgebras.Deficiency
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Lightlike.OperatorAlgebras.WeakConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The deficiency indices of `-i d/dx` on `L²(0, 1)`

Helper lemmas for `T-OP1-P5` (`Tasks/OP/T_OP1_P5.lean`).
-/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

/-- A vector is in the domain of `momentumMin` iff it is the class of a `C²` test function. -/
lemma mem_momentumMin_domain {x : L2I} :
    x ∈ momentumMin.domain ↔ ∃ f : testFunctions, classI f.1 f.2.1.continuous f.2.2 = x := by
  constructor
  · intro hx
    have hg : (x, momentumMin ⟨x, hx⟩) ∈ momentumMin.graph := by
      rw [LinearPMap.mem_graph_iff]; exact ⟨⟨x, hx⟩, rfl, rfl⟩
    rw [momentumMin_graph] at hg
    obtain ⟨f, -, hf⟩ := hg
    exact ⟨f, congrArg Prod.fst hf⟩
  · rintro ⟨f, rfl⟩
    have hg : momentumPair f ∈ momentumGraph := ⟨f, trivial, rfl⟩
    rw [← momentumMin_graph] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg

/-- `momentumMin` maps the class of a test function `f` to `-i` times the class of `f'`. -/
lemma momentumMin_apply (f : testFunctions) (hx : (momentumPair f).1 ∈ momentumMin.domain) :
    momentumMin ⟨(momentumPair f).1, hx⟩ = (momentumPair f).2 := by
  have hg : momentumPair f ∈ momentumMin.graph := by
    rw [momentumMin_graph]; exact ⟨f, trivial, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have : y = ⟨(momentumPair f).1, hx⟩ := Subtype.ext hy1
  rw [← this]; exact hy2

/-- A real smooth function with compact support inside `(0, 1)`, as a `C²` test function. -/
lemma realTest_mem {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo (0 : ℝ) 1) :
    (fun x => (g x : ℂ)) ∈ testFunctions := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp hg).of_le (by norm_num), ?_⟩
  refine (closure_mono ?_).trans hs
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  exact fun h => hx (by simp [h])

/-- A vector of `L²(0, 1)` orthogonal to all test functions is zero. -/
lemma eq_zero_of_orthogonal {y : L2I} (h : ∀ f : testFunctions, ⟪classI f.1 f.2.1.continuous f.2.2, y⟫_ℂ = 0) :
    y = 0 := by
  have hint : Integrable (fun x => (y : ℝ → ℂ) x) ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) :=
    (Lp.memLp y).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hloc : LocallyIntegrableOn (fun x => (y : ℝ → ℂ) x) (Ioo (0 : ℝ) 1)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) :=
    hint.locallyIntegrable.locallyIntegrableOn _
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro g hg hc hs
    have h0 := h ⟨fun x => (g x : ℂ), realTest_mem hg hc hs⟩
    rw [MeasureTheory.L2.inner_def] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    have h1 : (classI (fun x => (g x : ℂ)) (realTest_mem hg hc hs).1.continuous
        (realTest_mem hg hc hs).2 : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)]
        fun x => (g x : ℂ) := MemLp.coeFn_toLp _
    filter_upwards [h1] with x hx
    simp only [hx]
    simp [Complex.real_smul, mul_comm])
  have hy0 : (y : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxU
    exact hx hxU
  exact (Lp.eq_zero_iff_ae_eq_zero).2 hy0

/-- **The domain of `momentumMin` is dense in `L²(0, 1)`.** -/
theorem dense_momentumMin_domain : Dense (momentumMin.domain : Set L2I) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  exact eq_zero_of_orthogonal fun f => hy _ (mem_momentumMin_domain.2 ⟨f, rfl⟩)

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a densely defined operator `A`, `y` is in the deficiency space at `z` iff
`⟪z y, x⟫ = ⟪y, A x⟫` for all `x` in the domain of `A`. -/
lemma mem_deficiencySpace_iff {A : H →ₗ.[ℂ] H} (hA : Dense (A.domain : Set H)) (z : ℂ) (y : H) :
    y ∈ deficiencySpace A z ↔ ∀ x : A.domain, ⟪z • y, (x : H)⟫_ℂ = ⟪y, A x⟫_ℂ := by
  constructor
  · rintro ⟨hy, he⟩ x
    have := LinearPMap.adjoint_isFormalAdjoint hA ⟨y, hy⟩ x
    rw [← he]; exact this
  · intro h
    have hy : y ∈ (A†).domain :=
      LinearPMap.mem_adjoint_domain_of_exists y ⟨z • y, fun x => h x⟩
    refine ⟨hy, ?_⟩
    exact LinearPMap.adjoint_apply_eq hA ⟨y, hy⟩ fun x => h x

end Generic

/-- The real exponential `x ↦ exp (b x)` as a complex function. -/
noncomputable def expC (b : ℝ) : ℝ → ℂ := fun x => ((Real.exp (b * x) : ℝ) : ℂ)

lemma expC_contDiff (b : ℝ) : ContDiff ℝ ∞ (expC b) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

lemma expC_hasDerivAt (b x : ℝ) : HasDerivAt (expC b) (b * expC b x) x := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (b * x)) (Real.exp (b * x) * b) x := by
    simpa using ((hasDerivAt_id x).const_mul b).exp
  have := h1.ofReal_comp
  refine HasDerivAt.congr_deriv (f := fun y : ℝ => (((Real.exp (b * y) : ℝ)) : ℂ)) this ?_
  simp [expC]; ring

/-- **Integration by parts on `(0, 1)`** for a `C¹` function with support inside `(0, 1)`:
`∫ φ' e^{bx} = -b ∫ φ e^{bx}`. -/
lemma integral_deriv_mul_expC {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1)
    (b : ℝ) :
    ∫ x in Ioo (0 : ℝ) 1, deriv φ x * expC b x = -b * ∫ x in Ioo (0 : ℝ) 1, φ x * expC b x := by
  have hd : ∀ x, HasDerivAt (fun x => φ x * expC b x) (deriv φ x * expC b x + φ x * (b * expC b x)) x :=
    fun x => ((hφ.differentiable (by norm_num) x).hasDerivAt).mul (expC_hasDerivAt b x)
  have hc : Continuous fun x => deriv φ x * expC b x + φ x * (b * expC b x) :=
    ((hφ.continuous_deriv le_rfl).mul (expC_contDiff b).continuous).add
      (hφ.continuous.mul (continuous_const.mul (expC_contDiff b).continuous))
  have h0 : φ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (hs h).1
  have h1 : φ 1 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (hs h).2
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable 0 1)
  rw [h0, h1] at key
  simp only [zero_mul, sub_zero] at key
  have e1 : ∫ x in (0 : ℝ)..1, (deriv φ x * expC b x + φ x * (b * expC b x)) =
      ∫ x in Ioo (0 : ℝ) 1, (deriv φ x * expC b x + φ x * (b * expC b x)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [e1] at key
  have i1 : IntegrableOn (fun x => deriv φ x * expC b x) (Ioo (0 : ℝ) 1) :=
    ((hφ.continuous_deriv le_rfl).mul (expC_contDiff b).continuous).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have i2 : IntegrableOn (fun x => φ x * (b * expC b x)) (Ioo (0 : ℝ) 1) :=
    (hφ.continuous.mul (continuous_const.mul (expC_contDiff b).continuous)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [integral_add i1 i2] at key
  have e2 : ∫ x in Ioo (0 : ℝ) 1, φ x * (b * expC b x) = b * ∫ x in Ioo (0 : ℝ) 1, φ x * expC b x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e2] at key
  linear_combination key

/-- The inner product of `w` with the class of a function supported inside `(0, 1)` is an integral. -/
lemma inner_classI_right (w : L2I) {g : ℝ → ℂ} (hg : Continuous g) (hs : tsupport g ⊆ Ioo (0 : ℝ) 1) :
    ⟪w, classI g hg hs⟫_ℂ = ∫ x in Ioo (0 : ℝ) 1, g x * (starRingEnd ℂ) (w x) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 : (classI g hg hs : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] g :=
    MemLp.coeFn_toLp _
  filter_upwards [h1] with x hx
  rw [hx]; simp [RCLike.inner_apply]

/-- **Weak form of the deficiency equation**: `y` is in the deficiency space of `momentumMin` at `z` iff
`conj z ∫ φ conj y = -i ∫ φ' conj y` for every test function `φ`. -/
lemma mem_deficiencySpace_momentumMin_iff (z : ℂ) (y : L2I) :
    y ∈ deficiencySpace momentumMin z ↔ ∀ f : testFunctions,
      (starRingEnd ℂ) z * ∫ x in Ioo (0 : ℝ) 1, f.1 x * (starRingEnd ℂ) (y x) =
        (-Complex.I) * ∫ x in Ioo (0 : ℝ) 1, deriv f.1 x * (starRingEnd ℂ) (y x) := by
  rw [mem_deficiencySpace_iff dense_momentumMin_domain]
  have hform : ∀ f : testFunctions, ∀ hx : (momentumPair f).1 ∈ momentumMin.domain,
      (⟪z • y, (⟨(momentumPair f).1, hx⟩ : momentumMin.domain)⟫_ℂ = ⟪y, momentumMin ⟨(momentumPair f).1, hx⟩⟫_ℂ) ↔
      (starRingEnd ℂ) z * ∫ x in Ioo (0 : ℝ) 1, f.1 x * (starRingEnd ℂ) (y x) =
        (-Complex.I) * ∫ x in Ioo (0 : ℝ) 1, deriv f.1 x * (starRingEnd ℂ) (y x) := by
    intro f hx
    rw [momentumMin_apply f hx]
    show ⟪z • y, classI f.1 f.2.1.continuous f.2.2⟫_ℂ =
      ⟪y, (-Complex.I) • classI (deriv f.1) _ _⟫_ℂ ↔ _
    rw [inner_smul_left, inner_smul_right, inner_classI_right, inner_classI_right]
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

end Lightlike.OperatorAlgebras
