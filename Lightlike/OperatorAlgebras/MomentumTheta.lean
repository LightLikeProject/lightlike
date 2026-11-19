import Lightlike.OperatorAlgebras.MomentumBoundary
import Physlib.QuantumMechanics.Operators.Unbounded

/-!
# The self-adjoint extensions of the momentum on `L²(0, 1)`

Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Section 5.3, eq. (14), p. 8, and Appendix A.3, p. 19 (read): the closed momentum
`P = -i d/dx` on `[0, L]` has the domain `D₀ = {ψ ∈ D_max : ψ(0) = ψ(L) = 0}`, and its self-adjoint extensions are the operators `P_θ` with
domain `D_θ = {ψ ∈ D_max : ψ(L) = e^{iθ} ψ(0)}`. Here `L = 1`: `momentumZero`, the adjoint on `domZero`, is the closure of `momentumMin`
(`momentumZero_eq_closure`); `momentumTheta θ`, the adjoint on `domTheta θ`, is self-adjoint (`momentumTheta_isSelfAdjoint`); and a
self-adjoint extension of the momentum is some `momentumTheta θ` (`selfAdjoint_extensions_momentumZero`,
`selfAdjoint_extensions_eq_momentumTheta`). The proof uses the boundary form: the closure has zero boundary values, the boundary form vanishes
on `D_θ` since `|e^{iθ}| = 1`, and on the domain of a self-adjoint extension the boundary values `(y(0), y(1))` lie on one isotropic line,
`y(1) = e^{iθ} y(0)`.
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

/-- **The domain `D_θ`** of Bonneau-Faraut-Valent's eq. (14): the vectors of `D(A†)` with `y(1) = e^{iθ} y(0)`. -/
noncomputable def domTheta (θ : ℝ) : Submodule ℂ L2I :=
  (LinearMap.ker (bv1L - Complex.exp (θ * Complex.I) • bv0L)).map (momentumMin†).domain.subtype

lemma mem_domTheta {θ : ℝ} {y : L2I} :
    y ∈ domTheta θ ↔ ∃ h : y ∈ (momentumMin†).domain, bv1 ⟨y, h⟩ = Complex.exp (θ * Complex.I) * bv0 ⟨y, h⟩ := by
  constructor
  · rintro ⟨y', hy', rfl⟩
    refine ⟨y'.2, ?_⟩
    have := sub_eq_zero.mp (LinearMap.mem_ker.mp hy')
    simpa [bv1L, bv0L] using this
  · rintro ⟨h, hb⟩
    refine ⟨⟨y, h⟩, LinearMap.mem_ker.mpr (sub_eq_zero.mpr ?_), rfl⟩
    simpa [bv1L, bv0L] using hb

/-- **The extension `P_θ`**: `A†` on `D_θ`. -/
noncomputable def momentumTheta (θ : ℝ) : L2I →ₗ.[ℂ] L2I := (momentumMin†).domRestrict (domTheta θ)

lemma momentumTheta_domain (θ : ℝ) : (momentumTheta θ).domain = domTheta θ := by
  rw [momentumTheta, LinearPMap.domRestrict_domain]
  refine inf_eq_left.mpr fun y hy => ?_
  obtain ⟨h, -⟩ := mem_domTheta.mp hy
  exact h

lemma momentumTheta_apply (θ : ℝ) (y : (momentumTheta θ).domain) :
    (momentumTheta θ y : L2I) = momentumMin† ⟨(y : L2I), (Submodule.mem_inf.mp y.2).2⟩ :=
  LinearPMap.domRestrict_apply rfl

lemma norm_exp_I (θ : ℝ) : (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  simp

/-- The boundary form vanishes on `D_θ`. -/
lemma boundary_form_theta {θ : ℝ} {y z : (momentumMin†).domain}
    (hy : bv1 y = Complex.exp (θ * Complex.I) * bv0 y) (hz : bv1 z = Complex.exp (θ * Complex.I) * bv0 z) :
    ⟪(momentumMin† y : L2I), (z : L2I)⟫_ℂ = ⟪(y : L2I), (momentumMin† z : L2I)⟫_ℂ := by
  have hb := boundary_form_momentum y z
  rw [hy, hz, map_mul] at hb
  have : (starRingEnd ℂ) (Complex.exp (θ * Complex.I)) * (starRingEnd ℂ) (bv0 y) * (Complex.exp (θ * Complex.I) * bv0 z) -
      (starRingEnd ℂ) (bv0 y) * bv0 z = 0 := by
    have e := norm_exp_I θ
    linear_combination ((starRingEnd ℂ) (bv0 y) * bv0 z) * e
  rw [this, mul_zero] at hb
  exact sub_eq_zero.mp hb

/-- Integration by parts for two test functions: `∫ (f' conj g + f conj g') = 0` over `(0, 1)`. -/
lemma integral_deriv_conj_add (f g : testFunctions) :
    ∫ x in Ioo (0 : ℝ) 1, (deriv f.1 x * (starRingEnd ℂ) (g.1 x) + f.1 x * (starRingEnd ℂ) (deriv g.1 x)) = 0 := by
  have hf := f.2.1
  have hg := g.2.1
  have hd : ∀ x, HasDerivAt (fun x => f.1 x * (starRingEnd ℂ) (g.1 x))
      (deriv f.1 x * (starRingEnd ℂ) (g.1 x) + f.1 x * (starRingEnd ℂ) (deriv g.1 x)) x := by
    intro x
    exact ((hf.differentiable (by norm_num) x).hasDerivAt).mul ((hg.differentiable (by norm_num) x).hasDerivAt).star
  have hc : Continuous fun x => deriv f.1 x * (starRingEnd ℂ) (g.1 x) + f.1 x * (starRingEnd ℂ) (deriv g.1 x) :=
    ((continuous_deriv_of_two hf).mul (continuous_star.comp hg.continuous)).add
      (hf.continuous.mul (continuous_star.comp (continuous_deriv_of_two hg)))
  have h0 : f.1 0 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (f.2.2 h).1
  have h1 : f.1 1 = 0 := image_eq_zero_of_notMem_tsupport fun h => by simpa using (f.2.2 h).2
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable 0 1)
  rw [h0, h1] at key
  simp only [zero_mul, sub_zero] at key
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at key
  exact key

/-- The inner product of two classes is the integral of the functions. -/
lemma inner_classI_classI {a b : ℝ → ℂ} (ha : Continuous a) (hsa : tsupport a ⊆ Ioo (0 : ℝ) 1) (hb : Continuous b)
    (hsb : tsupport b ⊆ Ioo (0 : ℝ) 1) :
    ⟪classI a ha hsa, classI b hb hsb⟫_ℂ = ∫ x in Ioo (0 : ℝ) 1, b x * (starRingEnd ℂ) (a x) := by
  rw [inner_classI_right]
  refine integral_congr_ae ?_
  have h1 : (classI a ha hsa : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] a := MemLp.coeFn_toLp _
  filter_upwards [h1] with x hx
  rw [hx]

/-- **The momentum without boundary conditions is symmetric**. -/
theorem momentumMin_symm (x y : momentumMin.domain) :
    ⟪(momentumMin x : L2I), (y : L2I)⟫_ℂ = ⟪(x : L2I), (momentumMin y : L2I)⟫_ℂ := by
  obtain ⟨f, hf⟩ := mem_momentumMin_domain.mp x.2
  obtain ⟨g, hg⟩ := mem_momentumMin_domain.mp y.2
  have hxd : (momentumPair f).1 ∈ momentumMin.domain := by rw [show (momentumPair f).1 = (x : L2I) from hf]; exact x.2
  have hyd : (momentumPair g).1 ∈ momentumMin.domain := by rw [show (momentumPair g).1 = (y : L2I) from hg]; exact y.2
  have ex : x = ⟨(momentumPair f).1, hxd⟩ := Subtype.ext hf.symm
  have ey : y = ⟨(momentumPair g).1, hyd⟩ := Subtype.ext hg.symm
  rw [ex, ey, momentumMin_apply, momentumMin_apply]
  simp only [momentumPair, inner_smul_left, inner_smul_right, inner_classI_classI]
  have key := integral_deriv_conj_add g f
  have i1 : IntegrableOn (fun x => deriv g.1 x * (starRingEnd ℂ) (f.1 x)) (Ioo (0 : ℝ) 1) :=
    ((continuous_deriv_of_two g.2.1).mul (continuous_star.comp f.2.1.continuous)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have i2 : IntegrableOn (fun x => g.1 x * (starRingEnd ℂ) (deriv f.1 x)) (Ioo (0 : ℝ) 1) :=
    (g.2.1.continuous.mul (continuous_star.comp (continuous_deriv_of_two f.2.1))).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [integral_add i1 i2] at key
  simp only [map_neg, Complex.conj_I, neg_neg]
  linear_combination Complex.I * key

lemma momentumMin_isSymmetric : momentumMin.IsSymmetric := fun x y => momentumMin_symm x y

lemma momentumMin_isUnbounded : momentumMin.IsUnbounded :=
  ⟨dense_momentumMin_domain, momentumMin_isSymmetric.isClosable dense_momentumMin_domain⟩

lemma momentumMin_closure_adjoint : momentumMin.closure† = momentumMin† :=
  momentumMin_isUnbounded.adjoint_closure_eq_adjoint

lemma closure_le_adjoint : momentumMin.closure ≤ momentumMin† :=
  momentumMin_isSymmetric.closure_le_adjoint dense_momentumMin_domain

/-- **The closure has zero boundary values** (Bonneau-Faraut-Valent, Appendix A.3: `D₀ = {ψ ∈ D_max : ψ(0) = ψ(L) = 0}`, one inclusion). -/
theorem bv_closure (y : momentumMin.closure.domain) :
    bv0 ⟨(y : L2I), closure_le_adjoint.1 y.2⟩ = 0 ∧ bv1 ⟨(y : L2I), closure_le_adjoint.1 y.2⟩ = 0 := by
  set y' : (momentumMin†).domain := ⟨(y : L2I), closure_le_adjoint.1 y.2⟩
  have hAy : (momentumMin† y' : L2I) = momentumMin.closure y := (closure_le_adjoint.2 (x := y) (y := y') rfl).symm
  have hd : Dense (momentumMin.closure.domain : Set L2I) := LinearPMap.HasDenseDomain.closure dense_momentumMin_domain
  have hzero : ∀ z : (momentumMin†).domain, ⟪(momentumMin† y' : L2I), (z : L2I)⟫_ℂ = ⟪(y' : L2I), (momentumMin† z : L2I)⟫_ℂ := by
    intro z
    let z' : (momentumMin.closure†).domain := ⟨(z : L2I), momentumMin_closure_adjoint.symm.le.1 z.2⟩
    have hz : (momentumMin.closure† z' : L2I) = momentumMin† z := momentumMin_closure_adjoint.le.2 (x := z') (y := z) rfl
    have hfa := LinearPMap.adjoint_isFormalAdjoint hd z' y
    rw [hAy, ← hz]
    have h2 := congrArg (starRingEnd ℂ) hfa
    simp only [inner_conj_symm] at h2
    exact h2.symm
  have hb0 := boundary_form_momentum y' (linD 1 0)
  have hb1 := boundary_form_momentum y' (linD 0 1)
  rw [hzero, sub_self] at hb0 hb1
  obtain ⟨a0, a1⟩ := bv_linVec 1 0
  obtain ⟨c0, c1⟩ := bv_linVec 0 1
  have a0' : bv0 (linD 1 0) = 1 := a0
  have a1' : bv1 (linD 1 0) = 0 := a1
  have c0' : bv0 (linD 0 1) = 0 := c0
  have c1' : bv1 (linD 0 1) = 1 := c1
  rw [a0', a1'] at hb0
  rw [c0', c1'] at hb1
  simp only [mul_zero, mul_one, zero_sub, sub_zero] at hb0 hb1
  constructor
  · have : (starRingEnd ℂ) (bv0 y') = 0 := by
      have := hb0.symm; simpa using this
    simpa using this
  · have : (starRingEnd ℂ) (bv1 y') = 0 := by
      have := hb1.symm; simpa using this
    simpa using this

lemma linD_mem_domTheta (θ : ℝ) : (linD 1 (Complex.exp (θ * Complex.I)) : L2I) ∈ domTheta θ := by
  refine mem_domTheta.mpr ⟨(linD 1 _).2, ?_⟩
  obtain ⟨h0, h1⟩ := bv_linVec 1 (Complex.exp (θ * Complex.I))
  have key : bv1 (linD 1 (Complex.exp (θ * Complex.I))) =
      Complex.exp (θ * Complex.I) * bv0 (linD 1 (Complex.exp (θ * Complex.I))) := by
    show bv1 ⟨linVec 1 _, linVec_mem 1 _⟩ = _ * bv0 ⟨linVec 1 _, linVec_mem 1 _⟩
    rw [h0, h1, mul_one]
  exact key

/-- **`Ā ≤ P_θ`**: the closure of the momentum is contained in every `P_θ`. -/
theorem closure_le_momentumTheta (θ : ℝ) : momentumMin.closure ≤ momentumTheta θ := by
  refine ⟨fun y hy => ?_, fun y z hyz => ?_⟩
  · rw [momentumTheta_domain]
    obtain ⟨b0, b1⟩ := bv_closure ⟨y, hy⟩
    exact mem_domTheta.mpr ⟨closure_le_adjoint.1 hy, by rw [b0, b1, mul_zero]⟩
  · rw [momentumTheta_apply]
    exact closure_le_adjoint.2 hyz

lemma dense_momentumTheta (θ : ℝ) : Dense ((momentumTheta θ).domain : Set L2I) :=
  dense_momentumMin_domain.mono fun _ hx => (closure_le_momentumTheta θ).1 ((momentumMin.le_closure).1 hx)

/-- `P_θ` is symmetric: the boundary form vanishes on `D_θ`. -/
lemma momentumTheta_symm (θ : ℝ) (u v : (momentumTheta θ).domain) :
    ⟪(momentumTheta θ u : L2I), (v : L2I)⟫_ℂ = ⟪(u : L2I), (momentumTheta θ v : L2I)⟫_ℂ := by
  have hu : (u : L2I) ∈ domTheta θ := (Submodule.mem_inf.mp u.2).1
  have hv : (v : L2I) ∈ domTheta θ := (Submodule.mem_inf.mp v.2).1
  obtain ⟨hu1, hu2⟩ := mem_domTheta.mp hu
  obtain ⟨hv1, hv2⟩ := mem_domTheta.mp hv
  rw [momentumTheta_apply, momentumTheta_apply]
  exact boundary_form_theta hu2 hv2

/-- **`P_θ` is self-adjoint** (Bonneau-Faraut-Valent, Section 5.3, eq. (14)). -/
theorem momentumTheta_isSelfAdjoint (θ : ℝ) : IsSelfAdjoint (momentumTheta θ) := by
  have hd := dense_momentumTheta θ
  have hle : momentumTheta θ ≤ (momentumTheta θ)† :=
    (LinearPMap.isSymmetric_iff_le_adjoint hd).mp fun u v => momentumTheta_symm θ u v
  have hAP : momentumMin ≤ momentumTheta θ := momentumMin.le_closure.trans (closure_le_momentumTheta θ)
  have hPA : (momentumTheta θ)† ≤ momentumMin† := LinearPMap.adjoint_antitone (Or.inl dense_momentumMin_domain) hAP
  have hge : (momentumTheta θ)† ≤ momentumTheta θ := by
    refine ⟨fun y hy => ?_, fun y z hyz => ?_⟩
    · let y' : (momentumMin†).domain := ⟨y, hPA.1 hy⟩
      have hAy : (momentumMin† y' : L2I) = (momentumTheta θ)† ⟨y, hy⟩ := (hPA.2 (x := ⟨y, hy⟩) (y := y') rfl).symm
      set e := Complex.exp (θ * Complex.I)
      have hzθ := linD_mem_domTheta θ
      let zP : (momentumTheta θ).domain := ⟨(linD 1 e : L2I), by rw [momentumTheta_domain]; exact hzθ⟩
      have hfa := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ zP
      have hPz : (momentumTheta θ zP : L2I) = momentumMin† (linD 1 e) := by rw [momentumTheta_apply]
      have hb := boundary_form_momentum y' (linD 1 e)
      have h0 : ⟪(momentumMin† y' : L2I), ((linD 1 e : (momentumMin†).domain) : L2I)⟫_ℂ =
          ⟪(y' : L2I), (momentumMin† (linD 1 e) : L2I)⟫_ℂ := by
        rw [hAy, ← hPz]; exact hfa
      rw [h0, sub_self] at hb
      obtain ⟨b0, b1⟩ := bv_linVec 1 e
      have b0' : bv0 (linD 1 e) = 1 := b0
      have b1' : bv1 (linD 1 e) = e := b1
      rw [b0', b1', mul_one] at hb
      have hI : (starRingEnd ℂ) (bv1 y') * e - (starRingEnd ℂ) (bv0 y') = 0 :=
        (mul_eq_zero.mp hb.symm).resolve_left Complex.I_ne_zero
      have hc := congrArg (starRingEnd ℂ) (sub_eq_zero.mp hI)
      simp only [map_mul, Complex.conj_conj] at hc
      rw [momentumTheta_domain]
      refine mem_domTheta.mpr ⟨hPA.1 hy, ?_⟩
      have hn : (starRingEnd ℂ) e * e = 1 := norm_exp_I θ
      show bv1 y' = e * bv0 y'
      rw [← hc]
      linear_combination (-(bv1 y')) * hn
    · rw [momentumTheta_apply]
      have := (hPA.2 (x := y) (y := ⟨(z : L2I), (Submodule.mem_inf.mp z.2).2⟩) hyz)
      exact this
  exact le_antisymm hge hle

/-- **Every self-adjoint extension of the momentum is a `P_θ`** (Bonneau-Faraut-Valent, Section 5.3, eq. (14)): a self-adjoint `B ⊇ Ā` is `P_θ`
for some real `θ`. -/
theorem eq_momentumTheta_of_selfAdjoint {B : L2I →ₗ.[ℂ] L2I} (hAB : momentumMin.closure ≤ B) (hB : IsSelfAdjoint B) :
    ∃ θ : ℝ, B = momentumTheta θ := by
  have hdC : Dense (momentumMin.closure.domain : Set L2I) := LinearPMap.HasDenseDomain.closure dense_momentumMin_domain
  have hdB : Dense (B.domain : Set L2I) := hdC.mono hAB.1
  have hBB : B† = B := hB
  have hBA : B ≤ momentumMin† := by
    have h := LinearPMap.adjoint_antitone (Or.inl hdC) hAB
    rw [hBB, momentumMin_closure_adjoint] at h
    exact h
  let toD : B.domain → (momentumMin†).domain := fun u => ⟨(u : L2I), hBA.1 u.2⟩
  have hval : ∀ u : B.domain, (momentumMin† (toD u) : L2I) = B u := fun u => (hBA.2 (x := u) (y := toD u) rfl).symm
  -- the boundary form vanishes on `D(B)`
  have hiso : ∀ u v : B.domain,
      (starRingEnd ℂ) (bv1 (toD u)) * bv1 (toD v) = (starRingEnd ℂ) (bv0 (toD u)) * bv0 (toD v) := by
    intro u v
    have hb := boundary_form_momentum (toD u) (toD v)
    have hs : ⟪(B u : L2I), (v : L2I)⟫_ℂ = ⟪(u : L2I), (B v : L2I)⟫_ℂ := by
      have := (LinearPMap.isSymmetric_iff_le_adjoint hdB).mpr (by rw [hBB]) u v
      exact this
    rw [hval, hval, hs, sub_self] at hb
    exact sub_eq_zero.mp ((mul_eq_zero.mp hb.symm).resolve_left Complex.I_ne_zero)
  -- some vector of `D(B)` has a nonzero boundary value
  have hex : ∃ u : B.domain, bv0 (toD u) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ u : B.domain, bv1 (toD u) = 0 := by
      intro u
      have h := hiso u u
      rw [hcon u, mul_zero] at h
      have : ‖bv1 (toD u)‖ ^ 2 = 0 := by
        have h2 : ((‖bv1 (toD u)‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [← h, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        exact_mod_cast h2
      simpa using this
    -- then every `z ∈ D(A†)` lies in `D(B†) = D(B)`
    have hsub : ∀ z : (momentumMin†).domain, (z : L2I) ∈ B.domain := by
      intro z
      have hz : (z : L2I) ∈ (B†).domain := by
        refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨momentumMin† z, fun u => ?_⟩
        have hb := boundary_form_momentum (toD u) z
        simp only [hcon u, hall u, map_zero, zero_mul, sub_zero, mul_zero] at hb
        rw [hval] at hb
        have h2 := congrArg (starRingEnd ℂ) (sub_eq_zero.mp hb)
        simp only [inner_conj_symm] at h2
        exact h2.symm
      rw [hBB] at hz
      exact hz
    obtain ⟨c0, c1⟩ := bv_linVec 0 1
    have hu := hsub (linD 0 1)
    have h1 := hall ⟨_, hu⟩
    have : bv1 (toD ⟨_, hu⟩) = bv1 (linD 0 1) := rfl
    rw [this] at h1
    have c1' : bv1 (linD 0 1) = 1 := c1
    rw [c1'] at h1
    exact one_ne_zero h1
  obtain ⟨u₀, hu₀⟩ := hex
  set a := bv0 (toD u₀)
  set b := bv1 (toD u₀)
  have hab := hiso u₀ u₀
  have hna : ‖b‖ = ‖a‖ := by
    have h1 : ((‖b‖ ^ 2 : ℝ) : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_conj_mul_self]; exact hab
    have h2 : ‖b‖ ^ 2 = ‖a‖ ^ 2 := by exact_mod_cast h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  set e : ℂ := b / a
  have he : ‖e‖ = 1 := by rw [norm_div, hna, div_self (norm_ne_zero_iff.mpr hu₀)]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Complex.exp (θ * Complex.I) = e := by
    refine ⟨Complex.arg e, ?_⟩
    have := Complex.norm_mul_exp_arg_mul_I e
    rw [he, Complex.ofReal_one, one_mul] at this
    exact this
  refine ⟨θ, ?_⟩
  -- `D(B) ⊆ D_θ`
  have hBθ : B ≤ momentumTheta θ := by
    refine ⟨fun v hv => ?_, fun v z hvz => ?_⟩
    · rw [momentumTheta_domain]
      refine mem_domTheta.mpr ⟨hBA.1 hv, ?_⟩
      have h := hiso u₀ ⟨v, hv⟩
      show bv1 (toD ⟨v, hv⟩) = _ * bv0 (toD ⟨v, hv⟩)
      have hb' : b = e * a := (div_mul_cancel₀ b hu₀).symm
      have hca : (starRingEnd ℂ) a ≠ 0 := by simpa using hu₀
      rw [hθ]
      have h' : (starRingEnd ℂ) (e * a) * bv1 (toD ⟨v, hv⟩) = (starRingEnd ℂ) a * bv0 (toD ⟨v, hv⟩) := by rw [← hb']; exact h
      rw [map_mul] at h'
      have hn : (starRingEnd ℂ) e * e = 1 := by
        rw [Complex.conj_mul', he]; simp
      have : (starRingEnd ℂ) a * ((starRingEnd ℂ) e * bv1 (toD ⟨v, hv⟩) - bv0 (toD ⟨v, hv⟩)) = 0 := by
        linear_combination h'
      have h3 := (mul_eq_zero.mp this).resolve_left hca
      linear_combination e * h3 - (bv1 (toD ⟨v, hv⟩)) * hn
    · rw [momentumTheta_apply]
      exact hBA.2 hvz
  have hθB : momentumTheta θ ≤ B := by
    have h := LinearPMap.adjoint_antitone (Or.inl hdB) hBθ
    rw [hBB, show (momentumTheta θ)† = momentumTheta θ from momentumTheta_isSelfAdjoint θ] at h
    exact h
  exact le_antisymm hBθ hθB

/-- **The self-adjoint extensions of the momentum on `L²(0, 1)` are exactly the `P_θ`** (Bonneau-Faraut-Valent, Section 5.3, eq. (14), read):
every `P_θ` is a self-adjoint extension of the closure of `-i d/dx`, and every self-adjoint extension is a `P_θ`. -/
theorem selfAdjoint_extensions_eq_momentumTheta (B : L2I →ₗ.[ℂ] L2I) :
    (momentumMin.closure ≤ B ∧ IsSelfAdjoint B) ↔ ∃ θ : ℝ, B = momentumTheta θ := by
  constructor
  · rintro ⟨hAB, hB⟩
    exact eq_momentumTheta_of_selfAdjoint hAB hB
  · rintro ⟨θ, rfl⟩
    exact ⟨closure_le_momentumTheta θ, momentumTheta_isSelfAdjoint θ⟩

/-- **The domain `D₀`** of Bonneau-Faraut-Valent's Appendix A.3: the vectors of `D(A†)` with `y(0) = y(1) = 0`. -/
noncomputable def domZero : Submodule ℂ L2I :=
  (LinearMap.ker bv0L ⊓ LinearMap.ker bv1L).map (momentumMin†).domain.subtype

lemma mem_domZero {y : L2I} :
    y ∈ domZero ↔ ∃ h : y ∈ (momentumMin†).domain, bv0 ⟨y, h⟩ = 0 ∧ bv1 ⟨y, h⟩ = 0 := by
  constructor
  · rintro ⟨y', ⟨h0, h1⟩, rfl⟩
    exact ⟨y'.2, h0, h1⟩
  · rintro ⟨h, h0, h1⟩
    exact ⟨⟨y, h⟩, ⟨h0, h1⟩, rfl⟩

/-- **The minimal momentum `P` on `D₀`** of Appendix A.3: `A†` restricted to `D₀`. -/
noncomputable def momentumZero : L2I →ₗ.[ℂ] L2I := (momentumMin†).domRestrict domZero

lemma momentumZero_domain : momentumZero.domain = domZero := by
  rw [momentumZero, LinearPMap.domRestrict_domain]
  refine inf_eq_left.mpr fun y hy => ?_
  obtain ⟨h, -⟩ := mem_domZero.mp hy
  exact h

lemma momentumZero_apply (y : momentumZero.domain) :
    (momentumZero y : L2I) = momentumMin† ⟨(y : L2I), (Submodule.mem_inf.mp y.2).2⟩ :=
  LinearPMap.domRestrict_apply rfl

lemma closure_le_momentumZero : momentumMin.closure ≤ momentumZero := by
  refine ⟨fun y hy => ?_, fun y z hyz => ?_⟩
  · rw [momentumZero_domain]
    obtain ⟨b0, b1⟩ := bv_closure ⟨y, hy⟩
    exact mem_domZero.mpr ⟨closure_le_adjoint.1 hy, b0, b1⟩
  · rw [momentumZero_apply]
    exact closure_le_adjoint.2 hyz

lemma momentumZero_le_momentumTheta (θ : ℝ) : momentumZero ≤ momentumTheta θ := by
  refine ⟨fun y hy => ?_, fun y z hyz => ?_⟩
  · rw [momentumZero_domain] at hy
    rw [momentumTheta_domain]
    obtain ⟨h, h0, h1⟩ := mem_domZero.mp hy
    exact mem_domTheta.mpr ⟨h, by rw [h0, h1, mul_zero]⟩
  · rw [momentumZero_apply, momentumTheta_apply]
    congr 1
    exact Subtype.ext hyz

/-- **Eq. (14) of Bonneau-Faraut-Valent, Section 5.3** (read): the self-adjoint extensions of the momentum `P` on `D₀` (Appendix A.3) are exactly
the operators `P_θ`, `-i d/dx` on `D_θ = {ψ ∈ D_max : ψ(1) = e^{iθ} ψ(0)}`, `θ` real. -/
theorem selfAdjoint_extensions_momentumZero (B : L2I →ₗ.[ℂ] L2I) :
    (momentumZero ≤ B ∧ IsSelfAdjoint B) ↔ ∃ θ : ℝ, B = momentumTheta θ := by
  constructor
  · rintro ⟨hAB, hB⟩
    exact eq_momentumTheta_of_selfAdjoint (closure_le_momentumZero.trans hAB) hB
  · rintro ⟨θ, rfl⟩
    exact ⟨momentumZero_le_momentumTheta θ, momentumTheta_isSelfAdjoint θ⟩

/-- **`D₀` is the domain of the closure** (Bonneau-Faraut-Valent, Appendix A.3, read: the closed momentum `P` has the domain
`D₀ = {ψ ∈ D_max : ψ(0) = ψ(L) = 0}`): `A†` on the vectors with zero boundary values is the closure of `momentumMin`. The closure is `A††`
(Physlib's `adjoint_adjoint_eq_closure`), and a vector with zero boundary values lies in `D(A††)` by the boundary form. -/
theorem momentumZero_eq_closure : momentumZero = momentumMin.closure := by
  have hdA : Dense ((momentumMin†).domain : Set L2I) :=
    dense_momentumMin_domain.mono fun x hx => closure_le_adjoint.1 ((momentumMin.le_closure).1 hx)
  have hkey : ∀ (y : momentumZero.domain) (z : (momentumMin†).domain),
      ⟪(momentumZero y : L2I), (z : L2I)⟫_ℂ = ⟪(y : L2I), (momentumMin† z : L2I)⟫_ℂ := by
    intro y z
    have hy : (y : L2I) ∈ domZero := (Submodule.mem_inf.mp y.2).1
    obtain ⟨h, h0, h1⟩ := mem_domZero.mp hy
    have hb := boundary_form_momentum ⟨(y : L2I), h⟩ z
    simp only [h0, h1, map_zero, zero_mul, sub_zero, mul_zero] at hb
    rw [momentumZero_apply]
    exact sub_eq_zero.mp hb
  rw [← momentumMin_isUnbounded.adjoint_adjoint_eq_closure]
  have h1 : momentumZero ≤ momentumMin†† := by
    refine ⟨fun y hy => ?_, fun y w hyw => ?_⟩
    · exact LinearPMap.mem_adjoint_domain_of_exists y ⟨momentumZero ⟨y, hy⟩, fun z => hkey ⟨y, hy⟩ z⟩
    · refine (LinearPMap.adjoint_apply_eq hdA w fun z => ?_).symm
      rw [← hyw]
      exact hkey y z
  have h2 : momentumMin†† ≤ momentumZero := by
    rw [momentumMin_isUnbounded.adjoint_adjoint_eq_closure]
    exact closure_le_momentumZero
  exact le_antisymm h1 h2

end Lightlike.OperatorAlgebras
