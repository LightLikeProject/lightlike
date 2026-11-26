import Mathlib
import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.Lorentzian
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Lightlike.Spacetime.Causal.TimeOrientation
import Lightlike.Spacetime.Causal.CurveMargin
import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.Ladder

/-!
# Minkowski space with time rolled up: the cylinder `S¹ × ℝ`

The spacetime `S¹ × ℝ` with the flat metric `-dθ² + dx²`: the quotient of 1+1 Minkowski space by the time translation
`(t, x) ↦ (t + 2π, x)`. Here `S¹` is the unit circle of `ℂ` (Mathlib's manifold `Circle`, model `𝓡 1`), the manifold `Circle × ℝ`
has the product model, and the metric `timeCylinderMetric` is the pullback of the form `-⟪z, z'⟫ + s s'` of `ℂ × ℝ` by the
embedding `(z, s) ↦ (z, s)`. The curve `θ ↦ (exp (iθ), x)` is a closed timelike curve, so the cylinder violates chronology.
-/

open Manifold Metric Bundle TopologicalSpace
open scoped ContDiff RealInnerProductSpace

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

/-- The cylinder `S¹ × ℝ`, with `S¹` the unit circle of `ℂ`. -/
abbrev TimeCylinder : Type := Circle × ℝ

/-- the model of the cylinder -/
abbrev ICyl : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 1) × ℝ) (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) :=
  (𝓡 1).prod 𝓘(ℝ, ℝ)

example : IsManifold ICyl ∞ TimeCylinder := inferInstance

/-- The embedding of the cylinder into `ℂ × ℝ`. -/
def cylEmb (p : TimeCylinder) : ℂ × ℝ := ((p.1 : ℂ), p.2)

attribute [local instance] finrank_real_complex_fact'

theorem contMDiff_circleCoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
  contMDiff_coe_sphere

theorem contMDiff_cylEmb : ContMDiff ICyl 𝓘(ℝ, ℂ × ℝ) ∞ cylEmb := by
  have h1 : ContMDiff ICyl 𝓘(ℝ, ℂ) ∞ (fun p : TimeCylinder => (p.1 : ℂ)) :=
    contMDiff_circleCoe.comp (contMDiff_fst (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)))
  have h2 : ContMDiff ICyl 𝓘(ℝ, ℝ) ∞ (fun p : TimeCylinder => p.2) :=
    contMDiff_snd (I := 𝓡 1) (J := 𝓘(ℝ, ℝ))
  exact h1.prodMk_space h2

/-- The real inner product of `ℂ` as a bilinear map. -/
def LinnerC : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := innerSL ℝ

/-- The form `-⟪z, z'⟫ + s s'` of `ℂ × ℝ`. -/
def Lcyl : (ℂ × ℝ) →L[ℝ] (ℂ × ℝ) →L[ℝ] ℝ :=
  (-LinnerC).bilinearComp (ContinuousLinearMap.fst ℝ ℂ ℝ) (ContinuousLinearMap.fst ℝ ℂ ℝ)
    + (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.snd ℝ ℂ ℝ) (ContinuousLinearMap.snd ℝ ℂ ℝ)

theorem LinnerC_apply (a b : ℂ) : LinnerC a b = inner ℝ a b := rfl

theorem Lcyl_apply (x y : ℂ × ℝ) : Lcyl x y = -inner ℝ x.1 y.1 + x.2 * y.2 := by
  simp [Lcyl, LinnerC_apply]

/-- The derivative of the inclusion of the circle into `ℂ`. -/
def dcoeC (z : Circle) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ :=
  mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) z

theorem hasMFDerivAt_circleCoe (z : Circle) :
    HasMFDerivAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) z (dcoeC z) :=
  (contMDiff_circleCoe.mdifferentiableAt (by simp)).hasMFDerivAt

/-- The derivative of the embedding of the cylinder: `(u, s) ↦ (dcoeC u, s)`. -/
theorem dι_cylEmb (p : TimeCylinder) (u : TangentSpace ICyl p) :
    dι (I := ICyl) cylEmb p u = (dcoeC p.1 u.1, u.2) := by
  have h1 : HasMFDerivAt ICyl 𝓘(ℝ, ℂ) (fun p : TimeCylinder => (p.1 : ℂ))
      p ((dcoeC p.1).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)) := by
    have := (hasMFDerivAt_circleCoe p.1).comp p (hasMFDerivAt_fst (I := 𝓡 1) (I' := 𝓘(ℝ, ℝ)) p)
    exact this
  have h2 : HasMFDerivAt ICyl 𝓘(ℝ, ℝ) (fun p : TimeCylinder => p.2) p
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 1)) ℝ) :=
    hasMFDerivAt_snd (I := 𝓡 1) (I' := 𝓘(ℝ, ℝ)) p
  have h := h1.prodMk h2
  unfold dι
  have : HasMFDerivAt ICyl 𝓘(ℝ, ℂ × ℝ) cylEmb p _ := h
  rw [this.mfderiv]
  rfl

theorem injective_dcoeC (z : Circle) : Function.Injective (dcoeC z) :=
  injective_mvfderiv_subtypeVal_sphere (E := ℂ) (n := 1) z

/-- **A form `-⟪dcoeC z u, dcoeC z u'⟫ + s s'` on `E¹ × ℝ` is Lorentzian** (a Lorentz frame is the unit tangent vector of the
circle and `∂_s`). -/
theorem isLorentzianForm_cyl (z : Circle) (B : (EuclideanSpace ℝ (Fin 1) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin 1) × ℝ) →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = -inner ℝ (dcoeC z v.1) (dcoeC z w.1) + v.2 * w.2) : IsLorentzianForm 2 B := by
  set u0 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hu0
  have hu0ne : u0 ≠ 0 := by
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
    simp [hu0] at this
  have hd0 : dcoeC z u0 ≠ 0 := fun h => hu0ne (injective_dcoeC z (h.trans (map_zero _).symm))
  set c : ℝ := ‖dcoeC z u0‖ with hc
  have hcpos : 0 < c := norm_pos_iff.2 hd0
  have hcne : c ≠ 0 := hcpos.ne'
  have hcc : inner ℝ (dcoeC z u0) (dcoeC z u0) = c ^ 2 := by
    rw [real_inner_self_eq_norm_sq]
  let fe : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv
  let B1 : Module.Basis (Fin 1) ℝ (EuclideanSpace ℝ (Fin 1)) :=
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.map
      (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin 1)) c⁻¹ (inv_ne_zero hcne))
  let B2 : Module.Basis (Fin 1) ℝ ℝ := Module.Basis.singleton (Fin 1) ℝ
  let Bs : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 1) × ℝ) := (B1.prod B2).reindex fe
  refine ⟨Bs, fun i j => ?_⟩
  obtain ⟨k, rfl⟩ := fe.surjective i
  obtain ⟨l, rfl⟩ := fe.surjective j
  have hB' : ∀ m, Bs (fe m) = (B1.prod B2) m := fun m => by
    show ((B1.prod B2).reindex fe) (fe m) = _
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  have e1 : ∀ k : Fin 1, Bs (fe (Sum.inl k)) = (c⁻¹ • u0, (0 : ℝ)) := fun k => by
    rw [hB']
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simp [B1, hu0]
  have e2 : ∀ k : Fin 1, Bs (fe (Sum.inr k)) = ((0 : EuclideanSpace ℝ (Fin 1)), (1 : ℝ)) := fun k => by
    rw [hB']; simp [B2]
  have hd : etaDiag (fe (Sum.inl (0 : Fin 1))) = -1 := by
    have h0 : ((fe (Sum.inl (0 : Fin 1)) : Fin 2) : ℕ) = 0 := rfl
    unfold etaDiag; rw [if_pos h0]
  have hd' : etaDiag (fe (Sum.inr (0 : Fin 1))) = 1 := by
    have h1 : ((fe (Sum.inr (0 : Fin 1)) : Fin 2) : ℕ) = 1 := rfl
    unfold etaDiag; rw [if_neg (by rw [h1]; omega)]
  have hne : ∀ k l : Fin 1, fe (Sum.inl k) ≠ fe (Sum.inr l) := fun k l h => by
    simpa using fe.injective h
  rcases k with k | k <;> rcases l with l | l
  · rw [e1, e1, hB]
    have hk : k = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    subst hk hl
    rw [eta_apply, if_pos rfl, hd]
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right, hcc]
    field_simp
    simp
  · rw [e1, e2, hB, eta_apply, if_neg (hne _ _)]
    simp
  · rw [e2, e1, hB, eta_apply, if_neg (hne _ _).symm]
    simp
  · rw [e2, e2, hB]
    have hk : k = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    subst hk hl
    rw [eta_apply, if_pos rfl, hd']
    simp

/-- **The flat metric `-dθ² + dx²` of Minkowski space with time rolled up**, on the cylinder `S¹ × ℝ`. -/
def timeCylinderMetric : LorentzianMetric ICyl TimeCylinder 2 where
  g := pullbackForm (I := ICyl) Lcyl cylEmb
  contMDiff := contMDiff_pullbackForm Lcyl contMDiff_cylEmb
  lorentzian p := isLorentzianForm_cyl p.1 _ fun v w => by
    refine (pullbackForm_apply (I := ICyl) Lcyl cylEmb p v w).trans ?_
    rw [dι_cylEmb p v, dι_cylEmb p w, Lcyl_apply]

/-- The value of the metric: `g(v, w) = -⟪dcoeC v₁, dcoeC w₁⟫ + v₂ w₂`. -/
theorem timeCylinderMetric_apply (p : TimeCylinder) (v w : TangentSpace ICyl p) :
    timeCylinderMetric.g p v w = -inner ℝ (dcoeC p.1 v.1) (dcoeC p.1 w.1) + v.2 * w.2 := by
  refine (pullbackForm_apply (I := ICyl) Lcyl cylEmb p v w).trans ?_
  rw [dι_cylEmb p v, dι_cylEmb p w, Lcyl_apply]

/-- The tangent vector at `1` of the circle with `dcoeC 1 v = i`. -/
theorem exists_vC : ∃ v : GroupLieAlgebra (𝓡 1) Circle, dcoeC 1 v = Complex.I := by
  have h2 := range_mfderiv_coe_sphere (E := ℂ) (n := 1) (⟨1, by simp⟩ : sphere (0 : ℂ) 1)
  have hI : Complex.I ∈ (dcoeC 1 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ).range := by
    show Complex.I ∈ (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) ((↑) : sphere (0 : ℂ) 1 → ℂ) (⟨1, by simp⟩ : sphere (0 : ℂ) 1) :
      TangentSpace (𝓡 1) (⟨1, by simp⟩ : sphere (0 : ℂ) 1) →L[ℝ] ℂ).range
    rw [h2]
    refine (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).2 ?_
    simp [Complex.inner]
  obtain ⟨v, hv⟩ := hI
  exact ⟨v, hv⟩

/-- The left-invariant field `∂_θ` of the circle. -/
def vC : GroupLieAlgebra (𝓡 1) Circle := (exists_vC).choose

theorem dcoeC_vC : dcoeC 1 vC = Complex.I := (exists_vC).choose_spec

/-- The time field `∂_θ` of the cylinder. -/
def cylTimeField (p : TimeCylinder) : TangentSpace ICyl p := (mulInvariantVectorField vC p.1, (0 : ℝ))

theorem contMDiff_cylTimeField : ContMDiff ICyl ICyl.tangent 0
    (fun p : TimeCylinder => (⟨p, cylTimeField p⟩ : TangentBundle ICyl TimeCylinder)) := by
  have hX : ContMDiff (𝓡 1) (𝓡 1).tangent 0
      (fun g : Circle => (mulInvariantVectorField vC g : TangentBundle (𝓡 1) Circle)) :=
    (contMDiff_mulInvariantVectorField (I := 𝓡 1) (G := Circle) vC).of_le (by simp)
  have hZ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent 0
      (fun t : ℝ => (⟨t, (0 : TangentSpace 𝓘(ℝ, ℝ) t)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (contMDiff_zeroSection (n := ∞) ℝ (TangentSpace 𝓘(ℝ, ℝ))).of_le (by simp)
  have h1 := (hX.comp (contMDiff_fst (I := 𝓡 1) (J := 𝓘(ℝ, ℝ)))).prodMk
    (hZ.comp (contMDiff_snd (I := 𝓡 1) (J := 𝓘(ℝ, ℝ))))
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓡 1) (M := Circle) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ)).comp h1

theorem dcoeC_mulInvariant (z : Circle) : dcoeC z (mulInvariantVectorField vC z) = (z : ℂ) * Complex.I := by
  have hL : MDifferentiableAt (𝓡 1) (𝓡 1) (fun w : Circle => z * w) (1 : Circle) :=
    (contMDiff_mul_left (I := 𝓡 1) (a := z) (n := ∞)).mdifferentiableAt (by simp)
  have hc1 := (hasMFDerivAt_circleCoe (z * 1)).comp (1 : Circle) hL.hasMFDerivAt
  have hmul : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun w : ℂ => (z : ℂ) * w) ((1 : Circle) : ℂ)
      (ContinuousLinearMap.mul ℝ ℂ (z : ℂ)) :=
    (ContinuousLinearMap.mul ℝ ℂ (z : ℂ)).hasFDerivAt.hasMFDerivAt
  have hc2 := hmul.comp (1 : Circle) (hasMFDerivAt_circleCoe 1)
  have e : ((fun z : Circle => (z : ℂ)) ∘ (fun w : Circle => z * w)) =
      (fun w : ℂ => (z : ℂ) * w) ∘ (fun z : Circle => (z : ℂ)) := funext fun w => by simp
  rw [e] at hc1
  have hu := hasMFDerivAt_unique hc1 hc2
  have := congrArg (fun L => L vC) hu
  have h3 : dcoeC (z * 1) (mfderiv (𝓡 1) (𝓡 1) (fun w : Circle => z * w) (1 : Circle) vC) =
      (z : ℂ) * dcoeC 1 vC := this
  rw [dcoeC_vC] at h3
  have h4 : ∀ y : Circle, y = z → ∀ w : EuclideanSpace ℝ (Fin 1), dcoeC y w = dcoeC z w := fun y hy w => by
    subst hy; rfl
  exact (h4 (z * 1) (mul_one z) _).symm.trans h3

theorem norm_circle_mul_I (z : Circle) : ‖(z : ℂ) * Complex.I‖ = 1 := by
  simp

/-- **The time orientation `∂_θ` of the cylinder.** -/
def timeCylinderOrientation : Causal.TimeOrientation timeCylinderMetric where
  X := cylTimeField
  contMDiff := contMDiff_cylTimeField
  timelike p := by
    rw [timeCylinderMetric_apply]
    show -inner ℝ (dcoeC p.1 (mulInvariantVectorField vC p.1)) (dcoeC p.1 (mulInvariantVectorField vC p.1)) +
      (0 : ℝ) * 0 < 0
    rw [dcoeC_mulInvariant, real_inner_self_eq_norm_sq, norm_circle_mul_I]
    norm_num

variable (z₀ : Circle) (x₀ : ℝ)

/-- The closed curve `θ ↦ (z₀ exp (iθ), x₀)` around the circle. -/
def cylLoop : ℝ → TimeCylinder := fun t => (z₀ * Circle.exp t, x₀)

theorem contMDiff_cylLoop : ContMDiff 𝓘(ℝ, ℝ) ICyl ∞ (cylLoop z₀ x₀) := by
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ (fun t : ℝ => z₀ * Circle.exp t) :=
    (contMDiff_mul_left (I := 𝓡 1) (a := z₀) (n := ∞)).comp contMDiff_circleExp
  exact h1.prodMk contMDiff_const

theorem hasDerivAt_emb_cylLoop (t : ℝ) :
    HasDerivAt (fun t : ℝ => cylEmb (cylLoop z₀ x₀ t)) (((cylLoop z₀ x₀ t).1 : ℂ) * Complex.I, (0 : ℝ)) t := by
  have h : ∀ t : ℝ, cylEmb (cylLoop z₀ x₀ t) = ((z₀ : ℂ) * Complex.exp (t * Complex.I), x₀) := fun t => by
    simp [cylEmb, cylLoop, Circle.coe_exp]
  simp only [h]
  have he : HasDerivAt (fun w : ℂ => (z₀ : ℂ) * Complex.exp (w * Complex.I))
      ((z₀ : ℂ) * (Complex.exp ((t : ℂ) * Complex.I) * Complex.I)) (t : ℂ) := by
    have := (((hasDerivAt_id (t : ℂ)).mul_const Complex.I).cexp).const_mul (z₀ : ℂ)
    simpa using this
  have h1 := he.comp_ofReal
  have h2 := h1.prodMk (hasDerivAt_const t x₀)
  convert h2 using 1
  simp [cylLoop, Circle.coe_exp]
  ring

theorem dι_velocity_cylLoop {a b : ℝ} (hab : a < b) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    dι (I := ICyl) cylEmb (cylLoop z₀ x₀ t) (Causal.velocity ICyl (cylLoop z₀ x₀) (Set.Icc a b) t) =
      (((cylLoop z₀ x₀ t).1 : ℂ) * Complex.I, (0 : ℝ)) := by
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) ICyl (cylLoop z₀ x₀) t :=
    (contMDiff_cylLoop z₀ x₀).mdifferentiableAt (by simp)
  have hv : Causal.velocity ICyl (cylLoop z₀ x₀) (Set.Icc a b) t =
      mfderiv 𝓘(ℝ, ℝ) ICyl (cylLoop z₀ x₀) t (1 : ℝ) := by
    unfold Causal.velocity
    rw [mfderivWithin_eq_mfderiv (uniqueDiffOn_Icc hab t ht).uniqueMDiffWithinAt hγ]
  have hemb : HasMFDerivAt ICyl 𝓘(ℝ, ℂ × ℝ) cylEmb (cylLoop z₀ x₀ t) (dι (I := ICyl) cylEmb (cylLoop z₀ x₀ t)) :=
    (contMDiff_cylEmb.mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hemb.comp t hγ.hasMFDerivAt
  have hd := ((hasDerivAt_emb_cylLoop z₀ x₀ t).hasFDerivAt).hasMFDerivAt
  have hu := hasMFDerivAt_unique hcomp hd
  have := congrArg (fun L => L (1 : ℝ)) hu
  rw [hv]
  have h2 : (ContinuousLinearMap.toSpanSingleton ℝ (((cylLoop z₀ x₀ t).1 : ℂ) * Complex.I, (0 : ℝ))) (1 : ℝ) =
      (((cylLoop z₀ x₀ t).1 : ℂ) * Complex.I, (0 : ℝ)) := by simp
  exact this.trans h2

/-- The loop is a future-directed timelike curve. -/
theorem isFutureTimelikeCurve_cylLoop {a b : ℝ} (hab : a < b) :
    Causal.IsFutureTimelikeCurve timeCylinderOrientation (cylLoop z₀ x₀) (Set.Icc a b) := by
  refine Causal.isFutureTimelikeCurve_of_contMDiffOn timeCylinderOrientation hab
    ((contMDiff_cylLoop z₀ x₀).contMDiffOn.of_le (by simp)) fun t ht => ?_
  have h1 := dι_velocity_cylLoop z₀ x₀ hab ht
  set v := Causal.velocity ICyl (cylLoop z₀ x₀) (Set.Icc a b) t with hv
  rw [dι_cylEmb] at h1
  have hv1 : dcoeC (cylLoop z₀ x₀ t).1 v.1 = ((cylLoop z₀ x₀ t).1 : ℂ) * Complex.I := (Prod.ext_iff.1 h1).1
  have hv2 : v.2 = 0 := (Prod.ext_iff.1 h1).2
  have hXc : dcoeC (cylLoop z₀ x₀ t).1 (cylTimeField (cylLoop z₀ x₀ t)).1 =
      ((cylLoop z₀ x₀ t).1 : ℂ) * Complex.I := dcoeC_mulInvariant _
  have hX2 : (cylTimeField (cylLoop z₀ x₀ t)).2 = 0 := rfl
  refine ⟨?_, ?_⟩
  · show timeCylinderMetric.g (cylLoop z₀ x₀ t) v v < 0
    rw [timeCylinderMetric_apply, hv1, hv2, real_inner_self_eq_norm_sq, norm_circle_mul_I]
    norm_num
  · show timeCylinderMetric.g (cylLoop z₀ x₀ t) v (cylTimeField (cylLoop z₀ x₀ t)) < 0
    rw [timeCylinderMetric_apply, hv1, hv2, hXc, hX2, real_inner_self_eq_norm_sq, norm_circle_mul_I]
    norm_num

/-- **Minkowski space with time rolled up violates chronology**: the closed timelike curve `θ ↦ (exp (iθ), x)` joins every
point `(1, x)` of the cylinder to itself, so `x ∈ I⁺(x)`. -/
theorem timeCylinder_not_isChronological : ¬ Causal.IsChronological timeCylinderOrientation := by
  intro h
  have hx : ((1 : Circle), (0 : ℝ)) ∈ Causal.chronFuture timeCylinderOrientation ((1 : Circle), (0 : ℝ)) := by
    refine ⟨cylLoop 1 0, 0, 2 * Real.pi, by positivity, isFutureTimelikeCurve_cylLoop 1 0 (by positivity), ?_, ?_⟩
    · simp [cylLoop]
    · simp [cylLoop, Circle.exp_two_pi]
  exact h _ hx

end Lightlike
