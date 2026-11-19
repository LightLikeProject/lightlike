import Lightlike.Spacetime.Hypersurface
import Lightlike.Spacetime.FlatConnection

/-!
# Trust check of GE13: the round sphere in a Euclidean space

In a finite-dimensional real inner product space `F` with its flat metric `euclMetric F` and the flat (Levi-Civita)
connection, the spheres `‖y‖ = r` are the level sets of `φ y = ‖y‖²` with the outward unit normal `n y = y / ‖y‖`
(`isUnitNormal_sphere`).

* `secondFF_sphere`: the second fundamental form is `K(v, w) = ⟪v, w⟫ / r` on tangent vectors (`K = h / r`);
* `gaussCurv_sphere`: by the Gauss relation, `g(R^D(X, Y) Z, W) = (⟪Y, Z⟫⟪X, W⟫ − ⟪X, Z⟫⟪Y, W⟫) / r²` for tangent fields
  (constant sectional curvature `1/r²`);
* `scalarCurv_sphere`: in `ℝ³`, for an orthonormal frame `(e₁, e₂)` of the tangent plane and tangent fields extending it,
  `Σ_{a,b} g(R^D(E_a, E_b) E_b, E_a) = 2 / r²`, the scalar curvature `2/r²` of the sphere.

**Limits.** As in `Hypersurface.lean`, `R^D` is the curvature of the tangential connection on tangent fields (the leaves have
no manifold structure here), so the scalar curvature is the trace of `R^D` over an orthonormal tangent frame.
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace RealInnerProductSpace

noncomputable section
namespace Lightlike

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in
/-- **The flat metric of an inner product space**: `g(v, w) = ⟪v, w⟫` on every tangent space (Mathlib's
`riemannianMetricVectorSpace`). -/
def euclMetric (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] : NondegMetric 𝓘(ℝ, F) F where
  g _ := (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)
  symm _ v w := real_inner_comm _ _
  nondegenerate _ v hv := by
    have := hv v
    rw [innerSL_apply_apply] at this
    exact inner_self_eq_zero.1 this
  contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top

theorem euclMetric_apply (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) : (euclMetric F).g x v w = ⟪(v : F), w⟫ := rfl

variable [FiniteDimensional ℝ F]

/-- The flat connection is the Levi-Civita connection of the flat metric. -/
theorem flat_isLeviCivita_eucl : (flatConnection F).IsLeviCivita (euclMetric F) :=
  ⟨flat_torsion, fun X σ τ x _ hσ hτ => flat_compat (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) σ τ X x hσ hτ⟩

omit [FiniteDimensional ℝ F] in
/-- A vector field of a normed space that is smooth at `x` as a function is smooth at `x` as a section. -/
theorem contMDiffAt_vf_of_contDiffAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (σ : Π y : V, TangentSpace 𝓘(ℝ, V) y) (x : V) (h : ContDiffAt ℝ ∞ (σ : V → V) x) :
    ContMDiffAt 𝓘(ℝ, V) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) ∞ (fun q : V => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, V) V)) x := by
  refine (contMDiffAt_section (IB := 𝓘(ℝ, V)) (E := TangentSpace 𝓘(ℝ, V)) (F := V) (s := σ) x).2 ?_
  have key : (fun b => (trivializationAt V (TangentSpace 𝓘(ℝ, V)) x (⟨b, σ b⟩ : TangentBundle 𝓘(ℝ, V) V)).2)
      = (σ : V → V) := by
    funext b
    exact congrArg Prod.snd (trivializationAt_model_space_apply (I := 𝓘(ℝ, V)) ⟨b, σ b⟩ x)
  rw [key]
  exact h.contMDiffAt

omit [FiniteDimensional ℝ F] in
/-- The derivative of `‖y‖²`: `2 ⟪y, v⟫`. -/
theorem normSq_fderiv_apply (y v : F) : fderiv ℝ (fun y : F => ‖y‖ ^ 2) y v = 2 * ⟪y, v⟫ := by
  rw [(hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv]
  simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]

/-- **The flat connection is a smooth covariant derivative.** -/
instance flat_contMDiffCovariantDerivative {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    CovariantDerivative.ContMDiffCovariantDerivative (flatConnection V) ∞ where
  contMDiff := ⟨fun {σ} hσ => fun p _ => by
    refine ContMDiffAt.contMDiffWithinAt ?_
    have key : (fun b => (trivializationAt V (TangentSpace 𝓘(ℝ, V)) p (⟨b, σ b⟩ : TangentBundle 𝓘(ℝ, V) V)).2)
        = (σ : V → V) := by
      funext b
      exact congrArg Prod.snd (trivializationAt_model_space_apply (I := 𝓘(ℝ, V)) ⟨b, σ b⟩ p)
    have hs : ContDiff ℝ ∞ (σ : V → V) := by
      refine contDiff_iff_contDiffAt.2 fun y => ?_
      have h1 : ContMDiffAt 𝓘(ℝ, V) (𝓘(ℝ, V).prod 𝓘(ℝ, V)) ∞
          (fun q : V => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, V) V)) y :=
        ((hσ y (mem_univ y)).contMDiffAt Filter.univ_mem).of_le (by simp)
      have key' : (fun b => (trivializationAt V (TangentSpace 𝓘(ℝ, V)) y (⟨b, σ b⟩ : TangentBundle 𝓘(ℝ, V) V)).2)
          = (σ : V → V) := by
        funext b
        exact congrArg Prod.snd (trivializationAt_model_space_apply (I := 𝓘(ℝ, V)) ⟨b, σ b⟩ y)
      have h2 := (contMDiffAt_section (IB := 𝓘(ℝ, V)) (E := TangentSpace 𝓘(ℝ, V)) (F := V) (s := σ) y).1 h1
      rw [key'] at h2
      exact h2.contDiffAt
    have hd : ContDiff ℝ ∞ (fderiv ℝ (σ : V → V)) := hs.fderiv_right (by simp)
    rw [contMDiffAt_section]
    convert! hd.contMDiff.contMDiffAt (x := p)
    ext x
    rw [hom_trivializationAt_apply]
    simp only [ContinuousLinearMap.inCoordinates]
    erw [TangentBundle.continuousLinearMapAt_model_space, TangentBundle.symmL_model_space]
    rfl⟩

/-- The outward unit normal of the spheres: `n y = y / ‖y‖`. -/
def sphereNormal : Π y : F, TangentSpace 𝓘(ℝ, F) y := fun y => ‖y‖⁻¹ • y

omit [FiniteDimensional ℝ F] in
theorem hasFDerivAt_sphereNormal {x : F} (hx : x ≠ 0) :
    ∃ L : F →L[ℝ] ℝ, HasFDerivAt (sphereNormal : F → F) (‖x‖⁻¹ • ContinuousLinearMap.id ℝ F + L.smulRight x) x := by
  have hd : DifferentiableAt ℝ (fun y : F => ‖y‖⁻¹) x :=
    (differentiableAt_id.norm ℝ hx).inv (norm_ne_zero_iff.2 hx)
  refine ⟨fderiv ℝ (fun y : F => ‖y‖⁻¹) x, ?_⟩
  exact hd.hasFDerivAt.smul (hasFDerivAt_id x)

omit [FiniteDimensional ℝ F] in
theorem sphere_ker_aux (y u : F) (hy : y ≠ 0) : 2 * ⟪y, u⟫ = 0 ↔ ⟪‖y‖⁻¹ • y, u⟫ = 0 := by
  rw [real_inner_smul_left]
  have : ‖y‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.2 hy)
  constructor
  · intro h; rw [show ⟪y, u⟫ = 0 by linarith, mul_zero]
  · intro h; rw [(mul_eq_zero.1 h).resolve_left this, mul_zero]

omit [FiniteDimensional ℝ F] in
theorem secondFF_aux {x : F} (hx : x ≠ 0) (v w : F) (hw : ⟪x, w⟫ = 0) :
    ⟪fderiv ℝ (sphereNormal : F → F) x v, w⟫ = ⟪v, w⟫ / ‖x‖ := by
  obtain ⟨L, hL⟩ := hasFDerivAt_sphereNormal hx
  rw [hL.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    inner_add_left, real_inner_smul_left, hw, mul_zero, add_zero]
  rw [div_eq_inv_mul]

omit [FiniteDimensional ℝ F] in
/-- **The spheres are the level sets of `‖y‖²` with unit normal `y / ‖y‖`** near any `x₀ ≠ 0` (`ε = 1`). -/
theorem isUnitNormal_sphere {x₀ : F} (hx₀ : x₀ ≠ 0) :
    Hypersurface.IsUnitNormal (euclMetric F) (fun y : F => ‖y‖ ^ 2) sphereNormal 1 x₀ := by
  have hne : ∀ᶠ y in 𝓝 x₀, y ≠ 0 := isOpen_ne.mem_nhds hx₀
  refine ⟨Or.inl rfl, Eventually.of_forall fun y => (contDiff_norm_sq ℝ).contMDiff.contMDiffAt, ?_, ?_, ?_⟩
  · filter_upwards [hne] with y hy
    exact contMDiffAt_vf_of_contDiffAt _ y (((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.2 hy)).smul contDiffAt_id)
  · filter_upwards [hne] with y hy
    rw [euclMetric_apply]
    show ⟪‖y‖⁻¹ • y, ‖y‖⁻¹ • y⟫ = (1 : ℝ)
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    field_simp
  · filter_upwards [hne] with y hy v
    have hm : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y : F => ‖y‖ ^ 2) y = fderiv ℝ (fun y : F => ‖y‖ ^ 2) y :=
      mfderiv_eq_fderiv
    rw [euclMetric_apply, hm]
    have key := normSq_fderiv_apply y (v : F)
    change (fderiv ℝ (fun y : F => ‖y‖ ^ 2) y : F →L[ℝ] ℝ) (v : F) = 0 ↔ ⟪‖y‖⁻¹ • y, (v : F)⟫ = 0
    rw [key]
    exact sphere_ker_aux y v hy

omit [FiniteDimensional ℝ F] in
/-- **`K = h / r` for the sphere**: `K(v, w) = ⟪v, w⟫ / ‖x‖` for `w` tangent (`⟪x, w⟫ = 0`). -/
theorem secondFF_sphere {x : F} (hx : x ≠ 0) (v w : TangentSpace 𝓘(ℝ, F) x) (hw : ⟪x, (w : F)⟫ = 0) :
    Hypersurface.secondFF (flatConnection F) (euclMetric F) sphereNormal x v w = ⟪(v : F), w⟫ / ‖x‖ := by
  unfold Hypersurface.secondFF
  rw [euclMetric_apply, flatConnection_apply]
  exact secondFF_aux hx v w hw

/-- **The Gauss relation for the sphere**: constant sectional curvature `1/r²`,
`g(R^D(X, Y) Z, W) = (⟪Y, Z⟫⟪X, W⟫ − ⟪X, Z⟫⟪Y, W⟫) / ‖x₀‖²` for tangent fields. -/
theorem gaussCurv_sphere {x₀ : F} (hx₀ : x₀ ≠ 0) {X Y Z W : Π y : F, TangentSpace 𝓘(ℝ, F) y}
    (hXs : SmoothNear X x₀) (hYs : SmoothNear Y x₀) (hZs : SmoothNear Z x₀)
    (hX : Hypersurface.IsTangentNear (fun y : F => ‖y‖ ^ 2) X x₀)
    (hY : Hypersurface.IsTangentNear (fun y : F => ‖y‖ ^ 2) Y x₀)
    (hZ : Hypersurface.IsTangentNear (fun y : F => ‖y‖ ^ 2) Z x₀)
    (hW : Hypersurface.IsTangentNear (fun y : F => ‖y‖ ^ 2) W x₀) :
    (euclMetric F).g x₀ (Hypersurface.gaussCurv (flatConnection F) (euclMetric F) sphereNormal 1 X Y Z x₀) (W x₀) =
      (⟪(Y x₀ : F), Z x₀⟫ * ⟪(X x₀ : F), W x₀⟫ - ⟪(X x₀ : F), Z x₀⟫ * ⟪(Y x₀ : F), W x₀⟫) / ‖x₀‖ ^ 2 := by
  have hn := isUnitNormal_sphere hx₀
  have h := Hypersurface.gauss_relation (flatConnection F) flat_isLeviCivita_eucl.2 hn hXs hYs hZs hX hY hZ hW
  rw [flat_curvatureAt, map_zero, zero_apply] at h
  have ortho : ∀ {U : Π y : F, TangentSpace 𝓘(ℝ, F) y}, Hypersurface.IsTangentNear (fun y : F => ‖y‖ ^ 2) U x₀ →
      ⟪x₀, (U x₀ : F)⟫ = 0 := fun {U} hU => by
    have := hU.self_of_nhds
    have hm : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun y : F => ‖y‖ ^ 2) x₀ = fderiv ℝ (fun y : F => ‖y‖ ^ 2) x₀ :=
      mfderiv_eq_fderiv
    rw [hm] at this
    have key := normSq_fderiv_apply x₀ (U x₀ : F)
    change (fderiv ℝ (fun y : F => ‖y‖ ^ 2) x₀ : F →L[ℝ] ℝ) (U x₀ : F) = 0 at this
    rw [key] at this
    linarith
  rw [secondFF_sphere hx₀ (Y x₀) (Z x₀) (ortho hZ), secondFF_sphere hx₀ (X x₀) (W x₀) (ortho hW),
    secondFF_sphere hx₀ (X x₀) (Z x₀) (ortho hZ), secondFF_sphere hx₀ (Y x₀) (W x₀) (ortho hW)] at h
  have hr : ‖x₀‖ ≠ 0 := norm_ne_zero_iff.2 hx₀
  field_simp at h ⊢
  linarith

/-- **The scalar curvature of the round 2-sphere of radius `r` in `ℝ³` is `2 / r²`** (trust check of GE13): the trace of
`R^D` over an orthonormal frame `(e₁, e₂)` of the tangent plane at `x₀`, through tangent fields extending it. -/
theorem scalarCurv_sphere {x₀ : EuclideanSpace ℝ (Fin 3)} (hx₀ : x₀ ≠ 0)
    {E₁ E₂ : Π y : EuclideanSpace ℝ (Fin 3), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) y}
    (h₁ : SmoothNear E₁ x₀) (h₂ : SmoothNear E₂ x₀)
    (t₁ : Hypersurface.IsTangentNear (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2) E₁ x₀)
    (t₂ : Hypersurface.IsTangentNear (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2) E₂ x₀)
    (o₁ : ⟪(E₁ x₀ : EuclideanSpace ℝ (Fin 3)), E₁ x₀⟫ = 1) (o₂ : ⟪(E₂ x₀ : EuclideanSpace ℝ (Fin 3)), E₂ x₀⟫ = 1)
    (o₁₂ : ⟪(E₁ x₀ : EuclideanSpace ℝ (Fin 3)), E₂ x₀⟫ = 0) :
    let R := fun A B : Π y : EuclideanSpace ℝ (Fin 3), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) y =>
      (euclMetric _).g x₀ (Hypersurface.gaussCurv (flatConnection _) (euclMetric _) sphereNormal 1 A B B x₀) (A x₀)
    R E₁ E₁ + R E₁ E₂ + R E₂ E₁ + R E₂ E₂ = 2 / ‖x₀‖ ^ 2 := by
  intro R
  simp only [R]
  rw [gaussCurv_sphere hx₀ h₁ h₁ h₁ t₁ t₁ t₁ t₁, gaussCurv_sphere hx₀ h₁ h₂ h₂ t₁ t₂ t₂ t₁,
    gaussCurv_sphere hx₀ h₂ h₁ h₁ t₂ t₁ t₁ t₂, gaussCurv_sphere hx₀ h₂ h₂ h₂ t₂ t₂ t₂ t₂]
  have o₂₁ : ⟪(E₂ x₀ : EuclideanSpace ℝ (Fin 3)), E₁ x₀⟫ = 0 := by rw [real_inner_comm]; exact o₁₂
  rw [o₁, o₂, o₁₂, o₂₁]
  have hr : ‖x₀‖ ≠ 0 := norm_ne_zero_iff.2 hx₀
  field_simp
  ring

end Lightlike
