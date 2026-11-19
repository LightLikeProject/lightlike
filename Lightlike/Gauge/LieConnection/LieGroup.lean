import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Curvature for a general Lie group: the adjoint action (GC1, attempt 1 at general Lie groups)

Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1: the gauge group is a Lie group `G` with Lie
algebra `g`; the local gauge potential `A_U` is `g`-valued (p. 30), `F = dA + [A, A]` with the bracket of `g`
(eq. (62), p. 42), and `F ↦ Ad_{φ_U} F` under a gauge transformation (eq. (64), p. 43).

Here `G` is a Lie group in Mathlib's sense (`LieGroup I (minSmoothness 𝕜 3) G`) and `g = GroupLieAlgebra I G`, the
tangent space at `1` with the bracket of left-invariant vector fields.
* `adjoint g = d(conj_g)_1`, the adjoint action; `adjoint_one`, `adjoint_mul`;
* `adjoint_lie`: `Ad_g ⁅v, w⁆ = ⁅Ad_g v, Ad_g w⁆`, from the naturality of the Lie bracket of vector fields
  (`mpullback_mlieBracket`) and `conj_g^* X_w = X_{Ad_{g⁻¹} w}` for the left-invariant fields;
* `lieCurvature A x η ξ = dA(η, ξ) + ⁅A(η), A(ξ)⁆` (eq. (62)) for `A : F → (F →L E)` with values in the Lie algebra
  (`GroupLieAlgebra I G` is the model space `E` as a type, and carries no norm of its own); `lieCurvature_antisymm`;
* `lieCurvature_adjoint`: for a constant gauge transformation `g`, `F_{Ad_g A} = Ad_g F_A` (eq. (64) with `φ_U`
  constant).

Not reached (named missing pieces): for a gauge transformation `g(x)` that varies with `x`, eqs. (38) and (64) need the
right Maurer–Cartan form `dg g⁻¹` of `G` and the derivative of `Ad` (`d(Ad_{g(x)}) = ad(dg g⁻¹) ∘ Ad_{g(x)}`), which
Mathlib does not have (it has no `Ad` at all); the bundle-level statements need principal `G`-bundles, which neither
Mathlib nor Physlib has (Physlib's gauge-theory API map lists them as TODO).
-/

open Bundle Function VectorField
open scoped Manifold

noncomputable section

namespace Lightlike.Gauge

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness 𝕜 3) G]

/-- Conjugation by `g`: `h ↦ g h g⁻¹`. -/
def conjMap (g h : G) : G := g * h * g⁻¹

lemma conjMap_one (g : G) : conjMap g 1 = 1 := by simp [conjMap]

lemma conjMap_inv_conjMap (g h : G) : conjMap g⁻¹ (conjMap g h) = h := by
  simp only [conjMap]; group

lemma conjMap_mul (g k : G) : conjMap (g * k) = conjMap g ∘ conjMap k := by
  funext h; simp only [conjMap, comp_apply]; group

lemma conjMap_one_left : conjMap (1 : G) = id := by
  funext h; simp [conjMap]

variable (I) in
lemma contMDiff_conjMap (g : G) : ContMDiff I I (minSmoothness 𝕜 3) (conjMap g) :=
  contMDiff_mul_right.comp contMDiff_mul_left

lemma minSmoothness_three_ne_zero : minSmoothness 𝕜 3 ≠ 0 :=
  lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'

lemma mdifferentiableAt_conjMap (g h : G) : MDifferentiableAt I I (conjMap g) h :=
  (contMDiff_conjMap I g).contMDiffAt.mdifferentiableAt minSmoothness_three_ne_zero

lemma mdifferentiableAt_mul_left' (a h : G) : MDifferentiableAt I I (a * ·) h :=
  (contMDiff_mul_left (I := I) (n := minSmoothness 𝕜 3)).contMDiffAt.mdifferentiableAt
    minSmoothness_three_ne_zero

variable (I) in
/-- **The adjoint action** of `g` on the Lie algebra: `Ad_g = d(conj_g)_1`. -/
def adjoint (g : G) : GroupLieAlgebra I G →L[𝕜] GroupLieAlgebra I G := mfderiv I I (conjMap g) 1

lemma adjoint_one : adjoint I (1 : G) = ContinuousLinearMap.id 𝕜 _ := by
  rw [adjoint, conjMap_one_left]; exact mfderiv_id

lemma adjoint_mul (g k : G) : adjoint I (g * k) = (adjoint I g).comp (adjoint I k) := by
  have h := mfderiv_comp (I' := I) (1 : G) (mdifferentiableAt_conjMap (I := I) g (conjMap k 1))
    (mdifferentiableAt_conjMap (I := I) k 1)
  rw [← conjMap_mul] at h
  rw [adjoint, h, conjMap_one]
  rfl

/-- The derivative of a conjugation maps left-invariant vector fields to left-invariant vector fields. -/
lemma mfderiv_conjMap_mulInvariant (g h : G) (v : GroupLieAlgebra I G) :
    mfderiv I I (conjMap g) h (mulInvariantVectorField v h) =
      mulInvariantVectorField (adjoint I g v) (conjMap g h) := by
  have e : conjMap g ∘ (h * ·) = (conjMap g h * ·) ∘ conjMap g := by
    funext x; simp only [comp_apply, conjMap]; group
  have h1 := congrArg (fun F => mfderiv I I F 1 v) e
  rw [mfderiv_comp (I' := I) (1 : G) (mdifferentiableAt_conjMap g _) (mdifferentiableAt_mul_left' h 1),
    mfderiv_comp (I' := I) (1 : G) (mdifferentiableAt_mul_left' _ _) (mdifferentiableAt_conjMap g 1)] at h1
  simp only [ContinuousLinearMap.coe_comp, comp_apply] at h1
  rw [mul_one, conjMap_one] at h1
  exact h1

lemma inverse_mfderiv_conjMap (g h : G) :
    (mfderiv I I (conjMap g) h).inverse = mfderiv I I (conjMap g⁻¹) (conjMap g h) := by
  have A : mfderiv I I (conjMap g⁻¹ ∘ conjMap g) h = ContinuousLinearMap.id _ _ := by
    have : conjMap g⁻¹ ∘ conjMap g = id := funext fun x => conjMap_inv_conjMap g x
    rw [this]; exact mfderiv_id
  rw [mfderiv_comp (I' := I) _ (mdifferentiableAt_conjMap _ _) (mdifferentiableAt_conjMap _ _)] at A
  have A' : mfderiv I I (conjMap g ∘ conjMap g⁻¹) (conjMap g h) = ContinuousLinearMap.id _ _ := by
    have : conjMap g ∘ conjMap g⁻¹ = id := funext fun x => by
      have := conjMap_inv_conjMap g⁻¹ x; rwa [inv_inv] at this
    rw [this]; exact mfderiv_id
  rw [mfderiv_comp (I' := I) _ (mdifferentiableAt_conjMap _ _) (mdifferentiableAt_conjMap _ _),
    comp_apply, conjMap_inv_conjMap] at A'
  exact ContinuousLinearMap.inverse_eq A' A

/-- The pullback of a left-invariant vector field by a conjugation. -/
lemma mpullback_conjMap_mulInvariant (g : G) (w : GroupLieAlgebra I G) :
    mpullback I I (conjMap g) (mulInvariantVectorField w) = mulInvariantVectorField (adjoint I g⁻¹ w) := by
  funext h
  simp only [mpullback, inverse_mfderiv_conjMap]
  refine (mfderiv_conjMap_mulInvariant g⁻¹ (conjMap g h) w).trans ?_
  rw [conjMap_inv_conjMap]

variable [CompleteSpace E]

/-- **The adjoint action preserves the bracket**: `Ad_g ⁅v, w⁆ = ⁅Ad_g v, Ad_g w⁆`. -/
theorem adjoint_lie (g : G) (v w : GroupLieAlgebra I G) :
    adjoint I g ⁅v, w⁆ = ⁅adjoint I g v, adjoint I g w⁆ := by
  have h := mpullback_mlieBracket (I := I) (I' := I) (n := minSmoothness 𝕜 3) (f := conjMap g⁻¹)
    (V := mulInvariantVectorField v) (W := mulInvariantVectorField w) (x₀ := (1 : G))
    (mdifferentiableAt_mulInvariantVectorField _) (mdifferentiableAt_mulInvariantVectorField _)
    (contMDiff_conjMap I g⁻¹).contMDiffAt (minSmoothness_monotone (by norm_cast))
  rw [mpullback_conjMap_mulInvariant, mpullback_conjMap_mulInvariant, inv_inv] at h
  rw [GroupLieAlgebra.bracket_def, GroupLieAlgebra.bracket_def, ← h, mpullback,
    inverse_mfderiv_conjMap, inv_inv, conjMap_one]
  rfl

/-- **The adjoint action as a Lie algebra morphism**. -/
def adjointLieHom (g : G) : GroupLieAlgebra I G →ₗ⁅𝕜⁆ GroupLieAlgebra I G :=
  { (adjoint I g : GroupLieAlgebra I G →ₗ[𝕜] GroupLieAlgebra I G) with
    map_lie' := fun {v w} => adjoint_lie g v w }

variable (I G) in
/-- A vector of the model space as an element of the Lie algebra (`GroupLieAlgebra I G` is `E` as a type). -/
def toLie (u : E) : GroupLieAlgebra I G := u

variable (I G) in
/-- The bracket of the Lie algebra on its underlying space `E`. -/
def lieBr (u v : E) : E := (⁅toLie I G u, toLie I G v⁆ : GroupLieAlgebra I G)

lemma lieBr_skew (u v : E) : lieBr I G u v = -lieBr I G v u := by
  unfold lieBr
  exact (lie_skew (toLie I G u) (toLie I G v)).symm

variable (I) in
/-- The adjoint action on the underlying space `E`. -/
def adjointE (g : G) : E →L[𝕜] E := adjoint I g

lemma lieBr_adjointE (g : G) (u v : E) :
    lieBr I G (adjointE I g u) (adjointE I g v) = adjointE I g (lieBr I G u v) := by
  unfold lieBr adjointE toLie
  exact (adjoint_lie g u v).symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (I G) in
/-- **The curvature** of a one-form `A` on `F` with values in the Lie algebra of `G` (on its underlying space `E`)
(Svetlichny eq. (62)): `F(η, ξ) = dA(η, ξ) + ⁅A(η), A(ξ)⁆`, with `dA(η, ξ) = ∂_η A(ξ) - ∂_ξ A(η)` and the bracket of
`GroupLieAlgebra`. -/
def lieCurvature (A : F → F →L[𝕜] E) (x η ξ : F) : E :=
  fderiv 𝕜 A x η ξ - fderiv 𝕜 A x ξ η + lieBr I G (A x η) (A x ξ)

/-- The curvature is antisymmetric. -/
theorem lieCurvature_antisymm (A : F → F →L[𝕜] E) (x η ξ : F) :
    lieCurvature I G A x η ξ = -lieCurvature I G A x ξ η := by
  unfold lieCurvature
  rw [lieBr_skew (A x η) (A x ξ)]
  abel

/-- **Covariance under a constant gauge transformation** (eq. (64) with `φ_U` constant): the curvature of
`Ad_g ∘ A` is `Ad_g` of the curvature of `A`. -/
theorem lieCurvature_adjoint (g : G) {A : F → F →L[𝕜] E} {x : F} (hA : DifferentiableAt 𝕜 A x) (η ξ : F) :
    lieCurvature I G (fun y => (adjointE I g).comp (A y)) x η ξ =
      adjointE I g (lieCurvature I G A x η ξ) := by
  have hd : fderiv 𝕜 (fun y => (adjointE I g).comp (A y)) x =
      (ContinuousLinearMap.compL 𝕜 F E E (adjointE I g)).comp (fderiv 𝕜 A x) :=
    ((ContinuousLinearMap.compL 𝕜 F E E (adjointE I g)).hasFDerivAt.comp x hA.hasFDerivAt).fderiv
  unfold lieCurvature
  rw [hd, map_add, map_sub, ← lieBr_adjointE]
  rfl

end Lightlike.Gauge
