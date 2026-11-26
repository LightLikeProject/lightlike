import Mathlib
import Lightlike.Spacetime.Corners.CovDerivBilinTransport
import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.Corners.DivergenceFree

/-!
# Curvature, Ricci and scalar curvature for a model transported to `Fin n → ℝ`

For `e : E ≃L[ℝ] (Fin n → ℝ)`: the curvature of a locally smooth connection for a model on `Fin n → ℝ` is linear in each slot
(`curvatureAt_linearW`); hence so is the curvature of a locally smooth connection on any finite-dimensional model `E`
(`curvatureAt_linear_E`, by `curvatureAt_trans`), and the Ricci tensor of `cov'` is the transport of that of `cov`
(`ricciAt_trans`).
-/

open Bundle Manifold Set VectorField Filter
open scoped Manifold ContDiff Topology
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

section FinN
variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
  (cov : Connection I M) [LocallySmoothConnectionW cov]

/-- **The curvature is linear in each of its three slots** (model `Fin n → ℝ`, with corners). -/
theorem curvatureAt_linearW (x : M) :
    (∀ a a' b c : TangentSpace I x, cov.curvatureAt x (a + a') b c = cov.curvatureAt x a b c + cov.curvatureAt x a' b c) ∧
    (∀ (r : ℝ) (a b c : TangentSpace I x), cov.curvatureAt x (r • a) b c = r • cov.curvatureAt x a b c) ∧
    (∀ a b b' c : TangentSpace I x, cov.curvatureAt x a (b + b') c = cov.curvatureAt x a b c + cov.curvatureAt x a b' c) ∧
    (∀ (r : ℝ) (a b c : TangentSpace I x), cov.curvatureAt x a (r • b) c = r • cov.curvatureAt x a b c) ∧
    (∀ a b c c' : TangentSpace I x, cov.curvatureAt x a b (c + c') = cov.curvatureAt x a b c + cov.curvatureAt x a b c') ∧
    (∀ (r : ℝ) (a b c : TangentSpace I x), cov.curvatureAt x a b (r • c) = r • cov.curvatureAt x a b c) := by
  have hx : x ∈ (tTrivW (I := I) (E := Fin n → ℝ) x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have inj : ∀ u v : TangentSpace I x, hvW x x u = hvW x x v → u = v := fun u v h =>
    (symmL_hvW x hx u).symm.trans ((congrArg ((tTrivW (I := I) (E := Fin n → ℝ) x).symmL ℝ x) h).trans (symmL_hvW x hx v))
  have hR := fun a b c => hv_curvatureAtW cov x hx a b c
  refine ⟨fun a a' b c => inj _ _ ?_, fun r a b c => inj _ _ ?_, fun a b b' c => inj _ _ ?_,
    fun r a b c => inj _ _ ?_, fun a b c c' => inj _ _ ?_, fun r a b c => inj _ _ ?_⟩
  · simp only [hR, hv_addW x hx]
    exact Rhat_add_leftW cov x x _ _ _ _
  · simp only [hR, hv_smul'W x hx]
    exact Rhat_smul_leftW cov x x _ _ _ _
  · simp only [hR, hv_addW x hx]
    exact Rhat_add_midW cov x x _ _ _ _
  · simp only [hR, hv_smul'W x hx]
    exact Rhat_smul_midW cov x x _ _ _ _
  · simp only [hR, hv_addW x hx]
    exact Rhat_add_rightW cov x x _ _ _ _
  · simp only [hR, hv_smul'W x hx]
    exact Rhat_smul_rightW cov x x _ _ _ _

end FinN

section Generic
variable {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [CompleteSpace E₀] [FiniteDimensional ℝ E₀]
  {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E₀ H₀}
  {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [IsManifold I₀ 2 M₀]

/-- **The Ricci tensor is the trace of the curvature as a linear map of its first slot.** -/
theorem ricciAt_eq_trace_of_linear (cov : Connection I₀ M₀) (x : M₀) (Y Z : TangentSpace I₀ x)
    (A : TangentSpace I₀ x →ₗ[ℝ] TangentSpace I₀ x) (hA : ∀ a, cov.curvatureAt x a Y Z = A a) :
    cov.ricciAt x Y Z = LinearMap.trace ℝ (TangentSpace I₀ x) A := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (tbW (I := I₀) x)]
  unfold Connection.ricciAt Matrix.trace
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.toMatrix_apply, Matrix.diag]
  exact congrArg ((tbW (I := I₀) x).coord i) (hA ((tbW (I := I₀) x) i))

end Generic

section ModelE
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
  (e : E ≃L[ℝ] (Fin n → ℝ)) (cov : Connection I M) [LocallySmoothConnectionW cov]

include e in
theorem curvatureAt_eq_symm (x : M) (a b c : TangentSpace I x) :
    cov.curvatureAt x a b c = e.symm ((transCov e cov).curvatureAt x (e a) (e b) (e c)) := by
  rw [curvatureAt_trans]
  exact (e.symm_apply_apply _).symm

include e in
theorem curvatureAt_add_left_E (x : M) (a a' b c : TangentSpace I x) :
    cov.curvatureAt x (a + a') b c = cov.curvatureAt x a b c + cov.curvatureAt x a' b c := by
  have := locallySmoothConnectionW_transCov e cov
  have h := (curvatureAt_linearW (transCov e cov) x).1 (e a) (e a') (e b) (e c)
  apply e.injective
  rw [← curvatureAt_trans e cov x (a + a') b c]
  erw [map_add e a a']
  erw [h]
  erw [map_add e, curvatureAt_trans, curvatureAt_trans]
  rfl

include e in
theorem curvatureAt_smul_left_E (x : M) (r : ℝ) (a b c : TangentSpace I x) :
    cov.curvatureAt x (r • a) b c = r • cov.curvatureAt x a b c := by
  have := locallySmoothConnectionW_transCov e cov
  have h := (curvatureAt_linearW (transCov e cov) x).2.1 r (e a) (e b) (e c)
  apply e.injective
  rw [← curvatureAt_trans e cov x (r • a) b c]
  erw [map_smul e r a]
  erw [h]
  erw [map_smul e, curvatureAt_trans]
  rfl

include e in
theorem curvatureAt_add_mid_E (x : M) (a b b' c : TangentSpace I x) :
    cov.curvatureAt x a (b + b') c = cov.curvatureAt x a b c + cov.curvatureAt x a b' c := by
  have := locallySmoothConnectionW_transCov e cov
  have h := (curvatureAt_linearW (transCov e cov) x).2.2.1 (e a) (e b) (e b') (e c)
  apply e.injective
  rw [← curvatureAt_trans e cov x a (b + b') c]
  erw [map_add e b b']
  erw [h]
  erw [map_add e, curvatureAt_trans, curvatureAt_trans]
  rfl

include e in
theorem curvatureAt_smul_mid_E (x : M) (r : ℝ) (a b c : TangentSpace I x) :
    cov.curvatureAt x a (r • b) c = r • cov.curvatureAt x a b c := by
  have := locallySmoothConnectionW_transCov e cov
  have h := (curvatureAt_linearW (transCov e cov) x).2.2.2.1 r (e a) (e b) (e c)
  apply e.injective
  rw [← curvatureAt_trans e cov x a (r • b) c]
  erw [map_smul e r b]
  erw [h]
  erw [map_smul e, curvatureAt_trans]
  rfl

include e in
theorem curvatureAt_add_right_E (x : M) (a b c c' : TangentSpace I x) :
    cov.curvatureAt x a b (c + c') = cov.curvatureAt x a b c + cov.curvatureAt x a b c' := by
  have := locallySmoothConnectionW_transCov e cov
  have h := (curvatureAt_linearW (transCov e cov) x).2.2.2.2.1 (e a) (e b) (e c) (e c')
  apply e.injective
  rw [← curvatureAt_trans e cov x a b (c + c')]
  erw [map_add e c c']
  erw [h]
  erw [map_add e, curvatureAt_trans, curvatureAt_trans]
  rfl

include e in
theorem curvatureAt_smul_right_E (x : M) (r : ℝ) (a b c : TangentSpace I x) :
    cov.curvatureAt x a b (r • c) = r • cov.curvatureAt x a b c := by
  have := locallySmoothConnectionW_transCov e cov
  have h := (curvatureAt_linearW (transCov e cov) x).2.2.2.2.2 r (e a) (e b) (e c)
  apply e.injective
  rw [← curvatureAt_trans e cov x a b (r • c)]
  erw [map_smul e r c]
  erw [h]
  erw [map_smul e, curvatureAt_trans]
  rfl

/-- The curvature as a linear map of its first slot, for a finite-dimensional model. -/
def curvFstE (x : M) (Y Z : TangentSpace I x) : TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun a := cov.curvatureAt x a Y Z
  map_add' a a' := curvatureAt_add_left_E e cov x a a' Y Z
  map_smul' r a := curvatureAt_smul_left_E e cov x r a Y Z

/-- **The Ricci tensor of the transported connection is the transport of the Ricci tensor.** -/
theorem ricciAt_trans (x : M) (Y Z : TangentSpace I x) :
    (transCov e cov).ricciAt x (e Y) (e Z) = cov.ricciAt x Y Z := by
  have := locallySmoothConnectionW_transCov e cov
  have hE := ricciAt_eq_trace_of_linear cov x Y Z (curvFstE e cov x Y Z) (fun a => rfl)
  let A' : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    (e.toLinearEquiv.toLinearMap) ∘ₗ (curvFstE e cov x Y Z) ∘ₗ (e.toLinearEquiv.symm.toLinearMap)
  have hF := ricciAt_eq_trace_of_linear (transCov e cov) x (e Y) (e Z) A' (fun u => by
    have := curvatureAt_trans e cov x (e.symm u) Y Z
    erw [e.apply_symm_apply] at this
    exact this)
  rw [hF, hE]
  exact LinearMap.trace_conj' (curvFstE e cov x Y Z) e.toLinearEquiv

/-- The Ricci tensor as a bilinear map. -/
def RicE (x : M) : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun Y Z => cov.ricciAt x Y Z)
    (fun Y Y' Z => by
      rw [ricciAt_eq_trace_of_linear cov x (Y + Y') Z (curvFstE e cov x (Y + Y') Z) (fun a => rfl),
        ricciAt_eq_trace_of_linear cov x Y Z (curvFstE e cov x Y Z) (fun a => rfl),
        ricciAt_eq_trace_of_linear cov x Y' Z (curvFstE e cov x Y' Z) (fun a => rfl), ← map_add]
      congr 1
      ext a
      exact curvatureAt_add_mid_E e cov x a Y Y' Z)
    (fun r Y Z => by
      rw [ricciAt_eq_trace_of_linear cov x (r • Y) Z (curvFstE e cov x (r • Y) Z) (fun a => rfl),
        ricciAt_eq_trace_of_linear cov x Y Z (curvFstE e cov x Y Z) (fun a => rfl), ← map_smul]
      congr 1
      ext a
      exact curvatureAt_smul_mid_E e cov x r a Y Z)
    (fun Y Z Z' => by
      rw [ricciAt_eq_trace_of_linear cov x Y (Z + Z') (curvFstE e cov x Y (Z + Z')) (fun a => rfl),
        ricciAt_eq_trace_of_linear cov x Y Z (curvFstE e cov x Y Z) (fun a => rfl),
        ricciAt_eq_trace_of_linear cov x Y Z' (curvFstE e cov x Y Z') (fun a => rfl), ← map_add]
      congr 1
      ext a
      exact curvatureAt_add_right_E e cov x a Y Z Z')
    (fun r Y Z => by
      rw [ricciAt_eq_trace_of_linear cov x Y (r • Z) (curvFstE e cov x Y (r • Z)) (fun a => rfl),
        ricciAt_eq_trace_of_linear cov x Y Z (curvFstE e cov x Y Z) (fun a => rfl), ← map_smul]
      congr 1
      ext a
      exact curvatureAt_smul_right_E e cov x r a Y Z)

/-- **The scalar curvature of the transported connection and metric is the transport of the scalar curvature.** -/
theorem scalarCurvatureAt_trans (g : NondegMetric I M) (x : M) :
    (transCov e cov).scalarCurvatureAt (transMetric e g) x = cov.scalarCurvatureAt g x := by
  have := locallySmoothConnectionW_transCov e cov
  have h1 : cov.scalarCurvatureAt g x = LinearMap.trace ℝ (TangentSpace I x) (raiseW g x (RicE e cov x)) := by
    rw [trace_raiseW g x (RicE e cov x) (tbW (I := I) x)]
    rfl
  let b'' : Module.Basis (Fin (Module.finrank ℝ (Fin n → ℝ))) ℝ (TangentSpace I x) :=
    (Module.finBasis ℝ (Fin n → ℝ)).map e.symm.toLinearEquiv
  have h2 := trace_raiseW g x (RicE e cov x) b''
  rw [h1, h2]
  unfold Connection.scalarCurvatureAt
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hG : (Matrix.of fun i j => (((transMetric e g).g x) ((Module.finBasis ℝ (Fin n → ℝ)) i))
      ((Module.finBasis ℝ (Fin n → ℝ)) j)) = gramBW g x b'' := by
    ext i j
    rfl
  have hR := ricciAt_trans e cov x (e.symm ((Module.finBasis ℝ (Fin n → ℝ)) i))
    (e.symm ((Module.finBasis ℝ (Fin n → ℝ)) j))
  erw [e.apply_symm_apply, e.apply_symm_apply] at hR
  rw [hG]
  exact congrArg _ hR

/-- **The Einstein tensor of the transported connection and metric is the transport of the Einstein tensor.** -/
theorem einsteinField_trans (g : NondegMetric I M) (x : M) (v w : TangentSpace (I.transContinuousLinearEquiv e) x) :
    (transCov e cov).einsteinField (transMetric e g) x v w = cov.einsteinField g x (e.symm v) (e.symm w) := by
  have := locallySmoothConnectionW_transCov e cov
  have hr := ricciAt_trans e cov x (e.symm v) (e.symm w)
  erw [e.apply_symm_apply, e.apply_symm_apply] at hr
  have hs := scalarCurvatureAt_trans e cov g x
  unfold Connection.einsteinField
  rw [hr, hs]
  rfl

/-- **A contraction with the inverse of the Gram matrix is the same in the two models.** -/
theorem contraction_trans (g : NondegMetric I M) (x : M) (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    ∑ i, ∑ j, (gramBW g x (tbW (I := I) x))⁻¹ i j * B (tbW (I := I) x i) (tbW (I := I) x j) =
      ∑ i, ∑ j, (Matrix.of fun i j => (((transMetric e g).g x) ((Module.finBasis ℝ (Fin n → ℝ)) i))
        ((Module.finBasis ℝ (Fin n → ℝ)) j))⁻¹ i j *
        B (e.symm ((Module.finBasis ℝ (Fin n → ℝ)) i)) (e.symm ((Module.finBasis ℝ (Fin n → ℝ)) j)) := by
  let b'' : Module.Basis (Fin (Module.finrank ℝ (Fin n → ℝ))) ℝ (TangentSpace I x) :=
    (Module.finBasis ℝ (Fin n → ℝ)).map e.symm.toLinearEquiv
  rw [← trace_raiseW g x B (tbW (I := I) x), trace_raiseW g x B b'']
  have hG : (Matrix.of fun i j => (((transMetric e g).g x) ((Module.finBasis ℝ (Fin n → ℝ)) i))
      ((Module.finBasis ℝ (Fin n → ℝ)) j)) = gramBW g x b'' := by
    ext i j
    rfl
  rw [hG]
  rfl

/-- **The covariant derivative of the Einstein tensor is the transport.** -/
theorem nabla_einstein_trans (g : NondegMetric I M) (x : M) (X v w : TangentSpace I x) :
    (transCov e cov).covDerivBilinAt ((transCov e cov).einsteinField (transMetric e g)) x (e X) (e v) (e w) =
      cov.covDerivBilinAt (cov.einsteinField g) x X v w := by
  have := locallySmoothConnectionW_transCov e cov
  have hT : (transCov e cov).einsteinField (transMetric e g) =
      fun y (v' w' : TangentSpace (I.transContinuousLinearEquiv e) y) =>
        cov.einsteinField g y (e.symm v') (e.symm w') :=
    funext fun y => funext fun v' => funext fun w' => einsteinField_trans e cov g y v' w'
  rw [hT]
  exact covDerivBilinAt_trans e cov (cov.einsteinField g) x X v w

section DivForm
variable (g : NondegMetric I M) (h : cov.IsLeviCivita g)
include e h

theorem nabla_add_left_E (x : M) (X X' v w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (X + X') v w =
      cov.covDerivBilinAt (cov.einsteinField g) x X v w + cov.covDerivBilinAt (cov.einsteinField g) x X' v w := by
  have := locallySmoothConnectionW_transCov e cov
  have h' := isLeviCivita_trans e cov g h
  have hx : x ∈ (tTrivW (I := I.transContinuousLinearEquiv e) (E := Fin n → ℝ) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have k := covDerivBilinAt_einstein_add_leftW (transMetric e g) (transCov e cov) x h' hx (e X) (e X') (e v) (e w)
  exact (nabla_einstein_trans e cov g x (X + X') v w).symm.trans
    ((congrArg (fun z => (transCov e cov).covDerivBilinAt ((transCov e cov).einsteinField (transMetric e g)) x z (e v) (e w))
      (map_add e X X')).trans
      (k.trans (congrArg₂ (· + ·) (nabla_einstein_trans e cov g x X v w) (nabla_einstein_trans e cov g x X' v w))))

theorem nabla_smul_left_E (x : M) (r : ℝ) (X v w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (r • X) v w =
      r * cov.covDerivBilinAt (cov.einsteinField g) x X v w := by
  have := locallySmoothConnectionW_transCov e cov
  have h' := isLeviCivita_trans e cov g h
  have hx : x ∈ (tTrivW (I := I.transContinuousLinearEquiv e) (E := Fin n → ℝ) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have k := covDerivBilinAt_einstein_smul_leftW (transMetric e g) (transCov e cov) x h' hx r (e X) (e v) (e w)
  exact (nabla_einstein_trans e cov g x (r • X) v w).symm.trans
    ((congrArg (fun z => (transCov e cov).covDerivBilinAt ((transCov e cov).einsteinField (transMetric e g)) x z (e v) (e w))
      (map_smul e r X)).trans
      (k.trans (congrArg (r * ·) (nabla_einstein_trans e cov g x X v w))))

theorem nabla_add_mid_E (x : M) (X v v' w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X (v + v') w =
      cov.covDerivBilinAt (cov.einsteinField g) x X v w + cov.covDerivBilinAt (cov.einsteinField g) x X v' w := by
  have := locallySmoothConnectionW_transCov e cov
  have h' := isLeviCivita_trans e cov g h
  have hx : x ∈ (tTrivW (I := I.transContinuousLinearEquiv e) (E := Fin n → ℝ) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have k := covDerivBilinAt_einstein_add_midW (transMetric e g) (transCov e cov) x h' hx (e X) (e v) (e v') (e w)
  exact (nabla_einstein_trans e cov g x X (v + v') w).symm.trans
    ((congrArg (fun z => (transCov e cov).covDerivBilinAt ((transCov e cov).einsteinField (transMetric e g)) x (e X) z (e w))
      (map_add e v v')).trans
      (k.trans (congrArg₂ (· + ·) (nabla_einstein_trans e cov g x X v w) (nabla_einstein_trans e cov g x X v' w))))

theorem nabla_smul_mid_E (x : M) (r : ℝ) (X v w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X (r • v) w =
      r * cov.covDerivBilinAt (cov.einsteinField g) x X v w := by
  have := locallySmoothConnectionW_transCov e cov
  have h' := isLeviCivita_trans e cov g h
  have hx : x ∈ (tTrivW (I := I.transContinuousLinearEquiv e) (E := Fin n → ℝ) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  have k := covDerivBilinAt_einstein_smul_midW (transMetric e g) (transCov e cov) x h' hx r (e X) (e v) (e w)
  exact (nabla_einstein_trans e cov g x X (r • v) w).symm.trans
    ((congrArg (fun z => (transCov e cov).covDerivBilinAt ((transCov e cov).einsteinField (transMetric e g)) x (e X) z (e w))
      (map_smul e r v)).trans
      (k.trans (congrArg (r * ·) (nabla_einstein_trans e cov g x X v w))))

/-- The bilinear form `(X, v) ↦ (∇_X G)(v, w)` for a finite-dimensional model. -/
def divFormE (x : M) (w : TangentSpace I x) : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X v => cov.covDerivBilinAt (cov.einsteinField g) x X v w)
    (fun X X' v => nabla_add_left_E e cov g h x X X' v w)
    (fun r X v => nabla_smul_left_E e cov g h x r X v w)
    (fun X v v' => nabla_add_mid_E e cov g h x X v v' w)
    (fun r X v => nabla_smul_mid_E e cov g h x r X v w)

/-- **The divergence of the Einstein tensor vanishes for a locally smooth Levi-Civita connection on a manifold modelled with corners on
any finite-dimensional space** (boundary and corners allowed; no Hausdorff hypothesis): the theorem for `Fin n → ℝ` transported by a linear
equivalence. -/
theorem einstein_divergence_free_trans (x : M) (w : TangentSpace I x) :
    cov.divBilinAt g (cov.einsteinField g) x w = 0 := by
  have := locallySmoothConnectionW_transCov e cov
  have h' := isLeviCivita_trans e cov g h
  have key := einstein_divergence_free_provedW (transMetric e g) (transCov e cov) x h' (e w)
  have hc := contraction_trans e g x (divFormE e cov g h x w)
  refine (hc.trans ?_).trans key
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hn := nabla_einstein_trans e cov g x (e.symm ((Module.finBasis ℝ (Fin n → ℝ)) i))
    (e.symm ((Module.finBasis ℝ (Fin n → ℝ)) j)) w
  erw [e.apply_symm_apply, e.apply_symm_apply] at hn
  exact congrArg _ hn.symm

end DivForm

end ModelE

section Any
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
  (cov : Connection I M) [LocallySmoothConnectionW cov]

/-- **The Einstein tensor of a Levi-Civita connection is divergence free, on a manifold modelled with corners on any finite-dimensional
real normed space**: boundary and corners allowed, class `C²`, a locally smooth connection, no Hausdorff hypothesis, any signature. -/
theorem einstein_divergence_free_any (g : NondegMetric I M) (h : cov.IsLeviCivita g) (x : M) (w : TangentSpace I x) :
    cov.divBilinAt g (cov.einsteinField g) x w = 0 :=
  einstein_divergence_free_trans (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv cov g h x w

end Any

end Lightlike
