import Lightlike.Spacetime.ChartCurvature
import Lightlike.Spacetime.Corners.ChartCurvature
import Lightlike.Spacetime.CurvatureSymmetries
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.Corners.LieDerivation

/-!
# Symmetries of the curvature of a Levi-Civita connection

For a smooth connection `cov` on a manifold `M` modelled with corners (any `ModelWithCorners`) on a finite-dimensional space,
under the same hypotheses as `curvatureAt_apply_proved` (`ChartCurvature.lean`):

* `curvatureAt_apply_eventuallyW`: the curvature at `x` is `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` for any fields
  smooth near `x`;
* `bianchi_first_provedW`: the first Bianchi identity for a torsion-free connection (torsion freeness, the
  Jacobi identity `jacobi_cycW` of the Lie bracket);
* `riemannLowerAt_antisymm_lastW`: `g(R(X,Y)Z, W) = -g(R(X,Y)W, Z)` for a metric connection (from
  `mfderiv_mlieBracketW`), and `curvatureAt_antisymm_leftW` the antisymmetry in `X, Y`;
* `riemannLowerAt_pair_symmW`: `g(R(X,Y)Z, W) = g(R(Z,W)X, Y)` for the Levi-Civita connection;
* `ricciAt_symm_provedW`: the Ricci tensor is symmetric (trace with the inverse Gram matrix, `coord_eq_sumW`).

**Differences from the tasks `T-GE1-P3` and `T-GE1-P4`** (which stay open): the tasks are for any `ModelWithCorners` with
`IsLeviCivita`, with no Hausdorff hypothesis; these theorems hold for any `ModelWithCorners`, with a locally smooth connection (`LocallySmoothConnectionW`, no Hausdorff hypothesis) and take
torsion freeness and metric compatibility as two hypotheses. The comparison with Wald, *General Relativity*, Section 3.2
is pending: the source was not read at the cited location.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/CurvatureSymmetries.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E]
variable (cov : Connection I M) [LocallySmoothConnectionW cov]

/-- Smooth near a point. -/
def SmoothNearW (X : Π y : M, TangentSpace I y) (x : M) : Prop :=
  ∀ᶠ y in nhds x, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
    (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) y

/-- **The curvature through any fields smooth near the point**: `curvatureAt` at `x` of the values of `X, Y, Z` is `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `x`, for fields smooth near `x`. -/
theorem curvatureAt_apply_eventuallyW
    (X Y Z : Π y : M, TangentSpace I y) (x : M)
    (hX : SmoothNearW X x) (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x) :
    cov.curvatureAt x (X x) (Y x) (Z x) =
      cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
        - cov Z x (mlieBracket I X Y x) := by
  have hx : x ∈ (tTrivW (I := I) (E := E) x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have h1 := curvature_hatW cov x hx hX hY hZ
  have h2 := curvature_hatW cov x hx (eventually_extendW x (X x)) (eventually_extendW x (Y x))
    (eventually_extendW x (Z x))
  simp only [FiberBundle.extend_apply_self] at h2
  unfold Connection.curvatureAt
  have hE := h2.trans h1.symm
  dsimp only
  simp only [FiberBundle.extend_apply_self]
  exact (symmL_hvW x hx _).symm.trans ((congrArg ((tTrivW (I := I) (E := E) x).symmL ℝ x) hE).trans (symmL_hvW x hx _))

/-- The Lie bracket of fields smooth near `x` is smooth near `x`. -/
theorem smoothNear_mlieBracketW {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : SmoothNearW X x) (hY : SmoothNearW Y x) : SmoothNearW (mlieBracket I X Y) x := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  haveI : IsManifold I (((⊤ : ℕ∞) : ℕ∞ω) + 1) M := by
    refine IsManifold.of_le (n := ∞) ?_
    simp
  filter_upwards [hX, hY] with y hXy hYy
  exact ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) hXy hYy (by simp [minSmoothness])

/-- The torsion-free condition on fields differentiable at `x`. -/
theorem cov_torsionW {cov' : Connection I M} (h : cov'.torsion = 0)
    {X Y : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov' Y x (X x) - cov' X x (Y x) = mlieBracket I X Y x :=
  ((CovariantDerivative.torsion_eq_zero_iff cov').1 h) hX hY

/-- One term of the first Bianchi identity: `∇_X ∇_Y Z - ∇_X ∇_Z Y - ∇_{[Y,Z]} X = [X, [Y, Z]]` for a torsion-free connection. -/
theorem bianchi_first_auxW {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hT : cov.torsion = 0) (hX : SmoothNearW X x) (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x) :
    cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Y y (Z y)) x (X x) -
      cov X x (mlieBracket I Y Z x) = mlieBracket I X (mlieBracket I Y Z) x := by
  have hXp : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle I M)) x := hX.self_of_nhds
  have hYp := hY.self_of_nhds
  have hZp := hZ.self_of_nhds
  have hF1 : MDiffAt (T% (fun y => cov Z y (Y y))) x :=
    (contMDiffAt_covApplyW cov hYp hZ).mdifferentiableAt (by simp)
  have hF2 : MDiffAt (T% (fun y => cov Y y (Z y))) x :=
    (contMDiffAt_covApplyW cov hZp hY).mdifferentiableAt (by simp)
  have hF3s : SmoothNearW (mlieBracket I Y Z) x := smoothNear_mlieBracketW hY hZ
  have hF3 : MDiffAt (T% (mlieBracket I Y Z)) x := (hF3s.self_of_nhds).mdifferentiableAt (by simp)
  have heq : (fun y => cov Z y (Y y)) =ᶠ[nhds x]
      ((fun y => cov Y y (Z y)) + mlieBracket I Y Z) := by
    filter_upwards [hY, hZ] with y hYy hZy
    have := cov_torsionW hT (X := Y) (Y := Z) (x := y) (hYy.mdifferentiableAt (by simp))
      (hZy.mdifferentiableAt (by simp))
    simp only [Pi.add_apply]
    rw [← this]; abel
  have hc : cov (fun y => cov Z y (Y y)) x = cov (fun y => cov Y y (Z y)) x + cov (mlieBracket I Y Z) x := by
    rw [(cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq hF1 (mdifferentiableAt_add_section hF2 hF3)
      Filter.univ_mem heq]
    exact (cov.isCovariantDerivativeOn (s := Set.univ)).add hF2 hF3
  have ht := cov_torsionW hT (X := X) (Y := mlieBracket I Y Z) (x := x) (hXp.mdifferentiableAt (by simp)) hF3
  rw [hc, add_apply]
  rw [← ht]
  abel

/-- The Jacobi identity, cyclic form. -/
theorem jacobi_cycW {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : SmoothNearW X x) (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x) :
    mlieBracket I X (mlieBracket I Y Z) x + mlieBracket I Y (mlieBracket I Z X) x +
      mlieBracket I Z (mlieBracket I X Y) x = 0 := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have c2 : ∀ {V : Π y : M, TangentSpace I y}, SmoothNearW V x →
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun q : M => (⟨q, V q⟩ : TangentBundle I M)) x :=
    fun hV => (hV.self_of_nhds).of_le (by simp [minSmoothness])
  haveI : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have j1 := leibniz_identity_mlieBracket_apply (c2 hX) (c2 hY) (c2 hZ)
  have hXZ : MDiffAt (T% (mlieBracket I X Z)) x :=
    ((smoothNear_mlieBracketW hX hZ).self_of_nhds).mdifferentiableAt (by simp)
  have e1 : mlieBracket I Y (mlieBracket I Z X) x = - mlieBracket I Y (mlieBracket I X Z) x := by
    have : mlieBracket I Z X = (-1 : ℝ) • mlieBracket I X Z := by
      rw [mlieBracket_swap (V := Z) (W := X)]; funext y; simp
    rw [this, mlieBracket_const_smul_right hXZ]; simp
  have e2 := mlieBracket_swap_apply (I := I) (V := mlieBracket I X Y) (W := Z) (x := x)
  rw [e1, j1, e2]
  abel

/-- **The first Bianchi identity** for a torsion-free smooth connection. -/
theorem bianchi_first_provedW (hT : cov.torsion = 0) (x : M) (X₀ Y₀ Z₀ : TangentSpace I x) :
    cov.curvatureAt x X₀ Y₀ Z₀ + cov.curvatureAt x Y₀ Z₀ X₀ + cov.curvatureAt x Z₀ X₀ Y₀ = 0 := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  have hX : SmoothNearW X x := eventually_extendW x X₀
  have hY : SmoothNearW Y x := eventually_extendW x Y₀
  have hZ : SmoothNearW Z x := eventually_extendW x Z₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  rw [← hXx, ← hYx, ← hZx]
  rw [curvatureAt_apply_eventuallyW cov X Y Z x hX hY hZ, curvatureAt_apply_eventuallyW cov Y Z X x hY hZ hX,
    curvatureAt_apply_eventuallyW cov Z X Y x hZ hX hY]
  have a1 := bianchi_first_auxW cov (X := X) (Y := Y) (Z := Z) (x := x) hT hX hY hZ
  have a2 := bianchi_first_auxW cov (X := Y) (Y := Z) (Z := X) (x := x) hT hY hZ hX
  have a3 := bianchi_first_auxW cov (X := Z) (Y := X) (Z := Y) (x := x) hT hZ hX hY
  have j := jacobi_cycW hX hY hZ
  rw [← a1, ← a2, ← a3] at j
  rw [← j]
  abel

variable {n : ℕ} (g : NondegMetric I M)

/-- Metric compatibility in terms of `mvfderiv`. -/
theorem compat_mvW (hC : cov.IsMetricCompatible g) {A B V : Π y : M, TangentSpace I y} {y : M}
    (hA : MDiffAt (T% A) y) (hB : MDiffAt (T% B) y) (hV : MDiffAt (T% V) y) :
    mvfderiv I (gpair g A B) y (V y) =
      g.g y (cov A y (V y)) (B y) + g.g y (A y) (cov B y (V y)) :=
  hC V A B y hV hA hB

/-- Metric compatibility in terms of `mvfderiv` (second form). -/
theorem compat_mv'W (hC : cov.IsMetricCompatible g) {A B : Π y : M, TangentSpace I y} {y : M}
    {V : Π y : M, TangentSpace I y} (hA : MDiffAt (T% A) y) (hB : MDiffAt (T% B) y)
    (hV : MDiffAt (T% V) y) :
    mvfderiv I (gpair g A B) y (V y) =
      g.g y (cov A y (V y)) (B y) + g.g y (A y) (cov B y (V y)) :=
  compat_mvW cov g hC hA hB hV

/-- The pairing of two vector fields smooth at `x` by a smooth metric is smooth at `x`. -/
theorem contMDiffAt_gpairW {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle I M)) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle I M)) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (gpair g Y Z) x := by
  have hg : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g.g y)) x :=
    g.contMDiff x
  have := ContMDiffAt.clm_bundle_apply₂ (b := id) (F₁ := E) (F₂ := E) (F₃ := ℝ) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ) hg hY hZ
  rw [contMDiffAt_totalSpace] at this
  exact this.2

/-- Antisymmetry of the curvature in the last two slots, in terms of fields: `g(R(X,Y)Z, W) + g(Z, R(X,Y)W) = 0` for a metric connection (the proof uses `[X,Y] g = X(Y g) - Y(X g)`). -/
theorem riemann_antisymm_auxW {X Y Z W : Π y : M, TangentSpace I y} {x : M}
    (hC : cov.IsMetricCompatible g) (hX : SmoothNearW X x) (hY : SmoothNearW Y x) (hZ : SmoothNearW Z x)
    (hW : SmoothNearW W x) :
    g.g x (cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
        - cov Z x (mlieBracket I X Y x)) (W x) +
      g.g x (Z x) (cov (fun y => cov W y (Y y)) x (X x) - cov (fun y => cov W y (X y)) x (Y x)
        - cov W x (mlieBracket I X Y x)) = 0 := by
  have hXp := hX.self_of_nhds
  have hYp := hY.self_of_nhds
  have hZp := hZ.self_of_nhds
  have hWp := hW.self_of_nhds
  have mdX : MDiffAt (T% X) x := hXp.mdifferentiableAt (by simp)
  have mdY : MDiffAt (T% Y) x := hYp.mdifferentiableAt (by simp)
  have mdZ : MDiffAt (T% Z) x := hZp.mdifferentiableAt (by simp)
  have mdW : MDiffAt (T% W) x := hWp.mdifferentiableAt (by simp)
  -- the derivative of `g(Z, W)` along a field `V`, near `x`
  have inner : ∀ {V : Π y : M, TangentSpace I y}, SmoothNearW V x →
      dirDerivW (gpair g Z W) V =ᶠ[nhds x] gpair g (fun y => cov Z y (V y)) W + gpair g Z (fun y => cov W y (V y)) := by
    intro V hV
    filter_upwards [hV, hZ, hW] with y hVy hZy hWy
    exact compat_mvW cov g hC (hZy.mdifferentiableAt (by simp)) (hWy.mdifferentiableAt (by simp))
      (hVy.mdifferentiableAt (by simp))
  have outer : ∀ {V U : Π y : M, TangentSpace I y}, SmoothNearW V x → SmoothNearW U x →
      mvfderiv I (dirDerivW (gpair g Z W) V) x (U x) =
        g.g x (cov (fun y => cov Z y (V y)) x (U x)) (W x) + g.g x (cov Z x (V x)) (cov W x (U x)) +
        (g.g x (cov Z x (U x)) (cov W x (V x)) + g.g x (Z x) (cov (fun y => cov W y (V y)) x (U x))) := by
    intro V U hV hU
    have hVp := hV.self_of_nhds
    have hUp := hU.self_of_nhds
    have h1 : MDiffAt (T% (fun y => cov Z y (V y))) x :=
      (contMDiffAt_covApplyW cov hVp hZ).mdifferentiableAt (by simp)
    have h2 : MDiffAt (T% (fun y => cov W y (V y))) x :=
      (contMDiffAt_covApplyW cov hVp hW).mdifferentiableAt (by simp)
    have mdU : MDiffAt (T% U) x := hUp.mdifferentiableAt (by simp)
    have d1 := mdiffAt_gpair g h1 mdW
    have d2 := mdiffAt_gpair g mdZ h2
    rw [mvfderiv_congrW (inner hV), mvfderiv_add d1 d2, add_apply,
      compat_mvW cov g hC h1 mdW mdU, compat_mvW cov g hC mdZ h2 mdU]
  have hgs : ∀ᶠ y in nhds x, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (gpair g Z W) y := by
    filter_upwards [hZ, hW] with y hZy hWy using contMDiffAt_gpairW g hZy hWy
  have hd := mfderiv_mlieBracketW (gpair g Z W) X Y x hgs mdX mdY
  have hd' : mvfderiv I (gpair g Z W) x (mlieBracket I X Y x) =
      mvfderiv I (dirDerivW (gpair g Z W) Y) x (X x) -
        mvfderiv I (dirDerivW (gpair g Z W) X) x (Y x) := hd
  have hbr : MDiffAt (T% (mlieBracket I X Y)) x :=
    ((smoothNear_mlieBracketW hX hY).self_of_nhds).mdifferentiableAt (by simp)
  rw [compat_mv'W cov g hC mdZ mdW hbr, outer hY hX, outer hX hY] at hd'
  simp only [map_sub, sub_apply]
  linarith

/-- **The lowered curvature is antisymmetric in its last two slots** for a metric-compatible connection. -/
theorem riemannLowerAt_antisymm_lastW (hC : cov.IsMetricCompatible g) (x : M) (X₀ Y₀ Z₀ W₀ : TangentSpace I x) :
    cov.riemannLowerAt g x X₀ Y₀ Z₀ W₀ = - cov.riemannLowerAt g x X₀ Y₀ W₀ Z₀ := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  set W := FiberBundle.extend E W₀ with hWd
  have hX : SmoothNearW X x := eventually_extendW x X₀
  have hY : SmoothNearW Y x := eventually_extendW x Y₀
  have hZ : SmoothNearW Z x := eventually_extendW x Z₀
  have hW : SmoothNearW W x := eventually_extendW x W₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  have hWx : W x = W₀ := FiberBundle.extend_apply_self E W₀
  have key := riemann_antisymm_auxW cov g hC hX hY hZ hW
  unfold Connection.riemannLowerAt
  rw [← hXx, ← hYx, ← hZx, ← hWx, curvatureAt_apply_eventuallyW cov X Y Z x hX hY hZ,
    curvatureAt_apply_eventuallyW cov X Y W x hX hY hW]
  have hs := g.symm x (Z x) (cov (fun y => cov W y (Y y)) x (X x) - cov (fun y => cov W y (X y)) x (Y x)
        - cov W x (mlieBracket I X Y x))
  linarith

/-- The curvature is antisymmetric in its first two slots. -/
theorem curvatureAt_antisymm_leftW (x : M) (X₀ Y₀ Z₀ : TangentSpace I x) :
    cov.curvatureAt x X₀ Y₀ Z₀ = - cov.curvatureAt x Y₀ X₀ Z₀ := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  have hX : SmoothNearW X x := eventually_extendW x X₀
  have hY : SmoothNearW Y x := eventually_extendW x Y₀
  have hZ : SmoothNearW Z x := eventually_extendW x Z₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  rw [← hXx, ← hYx, ← hZx, curvatureAt_apply_eventuallyW cov X Y Z x hX hY hZ,
    curvatureAt_apply_eventuallyW cov Y X Z x hY hX hZ, mlieBracket_swap_apply (V := X) (W := Y)]
  simp only [map_neg]
  abel

/-- **The pair symmetry** `g(R(X,Y)Z, W) = g(R(Z,W)X, Y)` of the curvature of a Levi-Civita connection (from the first Bianchi identity and the antisymmetries). -/
theorem riemannLowerAt_pair_symmW (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) (x : M)
    (X Y Z W : TangentSpace I x) :
    cov.riemannLowerAt g x X Y Z W = cov.riemannLowerAt g x Z W X Y := by
  have A12 : ∀ a b c d : TangentSpace I x,
      cov.riemannLowerAt g x a b c d = - cov.riemannLowerAt g x b a c d := fun a b c d => by
    unfold Connection.riemannLowerAt
    rw [curvatureAt_antisymm_leftW cov x a b c, map_neg]; simp
  have A34 := riemannLowerAt_antisymm_lastW cov g hC x
  have B : ∀ a b c d : TangentSpace I x,
      cov.riemannLowerAt g x a b c d + cov.riemannLowerAt g x b c a d + cov.riemannLowerAt g x c a b d = 0 :=
    fun a b c d => by
      unfold Connection.riemannLowerAt
      rw [← add_apply, ← add_apply, ← map_add, ← map_add, bianchi_first_provedW cov hT x a b c]
      simp
  have tup : List (TangentSpace I x × TangentSpace I x × TangentSpace I x × TangentSpace I x) :=
    [(X,Y,Z,W),(Y,Z,X,W),(Z,X,Y,W),(Y,Z,W,X),(Z,W,Y,X),(W,Y,Z,X),(Z,W,X,Y),(W,X,Z,Y),(X,Z,W,Y),
     (W,X,Y,Z),(X,Y,W,Z),(Y,W,X,Z)]
  have := B X Y Z W
  have := B Y Z W X
  have := B Z W X Y
  have := B W X Y Z
  have := A34 X Y Z W
  have := A34 Y Z W X
  have := A34 Z X Y W
  have := A34 Z W Y X
  have := A34 W Y Z X
  have := A34 Z W X Y
  have := A34 W X Z Y
  have := A34 X Z W Y
  have := A34 W X Y Z
  have := A34 Y W X Z
  have := A34 Y Z X W
  have := A12 W Y Z X
  have := A12 Y W X Z
  have := A12 X Z W Y
  have := A12 Z X Y W
  have := A12 W X Y Z
  have := A12 W X Z Y
  have := A12 X Y W Z
  have := A12 Y Z W X
  have := A12 Z W Y X
  linarith

section Ricci
variable (x : M)

/-- The Gram matrix of `g` in the basis `Module.finBasis`. -/
def metricGramW : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.g x (Module.finBasis ℝ E i : TangentSpace I x)
    (Module.finBasis ℝ E j : TangentSpace I x)

/-- The basis of the tangent space. -/
def tbW : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) := Module.finBasis ℝ E

/-- The Gram matrix of a metric in a basis is invertible. -/
theorem metricGram_isUnitW : IsUnit (metricGramW g x).det := by
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (tbW x)).mp
    (g.bilinForm_nondegenerate x)
  have hmat : LinearMap.BilinForm.toMatrix (tbW x) (g.g x).toBilinForm = metricGramW g x := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [← hmat]
  exact h.isUnit

/-- The coordinates of a tangent vector are `Σ g^{ij} g(u, e_j)`. -/
theorem coord_eq_sumW (u : TangentSpace I x) (i : Fin (Module.finrank ℝ E)) :
    (tbW x).coord i u = ∑ j, (metricGramW g x)⁻¹ i j * g.g x u (tbW x j) := by
  have hsym : (metricGramW g x).transpose = metricGramW g x := by
    ext i j; exact g.symm x _ _
  have hG := Matrix.nonsing_inv_mul _ (metricGram_isUnitW g x)
  have hexp : ∀ j, g.g x u (tbW x j) = ∑ k, (tbW x).coord k u * metricGramW g x k j := by
    intro j
    conv_lhs => rw [← (tbW x).sum_repr u]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [metricGramW, Module.Basis.coord_apply]
    exact Or.inl rfl
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 := congrFun (congrFun hG i)
  simp only [Matrix.mul_apply, Matrix.one_apply] at h2
  have : ∀ k, ∑ j, (metricGramW g x)⁻¹ i j * ((tbW x).coord k u * metricGramW g x k j) = (tbW x).coord k u * (if i = k then 1 else 0) := by
    intro k
    rw [← h2 k]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (congrFun hsym k) j
    simp only [Matrix.transpose_apply] at this
    rw [← this]; ring
  simp only [this]
  simp

/-- The lowered curvature is antisymmetric in its first two slots. -/
theorem riemannLowerAt_antisymm_firstW (x : M) (a b c d : TangentSpace I x) :
    cov.riemannLowerAt g x a b c d = - cov.riemannLowerAt g x b a c d := by
  unfold Connection.riemannLowerAt
  rw [curvatureAt_antisymm_leftW cov x a b c, map_neg]; simp

/-- The Ricci tensor as `Σ g^{ij} R(e_i, Y, Z, e_j)`. -/
theorem ricciAt_eq_sumW (x : M) (Y Z : TangentSpace I x) :
    cov.ricciAt x Y Z = ∑ i, ∑ j, (metricGramW g x)⁻¹ i j *
      cov.riemannLowerAt g x (tbW x i) Y Z (tbW x j) := by
  unfold Connection.ricciAt Connection.riemannLowerAt
  refine Finset.sum_congr rfl fun i _ => ?_
  exact coord_eq_sumW g x _ i

/-- **The Ricci tensor of a Levi-Civita connection is symmetric.** -/
theorem ricciAt_symm_provedW (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) (x : M)
    (Y Z : TangentSpace I x) : cov.ricciAt x Y Z = cov.ricciAt x Z Y := by
  have hsym : (metricGramW g x).transpose = metricGramW g x := by
    ext i j; exact g.symm x _ _
  have hinv : ((metricGramW g x)⁻¹).transpose = (metricGramW g x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hsym]
  have hL : ∀ i j, cov.riemannLowerAt g x (tbW x i) Y Z (tbW x j) =
      cov.riemannLowerAt g x (tbW x j) Z Y (tbW x i) := fun i j => by
    rw [riemannLowerAt_pair_symmW cov g hT hC x, riemannLowerAt_antisymm_firstW cov g x Z (tbW x j) (tbW x i) Y,
      riemannLowerAt_antisymm_lastW cov g hC x (tbW x j) Z (tbW x i) Y]
    ring
  rw [ricciAt_eq_sumW cov g x Y Z, ricciAt_eq_sumW cov g x Z Y]
  simp only [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun hinv j) i
  simp only [Matrix.transpose_apply] at this
  rw [this]
end Ricci
end Lightlike
