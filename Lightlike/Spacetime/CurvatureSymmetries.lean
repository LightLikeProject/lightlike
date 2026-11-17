import Lightlike.Spacetime.ChartCurvature

/-!
# Symmetries of the curvature of a Levi-Civita connection

For a smooth connection `cov` on a Hausdorff manifold `M` modelled on a finite-dimensional space (no boundary),
under the same hypotheses as `curvatureAt_apply_proved` (`ChartCurvature.lean`):

* `curvatureAt_apply_eventually`: the curvature at `x` is `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` for any fields
  smooth near `x`;
* `bianchi_first_proved`: the first Bianchi identity for a torsion-free connection (torsion freeness, the
  Jacobi identity `jacobi_cyc` of the Lie bracket);
* `riemann_antisymm_last`: `g(R(X,Y)Z, W) = -g(R(X,Y)W, Z)` for a metric connection (from
  `mfderiv_mlieBracket`), and `curvatureAt_antisymm_left` the antisymmetry in `X, Y`;
* `riemann_pair_symm`: `g(R(X,Y)Z, W) = g(R(Z,W)X, Y)` for the Levi-Civita connection;
* `ricciAt_symm_proved`: the Ricci tensor is symmetric (trace with the inverse Gram matrix, `coord_eq_sum`).

**Limits.** Boundaryless Hausdorff manifolds; the symmetry statements of the tasks `T-GE1-P3` and `T-GE1-P4` are
for any `ModelWithCorners` and are not closed by this file.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
variable (cov : Connection 𝓘(ℝ, E) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- Smooth near a point. -/
def SmoothNear (X : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x : M) : Prop :=
  ∀ᶠ y in nhds x, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
    (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, E) M)) y

/-- **The curvature through any fields smooth near the point**: `curvatureAt` at `x` of the values of `X, Y, Z` is `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `x`, for fields smooth near `x`. -/
theorem curvatureAt_apply_eventually
    (X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y) (x : M)
    (hX : SmoothNear X x) (hY : SmoothNear Y x) (hZ : SmoothNear Z x) :
    cov.curvatureAt x (X x) (Y x) (Z x) =
      cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
        - cov Z x (mlieBracket 𝓘(ℝ, E) X Y x) := by
  have hx : x ∈ (tTriv (E := E) x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have h1 := curvature_hat cov x hx hX hY hZ
  have h2 := curvature_hat cov x hx (eventually_extend x (X x)) (eventually_extend x (Y x))
    (eventually_extend x (Z x))
  simp only [FiberBundle.extend_apply_self] at h2
  unfold Connection.curvatureAt
  have hE := h2.trans h1.symm
  dsimp only
  simp only [FiberBundle.extend_apply_self]
  exact (symmL_hv x hx _).symm.trans ((congrArg ((tTriv (E := E) x).symmL ℝ x) hE).trans (symmL_hv x hx _))

/-- The Lie bracket of fields smooth near `x` is smooth near `x`. -/
theorem smoothNear_mlieBracket {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : SmoothNear X x) (hY : SmoothNear Y x) : SmoothNear (mlieBracket 𝓘(ℝ, E) X Y) x := by
  haveI : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  haveI : IsManifold 𝓘(ℝ, E) (((⊤ : ℕ∞) : ℕ∞ω) + 1) M := by
    refine IsManifold.of_le (n := ∞) ?_
    simp
  filter_upwards [hX, hY] with y hXy hYy
  exact ContMDiffAt.mlieBracket_vectorField (m := ⊤) (n := ⊤) hXy hYy (by simp [minSmoothness])

/-- The torsion-free condition on fields differentiable at `x`. -/
theorem cov_torsion {cov' : Connection 𝓘(ℝ, E) M} (h : cov'.torsion = 0)
    {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cov' Y x (X x) - cov' X x (Y x) = mlieBracket 𝓘(ℝ, E) X Y x :=
  ((CovariantDerivative.torsion_eq_zero_iff cov').1 h) hX hY

/-- One term of the first Bianchi identity: `∇_X ∇_Y Z - ∇_X ∇_Z Y - ∇_{[Y,Z]} X = [X, [Y, Z]]` for a torsion-free connection. -/
theorem bianchi_first_aux {X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hT : cov.torsion = 0) (hX : SmoothNear X x) (hY : SmoothNear Y x) (hZ : SmoothNear Z x) :
    cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Y y (Z y)) x (X x) -
      cov X x (mlieBracket 𝓘(ℝ, E) Y Z x) = mlieBracket 𝓘(ℝ, E) X (mlieBracket 𝓘(ℝ, E) Y Z) x := by
  have hXp : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, E) M)) x := hX.self_of_nhds
  have hYp := hY.self_of_nhds
  have hZp := hZ.self_of_nhds
  have hF1 : MDiffAt (T% (fun y => cov Z y (Y y))) x :=
    (contMDiffAt_covApply cov hYp hZ).mdifferentiableAt (by simp)
  have hF2 : MDiffAt (T% (fun y => cov Y y (Z y))) x :=
    (contMDiffAt_covApply cov hZp hY).mdifferentiableAt (by simp)
  have hF3s : SmoothNear (mlieBracket 𝓘(ℝ, E) Y Z) x := smoothNear_mlieBracket hY hZ
  have hF3 : MDiffAt (T% (mlieBracket 𝓘(ℝ, E) Y Z)) x := (hF3s.self_of_nhds).mdifferentiableAt (by simp)
  have heq : (fun y => cov Z y (Y y)) =ᶠ[nhds x]
      ((fun y => cov Y y (Z y)) + mlieBracket 𝓘(ℝ, E) Y Z) := by
    filter_upwards [hY, hZ] with y hYy hZy
    have := cov_torsion hT (X := Y) (Y := Z) (x := y) (hYy.mdifferentiableAt (by simp))
      (hZy.mdifferentiableAt (by simp))
    simp only [Pi.add_apply]
    rw [← this]; abel
  have hc : cov (fun y => cov Z y (Y y)) x = cov (fun y => cov Y y (Z y)) x + cov (mlieBracket 𝓘(ℝ, E) Y Z) x := by
    rw [(cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq hF1 (mdifferentiableAt_add_section hF2 hF3)
      Filter.univ_mem heq]
    exact (cov.isCovariantDerivativeOn (s := Set.univ)).add hF2 hF3
  have ht := cov_torsion hT (X := X) (Y := mlieBracket 𝓘(ℝ, E) Y Z) (x := x) (hXp.mdifferentiableAt (by simp)) hF3
  rw [hc, add_apply]
  rw [← ht]
  abel

/-- The Jacobi identity, cyclic form. -/
theorem jacobi_cyc {X Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : SmoothNear X x) (hY : SmoothNear Y x) (hZ : SmoothNear Z x) :
    mlieBracket 𝓘(ℝ, E) X (mlieBracket 𝓘(ℝ, E) Y Z) x + mlieBracket 𝓘(ℝ, E) Y (mlieBracket 𝓘(ℝ, E) Z X) x +
      mlieBracket 𝓘(ℝ, E) Z (mlieBracket 𝓘(ℝ, E) X Y) x = 0 := by
  haveI : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have c2 : ∀ {V : Π y : M, TangentSpace 𝓘(ℝ, E) y}, SmoothNear V x →
      ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E) M)) x :=
    fun hV => (hV.self_of_nhds).of_le (by simp [minSmoothness])
  haveI : IsManifold 𝓘(ℝ, E) (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have j1 := leibniz_identity_mlieBracket_apply (c2 hX) (c2 hY) (c2 hZ)
  have hXZ : MDiffAt (T% (mlieBracket 𝓘(ℝ, E) X Z)) x :=
    ((smoothNear_mlieBracket hX hZ).self_of_nhds).mdifferentiableAt (by simp)
  have e1 : mlieBracket 𝓘(ℝ, E) Y (mlieBracket 𝓘(ℝ, E) Z X) x = - mlieBracket 𝓘(ℝ, E) Y (mlieBracket 𝓘(ℝ, E) X Z) x := by
    have : mlieBracket 𝓘(ℝ, E) Z X = (-1 : ℝ) • mlieBracket 𝓘(ℝ, E) X Z := by
      rw [mlieBracket_swap (V := Z) (W := X)]; funext y; simp
    rw [this, mlieBracket_const_smul_right hXZ]; simp
  have e2 := mlieBracket_swap_apply (I := 𝓘(ℝ, E)) (V := mlieBracket 𝓘(ℝ, E) X Y) (W := Z) (x := x)
  rw [e1, j1, e2]
  abel

/-- **The first Bianchi identity** for a torsion-free smooth connection. -/
theorem bianchi_first_proved (hT : cov.torsion = 0) (x : M) (X₀ Y₀ Z₀ : TangentSpace 𝓘(ℝ, E) x) :
    cov.curvatureAt x X₀ Y₀ Z₀ + cov.curvatureAt x Y₀ Z₀ X₀ + cov.curvatureAt x Z₀ X₀ Y₀ = 0 := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  have hX : SmoothNear X x := eventually_extend x X₀
  have hY : SmoothNear Y x := eventually_extend x Y₀
  have hZ : SmoothNear Z x := eventually_extend x Z₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  rw [← hXx, ← hYx, ← hZx]
  rw [curvatureAt_apply_eventually cov X Y Z x hX hY hZ, curvatureAt_apply_eventually cov Y Z X x hY hZ hX,
    curvatureAt_apply_eventually cov Z X Y x hZ hX hY]
  have a1 := bianchi_first_aux cov (X := X) (Y := Y) (Z := Z) (x := x) hT hX hY hZ
  have a2 := bianchi_first_aux cov (X := Y) (Y := Z) (Z := X) (x := x) hT hY hZ hX
  have a3 := bianchi_first_aux cov (X := Z) (Y := X) (Z := Y) (x := x) hT hZ hX hY
  have j := jacobi_cyc hX hY hZ
  rw [← a1, ← a2, ← a3] at j
  rw [← j]
  abel

variable {n : ℕ} (g : LorentzianMetric 𝓘(ℝ, E) M n)

/-- Metric compatibility in terms of `mvfderiv`. -/
theorem compat_mv (hC : cov.IsMetricCompatible g) {A B V : Π y : M, TangentSpace 𝓘(ℝ, E) y} {y : M}
    (hA : MDiffAt (T% A) y) (hB : MDiffAt (T% B) y) (hV : MDiffAt (T% V) y) :
    mvfderiv 𝓘(ℝ, E) (gpair g A B) y (V y) =
      g.g y (cov A y (V y)) (B y) + g.g y (A y) (cov B y (V y)) :=
  hC V A B y hV hA hB

/-- Metric compatibility in terms of `mvfderiv` (second form). -/
theorem compat_mv' (hC : cov.IsMetricCompatible g) {A B : Π y : M, TangentSpace 𝓘(ℝ, E) y} {y : M}
    {V : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hA : MDiffAt (T% A) y) (hB : MDiffAt (T% B) y)
    (hV : MDiffAt (T% V) y) :
    mvfderiv 𝓘(ℝ, E) (gpair g A B) y (V y) =
      g.g y (cov A y (V y)) (B y) + g.g y (A y) (cov B y (V y)) :=
  compat_mv cov g hC hA hB hV

/-- The pairing of two vector fields smooth at `x` by a smooth metric is smooth at `x`. -/
theorem contMDiffAt_gpair {Y Z : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hY : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Y q⟩ : TangentBundle 𝓘(ℝ, E) M)) x)
    (hZ : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, Z q⟩ : TangentBundle 𝓘(ℝ, E) M)) x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (gpair g Y Z) x := by
  have hg : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) y (g.g y)) x :=
    g.contMDiff x
  have := ContMDiffAt.clm_bundle_apply₂ (b := id) (F₁ := E) (F₂ := E) (F₃ := ℝ) (E₁ := TangentSpace 𝓘(ℝ, E))
    (E₂ := TangentSpace 𝓘(ℝ, E)) (E₃ := Bundle.Trivial M ℝ) hg hY hZ
  rw [contMDiffAt_totalSpace] at this
  exact this.2

/-- Antisymmetry of the curvature in the last two slots, in terms of fields: `g(R(X,Y)Z, W) + g(Z, R(X,Y)W) = 0` for a metric connection (the proof uses `[X,Y] g = X(Y g) - Y(X g)`). -/
theorem riemann_antisymm_aux {X Y Z W : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hC : cov.IsMetricCompatible g) (hX : SmoothNear X x) (hY : SmoothNear Y x) (hZ : SmoothNear Z x)
    (hW : SmoothNear W x) :
    g.g x (cov (fun y => cov Z y (Y y)) x (X x) - cov (fun y => cov Z y (X y)) x (Y x)
        - cov Z x (mlieBracket 𝓘(ℝ, E) X Y x)) (W x) +
      g.g x (Z x) (cov (fun y => cov W y (Y y)) x (X x) - cov (fun y => cov W y (X y)) x (Y x)
        - cov W x (mlieBracket 𝓘(ℝ, E) X Y x)) = 0 := by
  have hXp := hX.self_of_nhds
  have hYp := hY.self_of_nhds
  have hZp := hZ.self_of_nhds
  have hWp := hW.self_of_nhds
  have mdX : MDiffAt (T% X) x := hXp.mdifferentiableAt (by simp)
  have mdY : MDiffAt (T% Y) x := hYp.mdifferentiableAt (by simp)
  have mdZ : MDiffAt (T% Z) x := hZp.mdifferentiableAt (by simp)
  have mdW : MDiffAt (T% W) x := hWp.mdifferentiableAt (by simp)
  -- the derivative of `g(Z, W)` along a field `V`, near `x`
  have inner : ∀ {V : Π y : M, TangentSpace 𝓘(ℝ, E) y}, SmoothNear V x →
      dirDeriv (gpair g Z W) V =ᶠ[nhds x] gpair g (fun y => cov Z y (V y)) W + gpair g Z (fun y => cov W y (V y)) := by
    intro V hV
    filter_upwards [hV, hZ, hW] with y hVy hZy hWy
    exact compat_mv cov g hC (hZy.mdifferentiableAt (by simp)) (hWy.mdifferentiableAt (by simp))
      (hVy.mdifferentiableAt (by simp))
  have outer : ∀ {V U : Π y : M, TangentSpace 𝓘(ℝ, E) y}, SmoothNear V x → SmoothNear U x →
      mvfderiv 𝓘(ℝ, E) (dirDeriv (gpair g Z W) V) x (U x) =
        g.g x (cov (fun y => cov Z y (V y)) x (U x)) (W x) + g.g x (cov Z x (V x)) (cov W x (U x)) +
        (g.g x (cov Z x (U x)) (cov W x (V x)) + g.g x (Z x) (cov (fun y => cov W y (V y)) x (U x))) := by
    intro V U hV hU
    have hVp := hV.self_of_nhds
    have hUp := hU.self_of_nhds
    have h1 : MDiffAt (T% (fun y => cov Z y (V y))) x :=
      (contMDiffAt_covApply cov hVp hZ).mdifferentiableAt (by simp)
    have h2 : MDiffAt (T% (fun y => cov W y (V y))) x :=
      (contMDiffAt_covApply cov hVp hW).mdifferentiableAt (by simp)
    have mdU : MDiffAt (T% U) x := hUp.mdifferentiableAt (by simp)
    have d1 := mdiffAt_gpair g h1 mdW
    have d2 := mdiffAt_gpair g mdZ h2
    rw [mvfderiv_congr (inner hV), mvfderiv_add d1 d2, add_apply,
      compat_mv cov g hC h1 mdW mdU, compat_mv cov g hC mdZ h2 mdU]
  have hgs : ∀ᶠ y in nhds x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (gpair g Z W) y := by
    filter_upwards [hZ, hW] with y hZy hWy using contMDiffAt_gpair g hZy hWy
  have hd := mfderiv_mlieBracket (gpair g Z W) X Y x hgs mdX mdY
  have hd' : mvfderiv 𝓘(ℝ, E) (gpair g Z W) x (mlieBracket 𝓘(ℝ, E) X Y x) =
      mvfderiv 𝓘(ℝ, E) (dirDeriv (gpair g Z W) Y) x (X x) -
        mvfderiv 𝓘(ℝ, E) (dirDeriv (gpair g Z W) X) x (Y x) := hd
  have hbr : MDiffAt (T% (mlieBracket 𝓘(ℝ, E) X Y)) x :=
    ((smoothNear_mlieBracket hX hY).self_of_nhds).mdifferentiableAt (by simp)
  rw [compat_mv' cov g hC mdZ mdW hbr, outer hY hX, outer hX hY] at hd'
  simp only [map_sub, sub_apply]
  linarith

/-- **The lowered curvature is antisymmetric in its last two slots** for a metric-compatible connection. -/
theorem riemann_antisymm_last (hC : cov.IsMetricCompatible g) (x : M) (X₀ Y₀ Z₀ W₀ : TangentSpace 𝓘(ℝ, E) x) :
    cov.riemannLowerAt g x X₀ Y₀ Z₀ W₀ = - cov.riemannLowerAt g x X₀ Y₀ W₀ Z₀ := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  set W := FiberBundle.extend E W₀ with hWd
  have hX : SmoothNear X x := eventually_extend x X₀
  have hY : SmoothNear Y x := eventually_extend x Y₀
  have hZ : SmoothNear Z x := eventually_extend x Z₀
  have hW : SmoothNear W x := eventually_extend x W₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  have hWx : W x = W₀ := FiberBundle.extend_apply_self E W₀
  have key := riemann_antisymm_aux cov g hC hX hY hZ hW
  unfold Connection.riemannLowerAt
  rw [← hXx, ← hYx, ← hZx, ← hWx, curvatureAt_apply_eventually cov X Y Z x hX hY hZ,
    curvatureAt_apply_eventually cov X Y W x hX hY hW]
  have hs := g.symm x (Z x) (cov (fun y => cov W y (Y y)) x (X x) - cov (fun y => cov W y (X y)) x (Y x)
        - cov W x (mlieBracket 𝓘(ℝ, E) X Y x))
  linarith

/-- The curvature is antisymmetric in its first two slots. -/
theorem curvatureAt_antisymm_left (x : M) (X₀ Y₀ Z₀ : TangentSpace 𝓘(ℝ, E) x) :
    cov.curvatureAt x X₀ Y₀ Z₀ = - cov.curvatureAt x Y₀ X₀ Z₀ := by
  set X := FiberBundle.extend E X₀ with hXd
  set Y := FiberBundle.extend E Y₀ with hYd
  set Z := FiberBundle.extend E Z₀ with hZd
  have hX : SmoothNear X x := eventually_extend x X₀
  have hY : SmoothNear Y x := eventually_extend x Y₀
  have hZ : SmoothNear Z x := eventually_extend x Z₀
  have hXx : X x = X₀ := FiberBundle.extend_apply_self E X₀
  have hYx : Y x = Y₀ := FiberBundle.extend_apply_self E Y₀
  have hZx : Z x = Z₀ := FiberBundle.extend_apply_self E Z₀
  rw [← hXx, ← hYx, ← hZx, curvatureAt_apply_eventually cov X Y Z x hX hY hZ,
    curvatureAt_apply_eventually cov Y X Z x hY hX hZ, mlieBracket_swap_apply (V := X) (W := Y)]
  simp only [map_neg]
  abel

/-- **The pair symmetry** `g(R(X,Y)Z, W) = g(R(Z,W)X, Y)` of the curvature of a Levi-Civita connection (from the first Bianchi identity and the antisymmetries). -/
theorem riemann_pair_symm (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) (x : M)
    (X Y Z W : TangentSpace 𝓘(ℝ, E) x) :
    cov.riemannLowerAt g x X Y Z W = cov.riemannLowerAt g x Z W X Y := by
  have A12 : ∀ a b c d : TangentSpace 𝓘(ℝ, E) x,
      cov.riemannLowerAt g x a b c d = - cov.riemannLowerAt g x b a c d := fun a b c d => by
    unfold Connection.riemannLowerAt
    rw [curvatureAt_antisymm_left cov x a b c, map_neg]; simp
  have A34 := riemann_antisymm_last cov g hC x
  have B : ∀ a b c d : TangentSpace 𝓘(ℝ, E) x,
      cov.riemannLowerAt g x a b c d + cov.riemannLowerAt g x b c a d + cov.riemannLowerAt g x c a b d = 0 :=
    fun a b c d => by
      unfold Connection.riemannLowerAt
      rw [← add_apply, ← add_apply, ← map_add, ← map_add, bianchi_first_proved cov hT x a b c]
      simp
  have tup : List (TangentSpace 𝓘(ℝ, E) x × TangentSpace 𝓘(ℝ, E) x × TangentSpace 𝓘(ℝ, E) x × TangentSpace 𝓘(ℝ, E) x) :=
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
def gram : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j => g.g x (Module.finBasis ℝ E i : TangentSpace 𝓘(ℝ, E) x)
    (Module.finBasis ℝ E j : TangentSpace 𝓘(ℝ, E) x)

/-- The basis of the tangent space. -/
def tb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) x) := Module.finBasis ℝ E

/-- The Gram matrix of a Lorentzian metric in a basis is invertible. -/
theorem gram_isUnit : IsUnit (gram g x).det := by
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (tb x)).mp
    (g.lorentzian x).bilinForm_nondegenerate
  have hmat : LinearMap.BilinForm.toMatrix (tb x) (g.g x).toBilinForm = gram g x := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [← hmat]
  exact h.isUnit

/-- The coordinates of a tangent vector are `Σ g^{ij} g(u, e_j)`. -/
theorem coord_eq_sum (u : TangentSpace 𝓘(ℝ, E) x) (i : Fin (Module.finrank ℝ E)) :
    (tb x).coord i u = ∑ j, (gram g x)⁻¹ i j * g.g x u (tb x j) := by
  have hsym : (gram g x).transpose = gram g x := by
    ext i j; exact g.symm x _ _
  have hG := Matrix.nonsing_inv_mul _ (gram_isUnit g x)
  have hexp : ∀ j, g.g x u (tb x j) = ∑ k, (tb x).coord k u * gram g x k j := by
    intro j
    conv_lhs => rw [← (tb x).sum_repr u]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [gram, Module.Basis.coord_apply]
    exact Or.inl rfl
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 := congrFun (congrFun hG i)
  simp only [Matrix.mul_apply, Matrix.one_apply] at h2
  have : ∀ k, ∑ j, (gram g x)⁻¹ i j * ((tb x).coord k u * gram g x k j) = (tb x).coord k u * (if i = k then 1 else 0) := by
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
theorem riemannLower_antisymm_first (x : M) (a b c d : TangentSpace 𝓘(ℝ, E) x) :
    cov.riemannLowerAt g x a b c d = - cov.riemannLowerAt g x b a c d := by
  unfold Connection.riemannLowerAt
  rw [curvatureAt_antisymm_left cov x a b c, map_neg]; simp

/-- The Ricci tensor as `Σ g^{ij} R(e_i, Y, Z, e_j)`. -/
theorem ricciAt_eq_sum (x : M) (Y Z : TangentSpace 𝓘(ℝ, E) x) :
    cov.ricciAt x Y Z = ∑ i, ∑ j, (gram g x)⁻¹ i j *
      cov.riemannLowerAt g x (tb x i) Y Z (tb x j) := by
  unfold Connection.ricciAt Connection.riemannLowerAt
  refine Finset.sum_congr rfl fun i _ => ?_
  exact coord_eq_sum g x _ i

/-- **The Ricci tensor of a Levi-Civita connection is symmetric.** -/
theorem ricciAt_symm_proved (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) (x : M)
    (Y Z : TangentSpace 𝓘(ℝ, E) x) : cov.ricciAt x Y Z = cov.ricciAt x Z Y := by
  have hsym : (gram g x).transpose = gram g x := by
    ext i j; exact g.symm x _ _
  have hinv : ((gram g x)⁻¹).transpose = (gram g x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hsym]
  have hL : ∀ i j, cov.riemannLowerAt g x (tb x i) Y Z (tb x j) =
      cov.riemannLowerAt g x (tb x j) Z Y (tb x i) := fun i j => by
    rw [riemann_pair_symm cov g hT hC x, riemannLower_antisymm_first cov g x Z (tb x j) (tb x i) Y,
      riemann_antisymm_last cov g hC x (tb x j) Z (tb x i) Y]
    ring
  rw [ricciAt_eq_sum cov g x Y Z, ricciAt_eq_sum cov g x Z Y]
  simp only [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun hinv j) i
  simp only [Matrix.transpose_apply] at this
  rw [this]
end Ricci
end Lightlike
