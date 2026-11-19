import Lightlike.Spacetime.Connection

/-!
# The Levi-Civita connection of a Lorentzian metric

Existence and uniqueness of the connection that is torsion free and compatible with a Lorentzian
metric `g` (`Connection.IsLeviCivita`), for a manifold `M` modelled on a finite-dimensional space `E`
with any `ModelWithCorners`. The proof follows Mathlib's Riemannian one
(`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`) with the scalar product
replaced by `g`, which only needs that `g` is symmetric and non-degenerate:

* `koszul`: the Koszul expression `K(X, Y, Z) = ½ (X g(Y, Z) + Y g(Z, X) - Z g(X, Y) - g(Y, [X, Z]) -
  g(Z, [Y, X]) + g(X, [Z, Y]))`;
* it is tensorial in `X` and `Z` and obeys the Leibniz rule in `Y` (`koszul_smul_left`, `koszul_smul_right`,
  `koszul_smul_mid` and the additivity lemmas); `koszulHom` is the corresponding tensor (Mathlib's
  `TensorialAt.mkHom₂`);
* `sharp` is the inverse of the musical isomorphism `v ↦ g(v, ·)` (`LinearMap.BilinForm.toDual`), so that
  `leviAux` with `g(∇_X Y, Z) = K(X, Y, Z)` is a covariant derivative (`leviAux_isCov`);
* `leviCivita` is torsion free (`leviCivita_torsion`) and compatible with `g` (`leviCivita_compat`);
* any torsion-free metric connection satisfies the Koszul formula (`koszul_of_isLeviCivita`), hence is equal
  to `leviCivita` on vector fields differentiable at the point (`leviCivita_unique`).

`leviCivita_exists_unique_proved` is the existence and uniqueness statement.

**Limits.** As in Mathlib, a covariant derivative is unconstrained on vector fields that are not
differentiable at the point, so uniqueness is on differentiable fields. No smoothness of the connection is
proved here.

**References.** B. O'Neill, *Semi-Riemannian Geometry* (Academic Press, 1983), Theorem 3.11 (the fundamental
theorem); Mathlib's `CovariantDerivative.leviCivitaConnection` (Riemannian case).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}

/-- The function `y ↦ g(Y y, Z y)`. -/
def gpair (g : NondegMetric I M) (Y Z : Π x : M, TangentSpace I x) : M → ℝ :=
  fun y => g.g y (Y y) (Z y)

/-- The pairing `y ↦ g(Y y, Z y)` of two vector fields differentiable at `x` is differentiable at `x`. -/
theorem mdiffAt_gpair (g : NondegMetric I M) {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) : MDiffAt (gpair g Y Z) x := by
  have hg : MDiffAt (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) y (g.g y)) x :=
    (g.contMDiff x).mdifferentiableAt (by simp)
  have := hg.clm_bundle_apply₂ (b := id) (F₁ := E) (F₂ := E) (F₃ := ℝ) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ) hY hZ
  simp only [mdifferentiableAt_totalSpace] at this
  exact this.2

variable (g : NondegMetric I M)

/-- `g(f Y, Z) = f g(Y, Z)` as functions. -/
theorem gpair_smul_left (f : M → ℝ) (Y Z : Π x : M, TangentSpace I x) :
    gpair g (f • Y) Z = f * gpair g Y Z := by
  funext y; simp [gpair]

/-- `g(Y, f Z) = f g(Y, Z)` as functions. -/
theorem gpair_smul_right (f : M → ℝ) (Y Z : Π x : M, TangentSpace I x) :
    gpair g Y (f • Z) = f * gpair g Y Z := by
  funext y; simp [gpair]

/-- `g(Y + Y', Z) = g(Y, Z) + g(Y', Z)` as functions. -/
theorem gpair_add_left (Y Y' Z : Π x : M, TangentSpace I x) :
    gpair g (Y + Y') Z = gpair g Y Z + gpair g Y' Z := by
  funext y; simp [gpair]

/-- `g(Y, Z + Z') = g(Y, Z) + g(Y, Z')` as functions. -/
theorem gpair_add_right (Y Z Z' : Π x : M, TangentSpace I x) :
    gpair g Y (Z + Z') = gpair g Y Z + gpair g Y Z' := by
  funext y; simp [gpair]

/-- The pairing is symmetric. -/
theorem gpair_comm (Y Z : Π x : M, TangentSpace I x) : gpair g Y Z = gpair g Z Y := by
  funext y; exact g.symm y _ _

/-- The Koszul expression `2 g(∇_X Y, Z)` over two, as a function of three vector fields. -/
def koszul (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  (mvfderiv I (gpair g Y Z) x (X x) + mvfderiv I (gpair g Z X) x (Y x)
    - mvfderiv I (gpair g X Y) x (Z x)
    - g.g x (Y x) (mlieBracket I X Z x) - g.g x (Z x) (mlieBracket I Y X x)
    + g.g x (X x) (mlieBracket I Z Y x)) / 2

variable [IsManifold I 2 M] [CompleteSpace E]
/-- The Koszul expression is tensorial in the first slot: `K(f X, Y, Z) = f K(X, Y, Z)`. -/
theorem koszul_smul_left {X Y Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszul g (f • X) Y Z x = f x * koszul g X Y Z x := by
  have h1 := mdiffAt_gpair g hY hZ
  have h2 := mdiffAt_gpair g hZ hX
  have h3 := mdiffAt_gpair g hX hY
  unfold koszul
  rw [gpair_smul_right, gpair_smul_left, mvfderiv_mul hf h2, mvfderiv_mul hf h3,
    mlieBracket_smul_left hf hX, mlieBracket_smul_right hf hX]
  have hs : g.g x (X x) (Y x) = g.g x (Y x) (X x) := g.symm x _ _
  simp [Pi.smul_apply, gpair, hs]
  ring

/-- The Koszul expression is tensorial in the third slot: `K(X, Y, f Z) = f K(X, Y, Z)`. -/
theorem koszul_smul_right {X Y Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszul g X Y (f • Z) x = f x * koszul g X Y Z x := by
  have h1 := mdiffAt_gpair g hY hZ
  have h2 := mdiffAt_gpair g hZ hX
  have h3 := mdiffAt_gpair g hX hY
  unfold koszul
  rw [gpair_smul_right, gpair_smul_left, mvfderiv_mul hf h1, mvfderiv_mul hf h2,
    mlieBracket_smul_right hf hZ, mlieBracket_smul_left hf hZ]
  have hs : g.g x (Y x) (Z x) = g.g x (Z x) (Y x) := g.symm x _ _
  have hs2 : g.g x (X x) (Z x) = g.g x (Z x) (X x) := g.symm x _ _
  simp [gpair, hs, hs2]
  ring

/-- The Koszul expression is additive in the first slot. -/
theorem koszul_add_left {X X' Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszul g (X + X') Y Z x = koszul g X Y Z x + koszul g X' Y Z x := by
  have h2 := mdiffAt_gpair g hZ hX
  have h2' := mdiffAt_gpair g hZ hX'
  have h3 := mdiffAt_gpair g hX hY
  have h3' := mdiffAt_gpair g hX' hY
  unfold koszul
  rw [gpair_add_right, gpair_add_left, mvfderiv_add h2 h2', mvfderiv_add h3 h3',
    mlieBracket_add_left hX hX', mlieBracket_add_right hX hX']
  simp
  ring

/-- The Koszul expression is additive in the third slot. -/
theorem koszul_add_right {X Y Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    koszul g X Y (Z + Z') x = koszul g X Y Z x + koszul g X Y Z' x := by
  have h1 := mdiffAt_gpair g hY hZ
  have h1' := mdiffAt_gpair g hY hZ'
  have h2 := mdiffAt_gpair g hZ hX
  have h2' := mdiffAt_gpair g hZ' hX
  unfold koszul
  rw [gpair_add_right, gpair_add_left, mvfderiv_add h1 h1', mvfderiv_add h2 h2',
    mlieBracket_add_right hZ hZ', mlieBracket_add_left hZ hZ']
  simp
  ring

/-- The Koszul expression is additive in the second slot. -/
theorem koszul_add_mid {X Y Y' Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    koszul g X (Y + Y') Z x = koszul g X Y Z x + koszul g X Y' Z x := by
  have h1 := mdiffAt_gpair g hY hZ
  have h1' := mdiffAt_gpair g hY' hZ
  have h2 := mdiffAt_gpair g hZ hX
  have h3 := mdiffAt_gpair g hX hY
  have h3' := mdiffAt_gpair g hX hY'
  unfold koszul
  rw [gpair_add_left, gpair_add_right, mvfderiv_add h1 h1', mvfderiv_add h3 h3',
    mlieBracket_add_left hY hY', mlieBracket_add_right hY hY']
  simp
  ring

/-- The Koszul expression obeys the Leibniz rule in the second slot: `K(X, f Y, Z) = f K(X, Y, Z) + X(f) g(Y, Z)`. -/
theorem koszul_smul_mid {X Y Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszul g X (f • Y) Z x = f x * koszul g X Y Z x + mvfderiv I f x (X x) * g.g x (Y x) (Z x) := by
  have h1 := mdiffAt_gpair g hY hZ
  have h2 := mdiffAt_gpair g hZ hX
  have h3 := mdiffAt_gpair g hX hY
  unfold koszul
  rw [gpair_smul_left, gpair_smul_right, mvfderiv_mul hf h1, mvfderiv_mul hf h3,
    mlieBracket_smul_left hf hY, mlieBracket_smul_right hf hY]
  have hs : g.g x (Y x) (Z x) = g.g x (Z x) (Y x) := g.symm x _ _
  have hs2 : g.g x (X x) (Y x) = g.g x (Y x) (X x) := g.symm x _ _
  simp [gpair, hs, hs2]
  ring

/-- The Koszul expression is tensorial at `x` in its first argument. -/
theorem tensorial_koszul₁ {Y Z : Π x : M, TangentSpace I x} (x : M)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X => koszul g X Y Z x) x where
  smul hf hX := by rw [koszul_smul_left g hf hX hY hZ]; rfl
  add hX hX' := koszul_add_left g hX hX' hY hZ

/-- The Koszul expression is tensorial at `x` in its third argument. -/
theorem tensorial_koszul₃ {X Y : Π x : M, TangentSpace I x} (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z => koszul g X Y Z x) x where
  smul hf hZ := by rw [koszul_smul_right g hf hX hY hZ]; rfl
  add hZ hZ' := koszul_add_right g hX hY hZ hZ'

variable [FiniteDimensional ℝ E]

/-- The Koszul tensor `(X, Z) ↦ g(∇_X Y, Z)` at `x`, for `Y` differentiable at `x`. -/
def koszulHom {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Z => koszul g X Y Z x) x
    (fun _Z hZ => tensorial_koszul₁ g x hY hZ) (fun _X hX => tensorial_koszul₃ g x hX hY)

/-- The Koszul tensor evaluated on the values of vector fields differentiable at `x`. -/
theorem koszulHom_apply {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulHom g hY (X x) (Z x) = koszul g X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hZ

/-- The musical isomorphism `T*_x → T_x` of a Lorentzian metric (the inverse of `v ↦ g(v, ·)`). -/
def sharp (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) : TangentSpace I x :=
  ((g.g x).toBilinForm.toDual (g.bilinForm_nondegenerate x)).symm
    φ.toLinearMap

/-- `g(♯φ, v) = φ(v)`. -/
theorem g_sharp (x : M) (φ : TangentSpace I x →L[ℝ] ℝ) (v : TangentSpace I x) :
    g.g x (sharp g x φ) v = φ v :=
  LinearMap.BilinForm.apply_toDual_symm_apply (B := (g.g x).toBilinForm) (v := v)
    (hB := g.bilinForm_nondegenerate x) (f := φ.toLinearMap)

/-- `♯` is additive. -/
theorem sharp_add (x : M) (φ ψ : TangentSpace I x →L[ℝ] ℝ) :
    sharp g x (φ + ψ) = sharp g x φ + sharp g x ψ := by
  unfold sharp; rw [← map_add]; rfl

/-- `♯` is homogeneous. -/
theorem sharp_smul (x : M) (c : ℝ) (φ : TangentSpace I x →L[ℝ] ℝ) :
    sharp g x (c • φ) = c • sharp g x φ := by
  unfold sharp; rw [← map_smul]; rfl

/-- A tangent vector is determined by its pairing with all tangent vectors. -/
theorem eq_of_g_eq (x : M) {v w : TangentSpace I x} (h : ∀ u, g.g x v u = g.g x w u) : v = w := by
  have : v - w = 0 := g.nondegenerate x (v - w) fun u => by simp [h u]
  exact sub_eq_zero.1 this

/-- The tensor `X ↦ ∇_X Y` at `x` (as a linear map), for `Y` differentiable at `x`. -/
def leviOf {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X₀ => sharp g x (koszulHom g hY X₀)
      map_add' := fun a b => by simp [sharp_add]
      map_smul' := fun c a => by simp [sharp_smul] }

/-- `g(∇_X Y, Z)` is the Koszul tensor. -/
theorem g_leviOf {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (X₀ Z₀ : TangentSpace I x) : g.g x (leviOf g hY X₀) Z₀ = koszulHom g hY X₀ Z₀ :=
  g_sharp g x _ Z₀

open scoped Classical in
/-- The covariant derivative underlying the Levi-Civita connection (zero on non-differentiable fields). -/
def leviAux (Y : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then leviOf g hY else 0

/-- `g(∇_X Y, Z) = K(X, Y, Z)` for vector fields differentiable at `x`. -/
theorem g_leviAux {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    g.g x (leviAux g Y x (X x)) (Z x) = koszul g X Y Z x := by
  rw [leviAux, dite_eq_left hY, g_leviOf, koszulHom_apply g hX hY hZ]

/-- A tangent vector is determined by its pairing with the values of vector fields differentiable at `x`. -/
theorem eq_of_g_eq_fields {x : M} {v w : TangentSpace I x}
    (h : ∀ Z : Π y : M, TangentSpace I y, MDiffAt (T% Z) x → g.g x v (Z x) = g.g x w (Z x)) :
    v = w := by
  refine eq_of_g_eq g x fun u => ?_
  have := h (extend E u) (mdifferentiableAt_extend _ _ u)
  simpa using this

/-- The Koszul formula defines a covariant derivative: it is additive and satisfies the Leibniz rule. -/
theorem leviAux_isCov : IsCovariantDerivativeOn E (leviAux g (M := M)) Set.univ where
  add {Y Y'} {x} hY hY' _ := by
    apply injective_eval_mdifferentiableAt_vectorField I _ x
    ext X hX
    apply eq_of_g_eq_fields g
    intro Z hZ
    have hYY' : MDiffAt (T% (Y + Y')) x := mdifferentiableAt_add_section hY hY'
    simp only [add_apply, map_add]
    rw [g_leviAux g hX hYY' hZ, g_leviAux g hX hY hZ, g_leviAux g hX hY' hZ,
      koszul_add_mid g hX hY hY' hZ]
  leibniz {Y f} {x} hY hf _ := by
    apply injective_eval_mdifferentiableAt_vectorField I _ x
    ext X hX
    apply eq_of_g_eq_fields g
    intro Z hZ
    have hfY : MDiffAt (T% (f • Y)) x := hf.smul_section hY
    simp only [add_apply, smul_apply, map_add, map_smul,
      ContinuousLinearMap.smulRight_apply]
    rw [g_leviAux g hX hfY hZ, koszul_smul_mid g hf hX hY hZ, g_leviAux g hX hY hZ]
    simp [mvfderiv]

/-- **The Levi-Civita connection of a Lorentzian metric**: the covariant derivative given by the Koszul
formula `2 g(∇_X Y, Z) = X g(Y, Z) + Y g(Z, X) - Z g(X, Y) - g(Y, [X, Z]) - g(Z, [Y, X]) + g(X, [Z, Y])`. -/
def leviCivita : Connection I M := ⟨leviAux g, leviAux_isCov g⟩

/-- The Koszul formula for the Levi-Civita connection. -/
theorem g_leviCivita {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    g.g x (leviCivita g Y x (X x)) (Z x) = koszul g X Y Z x :=
  g_leviAux g hX hY hZ

/-- The Levi-Civita connection is torsion free. -/
theorem leviCivita_torsion : (leviCivita g).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply eq_of_g_eq_fields g
  intro Z hZ
  rw [map_sub, sub_apply, g_leviCivita g hX hY hZ, g_leviCivita g hY hX hZ]
  have h1 := mdiffAt_gpair g hY hZ
  have h2 := mdiffAt_gpair g hZ hX
  have h3 := mdiffAt_gpair g hX hY
  unfold koszul
  have e1 := gpair_comm g Z Y
  have e2 := gpair_comm g X Z
  have e3 := gpair_comm g Y X
  rw [e1, e2, e3]
  have s1 := g.symm x (Z x) (mlieBracket I Y X x)
  have s2 := g.symm x (Y x) (mlieBracket I X Z x)
  rw [mlieBracket_swap_apply (V := Y) (W := X), mlieBracket_swap_apply (V := Z) (W := Y),
    mlieBracket_swap_apply (V := Z) (W := X), g.symm x (mlieBracket I X Y x) (Z x)]
  simp only [map_neg]
  ring

/-- The Levi-Civita connection is compatible with `g`. -/
theorem leviCivita_compat : (leviCivita g).IsMetricCompatible g := by
  intro X σ τ x hX hσ hτ
  have h : g.g x (σ x) (leviCivita g τ x (X x)) = g.g x (leviCivita g τ x (X x)) (σ x) := g.symm x _ _
  rw [h, g_leviCivita g hX hσ hτ, g_leviCivita g hX hτ hσ]
  show mvfderiv I (gpair g σ τ) x (X x) = _
  unfold koszul
  have e1 := gpair_comm g τ σ
  have e2 := gpair_comm g X σ
  have e3 := gpair_comm g τ X
  rw [e1, e2, e3]
  rw [mlieBracket_swap_apply (V := τ) (W := X), mlieBracket_swap_apply (V := σ) (W := X),
    mlieBracket_swap_apply (V := τ) (W := σ)]
  simp only [map_neg]
  ring

/-- **The Koszul formula** for any connection that is torsion free and compatible with `g`. -/
theorem koszul_of_isLeviCivita {cov : Connection I M} (h : cov.IsLeviCivita g)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    g.g x (cov Y x (X x)) (Z x) = koszul g X Y Z x := by
  have c1 : mvfderiv I (gpair g Y Z) x (X x) =
      g.g x (cov Y x (X x)) (Z x) + g.g x (Y x) (cov Z x (X x)) := h.2 X Y Z x hX hY hZ
  have c2 : mvfderiv I (gpair g Z X) x (Y x) =
      g.g x (cov Z x (Y x)) (X x) + g.g x (Z x) (cov X x (Y x)) := h.2 Y Z X x hY hZ hX
  have c3 : mvfderiv I (gpair g X Y) x (Z x) =
      g.g x (cov X x (Z x)) (Y x) + g.g x (X x) (cov Y x (Z x)) := h.2 Z X Y x hZ hX hY
  have tXZ := ((CovariantDerivative.torsion_eq_zero_iff cov).1 h.1) hX hZ
  have tYX := ((CovariantDerivative.torsion_eq_zero_iff cov).1 h.1) hY hX
  have tZY := ((CovariantDerivative.torsion_eq_zero_iff cov).1 h.1) hZ hY
  have p1 := congrArg (fun v => g.g x v (Y x)) tXZ
  have p2 := congrArg (fun v => g.g x v (Z x)) tYX
  have p3 := congrArg (fun v => g.g x v (X x)) tZY
  simp only [map_sub, sub_apply] at p1 p2 p3
  have s1 := g.symm x (Y x) (cov Z x (X x))
  have s2 := g.symm x (Z x) (cov X x (Y x))
  have s3 := g.symm x (X x) (cov Y x (Z x))
  have s4 := g.symm x (Y x) (mlieBracket I X Z x)
  have s5 := g.symm x (Z x) (mlieBracket I Y X x)
  have s6 := g.symm x (X x) (mlieBracket I Z Y x)
  unfold koszul
  rw [c1, c2, c3]
  linarith

/-- **Uniqueness of the Levi-Civita connection**: two torsion-free connections compatible with `g` agree on
every vector field differentiable at a point. -/
theorem leviCivita_unique {cov cov' : Connection I M} (h : cov.IsLeviCivita g) (h' : cov'.IsLeviCivita g)
    {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) : cov Y x = cov' Y x := by
  apply injective_eval_mdifferentiableAt_vectorField I _ x
  ext X hX
  apply eq_of_g_eq_fields g
  intro Z hZ
  rw [koszul_of_isLeviCivita g h hX hY hZ, koszul_of_isLeviCivita g h' hX hY hZ]

/-- **Existence and uniqueness of the Levi-Civita connection of a Lorentzian metric** . -/
theorem leviCivita_exists_unique_proved (g : NondegMetric I M) :
    (∃ cov : Connection I M, cov.IsLeviCivita g) ∧
      ∀ cov cov' : Connection I M, cov.IsLeviCivita g → cov'.IsLeviCivita g →
        ∀ (Y : Π x : M, TangentSpace I x) (x : M), MDiffAt (T% Y) x → cov Y x = cov' Y x :=
  ⟨⟨leviCivita g, leviCivita_torsion g, leviCivita_compat g⟩,
    fun _ _ h h' _ _ hY => leviCivita_unique g h h' hY⟩
end Lightlike
