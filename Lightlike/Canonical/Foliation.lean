import Lightlike.Spacetime.Hypersurface

/-!
# The ADM data of a foliation: lapse, normal, shift, induced metric and extrinsic curvature (chart-free)

A **foliation** of a manifold `M` with a metric `g` (a `NondegMetric`, in applications Lorentzian) is given by a time
function `τ : M → ℝ`, smooth with a timelike gradient; the leaves are the level sets `Σ_t = {τ = t}`. From `(g, τ)`, and a
time vector field `T` with `dτ(T) = 1`, this file builds the ADM data at every point, without charts:

* `timeGrad g τ`: the gradient `∇τ = (dτ)♯`;
* `lapse g τ`: `N = (−g(∇τ, ∇τ))^{−1/2}` (Gourgoulhon (3.5)); `unitNormal g τ`: `n = −N ∇τ` (3.4);
  `normalEvolution g τ`: `m = N n` (3.8);
* `shift g τ T`: `β = T − m` (4.28);
* `spatialProj g τ`: the orthogonal projector `v ↦ v + g(n, v) n` onto the tangent space of the leaf;
  `spatialMetric g τ`: the induced metric `γ = g + n♭ ⊗ n♭` extended to `T_xM` (2.68)–(2.69);
* `extrinsicCurvature cov g τ`: `K(u, v) = −g(P u, ∇_{P v} n)` (2.43), extended by the projector `P` (2.70), with the
  second fundamental form `Hypersurface.secondFF` of `Lightlike/Spacetime/Hypersurface.lean`.

Results: `N > 0` (3.6), `g(n, n) = −1`, `n♭ = −N dτ` (3.7), `dτ(m) = 1`, the normal is a unit normal of the leaves in the
sense of `Hypersurface.IsUnitNormal` (given its smoothness), the shift is tangent to the leaves (4.30), `T = N n + β` (4.31),
`g(T, T) = −N² + g(β, β)` (4.32); `γ` vanishes on `n` and equals `g` on tangent vectors (2.68); `K` vanishes on `n` and is
symmetric on tangent vectors for the Levi-Civita connection.

**Source (read at the cited locations).** E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*,
arXiv:gr-qc/0703035: eq. (2.43) (p. 24), eqs. (2.68)–(2.70) (pp. 30-31), Sec. 3.2.2 eqs. (3.1)–(3.3) (p. 40), Sec. 3.3.1
eqs. (3.4)–(3.7) (p. 41), Sec. 3.3.2 eqs. (3.8), (3.10) (p. 42), Sec. 2.3.4 (p. 23), Sec. 4.2 eqs. (4.28)–(4.32) (p. 56).

**Limits.** The leaves are not given a manifold structure (as in `Hypersurface.lean`), so `γ` and `K` are bilinear forms on
`T_xM` that vanish on the normal, Gourgoulhon's "four-dimensional point of view" (p. 30). The smoothness of the unit normal
is a hypothesis of `isUnitNormal`. Global hyperbolicity is not used: every time function with a timelike gradient gives the
data. The chart form of the data (`g_00 = −N² + β_iβ^i`, `g_0i = β_i`, `g_ij = γ_ij` in coordinates adapted to the foliation)
is not in this file.
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]

section Defs

variable (g : NondegMetric 𝓘(ℝ, E) M) (τ : M → ℝ)

/-- The differential `dτ` at `x`, as a linear form on `T_xM`. -/
abbrev dTime (x : M) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) τ x

/-- The gradient `∇τ = (dτ)♯` of the time function: `g(∇τ, v) = dτ(v)`. -/
def timeGrad (x : M) : TangentSpace 𝓘(ℝ, E) x :=
  Lightlike.sharp g x (dTime τ x)

/-- **A time function** for `g`: a smooth function whose gradient is timelike at every point, so that its level sets
`Σ_t = {τ = t}` are spacelike leaves covering `M` (Gourgoulhon, Sec. 3.2.2, eqs. (3.1)–(3.3); a timelike gradient never
vanishes, so `τ` is regular). -/
structure IsTimeFunction : Prop where
  smooth : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ τ
  timelike : ∀ x, g.g x (timeGrad g τ x) (timeGrad g τ x) < 0

/-- **The lapse function** `N = (−g(∇τ, ∇τ))^{−1/2}` (Gourgoulhon (3.5)). -/
def lapse (x : M) : ℝ := (Real.sqrt (-(g.g x (timeGrad g τ x) (timeGrad g τ x))))⁻¹

/-- **The unit normal** `n = −N ∇τ` to the leaves (Gourgoulhon (3.4)), future directed when `τ` increases to the
future. -/
def unitNormal (x : M) : TangentSpace 𝓘(ℝ, E) x := (-(lapse g τ x)) • timeGrad g τ x

/-- **The normal evolution vector** `m = N n` (Gourgoulhon (3.8)). -/
def normalEvolution (x : M) : TangentSpace 𝓘(ℝ, E) x := lapse g τ x • unitNormal g τ x

/-- **The shift vector** `β = T − m` of a time vector field `T` (Gourgoulhon (4.28), with `T = ∂_t`). -/
def shift (T : Π x : M, TangentSpace 𝓘(ℝ, E) x) (x : M) : TangentSpace 𝓘(ℝ, E) x :=
  T x - normalEvolution g τ x

/-- The orthogonal projector `P v = v + g(n, v) n` onto the tangent space of the leaf (Gourgoulhon's `γ⃗`, (2.69)). -/
def spatialProj (x : M) (v : TangentSpace 𝓘(ℝ, E) x) : TangentSpace 𝓘(ℝ, E) x :=
  v + g.g x (unitNormal g τ x) v • unitNormal g τ x

/-- **The induced metric** of the leaf, extended to `T_xM`: `γ(u, v) = g(u, v) + g(n, u) g(n, v)`, that is
`γ = g + n♭ ⊗ n♭` (Gourgoulhon (2.68)). -/
def spatialMetric (x : M) (u v : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  g.g x u v + g.g x (unitNormal g τ x) u * g.g x (unitNormal g τ x) v

/-- **The extrinsic curvature** of the leaves, extended to `T_xM` by the projector: `K(u, v) = −g(P u, ∇_{P v} n)`
(Gourgoulhon (2.43) and (2.70)), in terms of the second fundamental form `K_lib(v, w) = g(∇_v n, w)` of
`Hypersurface.secondFF`. -/
def extrinsicCurvature (cov : Connection 𝓘(ℝ, E) M) (x : M) (u v : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  -Hypersurface.secondFF cov g (unitNormal g τ) x (spatialProj g τ x v) (spatialProj g τ x u)

end Defs

variable {g : NondegMetric 𝓘(ℝ, E) M} {τ : M → ℝ}

omit [T2Space M] in
/-- `g(∇τ, v) = dτ(v)`. -/
theorem g_timeGrad (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    g.g x (timeGrad g τ x) v = dTime τ x v :=
  Lightlike.g_sharp g x _ v

omit [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] in
/-- **The lapse is positive** (Gourgoulhon (3.6)). -/
theorem lapse_pos (h : IsTimeFunction g τ) (x : M) : 0 < lapse g τ x :=
  inv_pos.2 (Real.sqrt_pos.2 (neg_pos.2 (h.timelike x)))

omit [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] in
/-- `N² · (−g(∇τ, ∇τ)) = 1`. -/
theorem lapse_sq_mul (h : IsTimeFunction g τ) (x : M) :
    lapse g τ x ^ 2 * (-(g.g x (timeGrad g τ x) (timeGrad g τ x))) = 1 := by
  have hpos : 0 < -(g.g x (timeGrad g τ x) (timeGrad g τ x)) := neg_pos.2 (h.timelike x)
  unfold lapse
  rw [inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- **`n♭ = −N dτ`** (Gourgoulhon (3.7)): `g(n, v) = −N dτ(v)`. -/
theorem g_unitNormal (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    g.g x (unitNormal g τ x) v = -(lapse g τ x) * dTime τ x v := by
  simp [unitNormal, g_timeGrad]

/-- **The normal is a unit timelike vector**: `g(n, n) = −1`. -/
theorem g_unitNormal_self (h : IsTimeFunction g τ) (x : M) :
    g.g x (unitNormal g τ x) (unitNormal g τ x) = -1 := by
  have h2 := lapse_sq_mul h x
  simp only [unitNormal, map_smul, _root_.smul_apply, smul_eq_mul]
  linear_combination (-1 : ℝ) * h2

/-- `dτ(n) = 1/N`. -/
theorem dTime_unitNormal (h : IsTimeFunction g τ) (x : M) :
    dTime τ x (unitNormal g τ x) = (lapse g τ x)⁻¹ := by
  have h2 := lapse_sq_mul h x
  have hN := (lapse_pos h x).ne'
  have : dTime τ x (unitNormal g τ x) =
      -(lapse g τ x) * g.g x (timeGrad g τ x) (timeGrad g τ x) := by
    rw [unitNormal, map_smul, ← g_timeGrad (g := g) x (timeGrad g τ x), smul_eq_mul]
  rw [this]
  field_simp
  linear_combination h2

/-- **The normal evolution vector carries the leaves to the next ones**: `dτ(m) = 1` (Gourgoulhon (3.10)). -/
theorem dTime_normalEvolution (h : IsTimeFunction g τ) (x : M) :
    dTime τ x (normalEvolution g τ x) = 1 := by
  simp only [normalEvolution, map_smul, smul_eq_mul, dTime_unitNormal h]
  exact mul_inv_cancel₀ (lapse_pos h x).ne'

/-- **A vector is tangent to the leaf iff it is orthogonal to the normal**: `dτ(v) = 0 ↔ g(n, v) = 0`. -/
theorem dTime_eq_zero_iff (h : IsTimeFunction g τ) (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    dTime τ x v = 0 ↔ g.g x (unitNormal g τ x) v = 0 := by
  rw [g_unitNormal]
  have hN := (lapse_pos h x).ne'
  constructor
  · intro hv; rw [hv, mul_zero]
  · intro hv
    rcases mul_eq_zero.1 hv with h0 | h0
    · exact absurd (neg_eq_zero.1 h0) hN
    · exact h0

/-- **The unit normal of a time function is a unit normal of its leaves** in the sense of `Hypersurface.IsUnitNormal`,
with `ε = −1`, given that it is smooth near `x₀`. -/
theorem isUnitNormal (h : IsTimeFunction g τ) {x₀ : M} (hs : SmoothNear (unitNormal g τ) x₀) :
    Hypersurface.IsUnitNormal g τ (unitNormal g τ) (-1) x₀ where
  eps := Or.inr rfl
  phi := Eventually.of_forall fun _ => h.smooth.contMDiffAt
  smooth := hs
  norm := Eventually.of_forall fun y => g_unitNormal_self h y
  ker := Eventually.of_forall fun y v => dTime_eq_zero_iff h y v

/-! ### The shift -/

/-- **The shift is tangent to the leaves** (Gourgoulhon (4.29), (4.30)): if `dτ(T) = 1` then `dτ(β) = 0`. -/
theorem dTime_shift (h : IsTimeFunction g τ) {T : Π x : M, TangentSpace 𝓘(ℝ, E) x} {x : M}
    (hT : dTime τ x (T x) = 1) :
    dTime τ x (shift g τ T x) = 0 := by
  simp [shift, hT, dTime_normalEvolution h]

omit [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] in
/-- **The 3+1 decomposition of the time vector** `T = N n + β` (Gourgoulhon (4.31)). -/
theorem time_eq_lapse_normal_add_shift (T : Π x : M, TangentSpace 𝓘(ℝ, E) x) (x : M) :
    T x = lapse g τ x • unitNormal g τ x + shift g τ T x := by
  simp [shift, normalEvolution]

/-- **The norm of the time vector** `g(T, T) = −N² + g(β, β)` (Gourgoulhon (4.32)). -/
theorem g_time_time (h : IsTimeFunction g τ) {T : Π x : M, TangentSpace 𝓘(ℝ, E) x} {x : M}
    (hT : dTime τ x (T x) = 1) :
    g.g x (T x) (T x) = -(lapse g τ x) ^ 2 + g.g x (shift g τ T x) (shift g τ T x) := by
  have hb : g.g x (unitNormal g τ x) (shift g τ T x) = 0 := (dTime_eq_zero_iff h x _).1 (dTime_shift h hT)
  have hb' : g.g x (shift g τ T x) (unitNormal g τ x) = 0 := by rw [g.symm]; exact hb
  have hnn := g_unitNormal_self h x
  conv_lhs => rw [time_eq_lapse_normal_add_shift (g := g) (τ := τ) T x]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, _root_.smul_apply, smul_eq_mul,
    hb, hb', hnn]
  ring

/-! ### The induced metric and the projector -/

/-- The projector maps into the tangent space of the leaf: `dτ(P v) = 0`. -/
theorem dTime_spatialProj (h : IsTimeFunction g τ) (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    dTime τ x (spatialProj g τ x v) = 0 := by
  have hN := (lapse_pos h x).ne'
  simp only [spatialProj, map_add, map_smul, smul_eq_mul, dTime_unitNormal h, g_unitNormal]
  field_simp
  ring

/-- The projector fixes tangent vectors. -/
theorem spatialProj_of_tangent (h : IsTimeFunction g τ) {x : M} {v : TangentSpace 𝓘(ℝ, E) x}
    (hv : dTime τ x v = 0) : spatialProj g τ x v = v := by
  simp [spatialProj, (dTime_eq_zero_iff h x v).1 hv]

/-- The projector kills the normal: `P n = 0`. -/
theorem spatialProj_unitNormal (h : IsTimeFunction g τ) (x : M) :
    spatialProj g τ x (unitNormal g τ x) = 0 := by
  simp only [spatialProj, g_unitNormal_self h x, neg_smul, one_smul, add_neg_cancel]

/-- **The induced metric vanishes on the normal** (Gourgoulhon (2.68)): `γ(n, v) = 0`. -/
theorem spatialMetric_unitNormal (h : IsTimeFunction g τ) (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    spatialMetric g τ x (unitNormal g τ x) v = 0 := by
  simp only [spatialMetric, g_unitNormal_self h x]
  ring

/-- **The induced metric is `g` on tangent vectors** (Gourgoulhon (2.68)). -/
theorem spatialMetric_of_tangent (h : IsTimeFunction g τ) {x : M} {u v : TangentSpace 𝓘(ℝ, E) x}
    (hu : dTime τ x u = 0) :
    spatialMetric g τ x u v = g.g x u v := by
  simp [spatialMetric, (dTime_eq_zero_iff h x u).1 hu]

omit [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E] in
/-- The induced metric is symmetric. -/
theorem spatialMetric_symm (x : M) (u v : TangentSpace 𝓘(ℝ, E) x) :
    spatialMetric g τ x u v = spatialMetric g τ x v u := by
  simp only [spatialMetric, g.symm x u v]
  ring

/-- The induced metric is `g(P u, P v)`. -/
theorem spatialMetric_eq_proj (h : IsTimeFunction g τ) (x : M) (u v : TangentSpace 𝓘(ℝ, E) x) :
    spatialMetric g τ x u v = g.g x (spatialProj g τ x u) (spatialProj g τ x v) := by
  have hnn := g_unitNormal_self h x
  have hs := g.symm x u (unitNormal g τ x)
  have hs' := g.symm x v (unitNormal g τ x)
  simp only [spatialMetric, spatialProj, map_add, map_smul, ContinuousLinearMap.add_apply,
    _root_.smul_apply, smul_eq_mul, hnn, hs, hs']
  ring

/-! ### The extrinsic curvature -/

/-- **The extrinsic curvature vanishes on the normal**: `K(n, v) = K(v, n) = 0`. -/
theorem extrinsicCurvature_unitNormal_left (h : IsTimeFunction g τ) (cov : Connection 𝓘(ℝ, E) M) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) : extrinsicCurvature g τ cov x (unitNormal g τ x) v = 0 := by
  simp [extrinsicCurvature, Hypersurface.secondFF, spatialProj_unitNormal h x]

theorem extrinsicCurvature_unitNormal_right (h : IsTimeFunction g τ) (cov : Connection 𝓘(ℝ, E) M) (x : M)
    (u : TangentSpace 𝓘(ℝ, E) x) : extrinsicCurvature g τ cov x u (unitNormal g τ x) = 0 := by
  simp [extrinsicCurvature, Hypersurface.secondFF, spatialProj_unitNormal h x]

/-- **The extrinsic curvature is symmetric** for the Levi-Civita connection (Gourgoulhon, the Weingarten map is
self-adjoint, Sec. 2.3.4, p. 23; here through `Hypersurface.secondFF_symm_fields`), given that the unit normal is smooth near
the point. -/
theorem extrinsicCurvature_symm (h : IsTimeFunction g τ) {cov : Connection 𝓘(ℝ, E) M} (hc : cov.IsLeviCivita g)
    {x₀ : M} (hs : SmoothNear (unitNormal g τ) x₀) (u v : TangentSpace 𝓘(ℝ, E) x₀) :
    extrinsicCurvature g τ cov x₀ u v = extrinsicCurvature g τ cov x₀ v u := by
  have hn := isUnitNormal h hs
  obtain ⟨X, hXs, hXt, hX0⟩ := Hypersurface.exists_tangent_extension hn (spatialProj g τ x₀ u)
    (dTime_spatialProj h x₀ u)
  obtain ⟨Y, hYs, hYt, hY0⟩ := Hypersurface.exists_tangent_extension hn (spatialProj g τ x₀ v)
    (dTime_spatialProj h x₀ v)
  have := Hypersurface.secondFF_symm_fields hc hn hXs hYs hXt hYt
  rw [hX0, hY0] at this
  simp only [extrinsicCurvature]
  rw [this]

end Lightlike.Canonical
