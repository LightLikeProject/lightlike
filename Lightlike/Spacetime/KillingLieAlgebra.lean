import Lightlike.Spacetime.KillingAlgebra
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# The Lie algebra of Killing fields (GE12)

`killingSubmodule g` is the real vector space of smooth vector fields `X` on `M` with `L_X g = 0` everywhere
(`IsKillingNear g X x` at every point). The Lie bracket of vector fields, `VectorField.mlieBracket`, makes it a real
Lie algebra: `Lightlike.instLieRingKilling` and `Lightlike.instLieAlgebraKilling`.

* `smoothNear_add`, `smoothNear_smul`: sums and real multiples of fields smooth near `x` are smooth near `x`;
* `killingSubmodule`: the vector subspace (closed under sums and real multiples: `IsKillingNear.add`, `.smul`);
* the bracket is closed by `IsKillingNear.lieBracket`, antisymmetric, bilinear and satisfies the Jacobi identity
  (`mlieBracket_jacobi`).

**Limits.** The fields are smooth (`C^∞`) vector fields defined on all of `M`; the infinite dimension of the space of
all smooth fields is not an issue, but finite-dimensionality of the Killing algebra is not proved here (it is for
Minkowski space in `KillingMinkowski.lean`). The Lie bracket sign is Mathlib's, `[V, W] = DW(V) - DV(W)`.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]

/-- The sum of two fields smooth near `x` is smooth near `x`. -/
theorem smoothNear_add {X Y : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hX : SmoothNear X x) (hY : SmoothNear Y x) : SmoothNear (X + Y) x := by
  filter_upwards [hX, hY] with y hXy hYy
  exact ContMDiffAt.add_section hXy hYy

/-- A real multiple of a field smooth near `x` is smooth near `x`. -/
theorem smoothNear_smul {X : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M} (c : ℝ)
    (hX : SmoothNear X x) : SmoothNear (c • X) x := by
  filter_upwards [hX] with y hXy
  exact ContMDiffAt.const_smul_section hXy

variable (g : NondegMetric 𝓘(ℝ, E) M)

/-- **The Killing fields of `g`**: the smooth vector fields `X` on `M` with `L_X g = 0` near every point, as a
real vector subspace of the vector fields. -/
def killingSubmodule : Submodule ℝ (Π y : M, TangentSpace 𝓘(ℝ, E) y) where
  carrier := {X | (∀ x, SmoothNear X x) ∧ ∀ x, IsKillingNear g X x}
  add_mem' := fun {X Y} hX hY =>
    ⟨fun x => smoothNear_add (hX.1 x) (hY.1 x), fun x => IsKillingNear.add (hX.1 x) (hY.1 x) (hX.2 x) (hY.2 x)⟩
  zero_mem' := ⟨fun x => by
      filter_upwards with y
      exact contMDiffAt_zeroSection ℝ _, fun x => IsKillingNear.zero x⟩
  smul_mem' := fun c {X} hX =>
    ⟨fun x => smoothNear_smul c (hX.1 x), fun x => IsKillingNear.smul c (hX.1 x) (hX.2 x)⟩

/-- The bracket of two Killing fields. -/
instance : Bracket (killingSubmodule g) (killingSubmodule g) :=
  ⟨fun X Y => ⟨mlieBracket 𝓘(ℝ, E) (X : Π y : M, TangentSpace 𝓘(ℝ, E) y) Y,
    fun x => smoothNear_mlieBracket (X.2.1 x) (Y.2.1 x),
    fun x => IsKillingNear.lieBracket (X.2.1 x) (Y.2.1 x) (X.2.2 x) (Y.2.2 x)⟩⟩

theorem killing_bracket_val (X Y : killingSubmodule g) :
    ((⁅X, Y⁆ : killingSubmodule g) : Π y : M, TangentSpace 𝓘(ℝ, E) y) =
      mlieBracket 𝓘(ℝ, E) (X : Π y : M, TangentSpace 𝓘(ℝ, E) y) Y := rfl

/-- **The Killing fields of a metric form a real Lie algebra** (a Lie ring under the Lie bracket of vector fields). -/
instance instLieRingKilling : LieRing (killingSubmodule g) where
  add_lie X Y Z := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [killing_bracket_val, Submodule.coe_add, Pi.add_apply]
    exact mlieBracket_add_left (mdiffAt_of_smoothNear (X.2.1 x)) (mdiffAt_of_smoothNear (Y.2.1 x))
  lie_add X Y Z := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [killing_bracket_val, Submodule.coe_add, Pi.add_apply]
    exact mlieBracket_add_right (mdiffAt_of_smoothNear (Y.2.1 x)) (mdiffAt_of_smoothNear (Z.2.1 x))
  lie_self X := by
    refine Subtype.ext ?_
    simp only [killing_bracket_val]
    exact mlieBracket_self
  leibniz_lie X Y Z := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [killing_bracket_val, Submodule.coe_add, Pi.add_apply]
    have j := mlieBracket_jacobi (X.2.1 x) (Y.2.1 x) (Z.2.1 x)
    rw [j]
    abel

/-- The Killing fields form a Lie algebra over `ℝ`. -/
instance instLieAlgebraKilling : LieAlgebra ℝ (killingSubmodule g) where
  lie_smul c X Y := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [killing_bracket_val, Submodule.coe_smul, Pi.smul_apply]
    exact mlieBracket_const_smul_right (mdiffAt_of_smoothNear (Y.2.1 x))

end Lightlike
