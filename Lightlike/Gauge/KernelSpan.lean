import Lightlike.Gauge.GaugeFlow

/-!
# The kernel of the form on the constraint surface is spanned by the first-class Hamiltonian fields

Wipf's lectures (arXiv:hep-th/9312078), Section 5.2, Theorem 4: for first-class constraints the two-form induced on the
constraint surface is maximally degenerate and its kernel is spanned by the Hamiltonian vector fields of the constraints.
On Physlib's finite-dimensional flat phase space `X × X` (`FiniteDimensional ℝ X`), at a point: let `K` be the span of the
fields `X_{φ_b}` and `T = K^Ω` the tangent space of the surface, `{v | dφ_b(v) = 0 ∀ b}` (`mem_tangentSub_iff`). If the fields
are tangent (first class at the point), then the radical `T ∩ T^Ω` of the form on `T` is exactly `K` (`radical_eq`).

Pointwise linear algebra: no manifold structure, and the regularity (independence of the `dφ_b`) is not needed for this
equality; with it, `dim K = m` and the radical has dimension `m` (the source's "maximally degenerate").
-/

open InnerProductSpace
open ClassicalMechanics

namespace Lightlike.Gauge

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {m : ℕ}

/-- The span `K` of the Hamiltonian fields of the constraints at a point. -/
noncomputable def hamSpan (φ : Fin m → X → X → ℝ) (p q : X) : Submodule ℝ (X × X) :=
  Submodule.span ℝ (Set.range fun b => hamField (φ b) p q)

/-- The tangent space `T = K^Ω` of the constraint surface at a point. -/
noncomputable def tangentSub (φ : Fin m → X → X → ℝ) (p q : X) : Submodule ℝ (X × X) :=
  LinearMap.BilinForm.orthogonal (gradForm : LinearMap.BilinForm ℝ (X × X)) (hamSpan φ p q)

/-- **`T` is the common kernel of the differentials**: `v ∈ K^Ω` iff `dφ_b(v) = 0` for all `b`. -/
theorem mem_tangentSub_iff (φ : Fin m → X → X → ℝ) (p q : X) (v : X × X) :
    v ∈ tangentSub φ p q ↔ ∀ b, pairing (phaseGrad (φ b) p q) v = 0 := by
  rw [tangentSub, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h b
    have := h (hamField (φ b) p q) (Submodule.subset_span ⟨b, rfl⟩)
    rw [← gradForm_hamField]
    exact this
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      show gradForm _ v = 0
      rw [gradForm_hamField]; exact h b
    | zero => show gradForm 0 v = 0; simp
    | add y z _ _ hy hz =>
      have hy' : gradForm y v = 0 := hy
      have hz' : gradForm z v = 0 := hz
      show gradForm (y + z) v = 0
      rw [map_add, LinearMap.add_apply, hy', hz', add_zero]
    | smul c y _ hy =>
      have hy' : gradForm y v = 0 := hy
      show gradForm (c • y) v = 0
      rw [map_smul, LinearMap.smul_apply, hy', smul_zero]

/-- If the constraints are first class at the point, their Hamiltonian fields are tangent: `K ≤ T`. -/
theorem hamSpan_le_tangentSub (φ : Fin m → X → X → ℝ) (p q : X)
    (hfirst : ∀ a b, pairing (phaseGrad (φ b) p q) (hamField (φ a) p q) = 0) :
    hamSpan φ p q ≤ tangentSub φ p q := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  exact (mem_tangentSub_iff φ p q _).mpr fun b => hfirst a b

/-- **Wipf's Theorem 4 at a point**: for first-class constraints on the finite-dimensional flat phase space, the radical of
the symplectic form on the tangent space `T` of the constraint surface is the span `K` of the Hamiltonian fields. -/
theorem radical_eq [FiniteDimensional ℝ X] (φ : Fin m → X → X → ℝ) (p q : X)
    (hfirst : ∀ a b, pairing (phaseGrad (φ b) p q) (hamField (φ a) p q) = 0) :
    {u | u ∈ tangentSub φ p q ∧ ∀ v ∈ tangentSub φ p q, (gradForm : LinearMap.BilinForm ℝ (X × X)) u v = 0} =
      (hamSpan φ p q : Set (X × X)) := by
  have hσ := isSymplecticForm_gradForm (X := X)
  have hr : (gradForm : LinearMap.BilinForm ℝ (X × X)).IsRefl := LinearMap.BilinForm.IsAlt.isRefl hσ.alt
  have hKT := hamSpan_le_tangentSub φ p q hfirst
  ext u
  constructor
  · rintro ⟨huT, hu⟩
    have hmem : u ∈ LinearMap.BilinForm.orthogonal (gradForm : LinearMap.BilinForm ℝ (X × X))
        (tangentSub φ p q) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      exact hr _ _ (hu v hv)
    rw [tangentSub, LinearMap.BilinForm.orthogonal_orthogonal hσ.nondeg hr] at hmem
    exact hmem
  · intro huK
    refine ⟨hKT huK, fun v hv => ?_⟩
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) u huK
    exact this

end Lightlike.Gauge
