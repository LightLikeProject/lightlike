module

public import Lightlike.Spacetime.Connection
public import Lightlike.Spacetime.Minkowski

/-!
# The flat connection of a normed space and Minkowski space as an Einstein solution

On a normed space `V` (the model space `𝓘(ℝ, V)`, tangent spaces identified with `V`), the flat
connection is `∇_v Y = DY(v)`. This file proves that it is a covariant derivative in Mathlib's sense
(`flat_isCov`), that it is torsion free, that it is compatible with a constant bilinear form, and that its
curvature vanishes. For the Minkowski metric of `ℝⁿ` this gives a Levi-Civita connection with
`Ric = 0`, hence a solution of the Einstein equations with `Λ = 0` (`minkowski_satisfiesEinstein`,
an Einstein solution).

**Limits.** Normed spaces and the constant metric only; nothing about other manifolds.
-/

@[expose] public section

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Differentiability of a vector field of a normed space (a section of its tangent bundle) at a point is
ordinary differentiability. -/
theorem mdiffAt_vf_iff (σ : Π y : V, TangentSpace 𝓘(ℝ, V) y) (x : V) :
    MDiffAt (T% (σ : Π y : V, TangentSpace 𝓘(ℝ, V) y)) x ↔ DifferentiableAt ℝ (σ : V → V) x := by
  refine (mdifferentiableAt_section (IB := 𝓘(ℝ, V)) (E := TangentSpace 𝓘(ℝ, V)) (F := V) (s := σ)).trans ?_
  have key : (fun b => (trivializationAt V (TangentSpace 𝓘(ℝ, V)) x (⟨b, σ b⟩ : TangentBundle 𝓘(ℝ, V) V)).2)
      = (σ : V → V) := by
    funext b
    exact congrArg Prod.snd (trivializationAt_model_space_apply (I := 𝓘(ℝ, V)) ⟨b, σ b⟩ x)
  rw [key]
  exact mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ) (E := V) (E' := V)

/-- The flat connection of a normed space: `∇_v Y = DY(v)`. -/
noncomputable def flatCovFun (σ : Π y : V, TangentSpace 𝓘(ℝ, V) y) (x : V) : TangentSpace 𝓘(ℝ, V) x →L[ℝ] TangentSpace 𝓘(ℝ, V) x :=
  fderiv ℝ (σ : V → V) x

/-- The Leibniz rule of the flat connection, in terms of plain functions. -/
theorem flat_leibniz (σ : V → V) (g : V → ℝ) (x : V) (h1 : DifferentiableAt ℝ σ x)
    (h2 : DifferentiableAt ℝ g x) :
    fderiv ℝ (g • σ) x = g x • fderiv ℝ σ x
      + (show V →L[ℝ] ℝ from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) g x).smulRight (σ x) := by
  rw [fderiv_smul h2 h1]
  have hm : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) g x = fderiv ℝ g x := mfderiv_eq_fderiv
  rw [show (show V →L[ℝ] ℝ from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) g x) = fderiv ℝ g x from hm]

/-- The flat connection `∇_v Y = DY(v)` is a covariant derivative. -/
theorem flat_isCov : IsCovariantDerivativeOn V (flatCovFun (V := V)) Set.univ where
  add {σ σ'} {x} hσ hσ' _ := by
    have h1 := (mdiffAt_vf_iff σ x).1 hσ
    have h2 := (mdiffAt_vf_iff σ' x).1 hσ'
    show fderiv ℝ ((σ : V → V) + σ') x = _
    exact fderiv_add h1 h2
  leibniz {σ g} {x} hσ hg _ := by
    have h1 := (mdiffAt_vf_iff σ x).1 hσ
    have h2 : DifferentiableAt ℝ g x := mdifferentiableAt_iff_differentiableAt.1 hg
    exact flat_leibniz (σ : V → V) g x h1 h2

/-- On the tangent bundle of a normed space the extension of a tangent vector is the constant field. -/
theorem extend_flat (x : V) (v : TangentSpace 𝓘(ℝ, V) x) (y : V) :
    (FiberBundle.extend V v y : V) = (v : V) := by
  unfold FiberBundle.extend
  set t := trivializationAt V (TangentSpace 𝓘(ℝ, V)) x with ht
  have h1 : t ⟨x, v⟩ = (x, v) := trivializationAt_model_space_apply (I := 𝓘(ℝ, V)) ⟨x, v⟩ x
  have h2 : t ⟨y, v⟩ = (y, v) := trivializationAt_model_space_apply (I := 𝓘(ℝ, V)) ⟨y, v⟩ x
  have hb : y ∈ t.baseSet := by
    simp [ht, TangentBundle.trivializationAt_baseSet]
  have := t.symm_apply_apply_mk hb (v : TangentSpace 𝓘(ℝ, V) y)
  rw [h2] at this
  rw [h1]
  exact this

/-- The flat connection of a normed space as a bundled covariant derivative on its tangent bundle. -/
def flatConnection (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Connection 𝓘(ℝ, V) V :=
  ⟨flatCovFun, flat_isCov⟩

/-- The flat connection is `DY(v)`. -/
theorem flatConnection_apply (σ : Π y : V, TangentSpace 𝓘(ℝ, V) y) (x : V) :
    flatConnection V σ x = fderiv ℝ (σ : V → V) x := rfl

/-- The Lie bracket of plain functions on a normed space, within the whole space. -/
theorem lieBracketWithin_univ_apply (X Y : V → V) (x : V) :
    lieBracketWithin ℝ X Y univ x = fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x) := by
  rw [lieBracketWithin_univ]; rfl

/-- The Lie bracket of vector fields of a normed space is `DW(V) - DV(W)`. -/
theorem mlieBracket_flat (X Y : Π y : V, TangentSpace 𝓘(ℝ, V) y) (x : V) :
    (mlieBracket 𝓘(ℝ, V) X Y x : V) = fderiv ℝ (Y : V → V) x (X x) - fderiv ℝ (X : V → V) x (Y x) := by
  have := congrFun (mlieBracketWithin_eq_lieBracketWithin (V := X) (W := Y) (s := univ)) x
  rw [mlieBracketWithin_univ] at this
  exact this.trans (lieBracketWithin_univ_apply X Y x)

section Curvature

variable [FiniteDimensional ℝ V] [CompleteSpace V]

/-- The flat connection is torsion free. -/
theorem flat_torsion : (flatConnection V).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x _ _
  exact (mlieBracket_flat X Y x).symm

omit [FiniteDimensional ℝ V] [CompleteSpace V] in
/-- The flat connection of the extension of a vector vanishes. -/
theorem flat_extend (x : V) (w : TangentSpace 𝓘(ℝ, V) x) (y : V) :
    flatConnection V (FiberBundle.extend V w) y = 0 := by
  have h : (fun y => (FiberBundle.extend V w y : V)) = fun _ => (w : V) := funext (extend_flat x w)
  show fderiv ℝ (fun y => (FiberBundle.extend V w y : V)) y = 0
  rw [h]
  exact congrFun (fderiv_const (𝕜 := ℝ) (w : V)) y

omit [FiniteDimensional ℝ V] [CompleteSpace V] in
/-- **The flat connection has zero curvature.** -/
theorem flat_curvatureAt (x : V) (X₀ Y₀ Z₀ : TangentSpace 𝓘(ℝ, V) x) :
    (flatConnection V).curvatureAt x X₀ Y₀ Z₀ = 0 := by
  unfold Connection.curvatureAt
  have hA : ∀ A : TangentSpace 𝓘(ℝ, V) x, flatConnection V
      (fun y => flatConnection V (FiberBundle.extend V Z₀) y (FiberBundle.extend V A y)) x = 0 := by
    intro A
    show fderiv ℝ (fun y => flatConnection V (FiberBundle.extend V Z₀) y (FiberBundle.extend V A y)) x = 0
    have : (fun y => flatConnection V (FiberBundle.extend V Z₀) y (FiberBundle.extend V A y))
        = fun _ => (0 : V) := funext fun y => by rw [flat_extend]; rfl
    rw [this]
    exact congrFun (fderiv_const (𝕜 := ℝ) (0 : V)) x
  dsimp only
  rw [hA Y₀, hA X₀, flat_extend]
  simp

end Curvature

/-- The flat connection is compatible with a constant bilinear form `B`: `X B(σ, τ) = B(∇_X σ, τ) + B(σ, ∇_X τ)`. -/
theorem flat_compat (B : V →L[ℝ] V →L[ℝ] ℝ)
    (σ τ X : Π y : V, TangentSpace 𝓘(ℝ, V) y) (x : V)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    (show ℝ from mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (fun y => B (σ y) (τ y)) x (X x))
      = B (flatConnection V σ x (X x)) (τ x) + B (σ x) (flatConnection V τ x (X x)) := by
  have h1 := (mdiffAt_vf_iff σ x).1 hσ
  have h2 := (mdiffAt_vf_iff τ x).1 hτ
  have hc : HasFDerivAt (fun y => B ((σ : V → V) y)) (B.comp (fderiv ℝ (σ : V → V) x)) x :=
    B.hasFDerivAt.comp x h1.hasFDerivAt
  have hf := hc.clm_apply h2.hasFDerivAt
  have hm := hf.hasMFDerivAt.mfderiv
  show (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, ℝ) (fun y => B (σ y) (τ y)) x) (X x) = _
  rw [hm]
  exact add_comm _ _

/-- **The Minkowski metric is compatible with the flat connection.** -/
theorem flat_isMetricCompatible (n : ℕ) :
    (flatConnection (Fin n → ℝ)).IsMetricCompatible (minkowskiMetric n) := by
  intro X σ τ x _ hσ hτ
  exact flat_compat (minkowskiForm n) σ τ X x hσ hτ

/-- **Minkowski space solves the Einstein equations.** The flat connection is the Levi-Civita
connection of the Minkowski metric and its Ricci and scalar curvatures vanish, so the Einstein
equations hold with `Λ = 0`. -/
theorem minkowski_satisfiesEinstein_flat (n : ℕ) :
    (minkowskiMetric n).SatisfiesEinstein (flatConnection (Fin n → ℝ)) 0 := by
  refine ⟨⟨flat_torsion, flat_isMetricCompatible n⟩, fun x v w => ?_⟩
  have hric : ∀ (y : Fin n → ℝ) (v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) y),
      (flatConnection (Fin n → ℝ)).ricciAt y v w = 0 := fun y v w => by
    unfold Connection.ricciAt
    exact Finset.sum_eq_zero fun i _ =>
      (congrArg ((Module.finBasis ℝ (Fin n → ℝ)).coord i) (flat_curvatureAt y _ v w)).trans (map_zero _)
  have hs : (flatConnection (Fin n → ℝ)).scalarCurvatureAt (minkowskiMetric n) x = 0 := by
    unfold Connection.scalarCurvatureAt
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      (congrArg (fun r => _ * r) (hric x _ _)).trans (mul_zero _)
  rw [hric, hs]; simp

/-- **Minkowski space is a vacuum solution**:
the Minkowski metric of `ℝⁿ` satisfies the Einstein equations with `Λ = 0` for some connection. -/
theorem minkowski_satisfiesEinstein_proved (n : ℕ) :
    ∃ cov : Connection 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ),
      (minkowskiMetric n).SatisfiesEinstein cov 0 :=
  ⟨flatConnection (Fin n → ℝ), minkowski_satisfiesEinstein_flat n⟩

end Lightlike
