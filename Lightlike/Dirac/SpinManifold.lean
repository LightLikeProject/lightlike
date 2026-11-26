import Mathlib
import Lightlike.Dirac.SpinStructure
import Lightlike.Dirac.SpinConnection
import Lightlike.Dirac.RicciIdentity
import Lightlike.Spacetime.LeviCivita

/-!
# The Dirac operator and the rough Laplacian on a manifold with a spin structure

For a spin structure `S` (atlas form, `SpinStructure`) of a metric `g` on `M` and a Clifford module
`ρ` on `V`, a *spinor field* is a family of local representations `ψ i : M → V`, one per frame,
related on overlaps by the spin lifts, `ψ i x = ρ (lift i j x) (ψ j x)`.  In the frame `i` the
spin connection has the coefficients of the Levi-Civita connection in that frame,
`ω x a b c = g(∇_{Fₐ} F_b, F_c)`, and

* `∇ₐ φ = ∂_{Fₐ} φ + ¼ ∑ ωₐ,ₖₗ γₖγₗ φ`,
* `D φ = ∑ₐ γₐ ∇ₐ φ`,
* `∇*∇ φ = -∑ₐ (∇ₐ∇ₐ φ - ∑ₖ ωₐ,ₐₖ ∇ₖ φ)`.

These are the manifold counterparts of `Lightlike.Dirac.nablaF`, `diracF` and `hessF`, which
treat a frame on `ℝⁿ`.  Only the atlas form of a spin structure is used; its equivalence with the
principal `Spin(n)`-bundle definition is not proved.  The independence of the frame is not part of
this file.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, §4 (the Dirac operator), no
  equation number is claimed.
-/

open Bundle Manifold CliffordAlgebra
open scoped Manifold ContDiff

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- A **spinor field** for the spin structure `S` and the Clifford module `ρ`: local
representations `ψ i : M → V`, one per frame, with `ψ i x = ρ (lift i j x) (ψ j x)` on overlaps. -/
structure SpinorField {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*}
    (S : SpinStructure g ι) (ρ : CliffordRep n V) where
  /-- The representation of the spinor field in the frame `i`. -/
  rep : ι → M → V
  transform : ∀ i j x, x ∈ S.dom i → x ∈ S.dom j → rep i x = ρ (S.lift i j x) (rep j x)

section Operators

variable {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*} (S : SpinStructure g ι)

/-- The coefficients of the Levi-Civita connection in the frame `i` at `x`:
`ω x a b c = g(∇_{Fₐ} F_b, F_c)`, so that `∇_{Fₐ} F_b = ∑ₖ ωₐ,bk F_k` in an orthonormal frame. -/
noncomputable def SpinStructure.connForm (i : ι) (x : M) (a : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun b c => g.g x (leviCivita g (S.frame i b) x (S.frame i a x)) (S.frame i c x)

variable (ρ : CliffordRep n V)

/-- The spinor covariant derivative along the frame vector `Fₐ`:
`∇ₐ φ = ∂_{Fₐ} φ + ¼ ∑ ωₐ,ₖₗ γₖγₗ φ`, for a local representation `φ : M → V` in the frame `i`. -/
noncomputable def SpinStructure.nabla (i : ι) (a : Fin n) (φ : M → V) (x : M) : V :=
  let d : V := mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, V) φ x (S.frame i a x)
  d + spinForm ρ (S.connForm i x a) (φ x)

/-- The **Dirac operator** in the frame `i`: `D φ = ∑ₐ γₐ ∇ₐ φ`. -/
noncomputable def SpinStructure.dirac (i : ι) (φ : M → V) (x : M) : V :=
  ∑ a, gam ρ a (S.nabla ρ i a φ x)

/-- The **rough Laplacian** `∇*∇` in the frame `i`:
`∇*∇ φ = -∑ₐ (∇ₐ∇ₐ φ - ∑ₖ ωₐ,ₐₖ ∇ₖ φ)`. -/
noncomputable def SpinStructure.roughLaplacian (i : ι) (φ : M → V) (x : M) : V :=
  -∑ a, (S.nabla ρ i a (fun y => S.nabla ρ i a φ y) x -
    ∑ k, S.connForm i x a a k • S.nabla ρ i k φ x)

end Operators

end Lightlike.Dirac
