import Mathlib
import Lightlike.Dirac.SpinConnection

/-!
# The spinor covariant derivative in an orthonormal frame

On `ℝⁿ` with a field of skew matrices `ω x` (the Levi-Civita connection forms in an orthonormal
frame, `ωᵢ = ω x i` being the form evaluated on the `i`-th frame vector), the spinor covariant
derivative of a `V`-valued function `f` is `∇ᵢ f = ∂ᵢ f + spinForm (ωᵢ) f`, and the Dirac operator
is `D f = ∑ᵢ γᵢ ∇ᵢ f`. Clifford multiplication is parallel up to the connection on the vector index:
`∇ᵢ (γₖ g) = γₖ ∇ᵢ g + ∑ⱼ (ωᵢ)ₖⱼ γⱼ g`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); definitions only, no equation
  number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The spinor covariant derivative `∇ᵢ f = ∂ᵢ f + ¼ ∑ₖₗ (ωᵢ)ₖₗ γₖγₗ f` in the direction of the
`i`-th frame vector, for connection forms `ω : ℝⁿ → Fin n → Matrix`. -/
noncomputable def nabla (ρ : CliffordRep n V) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (f : E n → V) (x : E n) : V :=
  fderiv ℝ f x (e i) + spinForm ρ (ω x i) (f x)

/-- The Dirac operator `D f = ∑ᵢ γᵢ ∇ᵢ f` of the spin connection with forms `ω`. -/
noncomputable def diracConn (ρ : CliffordRep n V) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (f : E n → V) : E n → V :=
  fun x => ∑ i, gam ρ i (nabla ρ ω i f x)

/-- Clifford multiplication is parallel up to the vector-index connection:
`∇ᵢ (γₖ g) = γₖ ∇ᵢ g + ∑ⱼ (ωᵢ)ₖⱼ γⱼ g`, for skew `ωᵢ`. -/
theorem nabla_gam (ρ : CliffordRep n V) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hω : ∀ x i a b, ω x i a b = -ω x i b a) (i k : Fin n) {g : E n → V} (x : E n)
    (hg : DifferentiableAt ℝ g x) :
    nabla ρ ω i (fun y => gam ρ k (g y)) x =
      gam ρ k (nabla ρ ω i g x) + ∑ j, (ω x i k j) • gam ρ j (g x) := by
  have hd : fderiv ℝ (fun y => gam ρ k (g y)) x (e i) = gam ρ k (fderiv ℝ g x (e i)) := by
    rw [show (fun y => gam ρ k (g y)) = gam ρ k ∘ g from rfl,
      ((gam ρ k).hasFDerivAt.comp x hg.hasFDerivAt).fderiv]
    rfl
  have hc := congrArg (fun L => L (g x)) (spinForm_comm ρ (hω x i) k)
  simp only [sub_apply, mul_apply_eq_comp, sum_apply, smul_apply] at hc
  unfold nabla
  rw [hd, map_add, ← hc]
  abel

end Lightlike.Dirac
