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

/-- `∇ᵢ` commutes with finite sums of functions differentiable at `x`. -/
theorem nabla_sum (ρ : CliffordRep n V) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) {ι : Type*} (s : Finset ι) (g : ι → E n → V) (x : E n)
    (hg : ∀ j ∈ s, DifferentiableAt ℝ (g j) x) :
    nabla ρ ω i (fun y => ∑ j ∈ s, g j y) x = ∑ j ∈ s, nabla ρ ω i (g j) x := by
  have hd : fderiv ℝ (fun y => ∑ j ∈ s, g j y) x = ∑ j ∈ s, fderiv ℝ (g j) x := by
    exact (HasFDerivAt.fun_sum (fun j hj => (hg j hj).hasFDerivAt)).fderiv
  unfold nabla
  rw [hd, sum_apply, map_sum, Finset.sum_add_distrib]

/-- `D²` in a frame: `D² f = ∑ᵢⱼ γᵢγⱼ ∇ᵢ∇ⱼ f + ∑ᵢⱼₖ (ωᵢ)ⱼₖ γᵢγₖ ∇ⱼ f`, the second sum being the
connection on the vector index of `∇ f`. Needs each `∇ⱼ f` differentiable at `x`. -/
theorem diracConn_diracConn (ρ : CliffordRep n V)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hω : ∀ x i a b, ω x i a b = -ω x i b a) {f : E n → V} (x : E n)
    (hf : ∀ j, DifferentiableAt ℝ (fun y => nabla ρ ω j f y) x) :
    diracConn ρ ω (diracConn ρ ω f) x =
      ∑ i, ∑ j, gam ρ i (gam ρ j (nabla ρ ω i (fun y => nabla ρ ω j f y) x)) +
      ∑ i, ∑ j, ∑ k, (ω x i j k) • gam ρ i (gam ρ k (nabla ρ ω j f x)) := by
  unfold diracConn
  have h1 : ∀ i, nabla ρ ω i (fun y => ∑ j, gam ρ j (nabla ρ ω j f y)) x =
      ∑ j, (gam ρ j (nabla ρ ω i (fun y => nabla ρ ω j f y) x) +
        ∑ k, (ω x i j k) • gam ρ k (nabla ρ ω j f x)) := by
    intro i
    rw [nabla_sum ρ ω i Finset.univ (fun j y => gam ρ j (nabla ρ ω j f y)) x
      (fun j _ => (gam ρ j).differentiableAt.comp x (hf j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact nabla_gam ρ ω hω i j x (hf j)
  simp only [h1, map_sum, map_add, Finset.sum_add_distrib, map_smul]

end Lightlike.Dirac
