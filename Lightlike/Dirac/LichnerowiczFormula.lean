import Mathlib
import Lightlike.Dirac.Covariant
import Lightlike.Dirac.SecondOrder
import Lightlike.Dirac.Lichnerowicz

/-!
# The Lichnerowicz formula in a frame, with the curvature identity as hypothesis

Combining `diracConn_diracConn_hessian` with `clifford_double_sum` gives
`D² f = -∑ᵢ ∇²f(eᵢ,eᵢ) + ½ ∑ᵢⱼ γᵢγⱼ (∇²f(eᵢ,eⱼ) - ∇²f(eⱼ,eᵢ))`. If the antisymmetric part of the
frame Hessian is the action of the spinor curvature (the Ricci identity, taken as a hypothesis),
then `D² f = -∑ᵢ ∇²f(eᵢ,eᵢ) + (s/4) f` with `s = ∑ᵢⱼ Rᵢⱼⱼᵢ`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Clifford relations for the operators `γᵢ` on `V`, in the form used by `curvatureTerm_eq`. -/
lemma gam_relations (ρ : CliffordRep n V) (j k : Fin n) :
    gam ρ j * gam ρ k + gam ρ k * gam ρ j = (if j = k then (-2 : ℝ) else 0) • (1 : V →L[ℝ] V) := by
  ext w
  by_cases h : j = k
  · subst h
    simp only [add_apply, mul_apply_eq_comp, ite_true, smul_apply, one_apply_eq_self, gam_sq]
    module
  · simp [h, gam_anticomm ρ h w]

/-- `D² f = -∑ᵢ aᵢᵢ + ½ ∑ᵢⱼ γᵢγⱼ (aᵢⱼ - aⱼᵢ)` for the frame Hessian `a`. -/
theorem diracConn_diracConn_antisymm (ρ : CliffordRep n V)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hω : ∀ x i a b, ω x i a b = -ω x i b a) {f : E n → V} (x : E n)
    (hf : ∀ j, DifferentiableAt ℝ (fun y => nabla ρ ω j f y) x) :
    diracConn ρ ω (diracConn ρ ω f) x =
      -∑ i, (nabla ρ ω i (fun y => nabla ρ ω i f y) x - ∑ k, (ω x i i k) • nabla ρ ω k f x) +
      (1 / 2 : ℝ) • ∑ i, ∑ j, gam ρ i (gam ρ j
        ((nabla ρ ω i (fun y => nabla ρ ω j f y) x - ∑ k, (ω x i j k) • nabla ρ ω k f x) -
         (nabla ρ ω j (fun y => nabla ρ ω i f y) x - ∑ k, (ω x j i k) • nabla ρ ω k f x))) := by
  rw [diracConn_diracConn_hessian ρ ω hω x hf]
  exact clifford_double_sum ρ
    (fun i j => nabla ρ ω i (fun y => nabla ρ ω j f y) x - ∑ k, (ω x i j k) • nabla ρ ω k f x)

/-- The Ricci identity for the frame Hessian of `f` at `x`: its antisymmetric part is the action of
the spinor curvature `¼ ∑ Rᵢⱼₖₗ γₖγₗ` of `R` on `f x`. A hypothesis of `lichnerowicz_frame`, not
derived there; `ricci_identity` proves the corresponding statement for the frame connection. -/
def FrameRicciIdentity (ρ : CliffordRep n V) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (f : E n → V) (x : E n) (R : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ i j,
    (nabla ρ ω i (fun y => nabla ρ ω j f y) x - ∑ k, (ω x i j k) • nabla ρ ω k f x) -
      (nabla ρ ω j (fun y => nabla ρ ω i f y) x - ∑ k, (ω x j i k) • nabla ρ ω k f x) =
    spinorCurvature (gam ρ) R i j (f x)

/-- **Lichnerowicz formula in a frame (Ricci identity as hypothesis).**  If the antisymmetric part
of the frame Hessian of `f` at `x` is the action of the spinor curvature `¼ ∑ Rᵢⱼₖₗ γₖγₗ`, and `R`
has the symmetries of a Riemann tensor, then `D² f x = -∑ᵢ ∇²f(eᵢ,eᵢ) + (s/4) f x`. -/
theorem lichnerowicz_frame (ρ : CliffordRep n V)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hω : ∀ x i a b, ω x i a b = -ω x i b a) {f : E n → V} (x : E n)
    (hf : ∀ j, DifferentiableAt ℝ (fun y => nabla ρ ω j f y) x)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hR1 : ∀ i j k l, R i j k l = - R j i k l)
    (hP : ∀ i j k l, R i j k l = R k l i j)
    (hB : ∀ i j k l, R i j k l + R j k i l + R k i j l = 0)
    (hRicci : FrameRicciIdentity ρ ω f x R) :
    diracConn ρ ω (diracConn ρ ω f) x =
      -∑ i, (nabla ρ ω i (fun y => nabla ρ ω i f y) x - ∑ k, (ω x i i k) • nabla ρ ω k f x) +
      ((1 / 4 : ℝ) * ∑ i, ∑ j, R i j j i) • f x := by
  unfold FrameRicciIdentity at hRicci
  rw [diracConn_diracConn_antisymm ρ ω hω x hf]
  simp only [hRicci]
  have h := congrArg (fun L => L (f x))
    (curvatureTerm_eq (gam ρ) R (gam_relations ρ) hR1 hP hB)
  simp only [curvatureTerm, smul_apply, sum_apply, mul_apply_eq_comp, one_apply_eq_self] at h
  rw [← h]

end Lightlike.Dirac
