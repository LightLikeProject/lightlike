import Mathlib
import Lightlike.Dirac.SpinDeriv
import Lightlike.Dirac.Lichnerowicz

/-!
# The Ricci identity for the spin connection in a general frame

Let `F x a ∈ ℝⁿ` (`a : Fin n`) be a frame field (not necessarily constant), `ω x a` the skew
connection matrices, and `∇ₐ f = ∂_{Fₐ} f + spinForm (ωₐ) f`. For `f` of class `C²` the second
derivative is symmetric, so the commutator `[∇ₐ, ∇_b] f` has no second-order part:

`[∇ₐ, ∇_b] f = ∑_c cₐbc ∂_{F_c} f + spinForm (∂ₐω_b - ∂_bωₐ + ω_b ωₐ - ωₐ ω_b) f`

where `cₐbc` are the structure functions `[Fₐ, F_b] = ∑ c cₐbc F_c`. If the connection is torsion-free
(`ωₐbc - ω_baс = cₐbc`, with `∇ₐ F_b = ∑_c ωₐbc F_c`), the Hessian
`∇²f(Fₐ,F_b) = ∇ₐ∇_b f - ∑_k ωₐbk ∇ₖ f` has antisymmetric part `spinorCurvature` of the structure
equation curvature `Rₐb = ∂ₐω_b - ∂_bωₐ + ω_b ωₐ - ωₐ ω_b - ∑_c cₐbc ω_c`
(`ricci_identity`). This replaces the hypothesis `hRicci` of `lichnerowicz_frame`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The spinor covariant derivative along the frame vector `F x a`:
`∇ₐ f = ∂_{F x a} f + spinForm (ω x a) (f x)`. -/
noncomputable def nablaF (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n) (f : E n → V) (x : E n) : V :=
  fderiv ℝ f x (F x a) + spinForm ρ (ω x a) (f x)

/-- The second covariant derivative `∇ₐ ∇_b f` in a general frame (product rule). -/
theorem nablaF_nablaF (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) (hF : ∀ a, DifferentiableAt ℝ (fun y => F y a) x)
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x) (a b : Fin n) :
    nablaF ρ F ω a (fun y => nablaF ρ F ω b f y) x =
      fderiv ℝ (fderiv ℝ f) x (F x a) (F x b) +
      fderiv ℝ f x (fderiv ℝ (fun y => F y b) x (F x a)) +
      spinForm ρ (fun k l => fderiv ℝ (fun y => ω y b k l) x (F x a)) (f x) +
      spinForm ρ (ω x b) (fderiv ℝ f x (F x a)) +
      spinForm ρ (ω x a) (nablaF ρ F ω b f x) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt le_rfl
  have h1 := hf2.hasFDerivAt.clm_apply (hF b).hasFDerivAt
  have h2 := hasFDerivAt_spinForm ρ (M := fun y => ω y b) (g := f) (hω b) hfd
  have key : fderiv ℝ (fun y => nablaF ρ F ω b f y) x =
      fderiv ℝ (fun y => fderiv ℝ f y (F y b)) x +
        fderiv ℝ (fun y => spinForm ρ (ω y b) (f y)) x :=
    (h1.differentiableAt.hasFDerivAt.add h2.differentiableAt.hasFDerivAt).fderiv
  have e : nablaF ρ F ω a (fun y => nablaF ρ F ω b f y) x =
      fderiv ℝ (fun y => nablaF ρ F ω b f y) x (F x a) +
        spinForm ρ (ω x a) (nablaF ρ F ω b f x) := rfl
  rw [e, key, add_apply, fderiv_clm_apply hf2 (hF b), fderiv_spinForm_apply ρ (hω b) hfd]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  abel

end Lightlike.Dirac
