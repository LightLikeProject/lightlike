import Mathlib
import Lightlike.Dirac.Flat

/-!
# Trust checks for the flat Dirac operator

* Non-vacuity: a concrete Clifford module on `ℝ¹`, namely `ℂ` with `e₀` acting as multiplication
  by `i` (`repC`), so `dirac_dirac` has a model.
* Wrong-sign control: for `f x = x₀²` the module gives `D² f = -2` while `Δ f = 2`, so the
  statement `D² = +Δ` (what the form `+‖·‖²` would give) fails; the sign `-Δ` is the right one.
-/

open CliffordAlgebra InnerProductSpace Laplacian

namespace Lightlike.Dirac

/-- The linear map `v ↦ v₀ • (z ↦ i z)` from `ℝ¹` to `ℂ →L[ℝ] ℂ`. -/
noncomputable def repLin : E 1 →ₗ[ℝ] (ℂ →L[ℝ] ℂ) :=
  ((EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ).toLinearMap).smulRight
    (ContinuousLinearMap.mul ℝ ℂ Complex.I)

/-- Clifford module on `ℂ` over `Cl(ℝ¹, -‖·‖²)`: `e₀` acts as multiplication by `i`. -/
noncomputable def repC : CliffordRep 1 ℂ :=
  CliffordAlgebra.lift (Qneg 1) ⟨repLin, by
    intro v
    ext w
    simp [repLin, Qneg_apply, EuclideanSpace.norm_sq_eq]
    ring_nf
    simp⟩

lemma gam_repC (w : ℂ) : gam repC 0 w = Complex.I * w := by
  simp [gam, repC, e, repLin]

/-- The test function `x ↦ x₀²` as a `ℂ`-valued function. -/
noncomputable def sqf : E 1 → ℂ := fun x => ((x 0 ^ 2 : ℝ) : ℂ)

lemma sqf_contDiff : ContDiff ℝ 2 sqf := by
  unfold sqf
  have : ContDiff ℝ 2 (fun x : E 1 => x 0 ^ 2) :=
    ((EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ).contDiff).pow 2
  exact Complex.ofRealCLM.contDiff.comp this

lemma laplacian_sqf (x : E 1) : (Δ sqf) x = 2 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis sqf (EuclideanSpace.basisFun (Fin 1) ℝ)]
  set P : E 1 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 1) with hP
  set L : E 1 →L[ℝ] ℂ := Complex.ofRealCLM.comp P with hL
  have h1 : ∀ y : E 1, HasFDerivAt sqf ((2 * y 0 : ℝ) • L) y := by
    intro y
    have h0 : HasFDerivAt (fun x : E 1 => x 0 ^ 2) ((2 * y 0 : ℝ) • P) y := by
      simpa [hP] using (P.hasFDerivAt (x := y)).pow 2
    have := Complex.ofRealCLM.hasFDerivAt.comp y h0
    have e1 : sqf = (Complex.ofRealCLM ∘ fun x : E 1 => x 0 ^ 2) := by
      funext z; simp [sqf]
    have e2 : ((2 * y 0 : ℝ) • L) = Complex.ofRealCLM.comp ((2 * y 0 : ℝ) • P) := by
      ext z; simp [hL]
    rw [e1, e2]
    exact this
  have h2 : fderiv ℝ sqf = fun y => (2 * y 0 : ℝ) • L := funext fun y => (h1 y).fderiv
  have h3 : HasFDerivAt (fun y : E 1 => (2 * y 0 : ℝ) • L) (((2 : ℝ) • P).smulRight L) x := by
    have := (P.hasFDerivAt (x := x)).const_mul 2 |>.smul_const L
    exact this
  simp only [iteratedFDeriv_two_apply, h2, h3.fderiv]
  simp [hP, hL]

/-- Non-vacuity of `dirac_dirac`: on the module `repC`, `D² (x ↦ x₀²) = -2`. -/
lemma dirac_dirac_sqf (x : E 1) : dirac repC (dirac repC sqf) x = -2 := by
  rw [dirac_dirac repC sqf_contDiff, laplacian_sqf]

/-- Wrong-sign control: `D² f = +Δ f` fails for `f x = x₀²` (`-2 ≠ 2`), so `D² = -Δ` is not
a sign convention that can be flipped silently. -/
lemma dirac_dirac_ne_laplacian (x : E 1) : dirac repC (dirac repC sqf) x ≠ (Δ sqf) x := by
  rw [dirac_dirac_sqf, laplacian_sqf]
  intro h
  have := congrArg Complex.re h
  norm_num at this

end Lightlike.Dirac
