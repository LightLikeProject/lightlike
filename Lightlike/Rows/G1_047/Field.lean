import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.Basic
import Lightlike.Rows.G1_047.Pointwise

/-!
# Abelian-Higgs vortices: the field computation `curl J = 2 Im(conj D₁φ D₂φ) - e B |φ|²`

Row G1-047 (CO24). Data on the plane `ℝ × ℝ`: potentials `A₁ A₂ : ℝ × ℝ → ℝ`, Higgs field
`φ : ℝ × ℝ → ℂ`, all `C²`. Partial derivatives `d₁ f = ∂f(·)(1,0)`, `d₂ f = ∂f(·)(0,1)`.
Covariant derivative `D_j φ = ∂_j φ - i e A_j φ`, current `J_j = Im(φ̄ D_j φ)`, `B = ∂₁A₂ - ∂₂A₁`.
The main result `curl_current` is the hypothesis `hK` of `Pointwise.lean`.
Supporting lemmas; no catalogue entry.
-/

namespace Lightlike.Rows.G1_047

open Complex ComplexConjugate

/-- Partial derivative in the first variable. -/
noncomputable def d₁ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F)
    (x : ℝ × ℝ) : F := fderiv ℝ f x (1, 0)

/-- Partial derivative in the second variable. -/
noncomputable def d₂ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F)
    (x : ℝ × ℝ) : F := fderiv ℝ f x (0, 1)

/-- The covariant derivative `D φ = ∂φ - i e A φ` for a given partial derivative `dφ`. -/
noncomputable def covD (e : ℝ) (A : ℝ × ℝ → ℝ) (dφ φ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  dφ x - I * e * A x * φ x

/-- The current component `J = Im(φ̄ D φ)`. -/
noncomputable def current (e : ℝ) (A : ℝ × ℝ → ℝ) (dφ φ : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℝ :=
  (conj (φ x) * covD e A dφ φ x).im

/-- The magnetic field `B = ∂₁A₂ - ∂₂A₁`. -/
noncomputable def magField (A₁ A₂ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := d₁ A₂ x - d₂ A₁ x

/-- Product rule for the current: the derivative in direction `v`. -/
theorem fderiv_current (e : ℝ) {A : ℝ × ℝ → ℝ} {dφ φ : ℝ × ℝ → ℂ} {x : ℝ × ℝ}
    {A' : ℝ × ℝ →L[ℝ] ℝ} {φ' dφ' : ℝ × ℝ →L[ℝ] ℂ}
    (hA : HasFDerivAt A A' x) (hφ : HasFDerivAt φ φ' x) (hdφ : HasFDerivAt dφ dφ' x)
    (v : ℝ × ℝ) :
    fderiv ℝ (current e A dφ φ) x v =
      (conj (φ' v) * covD e A dφ φ x).im +
        (conj (φ x) * (dφ' v - I * e * (A' v * φ x + A x * φ' v))).im := by
  have h1 : HasFDerivAt (fun y => conj (φ y)) (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘L φ') x :=
    hφ.star
  have h2 : HasFDerivAt (fun y => (A y : ℂ)) (Complex.ofRealCLM ∘L A') x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hA
  have h3 : HasFDerivAt (fun y => covD e A dφ φ y)
      (dφ' - (I * e) • ((A x : ℂ) • φ' + (φ x) • (Complex.ofRealCLM ∘L A'))) x := by
    have h := hdφ.sub ((h2.mul hφ).const_mul ((I : ℂ) * e))
    convert h using 1
    funext y
    simp only [covD, Pi.sub_apply, Pi.mul_apply]
    ring
  have h4 := h1.mul h3
  have h5 := Complex.imCLM.hasFDerivAt.comp x h4
  have h7 : HasFDerivAt (current e A dφ φ) _ x := h5
  rw [h7.fderiv]
  simp
  ring

/-- The derivative of a partial derivative of a `C²` function, as second derivative. -/
theorem hasFDerivAt_partial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ 2 f) (w : ℝ × ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fun y => fderiv ℝ f y w)
      ((ContinuousLinearMap.apply ℝ F w) ∘L fderiv ℝ (fderiv ℝ f) x) x := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) x := (h1.differentiable (by norm_num)) x
  exact (ContinuousLinearMap.apply ℝ F w).hasFDerivAt.comp x h2.hasFDerivAt

/-- **The curl of the current.** For `C²` data,
`∂₁ J₂ - ∂₂ J₁ = 2 Im(conj(D₁φ) D₂φ) - e B |φ|²`. -/
theorem curl_current (e : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hA₁ : ContDiff ℝ 2 A₁) (hA₂ : ContDiff ℝ 2 A₂) (hφ : ContDiff ℝ 2 φ) (x : ℝ × ℝ) :
    d₁ (current e A₂ (d₂ φ) φ) x - d₂ (current e A₁ (d₁ φ) φ) x =
      2 * (conj (covD e A₁ (d₁ φ) φ x) * covD e A₂ (d₂ φ) φ x).im
        - e * magField A₁ A₂ x * ‖φ x‖ ^ 2 := by
  have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by norm_num)) x
  have hA₁d : DifferentiableAt ℝ A₁ x := (hA₁.differentiable (by norm_num)) x
  have hA₂d : DifferentiableAt ℝ A₂ x := (hA₂.differentiable (by norm_num)) x
  have hsymm := (hφ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  have e1 := fderiv_current e hA₂d.hasFDerivAt hφd.hasFDerivAt
    (hasFDerivAt_partial hφ (0, 1) x) (1, 0)
  have e2 := fderiv_current e hA₁d.hasFDerivAt hφd.hasFDerivAt
    (hasFDerivAt_partial hφ (1, 0) x) (0, 1)
  unfold d₁ d₂ magField
  rw [e1, e2]
  have hs := hsymm (1, 0) (0, 1)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs]
  simp only [covD, d₁, d₂, Complex.sq_norm, Complex.normSq_apply, Complex.mul_im, Complex.mul_re,
    Complex.sub_im, Complex.sub_re, Complex.add_im, Complex.add_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The hypothesis `hK` of `Pointwise.lean`, with `K = ∂₁J₂ - ∂₂J₁`, for `C²` data. -/
theorem hK_of_contDiff (e : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hA₁ : ContDiff ℝ 2 A₁) (hA₂ : ContDiff ℝ 2 A₂) (hφ : ContDiff ℝ 2 φ) (x : ℝ × ℝ) :
    2 * (conj (covD e A₁ (d₁ φ) φ x) * covD e A₂ (d₂ φ) φ x).im =
      (d₁ (current e A₂ (d₂ φ) φ) x - d₂ (current e A₁ (d₁ φ) φ) x) +
        e * magField A₁ A₂ x * ‖φ x‖ ^ 2 := by
  rw [curl_current e hA₁ hA₂ hφ x]
  ring

end Lightlike.Rows.G1_047
