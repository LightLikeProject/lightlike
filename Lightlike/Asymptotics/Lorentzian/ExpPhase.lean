import Lightlike.Oscillatory.StationaryPhase

/-!
# Stationary phase for `e^{λ S}` with `Re S ≤ 0`

The Lorentzian vertex amplitude is an integral of an amplitude against `e^{λ S}`, where the
action `S` has real part at most zero. Writing `S = i φ` turns this into the oscillatory form
`e^{iλφ}` with `Im φ = - Re S ≥ 0`, to which the stationary phase theorem of
`Lightlike.Oscillatory.StationaryPhase` applies. This file states the result in the `e^{λS}`
form, for a finite set of critical points with nondegenerate Hessian, in any dimension, with the
Hessian entering as `-∂²S`.
-/

open Complex Filter Asymptotics Lightlike.Oscillatory
open scoped Real ContDiff Topology

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- Multiplying a smooth phase by a constant multiplies its Hessian by the constant. -/
theorem hessMat_const_mul {S : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S) (c : ℂ)
    (x : Fin n → ℝ) : hessMat (fun y => c * S y) x = c • hessMat S x := by
  ext i j
  have h1 : ∀ y, coordDeriv (fun z => c * S z) i y = c * coordDeriv S i y := fun y =>
    coordDeriv_const_mul (hS.differentiable (by simp) y) c i
  have hd : DifferentiableAt ℝ (fun y => coordDeriv S i y) x :=
    (contDiff_coordDeriv hS i).differentiable (by simp) x
  simp only [hessMat, h1]
  rw [coordDeriv_const_mul hd]
  simp [hessMat]

/-- **Stationary phase for `e^{τ S}`.** Let `S` and the amplitude `a` be smooth, `a` compactly
supported, `Re S ≤ 0` on the support of `a`, and let the points of the support with `Re S = 0`
and `dS = 0` be a finite set `K` of points where `-∂²S` is invertible. Then
`∫ a e^{τ S}` equals the sum over `K` of `e^{τ S(x₀)} (2π/τ)^{n/2} (det (-∂²S(x₀)))^{-1/2} a(x₀)`
up to `O(τ^{-n/2-1})`. -/
theorem expPhase_asymptotics {S a : (Fin n → ℝ) → ℂ} (hS : ContDiff ℝ ∞ S)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hRe : ∀ x ∈ tsupport a, (S x).re ≤ 0) (K : Finset (Fin n → ℝ))
    (hK : ∀ x ∈ tsupport a, ((S x).re = 0 ∧ fderiv ℝ S x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport a) (hnd : ∀ x ∈ K, (-hessMat S x).det ≠ 0) :
    (fun τ : ℝ => (∫ x, a x * cexp (τ * S x)) - ∑ x₀ ∈ K, cexp (τ * S x₀) *
        ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-hessMat S x₀) * a x₀)
      =O[atTop] fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
  have hφ : ContDiff ℝ ∞ (fun x => -I * S x) := contDiff_const.mul hS
  have hder : ∀ x, fderiv ℝ (fun y => -I * S y) x = -I • fderiv ℝ S x := fun x => by
    rw [fderiv_const_mul (hS.differentiable (by simp) x)]
  have hI : ∀ τ : ℝ, ∀ x, cexp (I * τ * (-I * S x)) = cexp (τ * S x) := fun τ x => by
    congr 1
    have h : I * (τ : ℂ) * (-I * S x) = -(I * I) * (τ * S x) := by ring
    rw [h, I_mul_I]; ring
  have key := stationary_phase_pi (φ := fun x => -I * S x) hφ ha hc
    (fun x hx => by simpa using hRe x hx) K
    (fun x hx => by
      rw [← hK x hx, hder]
      have him : (-I * S x).im = -(S x).re := by simp
      rw [him]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨by linarith, ?_⟩
        have h3 : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr I_ne_zero
        exact (smul_eq_zero.mp h2).resolve_left h3
      · rintro ⟨h1, h2⟩
        refine ⟨by linarith, ?_⟩
        rw [h2]; ext v; simp)
    hKs (fun x hx => by
      have := hnd x hx
      rwa [show -I • hessMat (fun y => -I * S y) x = -hessMat S x by
        rw [hessMat_const_mul hS, smul_smul]; simp])
  refine key.congr' (Eventually.of_forall fun τ => ?_) EventuallyEq.rfl
  simp only [hI]
  congr 1
  refine Finset.sum_congr rfl fun x₀ _ => ?_
  rw [hessMat_const_mul hS, smul_smul]
  simp

/-! ### Trust checks -/

/-- The Gaussian action `S(x) = -x²/2` on `ℝ¹`. -/
noncomputable def gaussAction : (Fin 1 → ℝ) → ℂ := fun x => -((x 0 : ℂ) ^ 2) / 2

/-- Its real part is nonpositive, as the theorem requires. -/
theorem gaussAction_re_nonpos (x : Fin 1 → ℝ) : (gaussAction x).re ≤ 0 := by
  simp only [gaussAction, ← Complex.ofReal_pow, Complex.div_ofNat_re, Complex.neg_re,
    Complex.ofReal_re]
  nlinarith [sq_nonneg (x 0)]

/-- Control: the opposite sign `+x²/2` violates `Re S ≤ 0` at `x = 1`, so the hypothesis is
not vacuous and the theorem does not apply to a growing exponential. -/
theorem wrongSign_re_pos : ¬ ((fun x : Fin 1 → ℝ => ((x 0 : ℂ) ^ 2) / 2) (fun _ => 1)).re ≤ 0 := by
  norm_num

/-- The critical set of the Gaussian action at `x = 0`: `Re S = 0` forces `x = 0`. -/
theorem gaussAction_re_eq_zero {x : Fin 1 → ℝ} (h : (gaussAction x).re = 0) : x 0 = 0 := by
  simp only [gaussAction, ← Complex.ofReal_pow, Complex.div_ofNat_re, Complex.neg_re,
    Complex.ofReal_re] at h
  nlinarith [sq_nonneg (x 0)]

end Lightlike.Asymptotics.Lorentzian
