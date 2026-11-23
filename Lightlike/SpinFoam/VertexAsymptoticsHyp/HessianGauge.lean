import Lightlike.SpinFoam.VertexAsymptoticsHyp.HessianSecondOrder
import Lightlike.Oscillatory.GaussFourier

/-!
# Gauge directions are Hessian null vectors (SF10 P2, Tier 1)

If a `C²` phase `φ : ℝⁿ → ℂ` is invariant under translation by `t • v` near `x`, then the Hessian
annihilates `v`: `hessMat φ x *ᵥ cvec v = 0`, hence `det hessMat φ x = 0` for `v ≠ 0`.  This explains
why the vertex action must be gauge fixed before `det(-H) ≠ 0` can hold: an ungauged action has
a degenerate Hessian at every critical point, and the kernel criterion `hker` is consistent only for
the gauge-fixed chart.
-/

open Filter Topology Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Oscillatory

variable {n : ℕ}

/-- If `φ` is differentiable at `y` and constant along the line `y + t v`, its derivative in the
direction `v` vanishes at `y`. -/
theorem fderiv_apply_eq_zero_of_invariant {φ : (Fin n → ℝ) → ℂ} {y v : Fin n → ℝ}
    (hd : DifferentiableAt ℝ φ y) (hinv : ∀ t : ℝ, φ (y + t • v) = φ y) :
    fderiv ℝ φ y v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hc : HasDerivAt (fun t : ℝ => φ (y + t • v)) (fderiv ℝ φ y v) 0 := by
    have h0 : y + (0 : ℝ) • v = y := by simp
    have h : HasFDerivAt φ (fderiv ℝ φ y) (y + (0 : ℝ) • v) := by
      rw [h0]; exact hd.hasFDerivAt
    exact h.comp_hasDerivAt (0 : ℝ) hl
  have hconst : (fun t : ℝ => φ (y + t • v)) = fun _ => φ y := funext hinv
  rw [hconst] at hc
  exact hc.unique (hasDerivAt_const _ _)

/-- **Gauge directions lie in the Hessian kernel.** If `φ` is `C²` at `x` and invariant under the
translations `y ↦ y + t • v` for all `y` near `x`, then `H(x) v = 0`. -/
theorem hessMat_mulVec_eq_zero_of_invariant {φ : (Fin n → ℝ) → ℂ} {x v : Fin n → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x)
    (hinv : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, φ (y + t • v) = φ y) :
    hessMat φ x *ᵥ cvec v = 0 := by
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
  have hzero : (fun y => fderiv ℝ φ y v) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
    filter_upwards [hev, hinv] with y hy hy'
    exact fderiv_apply_eq_zero_of_invariant
      (hy.differentiableAt (by norm_num)) hy'
  have hd1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := hφ.fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := hd1.differentiableAt (by norm_num)
  have hf : fderiv ℝ (fun y => fderiv ℝ φ y v) x = 0 := by
    rw [hzero.fderiv_eq]; simp
  rw [fderiv_clm_apply hd (differentiableAt_const _)] at hf
  have hD : ∀ w : Fin n → ℝ, fderiv ℝ (fderiv ℝ φ) x w v = 0 := by
    intro w
    have := congrArg (fun L => L w) hf
    simpa using this
  have hsym := hessMat_isSymm_local hφ
  ext i
  have h1 : (hessMat φ x *ᵥ cvec v) i = ∑ j, hessMat φ x j i * (v j : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, cvec]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hsym.apply i j]
  have h2 : ∑ j, hessMat φ x j i * (v j : ℂ)
      = fderiv ℝ (fderiv ℝ φ) x (Pi.single i 1) (∑ j, v j • (Pi.single j 1 : Fin n → ℝ)) := by
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hessMat_eq_local hφ j i, Complex.real_smul, mul_comm]
  rw [h1, h2, ← pi_eq_sum_single_smul v]
  simpa using hD (Pi.single i 1)

/-- A phase invariant under translation along a nonzero direction has a degenerate Hessian. -/
theorem det_hessMat_eq_zero_of_invariant {φ : (Fin n → ℝ) → ℂ} {x v : Fin n → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (hv : v ≠ 0)
    (hinv : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, φ (y + t • v) = φ y) :
    (hessMat φ x).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨cvec v, ?_, hessMat_mulVec_eq_zero_of_invariant hφ hinv⟩
  intro h
  apply hv
  ext i
  have := congrFun h i
  simpa [cvec] using this

/-- The same for `-H`, the matrix whose determinant appears in the stationary-phase formula: a
gauge direction is a nonzero real vector in `ker Re(-H) ∩ ker Im(-H)`, so `hker` fails for an
ungauged action. -/
theorem det_neg_hessMat_eq_zero_of_invariant {φ : (Fin n → ℝ) → ℂ} {x v : Fin n → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (hv : v ≠ 0)
    (hinv : ∀ᶠ y in 𝓝 x, ∀ t : ℝ, φ (y + t • v) = φ y) :
    (-hessMat φ x).det = 0 := by
  rw [Matrix.det_neg, det_hessMat_eq_zero_of_invariant hφ hv hinv, mul_zero]

end Lightlike.Asymptotics.Lorentzian
