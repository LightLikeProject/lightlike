import Lightlike.Lorentz.SL2RPlancherel.LadderCasimir
import Lightlike.Lorentz.SL2RPlancherel.KTypePlancherel

/-!
# The ladder images of a radial function

For `G` smooth, the `k`-fold ladder image of the radial function `G ∘ cosh` (type `(0, 0)`) under the raising ladder
`ladUp k 0` (type `(k, 0)`, equivalently by the symmetry `inv` the type `(0, k)`) is `sinh^k ξ · G^{(k)}(cosh ξ)`
(`ladUp_profile`). So the profile `profile k G` is the function whose `L²(sinh ξ dξ)`-norm is the left side of
`norm_sq_ktype_eq_sph`, and it is the base `(0, r)` of the recursion on the left index in the type `(l, r)`.
-/

open Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The profile `ξ ↦ sinh^k ξ · G^{(k)}(cosh ξ)`: the `k`-fold ladder image of `G ∘ cosh`. -/
def profile (k : ℕ) (G : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ((Real.sinh ξ ^ k : ℝ) : ℂ) * iteratedDeriv k G (Real.cosh ξ)

/-- **One ladder step on the profile**: `ladUp k 0 (profile k G) = profile (k+1) G` on `ξ > 0`. -/
theorem ladUp_profile (k : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) {ξ : ℝ} (hξ : 0 < ξ) :
    ladUp (k : ℝ) 0 (profile k G) ξ = profile (k + 1) G ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hd : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G (Real.cosh ξ)) (Real.cosh ξ) := by
    rw [iteratedDeriv_succ]
    exact ((contDiff_iteratedDeriv_infty hG k).differentiable (by simp) _).hasDerivAt
  have hc : HasDerivAt (fun y : ℝ => iteratedDeriv k G (Real.cosh y))
      (Real.sinh ξ • iteratedDeriv (k + 1) G (Real.cosh ξ)) ξ := hd.scomp ξ (Real.hasDerivAt_cosh ξ)
  have hp : HasDerivAt (fun y : ℝ => ((Real.sinh y ^ k : ℝ) : ℂ))
      (((k * Real.sinh ξ ^ (k - 1) * Real.cosh ξ : ℝ)) : ℂ) ξ :=
    (((Real.hasDerivAt_sinh ξ).pow k)).ofReal_comp
  have h := hp.mul hc
  unfold ladUp profile
  have h' : HasDerivAt (fun y : ℝ => ((Real.sinh y ^ k : ℝ) : ℂ) * iteratedDeriv k G (Real.cosh y))
      (((k * Real.sinh ξ ^ (k - 1) * Real.cosh ξ : ℝ) : ℂ) * iteratedDeriv k G (Real.cosh ξ) +
        ((Real.sinh ξ ^ k : ℝ) : ℂ) * (Real.sinh ξ • iteratedDeriv (k + 1) G (Real.cosh ξ))) ξ := h
  rw [h'.deriv]
  simp only [ladCoeff, Complex.real_smul]
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_succ, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_zero,
      Complex.ofReal_one]
    field_simp
    ring

end Lightlike.Lorentz.SL2RPlancherel
