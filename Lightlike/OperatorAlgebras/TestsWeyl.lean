import Lightlike.OperatorAlgebras.Weyl
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Trust checks for the Bogoliubov definitions

One mode: `h = ℂ`. The squeezing `T (x + i y) = e^r x + i e^{-r} y` (that is, `T f = cosh r f + sinh r f̄`)
preserves `σ(f, g) = Im ⟪f, g⟫` and has `α = cosh r`, `β = sinh r`, so `|α|² - |β|² = 1`. The dilation
`f ↦ 2 f` does not preserve `σ`, so it is not a Bogoliubov transformation (negative control).

Not checked here: infinitely many modes with constant `|β|` give a map that is not Hilbert–Schmidt
(needs a Hilbert basis of `ℓ²`).
-/

namespace Lightlike.OperatorAlgebras

open Complex

/-- The squeezing `x + i y ↦ e^r x + i e^{-r} y` as a real-linear map of `ℂ`. -/
noncomputable def squeezeMap (r : ℝ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := ⟨Real.exp r * z.re, Real.exp (-r) * z.im⟩
  map_add' a b := by apply Complex.ext <;> simp <;> ring
  map_smul' c a := by apply Complex.ext <;> simp <;> ring

private lemma exp_mul_exp_neg (r x : ℝ) : Real.exp (-r) * (Real.exp r * x) = x := by
  rw [← mul_assoc, ← Real.exp_add]; simp

/-- The squeezing as a Bogoliubov transformation of the one-mode space `ℂ`. -/
noncomputable def squeeze (r : ℝ) : Bogoliubov ℂ where
  toEquiv :=
    ContinuousLinearEquiv.equivOfInverse (squeezeMap r).toContinuousLinearMap
      (squeezeMap (-r)).toContinuousLinearMap
      (fun z => by
        apply Complex.ext
        · simpa [squeezeMap] using exp_mul_exp_neg r z.re
        · simpa [squeezeMap] using exp_mul_exp_neg (-r) z.im)
      (fun z => by
        apply Complex.ext
        · simpa [squeezeMap] using exp_mul_exp_neg (-r) z.re
        · simpa [squeezeMap] using exp_mul_exp_neg r z.im)
  symp_map f g := by
    simp [symp, squeezeMap, ContinuousLinearEquiv.equivOfInverse, inner]
    have e : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (g.im * f.re - g.re * f.im) * e


/-- The squeezing acts as `x + i y ↦ e^r x + i e^{-r} y`. -/
lemma squeeze_apply (r : ℝ) (z : ℂ) :
    (squeeze r).toEquiv z = ⟨Real.exp r * z.re, Real.exp (-r) * z.im⟩ := rfl

/-- **Trust check, one mode**: the complex-linear part of the squeezing on the vector `1` is `cosh r`. -/
lemma squeeze_alpha (r : ℝ) : (squeeze r).alphaPart 1 = (Real.cosh r : ℂ) := by
  apply Complex.ext
  · simp [Bogoliubov.alphaPart, squeeze_apply]
    rw [Real.cosh_eq]; ring
  · simp [Bogoliubov.alphaPart, squeeze_apply]

/-- **Trust check, one mode**: the antilinear part of the squeezing on the vector `1` is `sinh r`. -/
lemma squeeze_beta (r : ℝ) : (squeeze r).betaPart 1 = (Real.sinh r : ℂ) := by
  apply Complex.ext
  · simp [Bogoliubov.betaPart, squeeze_apply]
    rw [← Complex.ofReal_sinh, Complex.ofReal_re, Real.sinh_eq]; ring
  · simp [Bogoliubov.betaPart, squeeze_apply]

/-- **Trust check, one mode**: `|α|² - |β|² = 1` for the squeezing. -/
theorem squeeze_norm_sq (r : ℝ) :
    ‖(squeeze r).alphaPart 1‖ ^ 2 - ‖(squeeze r).betaPart 1‖ ^ 2 = 1 := by
  rw [squeeze_alpha, squeeze_beta, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]
  exact Real.cosh_sq_sub_sinh_sq r

/-- **Negative control**: the dilation `f ↦ 2 f` does not preserve the symplectic form of `ℂ`
(`σ(1, i) = 1` becomes `4`), so no Bogoliubov transformation acts as the dilation. -/
theorem dilation_not_symplectic :
    ¬ ∀ f g : ℂ, symp ℂ ((2 : ℝ) • f) ((2 : ℝ) • g) = symp ℂ f g := by
  intro h
  have := h 1 Complex.I
  simp [symp, inner] at this
  norm_num at this

end Lightlike.OperatorAlgebras
