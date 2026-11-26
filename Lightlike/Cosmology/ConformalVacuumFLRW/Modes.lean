import Mathlib

/-!
# Mode functions and Bogoliubov coefficients on spatially flat FLRW (G1-037, stage 1)

Setting of the row G1-037 (milestone CO11, source `junker-schrohe-2002`, Section 6): a free scalar field on spatially flat
FLRW in conformal time `η`; after the rescaling `φ = χ / a` every spatial Fourier mode of momentum `k > 0` solves
`y'' + (k² + q(η)) y = 0`, with `q = m² a² − (1 − 6ξ) a''/a` smooth. A homogeneous quasi-free state is a family of
*normalized* solutions `y_k`, `y ȳ' − ȳ y' = i`; the vacuum of Minkowski space is `y_k = e^{-ikη}/√(2k)` (`q = 0`).

This file is the algebra of such families, with no analysis in `k`:

* `IsMode q k y`: `y` solves the mode equation (and is twice differentiable);
* `wr y z = y z' − y' z`, the Wronskian; it is constant along two modes (`IsMode.wr_const`);
* `IsNormalized y`: `wr y ȳ = i`, constant in `η` once it holds at one time (`IsMode.normalized_iff`);
* `alphaC y u = −i wr y ū`, `betaC y u = i wr y u`: the Bogoliubov coefficients of `y` relative to a normalized `u`;
  they are constant (`betaC_const`), `y = α u + β ū` (`eq_alpha_mul_add_beta_mul`) and, if `y` is also normalized,
  `|α|² − |β|² = 1` (`normSq_alphaC_sub_normSq_betaC`).

**Limits.** Only the mode ODE for one `k`; the state, the two-point function and the Hadamard condition are in later
files of the folder.
-/

namespace Lightlike
namespace Cosmology
namespace ConformalVacuumFLRW

open Complex

/-- The Wronskian `y z' − y' z` of two functions of conformal time. -/
noncomputable def wr (y z : ℝ → ℂ) (η : ℝ) : ℂ := y η * deriv z η - deriv y η * z η

/-- **The mode equation**: `y` is twice differentiable and `y'' + (k² + q) y = 0`. -/
structure IsMode (q : ℝ → ℝ) (k : ℝ) (y : ℝ → ℂ) : Prop where
  diff : Differentiable ℝ y
  diff' : Differentiable ℝ (deriv y)
  eqn : ∀ η, deriv (deriv y) η + ((k ^ 2 + q η : ℝ) : ℂ) * y η = 0

/-- A mode is *normalized* when its Wronskian with its conjugate is `i` (at all times). -/
def IsNormalized (y : ℝ → ℂ) : Prop := ∀ η, wr y (fun t => starRingEnd ℂ (y t)) η = Complex.I

/-- The derivative of the conjugate is the conjugate of the derivative. -/
lemma deriv_conj_fun (y : ℝ → ℂ) :
    deriv (fun t => starRingEnd ℂ (y t)) = fun t => starRingEnd ℂ (deriv y t) := by
  simpa [Complex.star_def] using deriv.star' (f := y)

/-- The conjugate of a mode is a mode (the equation has real coefficients). -/
lemma IsMode.conj {q : ℝ → ℝ} {k : ℝ} {y : ℝ → ℂ} (h : IsMode q k y) :
    IsMode q k (fun t => starRingEnd ℂ (y t)) where
  diff := fun t => (Complex.conjCLE.differentiableAt.comp t (h.diff t))
  diff' := by
    rw [deriv_conj_fun]
    exact fun t => (Complex.conjCLE.differentiableAt.comp t (h.diff' t))
  eqn η := by
    rw [deriv_conj_fun, deriv_conj_fun]
    have := congrArg (starRingEnd ℂ) (h.eqn η)
    simpa [Complex.conj_ofReal] using this

/-- **The Wronskian of two modes is constant in time.** -/
lemma IsMode.wr_const {q : ℝ → ℝ} {k : ℝ} {y z : ℝ → ℂ} (hy : IsMode q k y) (hz : IsMode q k z)
    (η₁ η₂ : ℝ) : wr y z η₁ = wr y z η₂ := by
  have hd : ∀ η, HasDerivAt (wr y z) 0 η := by
    intro η
    have h1 := (hy.diff η).hasDerivAt.mul (hz.diff' η).hasDerivAt
    have h2 := (hy.diff' η).hasDerivAt.mul (hz.diff η).hasDerivAt
    have h3 := h1.sub h2
    have e1 : deriv (deriv y) η = -(((k ^ 2 + q η : ℝ) : ℂ) * y η) :=
      eq_neg_of_add_eq_zero_left (hy.eqn η)
    have e2 : deriv (deriv z) η = -(((k ^ 2 + q η : ℝ) : ℂ) * z η) :=
      eq_neg_of_add_eq_zero_left (hz.eqn η)
    refine h3.congr_deriv ?_
    rw [e1, e2]
    ring
  exact is_const_of_deriv_eq_zero (fun η => (hd η).differentiableAt) (fun η => (hd η).deriv) η₁ η₂

/-- **Normalization is a condition at one time**: if `wr y ȳ = i` at some time, it holds at all times. -/
lemma IsMode.normalized_of_at {q : ℝ → ℝ} {k : ℝ} {y : ℝ → ℂ} (h : IsMode q k y) (η₀ : ℝ)
    (h0 : wr y (fun t => starRingEnd ℂ (y t)) η₀ = Complex.I) : IsNormalized y :=
  fun η => (h.wr_const h.conj η η₀).trans h0

/-- The Bogoliubov coefficient `α = −i W(y, ū)` of `y` relative to `u` (evaluated at time `0`; it is constant). -/
noncomputable def alphaC (y u : ℝ → ℂ) : ℂ := -Complex.I * wr y (fun t => starRingEnd ℂ (u t)) 0

/-- The Bogoliubov coefficient `β = i W(y, u)` of `y` relative to `u` (evaluated at time `0`; it is constant). -/
noncomputable def betaC (y u : ℝ → ℂ) : ℂ := Complex.I * wr y u 0

section Bogoliubov

variable {q : ℝ → ℝ} {k : ℝ} {y u : ℝ → ℂ}

/-- `α` is the Wronskian at any time. -/
lemma alphaC_eq (hy : IsMode q k y) (hu : IsMode q k u) (η : ℝ) :
    alphaC y u = -Complex.I * wr y (fun t => starRingEnd ℂ (u t)) η := by
  rw [alphaC, hy.wr_const hu.conj 0 η]

/-- `β` is the Wronskian at any time. -/
lemma betaC_eq (hy : IsMode q k y) (hu : IsMode q k u) (η : ℝ) :
    betaC y u = Complex.I * wr y u η := by
  rw [betaC, hy.wr_const hu 0 η]

/-- **The mode expands in the reference mode and its conjugate**: for a normalized `u`,
`y = α u + β ū` at every time, with the constant coefficients `alphaC`, `betaC`. -/
lemma eq_alpha_mul_add_beta_mul (hy : IsMode q k y) (hu : IsMode q k u) (hn : IsNormalized u)
    (η : ℝ) : y η = alphaC y u * u η + betaC y u * starRingEnd ℂ (u η) := by
  rw [alphaC_eq hy hu η, betaC_eq hy hu η]
  have key : y η * wr u (fun t => starRingEnd ℂ (u t)) η =
      u η * wr y (fun t => starRingEnd ℂ (u t)) η - starRingEnd ℂ (u η) * wr y u η := by
    unfold wr; ring
  rw [hn η] at key
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-Complex.I) * key + y η * hI

/-- **`|α|² − |β|² = 1`** for a normalized mode `y` expanded in a normalized reference mode `u`. -/
lemma normSq_alphaC_sub_normSq_betaC (hy : IsMode q k y) (hu : IsMode q k u) (hn : IsNormalized u)
    (hyn : IsNormalized y) :
    Complex.normSq (alphaC y u) - Complex.normSq (betaC y u) = 1 := by
  set a := alphaC y u
  set b := betaC y u
  have hfun : y = fun t => a * u t + b * starRingEnd ℂ (u t) :=
    funext fun t => eq_alpha_mul_add_beta_mul hy hu hn t
  have hd : deriv y 0 = a * deriv u 0 + b * starRingEnd ℂ (deriv u 0) := by
    have hc : HasDerivAt (fun t => starRingEnd ℂ (u t)) (starRingEnd ℂ (deriv u 0)) 0 := by
      simpa [Complex.star_def] using ((hu.diff 0).hasDerivAt).star
    have h1 := ((hu.diff 0).hasDerivAt.const_mul a).add (hc.const_mul b)
    rw [hfun]
    exact h1.deriv
  have h0 := hyn 0
  have hu0 := hn 0
  unfold wr at h0 hu0
  rw [deriv_conj_fun] at h0 hu0
  beta_reduce at h0 hu0
  rw [hd, hfun] at h0
  simp only [map_add, map_mul, Complex.conj_conj] at h0
  have h3 : (a * starRingEnd ℂ a - b * starRingEnd ℂ b) * Complex.I = Complex.I := by
    linear_combination h0 - (a * starRingEnd ℂ a - b * starRingEnd ℂ b) * hu0
  rw [Complex.mul_conj, Complex.mul_conj] at h3
  have h4 : ((Complex.normSq a : ℂ) - (Complex.normSq b : ℂ)) = 1 :=
    mul_right_cancel₀ Complex.I_ne_zero (by rw [h3, one_mul])
  exact_mod_cast h4

end Bogoliubov

end ConformalVacuumFLRW
end Cosmology
end Lightlike

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsMode := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsMode
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsMode.conj := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsMode.conj
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsMode.diff := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsMode.diff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsMode.diff' := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsMode.diff'
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsMode.eqn := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsMode.eqn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsMode.normalized_of_at := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsMode.normalized_of_at
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsMode.wr_const := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsMode.wr_const
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.IsNormalized := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.IsNormalized
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.alphaC := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.alphaC
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.alphaC_eq := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.alphaC_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.betaC := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.betaC
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.betaC_eq := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.betaC_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.deriv_conj_fun := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.deriv_conj_fun
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.eq_alpha_mul_add_beta_mul := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.eq_alpha_mul_add_beta_mul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.normSq_alphaC_sub_normSq_betaC := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.normSq_alphaC_sub_normSq_betaC
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_037.wr := _root_.Lightlike.Cosmology.ConformalVacuumFLRW.wr
