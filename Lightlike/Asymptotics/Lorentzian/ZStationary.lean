import Lightlike.Asymptotics.Lorentzian.Stationary
import Lightlike.Asymptotics.Lorentzian.Parity

/-!
# Stationarity of the vertex action in the spinor variables

The first variation of the triangle factor along a simultaneous variation of its two spinors
(`hasDerivAt_triFactor_joint`), the target-side variation along a general direction
(`hasDerivAt_triFactor_target`), and the cancellation of the `z`-variation on a critical edge
(`zedge_cancel`, `edge_variation`): at `Z = ξ`, `Z' = r c J ξ'` the second critical equation (21)
makes the `z` terms cancel for every `δz`, and the group terms are the `logDeriv` of
`Stationary.lean`. `sum_logDeriv_nodes` sums them over the nodes, where closure makes them vanish.
`hasDerivAt_triFactor_curve` extends the line derivative to curves (the triangle factor is
differentiable in both spinors). These are statements about the derivative of the action in the
spinor and group variables; the identification with the gradient of the chart action is not made here.
-/

open Complex
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian

/-- **The triangle factor separates**: for nonzero `Z`, `Z'`,
`triFactor n p Z ξ Z' ξ' = F(Z) · G(Z')` with
`F(Z) = ⟨Z,ξ⟩^n / ‖Z‖^n · exp(-i p log ‖Z‖²)` and `G(Z') = ⟨Jξ',Z'⟩^n / ‖Z'‖^n · exp(i p log ‖Z'‖²)`. -/
theorem triFactor_eq_mul (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) :
    triFactor n p Z ξ Z' ξ' =
      (inner ℂ Z ξ ^ n / ((‖Z‖ ^ n : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * p * (Real.log (‖Z‖ ^ 2) : ℝ)))) *
      (inner ℂ (jMap ξ') Z' ^ n / ((‖Z'‖ ^ n : ℝ) : ℂ) *
        Complex.exp (Complex.I * p * (Real.log (‖Z'‖ ^ 2) : ℝ))) := by
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  unfold triFactor
  rw [Real.log_div (by positivity) (by positivity), mul_pow, mul_pow]
  push_cast
  have : Complex.exp (Complex.I * p * (Real.log (‖Z'‖ ^ 2) - Real.log (‖Z‖ ^ 2) : ℝ)) =
      Complex.exp (-(Complex.I * p * (Real.log (‖Z‖ ^ 2) : ℝ))) *
        Complex.exp (Complex.I * p * (Real.log (‖Z'‖ ^ 2) : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  push_cast at this ⊢
  rw [this]
  ring

/-- **The target-side derivative along a general direction**: the derivative of the triangle factor
under `Z' ↦ Z' + t W'` (the companion of `hasDerivAt_triFactor`, obtained from it by the swap
`triFactor_swap`): `triFactor · (n ⟨Jξ',W'⟩/⟨Jξ',Z'⟩ - (n - 2ip) Re⟨Z',W'⟩/‖Z'‖²)`. -/
theorem hasDerivAt_triFactor_target (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (W' : Spinor)
    (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    HasDerivAt (fun t : ℝ => triFactor n p Z ξ (Z' + t • W') ξ')
      (triFactor n p Z ξ Z' ξ' *
        ((n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') Z') -
          ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ Z' W').re / ‖Z'‖ ^ 2 : ℝ) : ℂ))) 0 := by
  have e1 : ∀ Y : Spinor, inner ℂ (jMap ξ') Y = -inner ℂ (jMap Y) ξ' := by
    intro Y
    have : Y = -jMap (jMap Y) := by rw [jMap_jMap]; simp
    conv_lhs => rw [this]
    rw [inner_neg_right, inner_jMap_jMap, inner_conj_symm]
  have e2 : inner ℂ (jMap ξ) (jMap Z) = inner ℂ Z ξ := by
    rw [inner_jMap_jMap, inner_conj_symm]
  have hJZ : jMap Z ≠ 0 := jMap_ne_zero hZ
  have hJZ' : jMap Z' ≠ 0 := jMap_ne_zero hZ'
  have h1' : inner ℂ (jMap Z') ξ' ≠ 0 := by
    intro h; apply h2; rw [e1, h]; simp
  have h2' : inner ℂ (jMap ξ) (jMap Z) ≠ 0 := by rw [e2]; exact h1
  have hd := hasDerivAt_triFactor n (-p) (jMap W') hJZ' hJZ h1' h2'
  have hfun : (fun t : ℝ => triFactor n p Z ξ (Z' + t • W') ξ') =
      fun t : ℝ => (-1 : ℂ) ^ n * triFactor n (-p) (jMap Z' + t • jMap W') ξ' (jMap Z) ξ := by
    funext t
    rw [triFactor_swap, jMap_add, jMap_real_smul]
  rw [hfun]
  refine (hd.const_mul ((-1 : ℂ) ^ n)).congr_deriv ?_
  have hT : triFactor n p Z ξ Z' ξ' =
      (-1 : ℂ) ^ n * triFactor n (-p) (jMap Z') ξ' (jMap Z) ξ := triFactor_swap n p Z ξ Z' ξ'
  have hre : (inner ℂ (jMap Z') (jMap W')).re = (inner ℂ Z' W').re := by
    rw [inner_jMap_jMap, Complex.conj_re]
  rw [hT, e1 W', e1 Z', hre, norm_jMap]
  have hz : (inner ℂ (jMap Z') ξ') ≠ 0 := h1'
  push_cast
  field_simp
  ring

/-- **The joint derivative of the triangle factor** along `(Z + tW, Z' + tW')` (BDFHP Sec. 4.2.2): at
`t = 0` it is `triFactor` times the sum of the source and the target logarithmic derivatives,
`n ⟨W,ξ⟩/⟨Z,ξ⟩ - (n + 2ip) Re⟨Z,W⟩/‖Z‖² + n ⟨Jξ',W'⟩/⟨Jξ',Z'⟩ - (n - 2ip) Re⟨Z',W'⟩/‖Z'‖²`.
This is what a variation of `z` produces (`W = X_a† δz`, `W' = X_b† δz`). -/
theorem hasDerivAt_triFactor_joint (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (W W' : Spinor)
    (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    HasDerivAt (fun t : ℝ => triFactor n p (Z + t • W) ξ (Z' + t • W') ξ')
      (triFactor n p Z ξ Z' ξ' *
        (((n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) -
            ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ Z W).re / ‖Z‖ ^ 2 : ℝ) : ℂ)) +
          ((n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') Z') -
            ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ Z' W').re / ‖Z'‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  set T := triFactor n p Z ξ Z' ξ' with hTdef
  set A : ℂ := ((n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) -
    ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ Z W).re / ‖Z‖ ^ 2 : ℝ) : ℂ)) with hA
  set B : ℂ := ((n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') Z') -
    ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ Z' W').re / ‖Z'‖ ^ 2 : ℝ) : ℂ)) with hB
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  have hT0 : T ≠ 0 := by
    rw [hTdef]; unfold triFactor
    refine mul_ne_zero (div_ne_zero (pow_ne_zero _ (mul_ne_zero h1 h2)) ?_) (Complex.exp_ne_zero _)
    exact_mod_cast (pow_pos (mul_pos hz hz') n).ne'
  have hdA := hasDerivAt_triFactor n p W hZ hZ' h1 h2
  have hdB := hasDerivAt_triFactor_target n p W' hZ hZ' h1 h2
  have hprod := (hdA.mul hdB).div_const T
  have hev : ∀ᶠ t : ℝ in nhds 0, Z + t • W ≠ 0 ∧ Z' + t • W' ≠ 0 := by
    have c1 : ContinuousAt (fun t : ℝ => Z + t • W) 0 := by fun_prop
    have c2 : ContinuousAt (fun t : ℝ => Z' + t • W') 0 := by fun_prop
    have e1 := c1.eventually_ne (by simpa using hZ)
    have e2 := c2.eventually_ne (by simpa using hZ')
    exact e1.and e2
  refine (hprod.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [zero_smul, add_zero]
    rw [← hTdef, hA, hB]
    field_simp
  · filter_upwards [hev] with t ⟨ht, ht'⟩
    have e1 := triFactor_eq_mul n p (ξ := ξ) (ξ' := ξ') ht hZ'
    have e2 := triFactor_eq_mul n p (ξ := ξ) (ξ' := ξ') hZ ht'
    have e3 := triFactor_eq_mul n p (ξ := ξ) (ξ' := ξ') ht ht'
    have e4 := triFactor_eq_mul n p (ξ := ξ) (ξ' := ξ') hZ hZ'
    have hT0' : triFactor n p Z ξ Z' ξ' ≠ 0 := hT0
    rw [e4] at hT0'
    simp only [Pi.mul_apply]
    rw [e3, e1, e2, hTdef, e4]
    have hF : ((inner ℂ Z ξ ^ n / ((‖Z‖ ^ n : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * p * (Real.log (‖Z‖ ^ 2) : ℝ))))) ≠ 0 := left_ne_zero_of_mul hT0'
    have hG : ((inner ℂ (jMap ξ') Z' ^ n / ((‖Z'‖ ^ n : ℝ) : ℂ) *
        Complex.exp (Complex.I * p * (Real.log (‖Z'‖ ^ 2) : ℝ)))) ≠ 0 := right_ne_zero_of_mul hT0'
    have n1 : (((‖Z‖ ^ n : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hz n).ne'
    have n2 : (((‖Z'‖ ^ n : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hz' n).ne'
    have n3 : (((‖Z + t • W‖ ^ n : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos (norm_pos_iff.mpr ht) n).ne'
    have n4 : (((‖Z' + t • W'‖ ^ n : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos (norm_pos_iff.mpr ht') n).ne'
    field_simp

/-- The triangle factor is nonzero when the spinors and both overlaps are. -/
theorem triFactor_ne_zero (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0)
    (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) : triFactor n p Z ξ Z' ξ' ≠ 0 := by
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  unfold triFactor
  refine mul_ne_zero (div_ne_zero (pow_ne_zero _ (mul_ne_zero h1 h2)) ?_) (Complex.exp_ne_zero _)
  exact_mod_cast (pow_pos (mul_pos hz hz') n).ne'

/-- **The source logarithmic derivative along a group variation is `logDeriv`**: at `Z = lam • ξ`
(`‖ξ‖ = 1`), the coefficient of `hasDerivAt_triFactor` in the direction `W = (gen c)† Z` equals
`logDeriv n p c ξ`. (Uniqueness of the derivative against `hasDerivAt_triFactor_gen`.) -/
theorem srcCoeff_gen (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) {ξ Z' ξ' : Spinor} {lam : ℂ}
    (hlam : lam ≠ 0) (hξ : ‖ξ‖ = 1) (hZ' : Z' ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    ((n : ℂ) * (inner ℂ (LinearMap.adjoint (gen c) (lam • ξ)) ξ / inner ℂ (lam • ξ) ξ) -
        ((n : ℂ) + 2 * Complex.I * p) *
          (((inner ℂ (lam • ξ) (LinearMap.adjoint (gen c) (lam • ξ))).re / ‖lam • ξ‖ ^ 2 : ℝ) : ℂ))
      = logDeriv n p c ξ := by
  have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξ
  have hZ : lam • ξ ≠ 0 := smul_ne_zero hlam hξ0
  have hin : inner ℂ ξ ξ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hl : inner ℂ (lam • ξ) ξ = conj lam := by
    rw [inner_smul_left, hin, mul_one]
  have h1 : inner ℂ (lam • ξ) ξ ≠ 0 := by rw [hl]; simpa using hlam
  have hd1 := hasDerivAt_triFactor n p (LinearMap.adjoint (gen c) (lam • ξ)) hZ hZ' h1 h2
  have hd2 := hasDerivAt_triFactor_gen n p c (ξ := ξ) (Z' := Z') (ξ' := ξ') hlam hξ hZ' h2
  have := hd1.unique hd2
  exact mul_left_cancel₀ (triFactor_ne_zero n p hZ hZ' h1 h2) this

/-- **The target logarithmic derivative along a group variation is `logDeriv`**: if `J Z' = μ ξ'`
(`‖ξ'‖ = 1`), the coefficient of `hasDerivAt_triFactor_target` in the direction `W' = (gen c)† Z'`
equals `logDeriv n p c ξ'`. -/
theorem tgtCoeff_gen (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) {Z ξ ξ' : Spinor} (Z' : Spinor) {μ : ℂ}
    (hμ : μ ≠ 0) (hξ' : ‖ξ'‖ = 1) (hZ : Z ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (hY : jMap Z' = μ • ξ') :
    ((n : ℂ) * (inner ℂ (jMap ξ') (LinearMap.adjoint (gen c) Z') / inner ℂ (jMap ξ') Z') -
        ((n : ℂ) - 2 * Complex.I * p) *
          (((inner ℂ Z' (LinearMap.adjoint (gen c) Z')).re / ‖Z'‖ ^ 2 : ℝ) : ℂ))
      = logDeriv n p c ξ' := by
  have hZ' : Z' ≠ 0 := by
    intro h
    have h3 : ‖jMap Z'‖ = ‖μ • ξ'‖ := by rw [hY]
    rw [norm_jMap, h, norm_zero, norm_smul, hξ', mul_one] at h3
    exact hμ (norm_eq_zero.mp h3.symm)
  have hξ0 : ξ' ≠ 0 := by intro h; simp [h] at hξ'
  have h2 : inner ℂ (jMap ξ') Z' ≠ 0 := by
    have e : inner ℂ (jMap ξ') Z' = -inner ℂ (jMap Z') ξ' := by
      have : Z' = -jMap (jMap Z') := by rw [jMap_jMap]; simp
      conv_lhs => rw [this]
      rw [inner_neg_right, inner_jMap_jMap, inner_conj_symm]
    have hin : inner ℂ ξ' ξ' = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hξ']; simp
    rw [e, hY, inner_smul_left, hin]
    simpa using hμ
  have hd1 := hasDerivAt_triFactor_target n p (LinearMap.adjoint (gen c) Z') hZ hZ' h1 h2
  have hd2 := hasDerivAt_triFactor_gen_target n p c Z' hμ hξ' hZ h1 hY
  have := hd1.unique hd2
  exact mul_left_cancel₀ (triFactor_ne_zero n p hZ hZ' h1 h2) this

/-- **Stationarity in `z`, the algebraic core**: if `⟨ξ, W⟩ = a` and `⟨Jξ', W'⟩ = b` are related by
`a = r⁻¹ conj(c) b` (a consequence of the second critical equation (21)), the source and target
logarithmic derivatives cancel. -/
theorem zstat_algebra (n : ℕ) (p r : ℝ) (c a b : ℂ) (hr : 0 < r) (hc : ‖c‖ = 1)
    (ha : a = ((r : ℂ)⁻¹ * conj c) * b) :
    ((n : ℂ) * conj a - ((n : ℂ) + 2 * I * p) * ((a.re : ℝ) : ℂ)) +
      ((n : ℂ) * (b / ((r : ℂ) * c)) -
        ((n : ℂ) - 2 * I * p) * ((((conj ((r : ℂ) * c)) * b).re / r ^ 2 : ℝ) : ℂ)) = 0 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  have hre : a.re = r⁻¹ * ((conj c * b).re) := by
    rw [ha]
    have : ((r : ℂ)⁻¹ * conj c) * b = (((r⁻¹ : ℝ)) : ℂ) * (conj c * b) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  have hre2 : ((conj ((r : ℂ) * c)) * b).re = r * ((conj c * b).re) := by
    have : (conj ((r : ℂ) * c)) * b = ((r : ℝ) : ℂ) * (conj c * b) := by
      rw [map_mul, Complex.conj_ofReal]; ring
    rw [this, Complex.re_ofReal_mul]
  have hconj : conj a = (r : ℂ)⁻¹ * c * conj b := by
    rw [ha]; simp [map_mul, map_inv₀]
  have h2re : (2 : ℂ) * (((conj c * b).re : ℝ) : ℂ) = conj c * b + c * conj b := by
    have := Complex.re_add_im (conj c * b)
    have h' : conj (conj c * b) = c * conj b := by simp
    have hr' : (((conj c * b).re : ℝ) : ℂ) = (conj c * b + conj (conj c * b)) / 2 := by
      rw [Complex.add_conj]; push_cast; ring
    rw [hr', h']; ring
  rw [hre, hre2, hconj]
  have hinv : c⁻¹ = conj c := inv_eq_of_mul_eq_one_right hcc
  push_cast
  have e1 : b / ((r : ℂ) * c) = (r : ℂ)⁻¹ * conj c * b := by
    rw [div_eq_mul_inv, mul_inv, hinv]; ring
  rw [e1]
  have e3 : (r : ℂ) * (((conj c * b).re : ℝ) : ℂ) / (r : ℂ) ^ 2 =
      (r : ℂ)⁻¹ * (((conj c * b).re : ℝ) : ℂ) := by field_simp
  rw [e3]
  linear_combination ((n : ℂ) * (r : ℂ)⁻¹) * (-(1 : ℂ)) * h2re + 0 * hcc

/-- The adjoint of a matrix acting on spinors: `⟨u, M† v⟩ = ⟨M u, v⟩`. -/
theorem inner_spinAct_conjTranspose (M : Matrix (Fin 2) (Fin 2) ℂ) (u v : Spinor) :
    inner ℂ u (spinAct Mᴴ v) = inner ℂ (spinAct M u) v := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, spinAct_zero_apply,
    spinAct_one_apply, Matrix.conjTranspose_apply, map_add, map_mul,
    star_def]
  ring

/-- **Stationarity in `z` on one edge.** With `Z = ξ`, `Z' = r c J ξ'` (unit `ξ, ξ'`, `r > 0`, `|c| = 1`)
and the second critical equation `M ξ = r⁻¹ c N J ξ'`, the source and target logarithmic derivatives
in the direction `(W, W') = (M† δz, N† δz)` of a variation `δz` cancel. -/
theorem zedge_cancel (n : ℕ) (p r : ℝ) (c : ℂ) (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (ξ ξ' δz : Spinor) (hr : 0 < r) (hc : ‖c‖ = 1) (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1)
    (h21 : spinAct M ξ = ((r : ℂ)⁻¹ * c) • spinAct N (jMap ξ')) :
    ((n : ℂ) * (inner ℂ (spinAct Mᴴ δz) ξ / inner ℂ ξ ξ) -
        ((n : ℂ) + 2 * Complex.I * p) *
          (((inner ℂ ξ (spinAct Mᴴ δz)).re / ‖ξ‖ ^ 2 : ℝ) : ℂ)) +
      ((n : ℂ) * (inner ℂ (jMap ξ') (spinAct Nᴴ δz) /
            inner ℂ (jMap ξ') (((r : ℂ) * c) • jMap ξ')) -
        ((n : ℂ) - 2 * Complex.I * p) *
          (((inner ℂ (((r : ℂ) * c) • jMap ξ') (spinAct Nᴴ δz)).re /
            ‖((r : ℂ) * c) • jMap ξ'‖ ^ 2 : ℝ) : ℂ)) = 0 := by
  have hin : inner ℂ ξ ξ = 1 := by rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hjin : inner ℂ (jMap ξ') (jMap ξ') = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_jMap, hξ']; simp
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  set a := inner ℂ ξ (spinAct Mᴴ δz) with ha
  set b := inner ℂ (jMap ξ') (spinAct Nᴴ δz) with hb
  have hab : a = ((r : ℂ)⁻¹ * conj c) * b := by
    rw [ha, hb, inner_spinAct_conjTranspose, inner_spinAct_conjTranspose, h21, inner_smul_left]
    simp
  have e1 : inner ℂ (spinAct Mᴴ δz) ξ = conj a := by rw [ha, inner_conj_symm]
  have e2 : inner ℂ (jMap ξ') (((r : ℂ) * c) • jMap ξ') = (r : ℂ) * c := by
    rw [inner_smul_right, hjin, mul_one]
  have e3 : inner ℂ (((r : ℂ) * c) • jMap ξ') (spinAct Nᴴ δz) = conj ((r : ℂ) * c) * b := by
    rw [inner_smul_left]
  have e4 : ‖((r : ℂ) * c) • jMap ξ'‖ ^ 2 = r ^ 2 := by
    rw [norm_smul, norm_jMap, hξ', norm_mul, hc]; simp [abs_of_pos hr]
  rw [e1, hin, e2, e3, e4, hξ]
  have := zstat_algebra n p r c a b hr hc hab
  simpa using this


/-- **First variation on one edge at the critical spinors.** At `Z = ξ`, `Z' = r c J ξ'` with the
second critical equation, the source and target coefficients of `hasDerivAt_triFactor` in the
direction `(W, W') = ((gen c_a)† Z + M† δz, (gen c_b)† Z' + N† δz)` sum to
`logDeriv n p c_a ξ + logDeriv n p c_b ξ'`: the `δz` part cancels (`zedge_cancel`) and the group
parts are `srcCoeff_gen`, `tgtCoeff_gen`. -/
theorem edge_variation (n : ℕ) (p r : ℝ) (c : ℂ) (ca cb : Fin 3 → ℂ)
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (ξ ξ' δz : Spinor) (hr : 0 < r) (hc : ‖c‖ = 1)
    (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1)
    (h21 : spinAct M ξ = ((r : ℂ)⁻¹ * c) • spinAct N (jMap ξ')) :
    let W := LinearMap.adjoint (gen ca) ξ + spinAct Mᴴ δz
    let Z' := ((r : ℂ) * c) • jMap ξ'
    let W' := LinearMap.adjoint (gen cb) Z' + spinAct Nᴴ δz
    ((n : ℂ) * (inner ℂ W ξ / inner ℂ ξ ξ) -
        ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ ξ W).re / ‖ξ‖ ^ 2 : ℝ) : ℂ)) +
      ((n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') Z') -
        ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ Z' W').re / ‖Z'‖ ^ 2 : ℝ) : ℂ)) =
      logDeriv n p ca ξ + logDeriv n p cb ξ' := by
  intro W Z' W'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc; simp at hc
  have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξ
  have hin : inner ℂ ξ ξ = 1 := by rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hsrc := srcCoeff_gen n p ca (ξ := ξ) (Z' := Z') (ξ' := ξ') (lam := 1) one_ne_zero hξ
    (smul_ne_zero (mul_ne_zero hr0 hc0) (jMap_ne_zero (by intro h; simp [h] at hξ')))
    (by
      show inner ℂ (jMap ξ') (((r : ℂ) * c) • jMap ξ') ≠ 0
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_jMap, hξ']
      simpa using mul_ne_zero hr0 hc0)
  have hY : jMap Z' = (-conj ((r : ℂ) * c)) • ξ' := by
    show jMap (((r : ℂ) * c) • jMap ξ') = _
    ext i; fin_cases i <;> simp [jMap_zero_apply, jMap_one_apply] <;> ring
  have hμ : (-conj ((r : ℂ) * c)) ≠ 0 := by simpa using mul_ne_zero hr0 hc0
  have htgt := tgtCoeff_gen n p cb (Z := ξ) (ξ := ξ) (ξ' := ξ') Z' hμ hξ' hξ0
    (by rw [hin]; exact one_ne_zero) hY
  have hz := zedge_cancel n p r c M N ξ ξ' δz hr hc hξ hξ' h21
  simp only [one_smul] at hsrc
  show _ + ((n : ℂ) * (inner ℂ (jMap ξ') (LinearMap.adjoint (gen cb) Z' + spinAct Nᴴ δz) /
      inner ℂ (jMap ξ') Z') - _) = _
  simp only [W, W', inner_add_left, inner_add_right, Complex.add_re, add_div]
  push_cast at hsrc htgt hz ⊢
  linear_combination hsrc + htgt + hz

/-- **Summing the node terms.** If at every node `a` the logarithmic derivatives of the spinors of the
edges ending at `a` sum to zero for every `c` (closure of the normals, `stationary_iff_closure`),
the sum over edges of `logDeriv` at the group parameter of their source and of their target is zero
for any choice of group parameter `ca a` at each node. -/
theorem sum_logDeriv_nodes {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]
    (src tgt : E → V) (n : E → ℕ) (p : E → ℝ) (ξ ξ' : E → Spinor) (ca : V → Fin 3 → ℂ)
    (hcl : ∀ (a : V) (c : Fin 3 → ℂ), ∑ e, ((if src e = a then logDeriv (n e) (p e) c (ξ e) else 0) +
        (if tgt e = a then logDeriv (n e) (p e) c (ξ' e) else 0)) = 0) :
    ∑ e, (logDeriv (n e) (p e) (ca (src e)) (ξ e) + logDeriv (n e) (p e) (ca (tgt e)) (ξ' e)) = 0 := by
  have h1 : ∀ e, logDeriv (n e) (p e) (ca (src e)) (ξ e) + logDeriv (n e) (p e) (ca (tgt e)) (ξ' e) =
      ∑ a, ((if src e = a then logDeriv (n e) (p e) (ca a) (ξ e) else 0) +
        (if tgt e = a then logDeriv (n e) (p e) (ca a) (ξ' e) else 0)) := by
    intro e
    rw [Finset.sum_add_distrib]
    simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun a _ => hcl a (ca a)


theorem differentiableAt_inner_left (ξ : Spinor) (Z : Spinor) :
    DifferentiableAt ℝ (fun x : Spinor => inner ℂ x ξ) Z := by
  have : (fun x : Spinor => inner ℂ x ξ) = fun x => (starRingEnd ℂ) (inner ℂ ξ x) := by
    funext x; rw [inner_conj_symm]
  rw [this]
  exact (Complex.conjCLE.differentiableAt).comp Z
    (((innerSL ℂ ξ).restrictScalars ℝ).differentiableAt)

theorem differentiableAt_inner_right (ξ : Spinor) (Z : Spinor) :
    DifferentiableAt ℝ (fun x : Spinor => inner ℂ ξ x) Z :=
  ((innerSL ℂ ξ).restrictScalars ℝ).differentiableAt

theorem differentiableAt_triFactor (n : ℕ) (p : ℝ) (ξ ξ' : Spinor) {Z Z' : Spinor}
    (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) :
    DifferentiableAt ℝ (fun x : Spinor × Spinor => triFactor n p x.1 ξ x.2 ξ') (Z, Z') := by
  unfold triFactor
  have hn1 : DifferentiableAt ℝ (fun x : Spinor × Spinor => ‖x.1‖) (Z, Z') :=
    differentiableAt_fst.norm ℝ (by simpa using hZ)
  have hn2 : DifferentiableAt ℝ (fun x : Spinor × Spinor => ‖x.2‖) (Z, Z') :=
    differentiableAt_snd.norm ℝ (by simpa using hZ')
  have hi1 : DifferentiableAt ℝ (fun x : Spinor × Spinor => inner ℂ x.1 ξ) (Z, Z') :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := fun x : Spinor => inner ℂ x ξ) (f := Prod.fst) (Z, Z')
      (differentiableAt_inner_left ξ Z) differentiableAt_fst
  have hi2 : DifferentiableAt ℝ (fun x : Spinor × Spinor => inner ℂ (jMap ξ') x.2) (Z, Z') :=
    DifferentiableAt.comp (𝕜 := ℝ) (g := fun x : Spinor => inner ℂ (jMap ξ') x) (f := Prod.snd)
      (Z, Z') (differentiableAt_inner_right (jMap ξ') Z') differentiableAt_snd
  have hz : ‖Z‖ ≠ 0 := norm_ne_zero_iff.mpr hZ
  have hz' : ‖Z'‖ ≠ 0 := norm_ne_zero_iff.mpr hZ'
  have hq : DifferentiableAt ℝ (fun x : Spinor × Spinor => ‖x.2‖ ^ 2 / ‖x.1‖ ^ 2) (Z, Z') :=
    by
      simp only [div_eq_mul_inv]
      exact (hn2.fun_pow 2).mul ((hn1.fun_pow 2).inv (pow_ne_zero 2 hz))
  have hlog : DifferentiableAt ℝ
      (fun x : Spinor × Spinor => Real.log (‖x.2‖ ^ 2 / ‖x.1‖ ^ 2)) (Z, Z') :=
    hq.log (by simp [hz, hz'])
  have hden : DifferentiableAt ℝ (fun x : Spinor × Spinor => (((‖x.1‖ * ‖x.2‖) ^ n : ℝ) : ℂ))
      (Z, Z') :=
    (Complex.ofRealCLM.differentiableAt).comp (Z, Z') ((hn1.mul hn2).pow n)
  have hnum : DifferentiableAt ℝ (fun x : Spinor × Spinor =>
      (inner ℂ x.1 ξ * inner ℂ (jMap ξ') x.2) ^ n) (Z, Z') := (hi1.mul hi2).pow n
  have hden0 : (((‖Z‖ * ‖Z'‖) ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero n (mul_ne_zero hz hz'))
  simp only [div_eq_mul_inv]
  refine (hnum.mul (hden.inv hden0)).mul ?_
  · refine DifferentiableAt.cexp ?_
    exact ((differentiableAt_const _).mul
      ((Complex.ofRealCLM.differentiableAt).comp (Z, Z') hlog))

/-- **The derivative of the triangle factor along a curve**: if `Z(t)`, `Z'(t)` are differentiable
at `0` with derivatives `W`, `W'`, the derivative of `triFactor n p Z(t) ξ Z'(t) ξ'` at `0` is the
same as along the straight line in `hasDerivAt_triFactor_joint` (the triangle factor is
differentiable in both spinors where they are nonzero). -/
theorem hasDerivAt_triFactor_curve (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (W W' : Spinor)
    {Zc Z'c : ℝ → Spinor} (hZc : HasDerivAt Zc W 0) (hZ'c : HasDerivAt Z'c W' 0)
    (h0 : Zc 0 = Z) (h0' : Z'c 0 = Z')
    (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    HasDerivAt (fun t : ℝ => triFactor n p (Zc t) ξ (Z'c t) ξ')
      (triFactor n p Z ξ Z' ξ' *
        (((n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) -
            ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ Z W).re / ‖Z‖ ^ 2 : ℝ) : ℂ)) +
          ((n : ℂ) * (inner ℂ (jMap ξ') W' / inner ℂ (jMap ξ') Z') -
            ((n : ℂ) - 2 * Complex.I * p) * (((inner ℂ Z' W').re / ‖Z'‖ ^ 2 : ℝ) : ℂ)))) 0 := by
  have hF := (differentiableAt_triFactor n p ξ ξ' hZ hZ').hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => (Zc t, Z'c t)) (W, W') 0 := hZc.prodMk hZ'c
  have hline : HasDerivAt (fun t : ℝ => ((Z + t • W : Spinor), (Z' + t • W' : Spinor))) (W, W') 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const W).const_add Z
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const W').const_add Z'
  have hpt : (Zc 0, Z'c 0) = (Z, Z') := by rw [h0, h0']
  have hc := (hpt ▸ hF).comp_hasDerivAt (0 : ℝ) hcurve
  have hF0 : HasFDerivAt (fun x : Spinor × Spinor => triFactor n p x.1 ξ x.2 ξ')
      (fderiv ℝ (fun x : Spinor × Spinor => triFactor n p x.1 ξ x.2 ξ') (Z, Z'))
      (Z + (0 : ℝ) • W, Z' + (0 : ℝ) • W') := by simpa using hF
  have hl := hF0.comp_hasDerivAt (0 : ℝ) hline
  have hj := hasDerivAt_triFactor_joint n p W W' hZ hZ' h1 h2
  have hl' : HasDerivAt (fun t : ℝ => triFactor n p (Z + t • W) ξ (Z' + t • W') ξ')
      (fderiv ℝ (fun x : Spinor × Spinor => triFactor n p x.1 ξ x.2 ξ') (Z, Z') (W, W')) 0 := hl
  have hu := hl'.unique hj
  have hc' : HasDerivAt (fun t : ℝ => triFactor n p (Zc t) ξ (Z'c t) ξ')
      (fderiv ℝ (fun x : Spinor × Spinor => triFactor n p x.1 ξ x.2 ξ') (Z, Z') (W, W')) 0 := by
    rw [h0, h0'] at hc
    exact hc
  rw [← hu]; exact hc'

end Lightlike.Asymptotics.Lorentzian
