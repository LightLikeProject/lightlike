import Lightlike.Asymptotics.Lorentzian.Action

/-!
# Stationarity of the Lorentzian action in the group variables

The amplitude factor of a triangle (`triFactor`) is `e^{S_ab}`, with the spin `k = n/2` a
half-integer written without a branch of the logarithm. At a point where `Z = X_a† z` is parallel
to the boundary spinor `ξ` (the maximum of `Re S`), the infinitesimal change `X ↦ X exp(tL)` with
`L = ½ Σ c_i σ_i ∈ sl₂(ℂ)` (`gen c`, `c = β + iα`: `α` rotations, `β` boosts) moves `Z` to
`Z + t L† Z`, and the log derivative of the factor is

`logDeriv = i (n/2 · α·n̂ - p · β·n̂)`, with `n̂ = spinVec ξ`

(`hasDerivAt_triFactor_gen`, `logDeriv_eq`). The target end of a triangle gives the same
expression, by the antiunitary `J` (`triFactor_swap`, `hasDerivAt_triFactor_gen_target`). Summed
over the triangles at a vertex, stationarity in every direction is equivalent to
`Σ n_e n̂_e = 0` and `Σ p_e n̂_e = 0` (`stationary_iff`), which for `p = γk` is the closure of the
normals (`stationary_iff_closure`), eq. (24) and (25) of the source.
-/

open Complex
open scoped ComplexConjugate

namespace Lightlike.Asymptotics.Lorentzian

/-- The amplitude factor of a triangle, `e^{S_ab}` for the doubled spin `n = 2k`:
`(⟨Z,ξ⟩⟨Jξ',Z'⟩)^n / (‖Z‖‖Z'‖)^n · exp(i p log(‖Z'‖²/‖Z‖²))`. -/
noncomputable def triFactor (n : ℕ) (p : ℝ) (Z ξ Z' ξ' : Spinor) : ℂ :=
  (inner ℂ Z ξ * inner ℂ (jMap ξ') Z') ^ n / (((‖Z‖ * ‖Z'‖) ^ n : ℝ) : ℂ) *
    Complex.exp (Complex.I * p * (Real.log (‖Z'‖ ^ 2 / ‖Z‖ ^ 2) : ℝ))

/-- `|triFactor| = triWeight (n/2)`. -/
lemma norm_triFactor (n : ℕ) (p : ℝ) (Z ξ Z' ξ' : Spinor) :
    ‖triFactor n p Z ξ Z' ξ'‖ = triWeight ((n : ℝ) / 2) Z ξ Z' ξ' := by
  have hex : ‖Complex.exp (Complex.I * p * (Real.log (‖Z'‖ ^ 2 / ‖Z‖ ^ 2) : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]; simp
  unfold triFactor triWeight triReal
  rw [norm_mul, hex, mul_one, norm_div, norm_pow, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have hq : 0 ≤ (‖inner ℂ Z ξ‖ * ‖inner ℂ (jMap ξ') Z'‖) / (‖Z‖ * ‖Z'‖) := by positivity
  have e : ‖inner ℂ Z ξ‖ ^ 2 * ‖inner ℂ (jMap ξ') Z'‖ ^ 2 / (‖Z‖ ^ 2 * ‖Z'‖ ^ 2) =
      ((‖inner ℂ Z ξ‖ * ‖inner ℂ (jMap ξ') Z'‖) / (‖Z‖ * ‖Z'‖)) ^ (2 : ℕ) := by
    rw [div_pow]; ring
  rw [e, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hq]
  have : ((2 : ℕ) : ℝ) * ((n : ℝ) / 2) = n := by push_cast; ring
  rw [this, Real.rpow_natCast, div_pow]


/-- `n x^(n-1) y = n x^n (y/x)` for `x ≠ 0`, also for `n = 0`. -/
lemma pow_pred_mul {K : Type*} [Field K] (n : ℕ) {x : K} (hx : x ≠ 0) (y : K) :
    (n : K) * x ^ (n - 1) * y = (n : K) * x ^ n * (y / x) := by
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel, pow_succ]
    field_simp

lemma inner_line_left (Z W ξ : Spinor) (t : ℝ) :
    inner ℂ (Z + t • W) ξ = inner ℂ Z ξ + (t : ℂ) * inner ℂ W ξ := by
  rw [inner_add_left, ← Complex.coe_smul, inner_smul_left]; simp

lemma norm_line_sq (Z W : Spinor) (t : ℝ) :
    ‖Z + t • W‖ ^ 2 = ‖Z‖ ^ 2 + 2 * t * (inner ℂ Z W).re + t ^ 2 * ‖W‖ ^ 2 := by
  have h := @norm_add_sq ℂ _ _ _ _ Z (t • W)
  rw [h, inner_smul_right_eq_smul]
  simp [norm_smul, mul_pow]
  ring

lemma hasDerivAt_norm_line_sq (Z W : Spinor) :
    HasDerivAt (fun t : ℝ => ‖Z + t • W‖ ^ 2) (2 * (inner ℂ Z W).re) 0 := by
  have : (fun t : ℝ => ‖Z + t • W‖ ^ 2) =
      fun t => ‖Z‖ ^ 2 + 2 * (inner ℂ Z W).re * t + ‖W‖ ^ 2 * t ^ 2 := by
    funext t; rw [norm_line_sq]; ring
  rw [this]
  have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * (inner ℂ Z W).re)).const_add (‖Z‖ ^ 2)
  have h2 := (hasDerivAt_pow 2 (0 : ℝ)).const_mul (‖W‖ ^ 2)
  exact (h1.add h2).congr_deriv (by simp)

/-- **The log derivative of the triangle factor along `Z + tW`** (BDFHP Section 4.2.2): at `t = 0`,
`d/dt triFactor = triFactor · (n ⟨W,ξ⟩/⟨Z,ξ⟩ - (n + 2ip) Re⟨Z,W⟩/‖Z‖²)`. -/
theorem hasDerivAt_triFactor (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (W : Spinor) (hZ : Z ≠ 0)
    (hZ' : Z' ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    HasDerivAt (fun t : ℝ => triFactor n p (Z + t • W) ξ Z' ξ')
      (triFactor n p Z ξ Z' ξ' *
        ((n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) -
          ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ Z W).re / ‖Z‖ ^ 2 : ℝ) : ℂ))) 0 := by
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  set c := inner ℂ (jMap ξ') Z' with hc
  set R := (inner ℂ Z W).re with hR
  have hN := hasDerivAt_norm_line_sq Z W
  have hN0 : ‖Z + (0 : ℝ) • W‖ ^ 2 = ‖Z‖ ^ 2 := by simp
  have hNpos : 0 < ‖Z‖ ^ 2 := by positivity
  -- the factors
  have hg : HasDerivAt (fun t : ℝ => inner ℂ Z ξ + (t : ℂ) * inner ℂ W ξ) (inner ℂ W ξ) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const (inner ℂ W ξ)).const_add (inner ℂ Z ξ)
    simpa using this
  have hf1 := ((hg.mul_const c).pow n)
  have hs0 : Real.sqrt (‖Z + (0 : ℝ) • W‖ ^ 2) = ‖Z‖ := by
    rw [hN0, Real.sqrt_sq hz.le]
  have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (‖Z + t • W‖ ^ 2))
      (2 * R / (2 * ‖Z‖)) 0 := by
    have := HasDerivAt.sqrt hN (by rw [hN0]; exact hNpos.ne')
    rwa [hs0] at this
  have hr := ((hsq.mul_const ‖Z'‖).pow n)
  have hlog : HasDerivAt (fun t : ℝ => Real.log (‖Z'‖ ^ 2 / ‖Z + t • W‖ ^ 2))
      (-(2 * R) / ‖Z‖ ^ 2) 0 := by
    have hd := (hasDerivAt_const (0 : ℝ) (‖Z'‖ ^ 2)).div hN
      (show ‖Z + (0 : ℝ) • W‖ ^ 2 ≠ 0 by rw [hN0]; exact hNpos.ne')
    have hd2 := hd.log (show ‖Z'‖ ^ 2 / ‖Z + (0 : ℝ) • W‖ ^ 2 ≠ 0 by
      rw [hN0]; positivity)
    refine hd2.congr_deriv ?_
    simp only [Pi.div_apply, zero_smul, add_zero, hR]
    field_simp
    ring
  have hden := hr.ofReal_comp
  have hE := (((hlog.ofReal_comp).const_mul (Complex.I * p)).cexp)
  have hden0 : ((((Real.sqrt (‖Z + (0 : ℝ) • W‖ ^ 2) * ‖Z'‖) ^ n : ℝ)) : ℂ) ≠ 0 := by
    rw [hs0]; exact_mod_cast (pow_pos (mul_pos hz hz') n).ne'
  have hmain := (hf1.div hden hden0).mul hE
  have hfun : (fun t : ℝ => triFactor n p (Z + t • W) ξ Z' ξ') =
      ((fun y : ℝ => (inner ℂ Z ξ + (y : ℂ) * inner ℂ W ξ) * c) ^ n /
        fun y : ℝ => (((((fun y : ℝ => Real.sqrt (‖Z + y • W‖ ^ 2) * ‖Z'‖) ^ n) y : ℝ)) : ℂ)) *
      fun y : ℝ => Complex.exp (Complex.I * p * ((Real.log (‖Z'‖ ^ 2 / ‖Z + y • W‖ ^ 2) : ℝ) : ℂ)) := by
    funext t
    simp only [triFactor, Pi.mul_apply, Pi.div_apply, Pi.pow_apply, inner_line_left,
      Real.sqrt_sq (norm_nonneg _)]
    push_cast
    rfl
  rw [hfun]
  refine hmain.congr_deriv ?_
  have hA : inner ℂ Z ξ * c ≠ 0 := mul_ne_zero h1 h2
  have hB : ‖Z‖ * ‖Z'‖ ≠ 0 := (mul_pos hz hz').ne'
  have e1 := pow_pred_mul n hA (inner ℂ W ξ * c)
  have e2 := pow_pred_mul n hB (2 * R / (2 * ‖Z‖) * ‖Z'‖)
  have hn1 : inner ℂ W ξ * c / (inner ℂ Z ξ * c) = inner ℂ W ξ / inner ℂ Z ξ := by
    field_simp
  rw [hn1] at e1
  have hn2 : 2 * R / (2 * ‖Z‖) * ‖Z'‖ / (‖Z‖ * ‖Z'‖) = R / ‖Z‖ ^ 2 := by
    field_simp
  rw [hn2] at e2
  have hBn : (((‖Z‖ * ‖Z'‖) ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos (mul_pos hz hz') n).ne'
  have hsq0 : Real.sqrt (‖Z‖ ^ 2) = ‖Z‖ := Real.sqrt_sq hz.le
  simp only [zero_smul, add_zero, hsq0, Complex.ofReal_zero, zero_mul, Pi.pow_apply,
    Pi.div_apply] at *
  have e2c : (((n : ℝ) * (‖Z‖ * ‖Z'‖) ^ (n - 1) * (2 * R / (2 * ‖Z‖) * ‖Z'‖) : ℝ) : ℂ) =
      (((n : ℝ) * (‖Z‖ * ‖Z'‖) ^ n * (R / ‖Z‖ ^ 2) : ℝ) : ℂ) := by rw [e2]
  rw [e2c]
  unfold triFactor
  rw [e1]
  push_cast
  field_simp
  ring

/-! ### Infinitesimal group variations -/

/-- The spin vector (the unit normal, for a unit spinor) `n_i = ⟨ξ, σ_i ξ⟩` of a spinor. -/
noncomputable def spinVec (ξ : Spinor) : Fin 3 → ℝ
  | 0 => 2 * (conj (ξ 0) * ξ 1).re
  | 1 => 2 * (conj (ξ 0) * ξ 1).im
  | 2 => ‖ξ 0‖ ^ 2 - ‖ξ 1‖ ^ 2

/-- The element `½ Σ c_i σ_i` of `sl₂(ℂ)` with complex coefficients `c = β + iα`, acting on
spinors. Its anti-Hermitian part `α · J` generates rotations and its Hermitian part `β · K`
boosts. -/
noncomputable def gen (c : Fin 3 → ℂ) : Spinor →ₗ[ℂ] Spinor where
  toFun ξ := !₂[c 2 / 2 * ξ 0 + (c 0 - Complex.I * c 1) / 2 * ξ 1,
    (c 0 + Complex.I * c 1) / 2 * ξ 0 + -(c 2) / 2 * ξ 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

lemma gen_apply_zero (c : Fin 3 → ℂ) (ξ : Spinor) :
    gen c ξ 0 = c 2 / 2 * ξ 0 + (c 0 - Complex.I * c 1) / 2 * ξ 1 := rfl

lemma gen_apply_one (c : Fin 3 → ℂ) (ξ : Spinor) :
    gen c ξ 1 = (c 0 + Complex.I * c 1) / 2 * ξ 0 + -(c 2) / 2 * ξ 1 := rfl

/-- `⟨ξ, L ξ⟩ = ½ Σ c_i n_i`. -/
lemma inner_gen_self (c : Fin 3 → ℂ) (ξ : Spinor) :
    inner ℂ ξ (gen c ξ) = (1 / 2 : ℂ) * ∑ i, c i * (spinVec ξ i : ℂ) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_three, gen_apply_zero,
    gen_apply_one, spinVec]
  simp only [RCLike.inner_apply]
  set a := ξ.ofLp 0
  set b := ξ.ofLp 1
  have h1 : (((2 * (conj a * b).re : ℝ)) : ℂ) = conj a * b + a * conj b := by
    have := Complex.add_conj (conj a * b)
    simp only [map_mul, Complex.conj_conj] at this
    rw [this]
  have h2 : (((2 * (conj a * b).im : ℝ)) : ℂ) = -Complex.I * (conj a * b - a * conj b) := by
    have := Complex.sub_conj (conj a * b)
    simp only [map_mul, Complex.conj_conj] at this
    rw [this]; push_cast
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (2 * (conj a * b).im : ℂ) * hI
  have h3 : ((‖a‖ ^ 2 - ‖b‖ ^ 2 : ℝ) : ℂ) = a * conj a - b * conj b := by
    rw [Complex.mul_conj, Complex.mul_conj]
    push_cast
    simp [Complex.normSq_eq_norm_sq]
  rw [h1, h2, h3]
  ring_nf

/-- The logarithmic derivative of a triangle factor under the variation
`X ↦ X exp(tL)` with `L = gen c`, at a point where `Z` is parallel to `ξ`:
`(n/2) Σ c_i n_i - (n + 2ip)/2 Σ Re(c_i) n_i`, where `n_i` is the spin vector of `ξ`. -/
noncomputable def logDeriv (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) (ξ : Spinor) : ℂ :=
  ((n : ℂ) / 2) * ∑ i, c i * (spinVec ξ i : ℂ) -
    (((n : ℂ) + 2 * Complex.I * p) / 2) * ∑ i, ((c i).re * spinVec ξ i : ℝ)

/-- The variation of `Z = X† z` is `Z ↦ Z + t L† Z` to first order. At a point with `Z = λ ξ`,
`‖ξ‖ = 1`, the derivative of the triangle factor is `logDeriv` times the factor. -/
theorem hasDerivAt_triFactor_gen (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) {ξ Z' ξ' : Spinor} {lam : ℂ}
    (hlam : lam ≠ 0) (hξ : ‖ξ‖ = 1) (hZ' : Z' ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    HasDerivAt (fun t : ℝ =>
        triFactor n p (lam • ξ + t • LinearMap.adjoint (gen c) (lam • ξ)) ξ Z' ξ')
      (triFactor n p (lam • ξ) ξ Z' ξ' * logDeriv n p c ξ) 0 := by
  have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξ
  have hZ : lam • ξ ≠ 0 := smul_ne_zero hlam hξ0
  have hin : inner ℂ ξ ξ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hl : inner ℂ (lam • ξ) ξ = conj lam := by
    rw [inner_smul_left, hin, mul_one]
  have h1 : inner ℂ (lam • ξ) ξ ≠ 0 := by rw [hl]; simpa using hlam
  have hd := hasDerivAt_triFactor n p (LinearMap.adjoint (gen c) (lam • ξ)) hZ hZ' h1 h2
  refine hd.congr_deriv ?_
  congr 1
  unfold logDeriv
  have hW : inner ℂ (LinearMap.adjoint (gen c) (lam • ξ)) ξ =
      conj lam * inner ℂ ξ (gen c ξ) := by
    rw [LinearMap.adjoint_inner_left, inner_smul_left]
  have hZW : inner ℂ (lam • ξ) (LinearMap.adjoint (gen c) (lam • ξ)) =
      conj (conj lam * lam * inner ℂ ξ (gen c ξ)) := by
    rw [← inner_conj_symm, LinearMap.adjoint_inner_left, map_smul, inner_smul_left,
      inner_smul_right]
    simp
    ring
  have hnl : ‖lam • ξ‖ ^ 2 = ‖lam‖ ^ 2 := by rw [norm_smul, hξ, mul_one]
  have hlam0 : ‖lam‖ ^ 2 ≠ 0 := by positivity
  have hq : (inner ℂ ξ (gen c ξ)).re = (1 / 2 : ℝ) * ∑ i, ((c i).re * spinVec ξ i : ℝ) := by
    rw [inner_gen_self]
    simp [Complex.re_sum, Finset.mul_sum]
  have hre : (inner ℂ (lam • ξ) (LinearMap.adjoint (gen c) (lam • ξ))).re =
      ‖lam‖ ^ 2 * (inner ℂ ξ (gen c ξ)).re := by
    rw [hZW, Complex.conj_re, Complex.conj_mul']
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rw [hW, hl, hre, hnl, hq, inner_gen_self]
  have hc : (conj lam) ≠ 0 := by simpa using hlam
  have hl0 : (‖lam‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hlam
  push_cast
  field_simp

/-! ### The target side of a triangle -/

/-- `J` is antiunitary: `⟨Jx, Jy⟩ = conj ⟨x, y⟩`. -/
lemma inner_jMap_jMap (x y : Spinor) : inner ℂ (jMap x) (jMap y) = conj (inner ℂ x y) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, jMap_zero_apply,
    jMap_one_apply, map_add, map_mul, map_neg, Complex.conj_conj]
  ring

/-- Swapping the roles of the two ends of a triangle: `J` turns `⟨Jξ', Z'⟩` into `⟨J Z', ξ'⟩` up
to a sign, and `p` becomes `-p`. -/
lemma triFactor_swap (n : ℕ) (p : ℝ) (Z ξ Z' ξ' : Spinor) :
    triFactor n p Z ξ Z' ξ' = (-1) ^ n * triFactor n (-p) (jMap Z') ξ' (jMap Z) ξ := by
  have e1 : inner ℂ (jMap ξ') Z' = -inner ℂ (jMap Z') ξ' := by
    have : Z' = -jMap (jMap Z') := by rw [jMap_jMap]; simp
    conv_lhs => rw [this]
    rw [inner_neg_right, inner_jMap_jMap, inner_conj_symm]
  have e2 : inner ℂ (jMap ξ) (jMap Z) = inner ℂ Z ξ := by
    rw [inner_jMap_jMap, inner_conj_symm]
  unfold triFactor
  rw [e1, e2, norm_jMap, norm_jMap, mul_comm ‖Z'‖ ‖Z‖, mul_neg, neg_pow]
  have hl : Real.log (‖Z‖ ^ 2 / ‖Z'‖ ^ 2) = -Real.log (‖Z'‖ ^ 2 / ‖Z‖ ^ 2) := by
    rw [← Real.log_inv, inv_div]
  rw [hl]
  push_cast
  ring_nf

/-- `J` intertwines `gen d` with `gen (-conj d)`; on `su(2)` (`d` imaginary) it commutes. -/
lemma jMap_gen (d : Fin 3 → ℂ) (ξ : Spinor) :
    jMap (gen d ξ) = gen (fun i => -conj (d i)) (jMap ξ) := by
  ext i
  fin_cases i
  · simp [gen_apply_zero, gen_apply_one, map_ofNat]
    ring
  · simp [gen_apply_zero, gen_apply_one, map_ofNat]
    ring

/-- The adjoint of `gen c` is `gen (conj c)`. -/
lemma adjoint_gen (c : Fin 3 → ℂ) :
    LinearMap.adjoint (gen c) = gen (fun i => conj (c i)) := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, gen_apply_zero,
    gen_apply_one, map_add, map_mul, map_div₀, map_neg, Complex.conj_conj, Complex.conj_I,
    map_sub, map_ofNat]
  ring

lemma jMap_add (x y : Spinor) : jMap (x + y) = jMap x + jMap y := by
  ext i; fin_cases i <;> simp; ring

lemma jMap_real_smul (t : ℝ) (x : Spinor) : jMap (t • x) = t • jMap x := by
  ext i; fin_cases i <;> simp

/-- The log derivative is unchanged by `(p, c) ↦ (-p, -conj c)`. -/
lemma logDeriv_neg_conj (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) (ξ : Spinor) :
    logDeriv n (-p) (fun i => -conj (c i)) ξ = logDeriv n p c ξ := by
  unfold logDeriv
  have h1 : ∑ i, (-conj (c i)) * (spinVec ξ i : ℂ) =
      -(2 * ∑ i, ((c i).re : ℂ) * (spinVec ξ i : ℂ)) + ∑ i, c i * (spinVec ξ i : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := Complex.add_conj (c i)
    push_cast at h
    linear_combination (-(spinVec ξ i : ℂ)) * h
  have h2 : ∑ i, (((-conj (c i)).re * spinVec ξ i : ℝ)) =
      -∑ i, (((c i).re * spinVec ξ i : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have h3 : ∑ i, (((c i).re : ℂ) * (spinVec ξ i : ℂ)) =
      ((∑ i, ((c i).re * spinVec ξ i : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h1, h2, ← h3]
  push_cast
  ring

/-- The target side: if `J Z' = μ ξ'` (that is, `Z'` is parallel to `J ξ'`), the derivative of the
triangle factor under `Z' ↦ Z' + t L† Z'` is the same `logDeriv` of the spin vector of `ξ'`. -/
theorem hasDerivAt_triFactor_gen_target (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) {Z ξ ξ' : Spinor}
    (Z' : Spinor) {μ : ℂ} (hμ : μ ≠ 0) (hξ' : ‖ξ'‖ = 1) (hZ : Z ≠ 0)
    (h1 : inner ℂ Z ξ ≠ 0) (hY : jMap Z' = μ • ξ') :
    HasDerivAt (fun t : ℝ =>
        triFactor n p Z ξ (Z' + t • LinearMap.adjoint (gen c) Z') ξ')
      (triFactor n p Z ξ Z' ξ' * logDeriv n p c ξ') 0 := by
  set c₂ : Fin 3 → ℂ := fun i => -conj (c i) with hc₂
  have hJZ : jMap Z ≠ 0 := jMap_ne_zero hZ
  have e2 : inner ℂ (jMap ξ) (jMap Z) = inner ℂ Z ξ := by
    rw [inner_jMap_jMap, inner_conj_symm]
  have hd := hasDerivAt_triFactor_gen n (-p) c₂ (ξ := ξ') (Z' := jMap Z) (ξ' := ξ) hμ hξ' hJZ
    (by rw [e2]; exact h1)
  have hfun : (fun t : ℝ => triFactor n p Z ξ (Z' + t • LinearMap.adjoint (gen c) Z') ξ') =
      fun t : ℝ => (-1 : ℂ) ^ n * triFactor n (-p)
        (μ • ξ' + t • LinearMap.adjoint (gen c₂) (μ • ξ')) ξ' (jMap Z) ξ := by
    funext t
    rw [triFactor_swap, jMap_add, jMap_real_smul, hY, adjoint_gen, jMap_gen, adjoint_gen, hY]
    congr 4
  rw [hfun]
  have := (hd.const_mul ((-1 : ℂ) ^ n))
  refine this.congr_deriv ?_
  rw [← logDeriv_neg_conj n p c ξ', triFactor_swap n p Z ξ Z' ξ', hY]
  ring

/-! ### Stationarity at a vertex -/

/-- With `c = β + iα`, `logDeriv = i (n/2 · α·n̂ - p · β·n̂)`: rotations (`α`) see the spin `n/2`,
boosts (`β`) see the Immirzi-type parameter `p`. -/
lemma logDeriv_eq (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) (ξ : Spinor) :
    logDeriv n p c ξ = Complex.I * (((n : ℂ) / 2) * ((∑ i, (c i).im * spinVec ξ i : ℝ) : ℂ) -
      (p : ℂ) * ((∑ i, (c i).re * spinVec ξ i : ℝ) : ℂ)) := by
  unfold logDeriv
  have h : ∑ i, c i * (spinVec ξ i : ℂ) =
      ((∑ i, (c i).re * spinVec ξ i : ℝ) : ℂ) + Complex.I * ((∑ i, (c i).im * spinVec ξ i : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [← Complex.re_add_im (c i)]
    ring
  rw [h]
  ring

/-- **Stationarity in the group variables at one vertex.** The first variation of the sum of the
triangle log factors vanishes in every direction `L = gen c` of `sl₂(ℂ)` exactly when the
rotation part gives closure of the spin vectors, `Σ n_e n̂_e = 0`, and the boost part gives
`Σ p_e n̂_e = 0`. -/
theorem stationary_iff {ι : Type*} [Fintype ι] (n : ι → ℕ) (p : ι → ℝ) (ξ : ι → Spinor) :
    (∀ c : Fin 3 → ℂ, ∑ e, logDeriv (n e) (p e) c (ξ e) = 0) ↔
      (∀ j, ∑ e, (n e : ℝ) * spinVec (ξ e) j = 0) ∧ (∀ j, ∑ e, p e * spinVec (ξ e) j = 0) := by
  have key : ∀ c : Fin 3 → ℂ, ∑ e, logDeriv (n e) (p e) c (ξ e) =
      Complex.I * ((∑ i, ((1 / 2 : ℝ) * (c i).im * ∑ e, (n e : ℝ) * spinVec (ξ e) i -
        (c i).re * ∑ e, p e * spinVec (ξ e) i : ℝ) : ℝ) : ℂ) := by
    intro c
    simp only [logDeriv_eq]
    rw [← Finset.mul_sum]
    congr 1
    have hR : ∑ e, ((n e : ℝ) / 2 * ∑ i, (c i).im * spinVec (ξ e) i -
        p e * ∑ i, (c i).re * spinVec (ξ e) i) =
        ∑ i, ((1 / 2 : ℝ) * (c i).im * ∑ e, (n e : ℝ) * spinVec (ξ e) i -
          (c i).re * ∑ e, p e * spinVec (ξ e) i) := by
      calc _ = ∑ e, ∑ i, ((n e : ℝ) / 2 * ((c i).im * spinVec (ξ e) i) -
              p e * ((c i).re * spinVec (ξ e) i)) := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        _ = ∑ i, ∑ e, ((n e : ℝ) / 2 * ((c i).im * spinVec (ξ e) i) -
              p e * ((c i).re * spinVec (ξ e) i)) := Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun e _ => ?_
            ring
    have := congrArg (Complex.ofReal) hR
    push_cast at this ⊢
    exact this
  constructor
  · intro h
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have h0 := (mul_eq_zero.mp (key _ ▸ h (Pi.single j Complex.I))).resolve_left
        Complex.I_ne_zero
      have h1 := Complex.ofReal_eq_zero.mp h0
      simp [Pi.single_apply, apply_ite Complex.im, apply_ite Complex.re] at h1
      simpa using h1
    · have h0 := (mul_eq_zero.mp (key _ ▸ h (Pi.single j 1))).resolve_left Complex.I_ne_zero
      have h1 := Complex.ofReal_eq_zero.mp h0
      simp [Pi.single_apply, apply_ite Complex.im, apply_ite Complex.re] at h1
      simpa using h1
  · rintro ⟨hN, hP⟩ c
    rw [key]
    simp [hN, hP]

/-- **Closure from stationarity.** With `p_e = γ n_e / 2` (that is, `p = γ k` for the spin
`k = n/2`), stationarity in all group directions is exactly the closure
`Σ_e k_e n̂_e = 0` of the normals. -/
theorem stationary_iff_closure {ι : Type*} [Fintype ι] (n : ι → ℕ) (γ : ℝ)
    (ξ : ι → Spinor) :
    (∀ c : Fin 3 → ℂ, ∑ e, logDeriv (n e) (γ * ((n e : ℝ) / 2)) c (ξ e) = 0) ↔
      ∀ j, ∑ e, (n e : ℝ) * spinVec (ξ e) j = 0 := by
  rw [stationary_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, fun j => ?_⟩⟩
  have : ∑ e, γ * ((n e : ℝ) / 2) * spinVec (ξ e) j =
      γ / 2 * ∑ e, (n e : ℝ) * spinVec (ξ e) j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
  rw [this, h j, mul_zero]

/-! ### Trust checks and examples -/

/-- The spin vector of the basis spinors `e₀`, `e₁` is `±ẑ`. -/
lemma spinVec_e0 : spinVec e0 = ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [spinVec, e0]

lemma spinVec_e1 : spinVec e1 = ![0, 0, -1] := by
  ext i
  fin_cases i <;> simp [spinVec, e1]

/-- `J` reverses the spin vector: `n̂(Jξ) = -n̂(ξ)`. -/
lemma spinVec_jMap (ξ : Spinor) (i : Fin 3) : spinVec (jMap ξ) i = -spinVec ξ i := by
  fin_cases i
  · simp [spinVec]; ring_nf
  · simp [spinVec]; ring_nf
  · simp [spinVec]

/-- Non-vacuity: two opposite triangles with equal spin satisfy the stationarity condition for
every direction. -/
example (n : ℕ) (γ : ℝ) (c : Fin 3 → ℂ) :
    ∑ e : Fin 2, logDeriv n (γ * ((n : ℝ) / 2)) c (![e0, e1] e) = 0 := by
  have h := (stationary_iff (ι := Fin 2) (fun _ => n) (fun _ => γ * ((n : ℝ) / 2))
    ![e0, e1]).mpr
  refine h ⟨fun j => ?_, fun j => ?_⟩ c
  · fin_cases j <;> simp [Fin.sum_univ_two, spinVec_e0, spinVec_e1]
  · fin_cases j <;> simp [Fin.sum_univ_two, spinVec_e0, spinVec_e1]

/-- Wrong-model control: a single triangle of positive spin is not stationary, and the direction
that detects it is a rotation about `ẑ`. -/
example (n : ℕ) (hn : 0 < n) (p : ℝ) :
    logDeriv n p (fun i => if i = 2 then Complex.I else 0) e0 ≠ 0 := by
  rw [logDeriv_eq]
  simp [Fin.sum_univ_three, spinVec_e0, hn.ne']

end Lightlike.Asymptotics.Lorentzian
