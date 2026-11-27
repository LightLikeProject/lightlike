module

public import Lightlike.Lorentz.SL2RIrreducible.Criterion
public import Lightlike.Lorentz.SL2RPrincipal
public import Lightlike.Lorentz.SL2RCasimir

/-!
# The `K`-weight vectors of the principal series of `SL(2,ℝ)`, both parities

In the non-compact picture `L²(ℝ)` of `principalSeries ε ν` (multiplier `|t|^{iν-1} sgn(t)^ε`), put
`s = (iν - 1 - ε)/2` and

  `e_k(x) = (1 + x²)^s (x - i)^{k+ε} (x + i)^{-k}`,   `k ∈ ℤ`.

These are the vectors of `K`-weight `2k + ε` (`principalSeries_rot_weightL2`: `π(k_θ) e_k = e^{-i(2k+ε)θ}
e_k`), with `‖e_k(x)‖ = (1 + x²)^{-1/2}` (`norm_weightVec`), so `e_k ∈ L²`. One formula covers the even
(`ε = 0`) and the odd (`ε = 1`) principal series; for `ε = 0` it is the function
`(1 + x²)^{(iν-1)/2} ((x - i)/(x + i))^k` of `kVecP`, for `ε = 1` it is the half-integer `K`-type vector
`(1 + x²)^{(iν-1)/2} ((x - i)/(x + i))^{k+1/2}` written without a branch of the square root.

The derivative of `e_k` is `e_k'(x) = e_k(x) [(2s + ε) x + i(2k + ε)]/(1 + x²)` and gives the ladder
relation `x e_k' - w e_k = ((s - k)/2) e_{k+1} + ((s + k + ε)/2) e_{k-1}`, `w = (iν - 1)/2`
(`ladder_weightVec` in `PrincipalLadder.lean`; Kitaev, arXiv:1711.08169, Eq. (15), with
`m = k + ε/2`, `λ = 1/2 + iν/2`: the product `⟨m|L_{-1}L_1|m⟩ = (m + λ)(m + 1 - λ)` of Eq. (9) equals
`|s - k|²`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The exponent `s = (iν - 1 - ε)/2` of `1 + x²` in the weight vectors. -/
def weightExp (ε : ℤ) (ν : ℝ) : ℂ := (I * ν - 1 - ε) / 2

/-- **The `K`-weight vector** `e_k(x) = (1 + x²)^s (x - i)^{k+ε} (x + i)^{-k}` of weight `2k + ε` of the
principal series `P^{ε,iν}` (both parities; the power of `1 + x²` is written `exp(s log(1 + x²))`). -/
def weightVec (ε : ℤ) (ν : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (weightExp ε ν * (Real.log (1 + x ^ 2) : ℝ)) * ((x : ℂ) - I) ^ (k + ε) *
    ((x : ℂ) + I) ^ (-k)

variable (ε : ℤ) (ν : ℝ) (k : ℤ)

lemma ofReal_sub_I_ne_zero' (x : ℝ) : (x : ℂ) - I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

lemma ofReal_add_I_ne_zero' (x : ℝ) : (x : ℂ) + I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

lemma norm_sub_I (x : ℝ) : ‖(x : ℂ) - I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring

lemma norm_add_I (x : ℝ) : ‖(x : ℂ) + I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]; congr 1; simp; ring

lemma one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by positivity

lemma exp_zpow (y : ℝ) (n : ℤ) : Real.exp y ^ n = Real.exp (y * n) := by
  rw [← Real.rpow_intCast, ← Real.exp_mul]

/-- **The modulus** `‖e_k(x)‖ = (1 + x²)^{-1/2}`. -/
theorem norm_weightVec (x : ℝ) : ‖weightVec ε ν k x‖ = Real.exp (-Real.log (1 + x ^ 2) / 2) := by
  have hR := one_add_sq_pos x
  have hr : Real.sqrt (1 + x ^ 2) = Real.exp (Real.log (1 + x ^ 2) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hR]; congr 1; ring
  unfold weightVec
  rw [norm_mul, norm_mul, norm_zpow, norm_zpow, norm_sub_I, norm_add_I, Complex.norm_exp, hr]
  have hre : (weightExp ε ν * ((Real.log (1 + x ^ 2) : ℝ) : ℂ)).re =
      (-1 - (ε : ℝ)) / 2 * Real.log (1 + x ^ 2) := by
    simp [weightExp, Complex.mul_re]
  rw [hre, exp_zpow, exp_zpow, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem norm_weightVec_sq (x : ℝ) : ‖weightVec ε ν k x‖ ^ 2 = (1 + x ^ 2)⁻¹ := by
  rw [norm_weightVec, sq, ← Real.exp_add, show -Real.log (1 + x ^ 2) / 2 + -Real.log (1 + x ^ 2) / 2 =
    -Real.log (1 + x ^ 2) by ring, Real.exp_neg, Real.exp_log (one_add_sq_pos x)]

lemma weightVec_ne_zero (x : ℝ) : weightVec ε ν k x ≠ 0 := by
  intro h
  have := norm_weightVec_sq ε ν k x
  rw [h, norm_zero] at this
  have h2 : (0 : ℝ) < (1 + x ^ 2)⁻¹ := inv_pos.mpr (one_add_sq_pos x)
  linarith

lemma continuous_weightVec : Continuous (weightVec ε ν k) := by
  unfold weightVec
  refine ((Complex.continuous_exp.comp (continuous_const.mul ?_)).mul ?_).mul ?_
  · exact Complex.continuous_ofReal.comp (Continuous.log (by fun_prop) fun x => (one_add_sq_pos x).ne')
  · exact Continuous.zpow₀ (by fun_prop) _ fun x => Or.inl (ofReal_sub_I_ne_zero' x)
  · exact Continuous.zpow₀ (by fun_prop) _ fun x => Or.inl (ofReal_add_I_ne_zero' x)

theorem memLp_weightVec : MemLp (weightVec ε ν k) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_weightVec ε ν k).aestronglyMeasurable]
  simp_rw [norm_weightVec_sq]
  exact integrable_inv_one_add_sq

/-- **The weight vector `e_k` as an element of `L²(ℝ)`.** -/
def weightL2 : L2R := (memLp_weightVec ε ν k).toLp (weightVec ε ν k)

lemma weightL2_ae : (weightL2 ε ν k : ℝ → ℂ) =ᵐ[volume] weightVec ε ν k :=
  (memLp_weightVec ε ν k).coeFn_toLp

lemma weightL2_ne_zero : weightL2 ε ν k ≠ 0 := by
  intro h
  have h0 : weightVec ε ν k =ᵐ[volume] 0 := by
    have := weightL2_ae ε ν k
    rw [h] at this
    exact (this.symm.trans (Lp.coeFn_zero _ _ _))
  have hc := continuous_weightVec ε ν k
  have := (Continuous.ae_eq_iff_eq volume hc continuous_const).mp h0
  exact weightVec_ne_zero ε ν k 0 (congrFun this 0)

/-! ## The step `e_k ↦ e_{k±1}` -/

lemma weightVec_succ (x : ℝ) :
    weightVec ε ν (k + 1) x = weightVec ε ν k x * (((x : ℂ) - I) / ((x : ℂ) + I)) := by
  have h1 := ofReal_sub_I_ne_zero' x
  have h2 := ofReal_add_I_ne_zero' x
  unfold weightVec
  rw [show k + 1 + ε = (k + ε) + 1 by ring, show -(k + 1) = -k + -1 by ring, zpow_add₀ h1, zpow_add₀ h2]
  simp only [zpow_one, zpow_neg_one]
  ring

lemma weightVec_pred (x : ℝ) :
    weightVec ε ν (k - 1) x = weightVec ε ν k x * (((x : ℂ) + I) / ((x : ℂ) - I)) := by
  have h1 := ofReal_sub_I_ne_zero' x
  have h2 := ofReal_add_I_ne_zero' x
  unfold weightVec
  rw [show k - 1 + ε = (k + ε) + (-1) by ring, show -(k - 1) = -k + 1 by ring, zpow_add₀ h1,
    zpow_add₀ h2]
  simp only [zpow_one, zpow_neg_one]
  ring

/-! ## The rotations act on `e_k` by the character `e^{-i(2k+ε)θ}` -/

/-- The algebra behind `mult_mul_weightVec`: all the powers are atoms. -/
lemma alg_aux (X1 X2 E Aε Dε Dm Dn Pm Qn um vn : ℂ) (hA : Aε ≠ 0) (hDm : Dm ≠ 0) (hDn : Dn ≠ 0)
    (hexp : X1 * X2 = Aε * E) (hDmn : Dm * Dn = Dε) :
    X1 * (Dε / Aε) * (X2 * (Pm * um / Dm) * (Qn * vn / Dn)) = um * vn * (E * Pm * Qn) := by
  calc X1 * (Dε / Aε) * (X2 * (Pm * um / Dm) * (Qn * vn / Dn))
      = (X1 * X2) * Dε * (Pm * um * Qn * vn) / (Aε * Dm * Dn) := by ring
    _ = (Aε * E) * (Dm * Dn) * (Pm * um * Qn * vn) / (Aε * Dm * Dn) := by rw [hexp, hDmn]
    _ = um * vn * (E * Pm * Qn) := by field_simp

/-- **The multiplier and the Möbius change of variable on `e_k`.** If `n - i d = (x - i) u`,
`n + i d = (x + i) v` and `d² + n² = 1 + x²` (the situation of a rotation, with `u = e^{-iθ}`,
`v = e^{iθ}`), then `m(d) e_k(n/d) = u^{k+ε} v^{-k} e_k(x)`. -/
lemma mult_mul_weightVec {x d n : ℝ} {u v : ℂ} (hd : d ≠ 0)
    (H1 : (n : ℂ) - I * d = ((x : ℂ) - I) * u) (H2 : (n : ℂ) + I * d = ((x : ℂ) + I) * v)
    (H3 : d ^ 2 + n ^ 2 = 1 + x ^ 2) :
    mult ε ν d * weightVec ε ν k (n / d) = u ^ (k + ε) * v ^ (-k) * weightVec ε ν k x := by
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  have hA0 : ((|d| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hd)
  have hy1 : (((n / d : ℝ)) : ℂ) - I = ((x : ℂ) - I) * u / d := by
    rw [← H1]; push_cast; field_simp
  have hy2 : (((n / d : ℝ)) : ℂ) + I = ((x : ℂ) + I) * v / d := by
    rw [← H2]; push_cast; field_simp
  have hy3 : 1 + (n / d) ^ 2 = (1 + x ^ 2) / d ^ 2 := by
    rw [← H3]; field_simp
  have hlog : Real.log (1 + (n / d) ^ 2) = Real.log (1 + x ^ 2) - 2 * Real.log |d| := by
    rw [hy3, Real.log_div (one_add_sq_pos x).ne' (pow_ne_zero 2 hd), Real.log_pow, Real.log_abs]
    push_cast; ring
  have hA : ((|d| : ℝ) : ℂ) ^ (I * ν - 1) = Complex.exp ((Real.log |d| : ℝ) * (I * ν - 1)) := by
    rw [Complex.cpow_def_of_ne_zero hA0, Complex.ofReal_log (abs_nonneg d)]
  have hAexp : ((|d| : ℝ) : ℂ) = Complex.exp ((Real.log |d| : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (abs_pos.mpr hd)]
  have hexp : Complex.exp ((Real.log |d| : ℝ) * (I * ν - 1)) *
      Complex.exp (weightExp ε ν * ((Real.log (1 + x ^ 2) - 2 * Real.log |d| : ℝ) : ℂ)) =
      ((|d| : ℝ) : ℂ) ^ ε * Complex.exp (weightExp ε ν * (Real.log (1 + x ^ 2) : ℝ)) := by
    rw [← Complex.exp_add, hAexp, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    unfold weightExp
    push_cast
    ring
  have hσ : (((d / |d| : ℝ)) : ℂ) = (d : ℂ) / ((|d| : ℝ) : ℂ) := by push_cast; rfl
  have hDmn : (d : ℂ) ^ (k + ε) * (d : ℂ) ^ (-k) = (d : ℂ) ^ ε := by
    rw [← zpow_add₀ hdC]; congr 1; ring
  unfold mult weightVec
  rw [hy1, hy2, hlog, hA, hσ]
  simp only [div_zpow, mul_zpow]
  exact alg_aux _ _ _ _ _ _ _ _ _ _ _ (zpow_ne_zero _ hA0) (zpow_ne_zero _ hdC) (zpow_ne_zero _ hdC)
    hexp hDmn

lemma den_rot_eq (θ x : ℝ) : den (rot θ) x = Real.sin θ * x + Real.cos θ := by simp [den, rot]

lemma num_rot_eq (θ x : ℝ) : num (rot θ) x = Real.cos θ * x - Real.sin θ := by
  simp [num, rot, sub_eq_add_neg]

lemma exp_neg_mul_I (θ : ℝ) :
    Complex.exp (-((θ : ℂ) * I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
  have : -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast; ring

lemma exp_mul_I_real (θ : ℝ) :
    Complex.exp ((θ : ℂ) * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **`e_k` is an eigenvector of the rotation `k_θ`**, pointwise: off the pole of the Möbius map,
`(π(k_θ) e_k)(x) = e^{-i(2k+ε)θ} e_k(x)`. -/
theorem act_rot_weightVec (θ x : ℝ) (hx : den (rot θ) x ≠ 0) :
    act ε (ν : ℂ) (rot θ) (weightVec ε ν k) x =
      Complex.exp (-(((2 * k + ε : ℤ) : ℂ) * (θ : ℂ) * I)) * weightVec ε ν k x := by
  have H1 : ((num (rot θ) x : ℝ) : ℂ) - I * ((den (rot θ) x : ℝ) : ℂ) =
      ((x : ℂ) - I) * Complex.exp (-((θ : ℂ) * I)) := by
    rw [num_rot_eq, den_rot_eq, exp_neg_mul_I]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add]
    linear_combination (-(Real.sin θ : ℂ)) * Complex.I_mul_I
  have H2 : ((num (rot θ) x : ℝ) : ℂ) + I * ((den (rot θ) x : ℝ) : ℂ) =
      ((x : ℂ) + I) * Complex.exp ((θ : ℂ) * I) := by
    rw [num_rot_eq, den_rot_eq, exp_mul_I_real]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add]
    linear_combination (-(Real.sin θ : ℂ)) * Complex.I_mul_I
  have H3 : den (rot θ) x ^ 2 + num (rot θ) x ^ 2 = 1 + x ^ 2 := by
    rw [num_rot_eq, den_rot_eq]
    linear_combination (x ^ 2 + 1) * Real.sin_sq_add_cos_sq θ
  have key := mult_mul_weightVec ε ν k hx H1 H2 H3
  unfold act
  rw [mob_def, key, ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The weight vector `e_k ∈ L²(ℝ)` is an eigenvector of `π(k_θ)` with the character
`e^{-i(2k+ε)θ}`.** -/
theorem principalSeries_rot_weightL2 (θ : ℝ) :
    principalSeries ε ν (rot θ) (weightL2 ε ν k) =
      Complex.exp (-(((2 * k + ε : ℤ) : ℂ) * (θ : ℂ) * I)) • weightL2 ε ν k := by
  apply Lp.ext
  have h1 := coeFn_principalSeries ε ν (rot θ) (weightL2 ε ν k)
  have h2 := ae_eq_comp_mob (rot θ) (weightL2_ae ε ν k)
  have h3 := Lp.coeFn_smul (Complex.exp (-(((2 * k + ε : ℤ) : ℂ) * (θ : ℂ) * I))) (weightL2 ε ν k)
  have h4 := weightL2_ae ε ν k
  filter_upwards [h1, h2, h3, h4, ae_den_ne_zero (rot θ)] with x e1 e2 e3 e4 e5
  rw [e1, e3]
  simp only [Function.comp_apply] at e2
  rw [e2]
  have := act_rot_weightVec ε ν k θ x e5
  unfold act at this
  rw [this, Pi.smul_apply, e4]
  rfl

/-! ## The characters and the orthogonality of the weight vectors -/

/-- **The character** `θ ↦ e^{-i(2k+ε)θ}` of the rotation group by which `e_k` transforms. -/
def principalChar (ε k : ℤ) (θ : ℝ) : ℂ :=
  Complex.exp (-(((2 * k + ε : ℤ) : ℂ) * (θ : ℂ) * I))

/-- Different `k` give different characters. -/
lemma principalChar_ne {j k : ℤ} (h : j ≠ k) :
    ∃ θ : ℝ, principalChar ε j θ ≠ principalChar ε k θ := by
  have : ((2 * j + ε : ℤ) : ℝ) ≠ ((2 * k + ε : ℤ) : ℝ) := by
    intro h'
    exact h (by have := Int.cast_injective h'; omega)
  obtain ⟨θ, hθ⟩ := exists_exp_ne this
  exact ⟨θ, by simpa [principalChar] using hθ⟩

/-- **The weight vectors of distinct weights are orthogonal.** -/
theorem inner_weightL2_of_ne {j k : ℤ} (h : j ≠ k) : ⟪weightL2 ε ν j, weightL2 ε ν k⟫_ℂ = 0 :=
  inner_eq_zero_of_eigen (principalSeries ε ν) (principalSeries_inner ε ν) rot (weightL2 ε ν)
    (principalChar ε) (weightL2_ne_zero ε ν) (fun i θ => principalSeries_rot_weightL2 ε ν i θ)
    (fun _ _ h => principalChar_ne ε h) h (fun θ => principalSeries_rot_weightL2 ε ν k θ)

end Lightlike.Lorentz.SL2R
