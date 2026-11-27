import Mathlib
import Lightlike.Lorentz.SL2RPrincipal
import Lightlike.Lorentz.SL2RPlancherel.PolarIntegral

/-!
# The `K`-type vectors of the even principal series of `SL(2,ℝ)`

In the non-compact picture `L²(ℝ)` of `principalSeries 0 ν`, the functions
`e_k(x) = (1 + x²)^{(iν - 1)/2} ((x - i)/(x + i))^k`, `k ∈ ℤ`, are the `K`-type vectors:
`π(k_θ) e_k = e^{-2ikθ} e_k` (`act_rot_kVecP`).  The Möbius map of the rotation `k_θ` is
`x ↦ (x cos θ - sin θ)/(x sin θ + cos θ)` and multiplies `(x - i)/(x + i)` by `e^{-2iθ}`
(`mob_rot_phase`).  Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (the identification of the
block transforms with matrix coefficients), milestone HA3.
-/

open MeasureTheory Set Real Complex Lightlike.Lorentz.SL2R

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The `K`-type vectors** `e_k(x) = (1 + x²)^{(iν - 1)/2} ((x - i)/(x + i))^k` of the even
principal series with parameter `ν`. -/
def kVecP (ν : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  (((1 + x ^ 2 : ℝ)) : ℂ) ^ ((I * ν - 1) / 2) * (((x : ℂ) - I) / ((x : ℂ) + I)) ^ k

lemma den_rot (θ x : ℝ) : den (rot θ) x = Real.sin θ * x + Real.cos θ := by
  simp [den, rot]

lemma num_rot (θ x : ℝ) : num (rot θ) x = Real.cos θ * x - Real.sin θ := by
  simp [num, rot]; ring

/-- `x ± i` does not vanish for real `x`. -/
lemma ofReal_add_I_ne_zero (x : ℝ) : (x : ℂ) + I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

lemma ofReal_sub_I_ne_zero (x : ℝ) : (x : ℂ) - I ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this

/-- **The phase of the rotation**: for `den (k_θ) x ≠ 0`,
`(mob - i)/(mob + i) = e^{-2iθ} (x - i)/(x + i)` with `mob = mob (k_θ) x`. -/
theorem mob_rot_phase (θ x : ℝ) (hx : den (rot θ) x ≠ 0) :
    ((mob (rot θ) x : ℂ) - I) / ((mob (rot θ) x : ℂ) + I) =
      Complex.exp (-(2 * θ * I)) * (((x : ℂ) - I) / ((x : ℂ) + I)) := by
  set c : ℂ := (Real.cos θ : ℂ) with hc
  set sn : ℂ := (Real.sin θ : ℂ) with hs
  have hD : ((Real.sin θ * x + Real.cos θ : ℝ) : ℂ) ≠ 0 := by
    rw [← den_rot]; exact_mod_cast hx
  have hmob : (mob (rot θ) x : ℂ) =
      ((Real.cos θ * x - Real.sin θ : ℝ) : ℂ) / ((Real.sin θ * x + Real.cos θ : ℝ) : ℂ) := by
    simp only [mob, num_rot, den_rot]; push_cast; ring
  have e1 : (mob (rot θ) x : ℂ) - I = (c - I * sn) * ((x : ℂ) - I) /
      ((Real.sin θ * x + Real.cos θ : ℝ) : ℂ) := by
    rw [hmob, eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add]
    linear_combination (-sn) * Complex.I_sq
  have e2 : (mob (rot θ) x : ℂ) + I = (c + I * sn) * ((x : ℂ) + I) /
      ((Real.sin θ * x + Real.cos θ : ℝ) : ℂ) := by
    rw [hmob, eq_div_iff hD, add_mul, div_mul_cancel₀ _ hD]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_add]
    linear_combination (-sn) * Complex.I_sq
  have hcs : (c - I * sn) * (c + I * sn) = 1 := by
    have h := Real.cos_sq_add_sin_sq θ
    have h' : (c ^ 2 + sn ^ 2 : ℂ) = 1 := by simp only [hc, hs]; exact_mod_cast h
    linear_combination h' - sn ^ 2 * Complex.I_sq
  have hne : c + I * sn ≠ 0 := right_ne_zero_of_mul_eq_one hcs
  have hinv : (c + I * sn)⁻¹ = c - I * sn := (eq_inv_of_mul_eq_one_left hcs).symm
  have hexp : Complex.exp (-(2 * θ * I)) = (c - I * sn) ^ 2 := by
    have h1 : Complex.exp (-(θ * I)) = c - I * sn := by
      rw [show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
      simp only [hc, hs]; push_cast; rw [Complex.cos_neg, Complex.sin_neg]; ring
    rw [← h1, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hxI := ofReal_add_I_ne_zero x
  rw [e1, e2, hexp]
  calc (c - I * sn) * ((x : ℂ) - I) / ((Real.sin θ * x + Real.cos θ : ℝ) : ℂ) /
        ((c + I * sn) * ((x : ℂ) + I) / ((Real.sin θ * x + Real.cos θ : ℝ) : ℂ))
      = (c - I * sn) * (c + I * sn)⁻¹ * (((x : ℂ) - I) / ((x : ℂ) + I)) := by
        field_simp
    _ = (c - I * sn) ^ 2 * (((x : ℂ) - I) / ((x : ℂ) + I)) := by rw [hinv]; ring

/-- The `K`-type vectors are square integrable: `|e_k(x)|² = 1/(1 + x²)`. -/
theorem norm_kVecP (ν : ℝ) (k : ℤ) (x : ℝ) : ‖kVecP ν k x‖ = (1 + x ^ 2) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hphase : ‖((x : ℂ) - I) / ((x : ℂ) + I)‖ = 1 := by
    rw [norm_div]
    have h1 : ‖(x : ℂ) - I‖ = ‖(x : ℂ) + I‖ := by
      rw [← Complex.norm_conj ((x : ℂ) + I)]; simp [map_add, sub_eq_add_neg]
    rw [h1, div_self (norm_ne_zero_iff.mpr (ofReal_add_I_ne_zero x))]
  rw [kVecP, norm_mul, norm_zpow, hphase, one_zpow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 1
  simp

/-- `1 + mob(k_θ)(x)² = (1 + x²) / den(k_θ)(x)²`. -/
lemma one_add_mob_rot_sq (θ x : ℝ) (hx : den (rot θ) x ≠ 0) :
    1 + mob (rot θ) x ^ 2 = (1 + x ^ 2) / den (rot θ) x ^ 2 := by
  have h := Real.cos_sq_add_sin_sq θ
  have hmob : mob (rot θ) x = num (rot θ) x / den (rot θ) x := rfl
  rw [hmob, eq_div_iff (pow_ne_zero _ hx), add_mul, div_pow,
    div_mul_cancel₀ _ (pow_ne_zero _ hx), one_mul, num_rot, den_rot]
  linear_combination (1 + x ^ 2) * h

/-- **The rotations act on the `K`-type vectors by a phase**: for `den (k_θ) x ≠ 0`,
`(π(k_θ) e_k)(x) = e^{-2ikθ} e_k(x)` (even principal series). -/
theorem act_rot_kVecP (ν θ : ℝ) (k : ℤ) (x : ℝ) (hx : den (rot θ) x ≠ 0) :
    act 0 ν (rot θ) (kVecP ν k) x = Complex.exp (-(2 * k * θ * I)) * kVecP ν k x := by
  set d := den (rot θ) x with hd
  set w : ℂ := (I * ν - 1) / 2 with hw
  have had : 0 < |d| := abs_pos.mpr hx
  have hx2 : (0 : ℝ) ≤ 1 + x ^ 2 := by positivity
  -- the modulus
  have hmod : (((1 + mob (rot θ) x ^ 2 : ℝ)) : ℂ) ^ w =
      (((1 + x ^ 2 : ℝ)) : ℂ) ^ w * ((((|d| : ℝ) : ℂ)) ^ w * (((|d| : ℝ) : ℂ)) ^ w)⁻¹ := by
    have e : (1 + mob (rot θ) x ^ 2 : ℝ) = (1 + x ^ 2) * (|d| * |d|)⁻¹ := by
      rw [one_add_mob_rot_sq θ x hx, abs_mul_abs_self, div_eq_mul_inv, ← hd, sq d]
    have harg : ((((|d| * |d| : ℝ)) : ℂ)).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm
    rw [e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx2
      (inv_nonneg.2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))), Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _)]
  have hmult : mult 0 ν d = (((|d| : ℝ) : ℂ)) ^ w * (((|d| : ℝ) : ℂ)) ^ w := by
    rw [mult, zpow_zero, mul_one, show I * (ν : ℂ) - 1 = (2 : ℕ) * w by rw [hw]; push_cast; ring,
      Complex.cpow_nat_mul, sq]
  have hne : (((|d| : ℝ) : ℂ)) ^ w ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not
    intro h; exact absurd (by exact_mod_cast h) had.ne'
  rw [act, kVecP, kVecP, hmult, hmod, mob_rot_phase θ x hx, mul_zpow, ← Complex.exp_int_mul]
  have he : (k : ℂ) * -(2 * (θ : ℂ) * I) = -(2 * k * θ * I) := by ring
  rw [he]
  field_simp
  rw [hw]
  ring

lemma den_aR (ξ x : ℝ) : den (aR ξ) x = (Real.exp (ξ / 2))⁻¹ := by
  simp [den, aR, diagSL]

lemma mob_aR (ξ x : ℝ) : mob (aR ξ) x = Real.exp ξ * x := by
  have h : Real.exp ξ = Real.exp (ξ / 2) * Real.exp (ξ / 2) := by
    rw [← Real.exp_add]; ring_nf
  simp only [mob, num, den, aR, diagSL]
  simp
  rw [h]
  field_simp

/-- **The action of `a(ξ)`**: `(π(a(ξ)) f)(x) = e^{-(iν - 1) ξ / 2} f(e^ξ x)` (even principal
series). -/
theorem act_aR (ν ξ : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    act 0 ν (aR ξ) f x = Complex.exp (-((I * ν - 1) * ξ / 2)) * f (Real.exp ξ * x) := by
  rw [act, den_aR, mob_aR, mult, zpow_zero, mul_one]
  congr 1
  have habs : |(Real.exp (ξ / 2))⁻¹| = Real.exp (-(ξ / 2)) := by
    rw [abs_of_pos (inv_pos.2 (Real.exp_pos _)), Real.exp_neg]
  rw [habs, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  congr 1
  push_cast
  ring

lemma continuous_kVecP (ν : ℝ) (k : ℤ) : Continuous (kVecP ν k) := by
  unfold kVecP
  refine Continuous.mul ?_ ?_
  · refine continuous_iff_continuousAt.2 fun x => ?_
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have hc : ContinuousAt (fun y : ℝ => 1 + y ^ 2) x := by fun_prop
    exact ContinuousAt.comp (g := fun a : ℝ => (a : ℂ) ^ ((I * ν - 1) / 2))
      (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hpos.ne')) hc
  · refine Continuous.zpow₀ ((Complex.continuous_ofReal.sub continuous_const).div
      (Complex.continuous_ofReal.add continuous_const) fun x => ofReal_add_I_ne_zero x) k ?_
    intro x
    left
    exact div_ne_zero (ofReal_sub_I_ne_zero x) (ofReal_add_I_ne_zero x)

theorem memLp_kVecP (ν : ℝ) (k : ℤ) : MemLp (kVecP ν k) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_kVecP ν k).aestronglyMeasurable]
  refine integrable_inv_one_add_sq.congr (Filter.Eventually.of_forall fun x => ?_)
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  simp only
  rw [norm_kVecP, ← Real.rpow_mul_natCast hpos.le]
  norm_num
  rw [Real.rpow_neg_one]

/-- The `K`-type vector `e_k` as a vector of `L²(ℝ)`. -/
def kVecL2 (ν : ℝ) (k : ℤ) : L2R := (memLp_kVecP ν k).toLp (kVecP ν k)

/-- **The `K`-types of the even principal series**: `π(k_θ) e_k = e^{-2ikθ} e_k` in `L²(ℝ)`. -/
theorem principalSeries_rot_kVecL2 (ν θ : ℝ) (k : ℤ) :
    principalSeries 0 ν (rot θ) (kVecL2 ν k) = Complex.exp (-(2 * k * θ * I)) • kVecL2 ν k := by
  refine Lp.ext ?_
  have h1 := coeFn_principalSeries 0 ν (rot θ) (kVecL2 ν k)
  have h2 := ae_eq_comp_mob (rot θ) (MemLp.coeFn_toLp (memLp_kVecP ν k))
  have h3 := Lp.coeFn_smul (Complex.exp (-(2 * k * θ * I))) (kVecL2 ν k)
  have h4 : (kVecL2 ν k : ℝ → ℂ) =ᵐ[volume] kVecP ν k := MemLp.coeFn_toLp (memLp_kVecP ν k)
  filter_upwards [h1, h2, h3, h4, ae_den_ne_zero (rot θ)] with x e1 e2 e3 e4 hx
  simp only [Function.comp_apply] at e2
  rw [e1, e3, Pi.smul_apply, e4, smul_eq_mul, ← act_rot_kVecP ν θ k x hx, act]
  show mult 0 ν (den (rot θ) x) * (kVecL2 ν k) (mob (rot θ) x) = _
  rw [show (kVecL2 ν k : ℝ → ℂ) (mob (rot θ) x) = kVecP ν k (mob (rot θ) x) from e2]

/-- **The `K`-type vectors are orthogonal**: `⟪e_j, e_k⟫ = 0` for `j ≠ k` (unitarity of `π(k_θ)`
with `θ = π / (2 (j - k))`). -/
theorem inner_kVecL2_of_ne (ν : ℝ) {j k : ℤ} (h : j ≠ k) :
    inner ℂ (kVecL2 ν j) (kVecL2 ν k) = 0 := by
  set θ : ℝ := Real.pi / (2 * ((j : ℝ) - k)) with hθ
  have hjk : ((j : ℝ) - k) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
  have hu := principalSeries_inner 0 ν (rot θ) (kVecL2 ν j) (kVecL2 ν k)
  rw [principalSeries_rot_kVecL2, principalSeries_rot_kVecL2, inner_smul_left, inner_smul_right,
    ← mul_assoc, ← Complex.exp_conj, ← Complex.exp_add] at hu
  have he : (starRingEnd ℂ) (-(2 * (j : ℂ) * (θ : ℂ) * I)) + -(2 * (k : ℂ) * (θ : ℂ) * I) =
      Real.pi * I := by
    simp only [map_neg, map_mul, map_ofNat, map_intCast, Complex.conj_ofReal, Complex.conj_I]
    rw [hθ]
    push_cast
    have hjkC : ((j : ℂ) - k) ≠ 0 := by exact_mod_cast hjk
    field_simp
    ring
  rw [he, Complex.exp_pi_mul_I] at hu
  have : (2 : ℂ) * inner ℂ (kVecL2 ν j) (kVecL2 ν k) = 0 := by linear_combination -hu
  simpa using this

/-- `‖e_k‖² = π`. -/
theorem norm_sq_kVecL2 (ν : ℝ) (k : ℤ) : ‖kVecL2 ν k‖ ^ 2 = Real.pi := by
  have h : ‖kVecL2 ν k‖ ^ 2 = ∫ x, ‖kVecP ν k x‖ ^ 2 := by
    rw [kVecL2, Lp.norm_toLp, (memLp_kVecP ν k).eLpNorm_eq_integral_rpow_norm (by norm_num)
      (by norm_num), ENNReal.toReal_ofReal (by positivity)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
    norm_num
  rw [h, ← integral_univ_inv_one_add_sq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  simp only
  rw [norm_kVecP, ← Real.rpow_mul_natCast hpos.le]
  norm_num
  rw [Real.rpow_neg_one]

/-- **The radial matrix coefficients** `Φ^ν_{m,n}(ξ) = ⟪e_m, π(a(ξ)) e_n⟫` of the even principal
series. -/
def mcoefP (ν : ℝ) (m n : ℤ) (ξ : ℝ) : ℂ :=
  inner ℂ (kVecL2 ν m) (principalSeries 0 ν (aR ξ) (kVecL2 ν n))

/-- **The `KAK` form of the matrix coefficients**:
`⟪e_m, π(k_α a(ξ) k_θ) e_n⟫ = e^{-2i(mα + nθ)} Φ^ν_{m,n}(ξ)`. -/
theorem inner_kVecL2_kak (ν α ξ θ : ℝ) (m n : ℤ) :
    inner ℂ (kVecL2 ν m) (principalSeries 0 ν (rot α * aR ξ * rot θ) (kVecL2 ν n)) =
      Complex.exp (-(2 * (m * α + n * θ) * I)) * mcoefP ν m n ξ := by
  -- `⟪e_m, π(k_α) v⟫ = ⟪π(k_{-α}) e_m, v⟫`
  have hadj : ∀ v : L2R, inner ℂ (kVecL2 ν m) (principalSeries 0 ν (rot α) v) =
      inner ℂ (principalSeries 0 ν (rot (-α)) (kVecL2 ν m)) v := by
    intro v
    have h := principalSeries_inner 0 ν (rot (-α)) (kVecL2 ν m) (principalSeries 0 ν (rot α) v)
    rw [← h]
    congr 1
    rw [← ContinuousLinearMap.mul_apply, ← principalSeries_mul, ← rot_add, neg_add_cancel, rot_zero,
      principalSeries_one, ContinuousLinearMap.one_apply]
  rw [principalSeries_mul, principalSeries_mul, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, principalSeries_rot_kVecL2, map_smul, hadj,
    principalSeries_rot_kVecL2, inner_smul_left, inner_smul_right, mcoefP, ← mul_assoc,
    ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, map_ofNat, map_intCast, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Non-vacuity: the hypothesis `den (k_θ) x ≠ 0` holds for `θ = 0`. -/
example (ν : ℝ) (k : ℤ) (x : ℝ) :
    act 0 ν (rot 0) (kVecP ν k) x = Complex.exp (-(2 * k * (0 : ℝ) * I)) * kVecP ν k x :=
  act_rot_kVecP ν 0 k x (by simp)

end Lightlike.Lorentz.SL2RPlancherel
