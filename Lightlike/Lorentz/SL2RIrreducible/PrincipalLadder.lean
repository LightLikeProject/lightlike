module

public import Lightlike.Lorentz.SL2RIrreducible.PrincipalWeights

/-!
# The ladder relation of the principal-series weight vectors and the matrix coefficient between
neighbouring weights

With `s = (iν - 1 - ε)/2` and `w = (iν - 1)/2 = s + ε/2`, the weight vectors `e_k` of
`PrincipalWeights.lean` satisfy `x e_k'(x) - w e_k(x) = ((s - k)/2) e_{k+1}(x) + ((s + k + ε)/2) e_{k-1}(x)`
(`ladder_weightVec`), the explicit form of Kitaev's Eq. (15), arXiv:1711.08169, for the generator of
the diagonal subgroup. Hence the matrix coefficient `t ↦ ⟪e_{k+1}, π(exp(tH)) e_k⟫` has derivative
`(s - k) ‖e_{k+1}‖²` at `t = 0` (`hasDerivAt_pairing`), which vanishes only at the reducible point:
`s - k = 0` iff `ν = 0` and `2k + ε = -1`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The algebra of the ladder relation, in `P = x - i`, `Q = x + i`. -/
lemma ladder_alg (s ε' k' x P Q e : ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : x = (P + Q) / 2)
    (hPQ : 1 + x ^ 2 = P * Q) :
    x * (e * (s * (2 * x / (1 + x ^ 2)) + (k' + ε') / P - k' / Q)) - (s + ε' / 2) * e =
      ((s - k') / 2) * (e * (P / Q)) + ((s + k' + ε') / 2) * (e * (Q / P)) := by
  rw [hPQ]
  subst hx
  field_simp
  ring

variable (ε : ℤ) (ν : ℝ) (k : ℤ)

lemma hasDerivAt_log_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2)) (2 * x / (1 + x ^ 2)) x := by
  have h := ((hasDerivAt_pow 2 x).const_add (1 : ℝ)).log (one_add_sq_pos x).ne'
  convert h using 1
  simp

lemma hasDerivAt_zpow_sub (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) - I) ^ m) ((m : ℂ) * ((x : ℂ) - I) ^ (m - 1)) x :=
  ((hasDerivAt_zpow m ((x : ℂ) - I) (Or.inl (ofReal_sub_I_ne_zero' x))).comp_sub_const (x : ℂ) I
    ).comp_ofReal

lemma hasDerivAt_zpow_add (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) + I) ^ m) ((m : ℂ) * ((x : ℂ) + I) ^ (m - 1)) x :=
  ((hasDerivAt_zpow m ((x : ℂ) + I) (Or.inl (ofReal_add_I_ne_zero' x))).comp_add_const (x : ℂ) I
    ).comp_ofReal

/-- **The derivative of the weight vector**: `e_k' = e_k [2 s x/(1 + x²) + (k+ε)/(x - i) - k/(x + i)]`. -/
theorem hasDerivAt_weightVec (x : ℝ) :
    HasDerivAt (weightVec ε ν k)
      (weightVec ε ν k x * (weightExp ε ν * ((2 * x / (1 + x ^ 2) : ℝ) : ℂ) +
        ((k + ε : ℤ) : ℂ) / ((x : ℂ) - I) - (k : ℂ) / ((x : ℂ) + I))) x := by
  have h2 : HasDerivAt (fun y : ℝ => Complex.exp (weightExp ε ν * ((Real.log (1 + y ^ 2) : ℝ) : ℂ)))
      (Complex.exp (weightExp ε ν * ((Real.log (1 + x ^ 2) : ℝ) : ℂ)) *
        (weightExp ε ν * ((2 * x / (1 + x ^ 2) : ℝ) : ℂ))) x :=
    ((hasDerivAt_log_one_add_sq x).ofReal_comp.const_mul (weightExp ε ν)).cexp
  have h3 := hasDerivAt_zpow_sub (k + ε) x
  have h4 := hasDerivAt_zpow_add (-k) x
  have h := (h2.mul h3).mul h4
  refine h.congr_deriv ?_
  have hP := ofReal_sub_I_ne_zero' x
  have hQ := ofReal_add_I_ne_zero' x
  simp only [Pi.mul_apply]
  unfold weightVec
  rw [zpow_sub_one₀ hP, zpow_sub_one₀ hQ]
  push_cast
  ring

/-- **The ladder relation**: `x e_k' - w e_k = ((s - k)/2) e_{k+1} + ((s + k + ε)/2) e_{k-1}`
with `w = (iν - 1)/2` (Kitaev, arXiv:1711.08169, Eq. (15)). -/
theorem ladder_weightVec (x : ℝ) :
    (x : ℂ) * deriv (weightVec ε ν k) x - ((I * ν - 1) / 2) * weightVec ε ν k x =
      ((weightExp ε ν - k) / 2) * weightVec ε ν (k + 1) x +
      ((weightExp ε ν + k + ε) / 2) * weightVec ε ν (k - 1) x := by
  rw [(hasDerivAt_weightVec ε ν k x).deriv, weightVec_succ, weightVec_pred]
  have hw : (I * ν - 1) / 2 = weightExp ε ν + (ε : ℂ) / 2 := by unfold weightExp; ring
  rw [hw]
  have hP := ofReal_sub_I_ne_zero' x
  have hQ := ofReal_add_I_ne_zero' x
  have hPQ : (1 : ℂ) + (x : ℂ) ^ 2 = ((x : ℂ) - I) * ((x : ℂ) + I) := by
    linear_combination Complex.I_sq
  have hcast : ((2 * x / (1 + x ^ 2) : ℝ) : ℂ) = 2 * (x : ℂ) / (1 + (x : ℂ) ^ 2) := by
    push_cast; ring
  rw [hcast]
  have := ladder_alg (weightExp ε ν) (ε : ℂ) (k : ℂ) (x : ℂ) ((x : ℂ) - I) ((x : ℂ) + I)
    (weightVec ε ν k x) hP hQ (by ring) hPQ
  push_cast
  linear_combination this


/-! ## The matrix coefficient between neighbouring weights -/

/-- The ladder coefficient `(s - k)/2` of `e_{k+1}`. -/
def ladderUp (ε : ℤ) (ν : ℝ) (k : ℤ) : ℂ := (weightExp ε ν - k) / 2

/-- The ladder coefficient `(s + k + ε)/2` of `e_{k-1}`. -/
def ladderDown (ε : ℤ) (ν : ℝ) (k : ℤ) : ℂ := (weightExp ε ν + k + ε) / 2

/-- **The diagonal element acting on `e_k`**: `(π(exp(tH)) e_k)(x) = e^{-t(iν - 1)} e_k(e^{2t} x)`. -/
def diagPhase (ε : ℤ) (ν : ℝ) (k : ℤ) (t x : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ) * (I * ν - 1)) * weightVec ε ν k (Real.exp (2 * t) * x)

lemma principalSeries_expH_weightL2_ae (t : ℝ) :
    (principalSeries ε ν (expH t) (weightL2 ε ν k) : ℝ → ℂ) =ᵐ[volume] diagPhase ε ν k t := by
  have h1 := coeFn_principalSeries ε ν (expH t) (weightL2 ε ν k)
  have h2 := ae_eq_comp_mob (expH t) (weightL2_ae ε ν k)
  filter_upwards [h1, h2] with x e1 e2
  rw [e1]
  simp only [Function.comp_apply] at e2
  rw [e2, den_expH, mob_expH, diagPhase]
  have hm : mult ε (ν : ℂ) (Real.exp t)⁻¹ = Complex.exp (-(t : ℂ) * (I * ν - 1)) := by
    rw [mult_of_pos ε (ν : ℂ) (inv_pos.mpr (Real.exp_pos t)), Real.log_inv, Real.log_exp]
    congr 1
    push_cast
    ring
  rw [hm, show Real.exp t * x * Real.exp t = Real.exp (2 * t) * x by
    rw [two_mul, Real.exp_add]; ring]

/-- **The matrix coefficient** `t ↦ ⟪e_j, π(exp(tH)) e_k⟫`. -/
def diagPairing (ε : ℤ) (ν : ℝ) (j k : ℤ) (t : ℝ) : ℂ :=
  ⟪weightL2 ε ν j, principalSeries ε ν (expH t) (weightL2 ε ν k)⟫_ℂ

lemma diagPairing_eq_integral (j : ℤ) (t : ℝ) :
    diagPairing ε ν j k t = ∫ x, conj (weightVec ε ν j x) * diagPhase ε ν k t x := by
  unfold diagPairing
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [weightL2_ae ε ν j, principalSeries_expH_weightL2_ae ε ν k t] with x e1 e2
  rw [e1, e2, RCLike.inner_apply']

lemma inner_weightL2_eq_integral (a b : ℤ) :
    ⟪weightL2 ε ν a, weightL2 ε ν b⟫_ℂ = ∫ x, conj (weightVec ε ν a x) * weightVec ε ν b x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [weightL2_ae ε ν a, weightL2_ae ε ν b] with x e1 e2
  rw [e1, e2, RCLike.inner_apply']

lemma norm_weightVec_eq (j m : ℤ) (x : ℝ) : ‖weightVec ε ν j x‖ = ‖weightVec ε ν m x‖ := by
  rw [norm_weightVec, norm_weightVec]

lemma norm_conj_mul_weightVec (j m : ℤ) (x : ℝ) :
    ‖conj (weightVec ε ν j x) * weightVec ε ν m x‖ = (1 + x ^ 2)⁻¹ := by
  rw [norm_mul, RCLike.norm_conj, norm_weightVec_eq ε ν m j x, ← sq, norm_weightVec_sq]

lemma continuous_conj_mul_weightVec (j m : ℤ) :
    Continuous fun x => conj (weightVec ε ν j x) * weightVec ε ν m x :=
  (Complex.continuous_conj.comp (continuous_weightVec ε ν j)).mul (continuous_weightVec ε ν m)

lemma integrable_conj_mul_weightVec (j m : ℤ) :
    Integrable (fun x => conj (weightVec ε ν j x) * weightVec ε ν m x) := by
  refine Integrable.mono' integrable_inv_one_add_sq
    (continuous_conj_mul_weightVec ε ν j m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (norm_conj_mul_weightVec ε ν j m x).le)

/-- **Scaling by `e^{2t}` costs at most the factor `e²`** in the modulus of a weight vector. -/
lemma norm_weightVec_exp_le (m j : ℤ) {t : ℝ} (ht : |t| < 1) (x : ℝ) :
    ‖weightVec ε ν m (Real.exp (2 * t) * x)‖ ≤ Real.exp 2 * ‖weightVec ε ν j x‖ := by
  have hx := one_add_sq_pos x
  have hy : 0 < 1 + (Real.exp (2 * t) * x) ^ 2 := one_add_sq_pos _
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, norm_weightVec_sq,
    mul_pow (Real.exp 2), norm_weightVec_sq, show Real.exp 2 ^ 2 = Real.exp 4 by
      rw [sq, ← Real.exp_add]; norm_num]
  have h1 : 1 ≤ Real.exp 4 := Real.one_le_exp (by norm_num)
  have h2 : 1 ≤ Real.exp 4 * Real.exp (4 * t) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [(abs_lt.mp ht).1])
  have h3 : (Real.exp (2 * t) * x) ^ 2 = Real.exp (4 * t) * x ^ 2 := by
    rw [mul_pow, sq (Real.exp (2 * t)), ← Real.exp_add]; ring_nf
  have key : 1 + x ^ 2 ≤ Real.exp 4 * (1 + (Real.exp (2 * t) * x) ^ 2) := by
    rw [h3]
    nlinarith [sq_nonneg x, mul_le_mul_of_nonneg_right h2 (sq_nonneg x)]
  calc (1 + (Real.exp (2 * t) * x) ^ 2)⁻¹
      = (1 + x ^ 2) / (1 + (Real.exp (2 * t) * x) ^ 2) * (1 + x ^ 2)⁻¹ := by field_simp
    _ ≤ Real.exp 4 * (1 + x ^ 2)⁻¹ := by
      gcongr
      rw [div_le_iff₀ hy]; exact key

/-- **The derivative of `t ↦ diagPhase ε ν k t x`** is `2 e^{-t(iν-1)} (A e_{k+1} + B e_{k-1})(e^{2t} x)`,
by the ladder relation. -/
lemma hasDerivAt_diagPhase (t x : ℝ) :
    HasDerivAt (fun t => diagPhase ε ν k t x)
      (2 * Complex.exp (-(t : ℂ) * (I * ν - 1)) *
        (ladderUp ε ν k * weightVec ε ν (k + 1) (Real.exp (2 * t) * x) +
         ladderDown ε ν k * weightVec ε ν (k - 1) (Real.exp (2 * t) * x))) t := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * (I * ν - 1)))
      (Complex.exp (-(t : ℂ) * (I * ν - 1)) * (-(I * ν - 1))) t := by
    have := (((hasDerivAt_id t).ofReal_comp.neg).mul_const (I * (ν : ℂ) - 1)).cexp
    refine HasDerivAt.congr_deriv this ?_
    simp [Pi.neg_apply]
  have hy : HasDerivAt (fun t : ℝ => Real.exp (2 * t) * x) (2 * Real.exp (2 * t) * x) t := by
    have := ((hasDerivAt_id t).const_mul 2).exp.mul_const x
    refine HasDerivAt.congr_deriv this ?_
    simp only [id_eq]
    ring
  have h2 := (hasDerivAt_weightVec ε ν k (Real.exp (2 * t) * x)).scomp t hy
  refine HasDerivAt.congr_deriv (h1.mul h2) ?_
  have L := ladder_weightVec ε ν k (Real.exp (2 * t) * x)
  rw [(hasDerivAt_weightVec ε ν k (Real.exp (2 * t) * x)).deriv] at L
  simp only [Complex.real_smul]
  unfold ladderUp ladderDown
  push_cast at L ⊢
  linear_combination (2 * Complex.exp (-(t : ℂ) * (I * ν - 1))) * L

/-- The `t`-derivative of the integrand of `diagPairing`. -/
def diagPairingDeriv (ε : ℤ) (ν : ℝ) (k j : ℤ) (t x : ℝ) : ℂ :=
  conj (weightVec ε ν j x) * (2 * Complex.exp (-(t : ℂ) * (I * ν - 1)) *
    (ladderUp ε ν k * weightVec ε ν (k + 1) (Real.exp (2 * t) * x) +
     ladderDown ε ν k * weightVec ε ν (k - 1) (Real.exp (2 * t) * x)))

/-- **The derivative of the matrix coefficient at `t = 0`**: the generator of the diagonal subgroup
acts on the weight vectors by the ladder relation, so
`d/dt ⟪e_j, π(exp(tH)) e_k⟫|₀ = (s - k) ⟪e_j, e_{k+1}⟫ + (s + k + ε) ⟪e_j, e_{k-1}⟫`. -/
theorem hasDerivAt_diagPairing (j : ℤ) :
    HasDerivAt (diagPairing ε ν j k)
      ((weightExp ε ν - k) * ⟪weightL2 ε ν j, weightL2 ε ν (k + 1)⟫_ℂ +
        (weightExp ε ν + k + ε) * ⟪weightL2 ε ν j, weightL2 ε ν (k - 1)⟫_ℂ) 0 := by
  have hc : ∀ m, Continuous (weightVec ε ν m) := continuous_weightVec ε ν
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = 2 * Real.exp 1 * ((‖ladderUp ε ν k‖ + ‖ladderDown ε ν k‖) * Real.exp 2) := ⟨_, rfl⟩
  have hfun : diagPairing ε ν j k = fun t => ∫ x, conj (weightVec ε ν j x) * diagPhase ε ν k t x :=
    funext (diagPairing_eq_integral ε ν k j)
  have hcont : ∀ t, Continuous fun x => conj (weightVec ε ν j x) * diagPhase ε ν k t x := by
    intro t
    unfold diagPhase
    have := hc j
    have := hc k
    fun_prop
  have hcontD : ∀ t, Continuous fun x => diagPairingDeriv ε ν k j t x := by
    intro t
    unfold diagPairingDeriv
    have := hc j
    have := hc (k + 1)
    have := hc (k - 1)
    fun_prop
  have hint0 : Integrable (fun x => conj (weightVec ε ν j x) * diagPhase ε ν k 0 x) := by
    have : (fun x => conj (weightVec ε ν j x) * diagPhase ε ν k 0 x) =
        fun x => conj (weightVec ε ν j x) * weightVec ε ν k x := by
      funext x; simp [diagPhase]
    rw [this]; exact integrable_conj_mul_weightVec ε ν j k
  have hbound : ∀ x, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖diagPairingDeriv ε ν k j t x‖ ≤
      C * (1 + x ^ 2)⁻¹ := by
    intro x t ht
    have ht' : |t| < 1 := by simpa [Real.dist_eq] using ht
    have hn1 : ‖Complex.exp (-(t : ℂ) * (I * ν - 1))‖ ≤ Real.exp 1 := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      simp [Complex.mul_re]
      linarith [(abs_lt.mp ht').2]
    have hp := norm_weightVec_exp_le ε ν (k + 1) j ht' x
    have hm := norm_weightVec_exp_le ε ν (k - 1) j ht' x
    have hn2 : ‖ladderUp ε ν k * weightVec ε ν (k + 1) (Real.exp (2 * t) * x) +
        ladderDown ε ν k * weightVec ε ν (k - 1) (Real.exp (2 * t) * x)‖ ≤
        (‖ladderUp ε ν k‖ + ‖ladderDown ε ν k‖) * (Real.exp 2 * ‖weightVec ε ν j x‖) := by
      calc _ ≤ ‖ladderUp ε ν k * weightVec ε ν (k + 1) (Real.exp (2 * t) * x)‖ +
            ‖ladderDown ε ν k * weightVec ε ν (k - 1) (Real.exp (2 * t) * x)‖ := norm_add_le _ _
        _ = ‖ladderUp ε ν k‖ * ‖weightVec ε ν (k + 1) (Real.exp (2 * t) * x)‖ +
            ‖ladderDown ε ν k‖ * ‖weightVec ε ν (k - 1) (Real.exp (2 * t) * x)‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ ‖ladderUp ε ν k‖ * (Real.exp 2 * ‖weightVec ε ν j x‖) +
            ‖ladderDown ε ν k‖ * (Real.exp 2 * ‖weightVec ε ν j x‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
        _ = _ := by ring
    have hsq := norm_weightVec_sq ε ν j x
    calc ‖diagPairingDeriv ε ν k j t x‖
        = ‖weightVec ε ν j x‖ * (2 * ‖Complex.exp (-(t : ℂ) * (I * ν - 1))‖ *
            ‖ladderUp ε ν k * weightVec ε ν (k + 1) (Real.exp (2 * t) * x) +
              ladderDown ε ν k * weightVec ε ν (k - 1) (Real.exp (2 * t) * x)‖) := by
          unfold diagPairingDeriv
          rw [norm_mul, RCLike.norm_conj, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      _ ≤ ‖weightVec ε ν j x‖ * (2 * Real.exp 1 *
            ((‖ladderUp ε ν k‖ + ‖ladderDown ε ν k‖) * (Real.exp 2 * ‖weightVec ε ν j x‖))) := by
          gcongr
      _ = C * ‖weightVec ε ν j x‖ ^ 2 := by rw [hC]; ring
      _ = C * (1 + x ^ 2)⁻¹ := by rw [hsq]
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun t x => conj (weightVec ε ν j x) * diagPhase ε ν k t x)
    (F' := fun t x => diagPairingDeriv ε ν k j t x) (x₀ := (0 : ℝ))
    (bound := fun x => C * (1 + x ^ 2)⁻¹) (s := Metric.ball 0 1)
    (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun t => (hcont t).aestronglyMeasurable) hint0
    (hcontD 0).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) (integrable_inv_one_add_sq.const_mul C)
    (Filter.Eventually.of_forall fun x t _ => by
      exact (hasDerivAt_diagPhase ε ν k t x).const_mul (conj (weightVec ε ν j x)))
  rw [hfun]
  refine hmain.2.congr_deriv ?_
  have e0 : ∀ x, diagPairingDeriv ε ν k j 0 x =
      (2 * ladderUp ε ν k) * (conj (weightVec ε ν j x) * weightVec ε ν (k + 1) x) +
      (2 * ladderDown ε ν k) * (conj (weightVec ε ν j x) * weightVec ε ν (k - 1) x) := by
    intro x; simp [diagPairingDeriv]; ring
  simp_rw [e0]
  rw [integral_add ((integrable_conj_mul_weightVec ε ν j (k + 1)).const_mul _)
    ((integrable_conj_mul_weightVec ε ν j (k - 1)).const_mul _), integral_const_mul,
    integral_const_mul, ← inner_weightL2_eq_integral, ← inner_weightL2_eq_integral]
  unfold ladderUp ladderDown
  ring

/-- **The derivative of `t ↦ ⟪e_{k+1}, π(exp(tH)) e_k⟫` at `0` is `(s - k) ‖e_{k+1}‖²`.** -/
theorem hasDerivAt_diagPairing_succ :
    HasDerivAt (diagPairing ε ν (k + 1) k)
      ((weightExp ε ν - k) * ((‖weightL2 ε ν (k + 1)‖ ^ 2 : ℝ) : ℂ)) 0 := by
  have h := hasDerivAt_diagPairing ε ν k (k + 1)
  rw [inner_weightL2_of_ne ε ν (show k + 1 ≠ k - 1 by omega), inner_self_eq_norm_sq_to_K] at h
  simpa using h

/-- **Neighbouring weights are linked**: if `s - k ≠ 0`, some `π(g)` has a nonzero matrix coefficient
`⟪e_{k+1}, π(g) e_k⟫`. Here `s - k = 0` iff `ν = 0` and `1 + ε + 2k = 0`. -/
theorem exists_inner_ne_zero (h : weightExp ε ν - k ≠ 0) :
    ∃ g : SL2R, ⟪weightL2 ε ν (k + 1), principalSeries ε ν g (weightL2 ε ν k)⟫_ℂ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have h0 : diagPairing ε ν (k + 1) k = fun _ => 0 := funext fun t => hcon (expH t)
  have hd := hasDerivAt_diagPairing_succ ε ν k
  rw [h0] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  rcases mul_eq_zero.mp this with h1 | h1
  · exact h h1
  · have : ‖weightL2 ε ν (k + 1)‖ = 0 := by
      have h2 : (‖weightL2 ε ν (k + 1)‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h1
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact weightL2_ne_zero ε ν (k + 1) (norm_eq_zero.mp this)

end Lightlike.Lorentz.SL2R
