module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteSchurKfin

/-!
# Schur orthogonality for the `K`-weight vectors of `D_n⁺`

`lintegral_norm_sq_mcoef_kvec`: for `j, l ≥ 0`,
`∫ |⟨e_j, D_n(g) e_l⟩|² dg = c_n ‖e_j‖² ‖e_l‖² / ‖e₀‖²` with `c_n = 2π |c₀|²` the constant of
`schur_lowest`. The coefficient of the coherent vector `D_n(diag(A, 1/A)) e₀` in the `K`-weight basis, the
`K × K`-Plancherel identity of the coherent coefficient and the right translation invariance of `haarR`
give, for every `x ∈ [0, 1)`, a power-series identity whose coefficients are compared with those of `(1 - x)^{-n}`.
-/

@[expose] public section

open MeasureTheory Set Filter Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal Topology

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The constant `2π |c₀|²` of the Schur orthogonality against the lowest weight vector. -/
def schurConst (n : ℕ) : ℝ := 2 * π * ‖evalConst n‖ ^ 2

lemma schurConst_pos {n : ℕ} (hn : 2 ≤ n) : 0 < schurConst n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have h2 : evalConst n ≠ 0 := by
    unfold evalConst
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (div_pos (by positivity) (by linarith : (0 : ℝ) < n - 1)).ne'
    · simp [Complex.I_ne_zero]
  unfold schurConst
  have : 0 < ‖evalConst n‖ := norm_pos_iff.2 h2
  positivity

/-- **`schur_lowest` for `v = e_j`.** -/
theorem lintegral_norm_sq_mcoef_lowest {n : ℕ} (hn : 2 ≤ n) (j : ℕ) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n (kClass hn j) (lowestClass hn) g‖ ^ 2) ∂haarR =
      ENNReal.ofReal (schurConst n * ‖kClass hn j‖ ^ 2) := by
  have h := schur_lowest hn (v := kClass hn j) (φ := kVec n j) (mdifferentiable_kVec n j) (coeFn_kClass hn j)
  have h2 := enorm_sq_eq_lintegral (kClass hn j) (coeFn_kClass hn j)
  unfold mcoef
  rw [h, ← h2, ENNReal.ofReal_mul (schurConst_pos hn).le, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rfl

/-- The Plancherel norm of the coherent matrix coefficient, by right translation invariance. -/
theorem lintegral_norm_sq_coh_eq {n : ℕ} (hn : 2 ≤ n) (j : ℕ) {A : ℝ} (hA : 0 < A) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn)) g‖ ^ 2)
        ∂haarR = ENNReal.ofReal (schurConst n * ‖kClass hn j‖ ^ 2) := by
  have h1 : ∀ g : SL2R, mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn)) g =
      mcoef n (kClass hn j) (lowestClass hn) (g * diagSL A hA.ne') := by
    intro g
    unfold mcoef
    rw [discreteAction_mul']
  simp_rw [h1]
  rw [lintegral_mul_right_eq_self (fun g => ENNReal.ofReal (‖mcoef n (kClass hn j) (lowestClass hn) g‖ ^ 2))
    (diagSL A hA.ne')]
  exact lintegral_norm_sq_mcoef_lowest hn j

lemma norm_sq_cohCoeff (n : ℕ) (A : ℝ) (l : ℕ) :
    ‖cohCoeff n A l‖ ^ 2 = gam n A ^ 2 * (Nat.choose (n - 1 + l) (n - 1) : ℝ) ^ 2 * (tpar A ^ 2) ^ l := by
  have h1 : cohCoeff n A l = ((gam n A * ((Nat.choose (n - 1 + l) (n - 1) : ℝ) * (-tpar A) ^ l) : ℝ) : ℂ) := by
    unfold cohCoeff
    push_cast
    ring
  rw [h1, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h3 : ((-tpar A) ^ l) ^ 2 = (tpar A ^ 2) ^ l := by rw [← pow_mul, mul_comm, pow_mul, neg_sq]
  calc (gam n A * ((Nat.choose (n - 1 + l) (n - 1) : ℝ) * (-tpar A) ^ l)) ^ 2
      = gam n A ^ 2 * (Nat.choose (n - 1 + l) (n - 1) : ℝ) ^ 2 * ((-tpar A) ^ l) ^ 2 := by ring
    _ = _ := by rw [h3]

/-- **Schur orthogonality for the `K`-weight vectors**:
`∫ |⟨e_j, D_n(g) e_l⟩|² dg = c_n ‖e_j‖² ‖e_l‖² / ‖e₀‖²`. -/
theorem lintegral_norm_sq_mcoef_kvec {n : ℕ} (hn : 2 ≤ n) (j l : ℕ) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n (kClass hn j) (kClass hn l) g‖ ^ 2) ∂haarR =
      ENNReal.ofReal (schurConst n * ‖kClass hn j‖ ^ 2 * ‖kClass hn l‖ ^ 2 / ‖kClass hn 0‖ ^ 2) := by
  set N : ℕ → ℝ≥0∞ := fun l => ∫⁻ g, ENNReal.ofReal (‖mcoef n (kClass hn j) (kClass hn l) g‖ ^ 2) ∂haarR
    with hN
  set K : ℝ := schurConst n * ‖kClass hn j‖ ^ 2 with hK
  set β : ℕ → ℝ := fun l => (Nat.choose (n - 1 + l) (n - 1) : ℝ) with hβ
  have hβpos : ∀ l, 0 < β l := fun l => choose_pos hn l
  have hKpos : 0 < K := mul_pos (schurConst_pos hn) (pow_pos (norm_kClass_pos hn j) 2)
  have hE : ∀ x ∈ Ico (0 : ℝ) 1,
      ∑' l, ENNReal.ofReal ((1 - x) ^ n * β l ^ 2 * x ^ l) * N l = ENNReal.ofReal K := by
    intro x hx
    have ht : |Real.sqrt x| < 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (Real.sqrt_lt' one_pos).2 (by simpa using hx.2)
    obtain ⟨A, hA, hAt⟩ := exists_tpar_eq ht
    have hxA : tpar A ^ 2 = x := by rw [hAt, Real.sq_sqrt hx.1]
    have h := (lintegral_norm_sq_coh hn j hA).symm.trans (lintegral_norm_sq_coh_eq hn j hA)
    rw [← h]
    refine tsum_congr (fun l => ?_)
    rw [norm_sq_cohCoeff, gam_sq n hA, hxA]
  have hfin : ∀ l, N l ≠ ⊤ := by
    intro l hl
    have hx : (1 / 2 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have h := hE _ hx
    have hle : ENNReal.ofReal ((1 - 1 / 2) ^ n * β l ^ 2 * (1 / 2) ^ l) * N l ≤ ENNReal.ofReal K := by
      rw [← h]
      exact ENNReal.le_tsum (f := fun l => ENNReal.ofReal ((1 - 1 / 2) ^ n * β l ^ 2 * (1 / 2) ^ l) * N l) l
    have hpos : 0 < (1 - 1 / 2 : ℝ) ^ n * β l ^ 2 * (1 / 2) ^ l :=
      mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (hβpos l) 2)) (pow_pos (by norm_num) _)
    rw [hl, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne'] at hle
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hle)
  set n' : ℕ → ℝ := fun l => (N l).toReal with hn'
  have hNeq : ∀ l, N l = ENNReal.ofReal (n' l) := fun l => (ENNReal.ofReal_toReal (hfin l)).symm
  have hreal : ∀ x ∈ Ico (0 : ℝ) 1, HasSum (fun l => (1 - x) ^ n * β l ^ 2 * x ^ l * n' l) K := by
    intro x hx
    have h := hE x hx
    have hcoef : ∀ l, 0 ≤ (1 - x) ^ n * β l ^ 2 * x ^ l := fun l =>
      mul_nonneg (mul_nonneg (pow_nonneg (by linarith [hx.2]) _) (sq_nonneg _)) (pow_nonneg hx.1 _)
    have hnn : ∀ l, 0 ≤ (1 - x) ^ n * β l ^ 2 * x ^ l * n' l := fun l =>
      mul_nonneg (hcoef l) ENNReal.toReal_nonneg
    have h' : ∑' l, ENNReal.ofReal ((1 - x) ^ n * β l ^ 2 * x ^ l * n' l) = ENNReal.ofReal K := by
      rw [← h]
      refine tsum_congr (fun l => ?_)
      rw [hNeq l, ENNReal.ofReal_mul (hcoef l)]
    have hne : ∑' l, ENNReal.ofReal ((1 - x) ^ n * β l ^ 2 * x ^ l * n' l) ≠ ⊤ := by
      rw [h']; exact ENNReal.ofReal_ne_top
    have hsum := ENNReal.summable_toReal hne
    have hsum' : Summable fun l => (1 - x) ^ n * β l ^ 2 * x ^ l * n' l :=
      hsum.congr (fun l => ENNReal.toReal_ofReal (hnn l))
    have htsum : ∑' l, (1 - x) ^ n * β l ^ 2 * x ^ l * n' l = K := by
      have := ENNReal.tsum_toReal_eq (f := fun l => ENNReal.ofReal ((1 - x) ^ n * β l ^ 2 * x ^ l * n' l))
        (fun l => ENNReal.ofReal_ne_top)
      rw [h', ENNReal.toReal_ofReal hKpos.le] at this
      exact (tsum_congr (fun l => (ENNReal.toReal_ofReal (hnn l)).symm)).trans this.symm
    exact (hsum'.hasSum_iff).2 htsum
  have hreal2 : ∀ x ∈ Ico (0 : ℝ) 1, HasSum (fun l => (β l ^ 2 * n' l) * x ^ l) (K / (1 - x) ^ n) := by
    intro x hx
    have hpos : 0 < (1 - x) ^ n := pow_pos (by linarith [hx.2]) _
    have := (hreal x hx).div_const ((1 - x) ^ n)
    convert this using 1
    funext l
    field_simp
  have hreal3 : ∀ x ∈ Ico (0 : ℝ) 1, HasSum (fun l => (K * β l) * x ^ l) (K / (1 - x) ^ n) := by
    intro x hx
    have := (hasSum_choose_series' hn hx).mul_left K
    have e1 : (fun l => (K * β l) * x ^ l) = fun l => K * (β l * x ^ l) := by funext l; ring
    have e2 : K / (1 - x) ^ n = K * (1 / (1 - x) ^ n) := (mul_one_div _ _).symm
    rw [e1, e2]
    exact this
  have hcoef := coeff_eq_of_hasSum (a := fun l => β l ^ 2 * n' l) (b := fun l => K * β l)
    (fun l => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
    (fun l => mul_nonneg hKpos.le (hβpos l).le) (S := fun x => K / (1 - x) ^ n) hreal2 hreal3
  have hl' : β l ^ 2 * n' l = K * β l := congrFun hcoef l
  have h2 : β l * (β l * n' l) = β l * K := by linear_combination hl'
  have h3 : β l * n' l = K := mul_left_cancel₀ (hβpos l).ne' h2
  have hn'l : n' l = K / β l := eq_div_of_mul_eq (hβpos l).ne' (by rw [mul_comm]; exact h3)
  have hrel : β l * ‖kClass hn l‖ ^ 2 = ‖kClass hn 0‖ ^ 2 := choose_mul_norm_sq_kClass hn l
  have hn0 : 0 < ‖kClass hn 0‖ ^ 2 := pow_pos (norm_kClass_pos hn 0) 2
  show N l = _
  rw [hNeq l, hn'l]
  congr 1
  rw [div_eq_div_iff (hβpos l).ne' hn0.ne']
  linear_combination (-K) * hrel

end Lightlike.Lorentz.SL2RPlancherel
