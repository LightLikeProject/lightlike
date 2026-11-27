module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteDegree

/-!
# The `K`-weight vectors of the holomorphic discrete series

For `n ≥ 2` and `k ≥ 0` the function `e_k(z) = (z - i)^k (z + i)^{-(n+k)}` is a vector of the weighted Bergman space
`A²_n` (`kClass`), with `e_0 = (z + i)⁻ⁿ` the lowest weight vector (`kClass_zero`). The rotation `k_θ` acts on it by the
character `e^{-i(n+2k)θ}` (`discreteAction_rot_kClass`), so that the vectors are mutually orthogonal
(`kClass_orthogonal`). The completeness of the family and the norms are in the next sections.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real UpperHalfPlane Lightlike.Lorentz.SL2R
open scoped InnerProductSpace Manifold

noncomputable section

namespace Lightlike.Lorentz

/-- **The `K`-weight vector** `e_k(z) = (z - i)^k (z + i)^{-(n+k)}` of the holomorphic discrete series `D_n⁺`. -/
def kVec (n k : ℕ) (z : ℍ) : ℂ := ((z : ℂ) - Complex.I) ^ k * ((z : ℂ) + Complex.I) ^ (-((n + k : ℕ) : ℤ))

lemma kVec_zero (n : ℕ) : kVec n 0 = lowestVec n := by
  funext z; simp [kVec, lowestVec]

lemma continuous_kVec (n k : ℕ) : Continuous (kVec n k) := by
  unfold kVec
  refine Continuous.mul (by fun_prop) ?_
  refine Continuous.zpow₀ (by fun_prop) _ fun z => Or.inl (coe_add_I_ne_zero z)

lemma mdifferentiable_kVec (n k : ℕ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (kVec n k) := by
  unfold kVec
  refine MDifferentiable.mul ?_ ?_
  · refine MDifferentiable.pow ?_ k
    exact (UpperHalfPlane.mdifferentiable_coe).sub mdifferentiable_const
  · intro z
    have h : DifferentiableAt ℂ (fun w : ℂ => (w + Complex.I) ^ (-((n + k : ℕ) : ℤ))) z :=
      (differentiableAt_id.add_const Complex.I).zpow (Or.inl (coe_add_I_ne_zero z))
    exact (h.mdifferentiableAt).comp z (UpperHalfPlane.mdifferentiable_coe z)

/-- `|z - i| ≤ |z + i|` on the upper half-plane. -/
lemma norm_sub_I_le (z : ℍ) : ‖(z : ℂ) - Complex.I‖ ≤ ‖(z : ℂ) + Complex.I‖ := by
  have h : Complex.normSq ((z : ℂ) - Complex.I) ≤ Complex.normSq ((z : ℂ) + Complex.I) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.I_re, Complex.I_im]
    nlinarith [z.im_pos]
  rw [Complex.norm_def, Complex.norm_def]
  exact Real.sqrt_le_sqrt h

lemma norm_kVec_le (n k : ℕ) (z : ℍ) : ‖kVec n k z‖ ≤ ‖lowestVec n z‖ := by
  have hp : 0 < ‖(z : ℂ) + Complex.I‖ := norm_pos_iff.2 (coe_add_I_ne_zero z)
  have hle := norm_sub_I_le z
  unfold kVec lowestVec
  rw [norm_mul, norm_pow, norm_zpow, norm_zpow]
  have h1 : ‖(z : ℂ) - Complex.I‖ ^ k ≤ ‖(z : ℂ) + Complex.I‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) hle k
  have h2 : ‖(z : ℂ) + Complex.I‖ ^ (-((n + k : ℕ) : ℤ)) * ‖(z : ℂ) + Complex.I‖ ^ k =
      ‖(z : ℂ) + Complex.I‖ ^ (-(n : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ hp.ne']
    congr 1; push_cast; ring
  calc ‖(z : ℂ) - Complex.I‖ ^ k * ‖(z : ℂ) + Complex.I‖ ^ (-((n + k : ℕ) : ℤ))
      ≤ ‖(z : ℂ) + Complex.I‖ ^ k * ‖(z : ℂ) + Complex.I‖ ^ (-((n + k : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_right h1 (zpow_nonneg hp.le _)
    _ = ‖(z : ℂ) + Complex.I‖ ^ (-(n : ℤ)) := by rw [mul_comm]; exact h2

theorem memLp_kVec {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : MemLp (kVec n k) 2 (μn n) :=
  (memLp_lowestVec hn).mono (continuous_kVec n k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => norm_kVec_le n k z)

/-- **The class of `e_k` in `L²(ℍ, μ_n)`.** -/
def kClass {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : Hn n := (memLp_kVec hn k).toLp _

lemma coeFn_kClass {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : (kClass hn k : ℍ → ℂ) =ᵐ[μn n] kVec n k :=
  MemLp.coeFn_toLp _

theorem kClass_zero {n : ℕ} (hn : 2 ≤ n) : kClass hn 0 = lowestClass hn := by
  unfold kClass lowestClass
  congr 1
  exact kVec_zero n

theorem kClass_mem {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : kClass hn k ∈ holoSubmodule n :=
  ⟨kVec n k, mdifferentiable_kVec n k, coeFn_kClass hn k⟩

/-- The two linear factors of the rotation: `cos θ + i sin θ = e^{iθ}` in terms of the real `cos`, `sin`. -/
lemma exp_I_eq (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma jac_rot (θ : ℝ) (z : ℍ) : jac (rot θ) z = (Real.sin θ : ℂ) * (z : ℂ) + (Real.cos θ : ℂ) := by
  simp [jac]

lemma coe_tsmul_rot (θ : ℝ) (z : ℍ) :
    ((tsmul (rot θ) z : ℍ) : ℂ) = ((Real.cos θ : ℂ) * (z : ℂ) - (Real.sin θ : ℂ)) / jac (rot θ) z := by
  rw [coe_tsmul]; simp [sub_eq_add_neg]

lemma exp_neg_I_eq (θ : ℝ) :
    Complex.exp (-((θ : ℂ) * Complex.I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, exp_I_eq]
  simp [Real.cos_neg, Real.sin_neg, sub_eq_add_neg]

/-- `z' - i = e^{-iθ} (z - i) / (sin θ z + cos θ)` for `z' = k_θᵀ z`. -/
lemma tsmul_rot_sub_I (θ : ℝ) (z : ℍ) :
    ((tsmul (rot θ) z : ℍ) : ℂ) - Complex.I =
      Complex.exp (-((θ : ℂ) * Complex.I)) * ((z : ℂ) - Complex.I) / jac (rot θ) z := by
  have hj := jac_ne_zero (rot θ) z
  rw [coe_tsmul_rot, exp_neg_I_eq, eq_div_iff hj, sub_mul, div_mul_cancel₀ _ hj, jac_rot]
  linear_combination (-(Real.sin θ : ℂ)) * Complex.I_sq

/-- `z' + i = e^{iθ} (z + i) / (sin θ z + cos θ)` for `z' = k_θᵀ z`. -/
lemma tsmul_rot_add_I (θ : ℝ) (z : ℍ) :
    ((tsmul (rot θ) z : ℍ) : ℂ) + Complex.I =
      Complex.exp ((θ : ℂ) * Complex.I) * ((z : ℂ) + Complex.I) / jac (rot θ) z := by
  have hj := jac_ne_zero (rot θ) z
  rw [coe_tsmul_rot, exp_I_eq, eq_div_iff hj, add_mul, div_mul_cancel₀ _ hj, jac_rot]
  linear_combination (-(Real.sin θ : ℂ)) * Complex.I_sq

/-- **The rotation acts on `e_k` by the character `e^{-i(n+2k)θ}`**, pointwise. -/
lemma rot_kVec (n k : ℕ) (θ : ℝ) (z : ℍ) :
    jac (rot θ) z ^ (-(n : ℤ)) * kVec n k (tsmul (rot θ) z) =
      Complex.exp (-(((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) * kVec n k z := by
  have hj := jac_ne_zero (rot θ) z
  have hz := coe_add_I_ne_zero z
  unfold kVec
  rw [tsmul_rot_sub_I, tsmul_rot_add_I]
  set j := jac (rot θ) z with hjdef
  set E := Complex.exp (-((θ : ℂ) * Complex.I)) with hE
  have hE' : Complex.exp ((θ : ℂ) * Complex.I) = E⁻¹ := by
    rw [hE, ← Complex.exp_neg]; simp
  have hEne : E ≠ 0 := Complex.exp_ne_zero _
  have hpow : Complex.exp (-(((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) = E ^ (n + 2 * k) := by
    rw [hE, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [hE', hpow]
  generalize (z : ℂ) - Complex.I = A
  generalize hB : (z : ℂ) + Complex.I = B at hz ⊢
  simp only [zpow_neg, zpow_natCast]
  field_simp
  have hu : E ^ k * E⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hEne, one_pow]
  have hv : E ^ n * E⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hEne, one_pow]
  have hw : j ^ n * j⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hj, one_pow]
  linear_combination (-(E ^ k * A ^ k * j⁻¹ ^ k * B ^ k * B ^ n) * (E ^ n * E⁻¹ ^ n) * (j ^ n * j⁻¹ ^ n)) * hu +
    (-(E ^ k * A ^ k * j⁻¹ ^ k * B ^ k * B ^ n) * (j ^ n * j⁻¹ ^ n)) * hv +
    (-(E ^ k * A ^ k * j⁻¹ ^ k * B ^ k * B ^ n)) * hw

/-- **The rotation acts on the class of `e_k` by the character `e^{-i(n+2k)θ}`.** -/
theorem discreteAction_rot_kClass {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (θ : ℝ) :
    discreteAction n (rot θ) (kClass hn k) =
      Complex.exp (-(((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) • kClass hn k := by
  rw [discreteAction_apply, Lp.ext_iff]
  have h1 := coeFn_discreteIso n (rot θ) (kClass hn k)
  have h2 := (quasiMeasurePreserving_tsmul n (rot θ)).ae_eq_comp (coeFn_kClass hn k)
  have h3 := Lp.coeFn_smul (Complex.exp (-(((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I))) (kClass hn k)
  filter_upwards [h1, h2, h3, coeFn_kClass hn k] with z hz1 hz2 hz3 hz4
  rw [hz1, hz3]
  simp only [Function.comp_apply] at hz2
  rw [hz2, Pi.smul_apply, hz4, smul_eq_mul]
  exact rot_kVec n k θ z

/-- **The `K`-weight vectors are mutually orthogonal** (distinct characters of the rotation group). -/
theorem kClass_orthogonal {n : ℕ} (hn : 2 ≤ n) {j k : ℕ} (hjk : j ≠ k) :
    ⟪kClass hn j, kClass hn k⟫_ℂ = 0 := by
  set θ : ℝ := π / (2 * ((j : ℝ) - k)) with hθ
  have hd : ((j : ℝ) - k) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hjk)
  have h1 := discreteAction_inner n (rot θ) (kClass hn j) (kClass hn k)
  rw [discreteAction_rot_kClass hn j θ, discreteAction_rot_kClass hn k θ, inner_smul_left,
    inner_smul_right, ← mul_assoc, ← Complex.exp_conj, ← Complex.exp_add] at h1
  have hc : (starRingEnd ℂ) (-(((n + 2 * j : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) +
      -(((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I) = ((2 * ((j : ℝ) - k) * θ : ℝ) : ℂ) * Complex.I := by
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    push_cast; ring
  rw [hc] at h1
  have h2 : 2 * ((j : ℝ) - k) * θ = π := by rw [hθ]; field_simp
  rw [h2, Complex.exp_pi_mul_I] at h1
  linear_combination (-1 / 2 : ℂ) * h1

end Lightlike.Lorentz
