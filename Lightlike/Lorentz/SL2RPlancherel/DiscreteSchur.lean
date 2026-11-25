module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteDegree

/-!
# Schur orthogonality for the lowest weight vector of the holomorphic discrete series

For `v` in the weighted Bergman space `A²_n` the pairing `⟨e₀, v⟩ = (4π/(n-1)) (-2i)⁻ⁿ v(i)` is the evaluation at `i`
(`inner_lowest_holo`); with the unitarity of `D_n`, `|⟨v, D_n(g) e₀⟩|² = |c₀|² Im(u)ⁿ |v(u)|²` for `u = g⁻¹ᵀ · i`, and the
Iwasawa integral over `SL(2,ℝ)` reduces to the invariant integral over `ℍ`.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real UpperHalfPlane Lightlike.Lorentz.SL2R
open scoped InnerProductSpace Manifold

noncomputable section

namespace Lightlike.Lorentz

/-- **Evaluation at `i` is the pairing with the lowest weight vector**: for `ψ ∈ A²_n` with holomorphic
representative `φ`, `⟨e₀, ψ⟩ = (4π/(n-1)) (-2i)⁻ⁿ φ(i)`. -/
theorem inner_lowest_holo {n : ℕ} (hn : 2 ≤ n) {ψ : Hn n} {φ : ℍ → ℂ}
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hψ : ψ =ᵐ[μn n] φ) :
    ⟪lowestClass hn, ψ⟫_ℂ =
      ((4 * π / (n - 1) : ℝ) : ℂ) * ((-2 * Complex.I) ^ n)⁻¹ * φ UpperHalfPlane.I := by
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (lowestClass hn) ψ
  have h1 : lowestClass hn =ᵐ[μn n] lowestVec n := MemLp.coeFn_toLp _
  have hae : ∀ᵐ z ∂(μn n), ⟪(lowestClass hn : ℍ → ℂ) z, (ψ : ℍ → ℂ) z⟫_ℂ =
      (starRingEnd ℂ) (lowestVec n z) * φ z := by
    filter_upwards [h1, hψ] with z hz1 hz2
    rw [hz1, hz2]
    simp [RCLike.inner_apply, mul_comm]
  rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
  set F : ℍ → ℂ := fun z => (starRingEnd ℂ) (lowestVec n z) * φ z with hF
  have hFc : Measurable F := by
    have hc : Continuous F := by
      simp only [hF]
      exact (Complex.continuous_conj.comp (continuous_lowestVec n)).mul hφ.continuous
    exact hc.measurable
  rw [integral_μn_eq_halfplane hn F]
  have hφd : DifferentiableOn ℂ (fun w => φ (UpperHalfPlane.ofComplex w)) {z : ℂ | 0 < z.im} := by
    have := (UpperHalfPlane.mdifferentiable_iff.1 hφ)
    simpa [Function.comp_def] using this
  have hcongr : ∀ w ∈ {z : ℂ | 0 < z.im},
      (((w.im ^ (n - 2) : ℝ)) : ℂ) * F (UpperHalfPlane.ofComplex w) =
        φ (UpperHalfPlane.ofComplex w) * (starRingEnd ℂ) (((w + Complex.I) ^ n)⁻¹) *
          (((w.im ^ (n - 2) : ℝ)) : ℂ) := by
    intro w hw
    have hw' : (0 : ℝ) < w.im := hw
    have hz : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    simp only [hF, lowestVec, hz, zpow_neg, zpow_natCast]
    ring
  have hint : IntegrableOn (fun w : ℂ => φ (UpperHalfPlane.ofComplex w) *
      (starRingEnd ℂ) (((w + Complex.I) ^ n)⁻¹) * (((w.im ^ (n - 2) : ℝ)) : ℂ)) {z : ℂ | 0 < z.im} := by
    have hintF : Integrable F (μn n) := hi.congr hae
    have := (integrable_μn_iff_halfplane hn F hFc).1 hintF
    exact this.congr_fun (fun w hw => hcongr w hw) (measurableSet_lt measurable_const Complex.measurable_im)
  rw [setIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im) hcongr]
  have := SL2RPlancherel.bergman_reproducing hn hφd hint
  rw [this]
  have hI : UpperHalfPlane.ofComplex Complex.I = UpperHalfPlane.I := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simp)]; rfl
  rw [hI]

/-- The constant of the evaluation at `i`. -/
def evalConst (n : ℕ) : ℂ := ((4 * π / (n - 1) : ℝ) : ℂ) * ((-2 * Complex.I) ^ n)⁻¹

/-- `D_n(g)` of a class with a holomorphic representative `φ` is the class of the slash `jac⁻ⁿ φ(gᵀ ·)`. -/
lemma coeFn_discreteAction_holo (n : ℕ) (g : SL2R) {f : Hn n} {φ : ℍ → ℂ} (hf : f =ᵐ[μn n] φ) :
    discreteAction n g f =ᵐ[μn n] fun z : ℍ => jac g z ^ (-(n : ℤ)) * φ (tsmul g z) := by
  have h3 := (quasiMeasurePreserving_tsmul n g).ae_eq_comp hf
  filter_upwards [coeFn_discreteAction n g f, h3] with z h1 h2
  simp only [Function.comp_apply] at h2
  rw [h1, h2]

/-- **The matrix coefficient of a holomorphic vector against `e₀` is an evaluation**: for `v ∈ A²_n` with holomorphic
representative `φ`, `|⟨v, D_n(g) e₀⟩|² = |c₀|² Im(u)ⁿ |φ(u)|²` with `u = g⁻¹ᵀ · i`. -/
theorem norm_sq_pairing_holo {n : ℕ} (hn : 2 ≤ n) {v : Hn n} {φ : ℍ → ℂ}
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hv : v =ᵐ[μn n] φ) (g : SL2R) :
    ‖⟪v, discreteAction n g (lowestClass hn)⟫_ℂ‖ ^ 2 =
      ‖evalConst n‖ ^ 2 * ((tsmul g⁻¹ UpperHalfPlane.I).im ^ n * ‖φ (tsmul g⁻¹ UpperHalfPlane.I)‖ ^ 2) := by
  have h1 : ⟪v, discreteAction n g (lowestClass hn)⟫_ℂ =
      ⟪discreteAction n g⁻¹ v, lowestClass hn⟫_ℂ := by
    have hU := discreteAction_inner n g⁻¹ v (discreteAction n g (lowestClass hn))
    rw [← hU]
    congr 1
    rw [discreteAction_apply, discreteAction_apply, ← discreteIso_mul, inv_mul_cancel, discreteIso_one]
  have hψ := coeFn_discreteAction_holo n g⁻¹ hv
  have hφ' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : ℍ => jac g⁻¹ z ^ (-(n : ℤ)) * φ (tsmul g⁻¹ z) :=
    mdifferentiable_discrete n g⁻¹ hφ
  have h2 := inner_lowest_holo hn hφ' hψ
  rw [h1, ← inner_conj_symm, h2]
  rw [RCLike.norm_conj, norm_mul]
  have hjac := jac_ne_zero g⁻¹ UpperHalfPlane.I
  have him : (tsmul g⁻¹ UpperHalfPlane.I).im = 1 / Complex.normSq (jac g⁻¹ UpperHalfPlane.I) := by
    rw [im_tsmul]; simp
  have hns : 0 < Complex.normSq (jac g⁻¹ UpperHalfPlane.I) := Complex.normSq_pos.2 hjac
  have hnorm : ‖jac g⁻¹ UpperHalfPlane.I ^ (-(n : ℤ)) * φ (tsmul g⁻¹ UpperHalfPlane.I)‖ ^ 2 =
      (tsmul g⁻¹ UpperHalfPlane.I).im ^ n * ‖φ (tsmul g⁻¹ UpperHalfPlane.I)‖ ^ 2 := by
    rw [norm_mul, mul_pow, norm_zpow, him]
    congr 1
    rw [← zpow_natCast, ← zpow_mul, Complex.normSq_eq_norm_sq, one_div]
    generalize ‖g⁻¹.jac ↑UpperHalfPlane.I‖ = x
    rw [show (-(n : ℤ) * ((2 : ℕ) : ℤ)) = -((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      inv_pow, ← pow_mul]
  have hc : ‖(((4 * π / (n - 1) : ℝ) : ℂ) * ((-2 * Complex.I) ^ n)⁻¹ : ℂ)‖ = ‖evalConst n‖ := rfl
  rw [hc, mul_pow, hnorm]

/-- The matrix `S = [[0, -1], [1, 0]]`, `z ↦ -1/z`. -/
def Smat : SL2R := mk 0 (-1) 1 0 (by norm_num)

/-- `(g⁻¹)ᵀ = S g S⁻¹` on `SL(2,ℝ)`. -/
lemma tr_inv_eq (g : SL2R) : tr g⁻¹ = Smat * g * Smat⁻¹ := by
  have hd := det_eq g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Smat, tr_apply, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- `S` fixes `i`. -/
lemma Smat_smul_I : Smat • UpperHalfPlane.I = UpperHalfPlane.I := by
  ext
  have h := denom_ne_zero' Smat UpperHalfPlane.I
  rw [SL2R.coe_smul, div_eq_iff h]
  simp [Smat, SL2R.coe_mk]

/-- **The point `g⁻¹ᵀ · i` for `g = g_z k_θ` is `-1/z`.** -/
lemma tsmul_inv_iwasawa (z : ℍ) (θ : ℝ) :
    tsmul (z.toSL2R * rot θ)⁻¹ UpperHalfPlane.I = Smat • z := by
  rw [tsmul, tr_inv_eq, mul_smul, mul_smul, inv_smul_eq_iff.2 Smat_smul_I.symm, mul_smul, rot_smul_I,
    toSL2R_smul_I]

/-- **Schur orthogonality against the lowest weight vector**: for `v ∈ A²_n` with holomorphic representative `φ`,
`∫_{SL(2,ℝ)} |⟨v, D_n(g) e₀⟩|² dg = 2π |c₀|² ‖v‖²` with `c₀ = (4π/(n-1)) (-2i)⁻ⁿ`; for `v = e₀` this is
`formal_degree_lowest`. -/
theorem schur_lowest {n : ℕ} (hn : 2 ≤ n) {v : Hn n} {φ : ℍ → ℂ}
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hv : v =ᵐ[μn n] φ) :
    ∫⁻ g, ENNReal.ofReal (‖⟪v, discreteAction n g (lowestClass hn)⟫_ℂ‖ ^ 2) ∂haarR =
      ENNReal.ofReal (2 * π * ‖evalConst n‖ ^ 2) * ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂μn n := by
  set H : ℍ → ℝ := fun u => u.im ^ n * ‖φ u‖ ^ 2 with hH
  have hHc : Continuous H := by
    simp only [hH]
    exact (UpperHalfPlane.continuous_im.pow n).mul (hφ.continuous.norm.pow 2)
  have h1 : ∀ g : SL2R, ENNReal.ofReal (‖⟪v, discreteAction n g (lowestClass hn)⟫_ℂ‖ ^ 2) =
      ENNReal.ofReal (‖evalConst n‖ ^ 2 * H (tsmul g⁻¹ UpperHalfPlane.I)) := fun g => by
    rw [norm_sq_pairing_holo hn hφ hv g]
  simp only [h1]
  have hmeas : Measurable fun g : SL2R => ENNReal.ofReal (‖evalConst n‖ ^ 2 * H (tsmul g⁻¹ UpperHalfPlane.I)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have hc : Continuous fun g : SL2R => tsmul g⁻¹ UpperHalfPlane.I := by
      unfold tsmul
      exact (continuous_tr.comp continuous_inv).smul continuous_const
    exact (continuous_const.mul (hHc.comp hc)).measurable
  rw [lintegral_haarR hmeas]
  have h2 : ∀ z : ℍ, ∫⁻ θ in Ioc 0 (2 * π),
      ENNReal.ofReal (‖evalConst n‖ ^ 2 * H (tsmul (z.toSL2R * rot θ)⁻¹ UpperHalfPlane.I)) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (‖evalConst n‖ ^ 2 * H (Smat • z)) := by
    intro z
    simp only [tsmul_inv_iwasawa]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  simp only [h2]
  have hm2 : Measurable fun z : ℍ => ENNReal.ofReal (‖evalConst n‖ ^ 2 * H (Smat • z)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (continuous_const.mul (hHc.comp (continuous_const_smul Smat))).measurable
  rw [lintegral_const_mul _ hm2]
  have hmp : MeasurePreserving (fun z : ℍ => Smat • z) volume volume := measurePreserving_smul Smat volume
  have h3 : ∫⁻ z : ℍ, ENNReal.ofReal (‖evalConst n‖ ^ 2 * H (Smat • z)) =
      ∫⁻ u : ℍ, ENNReal.ofReal (‖evalConst n‖ ^ 2 * H u) := by
    have hm : Measurable fun u : ℍ => ENNReal.ofReal (‖evalConst n‖ ^ 2 * H u) :=
      (ENNReal.measurable_ofReal.comp (continuous_const.mul hHc).measurable)
    exact hmp.lintegral_comp hm
  rw [h3]
  have hφm : Measurable fun z : ℍ => ‖φ z‖ₑ ^ 2 := hφ.continuous.measurable.enorm.pow_const _
  rw [lintegral_μn n hφm]
  have h4 : ∀ u : ℍ, ENNReal.ofReal (‖evalConst n‖ ^ 2 * H u) =
      ENNReal.ofReal (‖evalConst n‖ ^ 2) * (wt n u * ‖φ u‖ₑ ^ 2) := by
    intro u
    simp only [hH, wt]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (pow_nonneg u.im_pos.le _),
      ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [h4]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end Lightlike.Lorentz
