module

public import Lightlike.Lorentz.SL2R
public import Lightlike.Lorentz.WeightedComp

/-!
# The holomorphic discrete series of SL(2,ℝ): the action on `L²(ℍ, yⁿ dμ_ℍ)`

For `n ∈ ℕ` the group `SL(2,ℝ)` acts on functions on the upper half-plane `ℍ` by

  `(D_n(g) f)(z) = (b z + d)^{-n} · f((a z + c) / (b z + d))`,   `g = [[a, b], [c, d]]`,

the weight-`n` slash action of `gᵀ`. This file shows that `D_n` is a unitary representation on
`L²(ℍ, μ_n)` with `μ_n = yⁿ dμ_ℍ = y^{n-2} dx dy`, and that it preserves the classes of
holomorphic functions. The holomorphic discrete series `D_n^+` (`n ≥ 2`) is its restriction to the
weighted Bergman space `A²_n` of holomorphic classes, whose closedness is proved in
`SL2RBergman.lean`.

As for the principal series (`SL2RPrincipal.lean`), the transpose replaces the inverse of the
usual form `(D(g) f)(z) = (-c z + a)^{-n} f(g⁻¹ z)` (Knapp, Ch. II §5; Lang, Ch. IX); since
`(gᵀ)⁻¹ = w g w⁻¹` with `w = [[0, 1], [-1, 0]]`, the two differ by an inner automorphism.

## Main results

* `tsmul g z = gᵀ • z` is a right action (`tsmul_mul`) with cocycle `jac_mul`, where
  `jac g z = b z + d`, and `Im (gᵀ • z) = Im z / |b z + d|²` (`im_tsmul`).
* `discreteAction n : ContRepresentation ℂ SL2R (L²(ℍ, μ_n))`, multiplicative and unitary
  (`discreteAction_norm`, `discreteAction_inner`, `discreteAction_mem_unitary`).
* `holoSubmodule n`: the classes with a holomorphic representative, invariant under `D_n`
  (`discreteAction_mem_holoSubmodule`).
* `continuous_discreteAction`, `continuous_discreteAction_action`: `D_n` is strongly and jointly
  continuous, proved on compactly supported continuous functions (`continuous_discreteCoeff`)
  and extended by density with the generic lemmas of `WeightedComp.lean`.

References: A. W. Knapp, *Representation Theory of Semisimple Groups* (Princeton, 1986),
Ch. II §5; S. Lang, *SL₂(ℝ)*, Graduate Texts in Mathematics 105 (Springer, 1985), Ch. IX §2.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology Metric UpperHalfPlane
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace Manifold

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-! ## The transpose action on `ℍ` and its automorphy factor -/

/-- The transpose `gᵀ` as an element of `SL(2,ℝ)`. -/
abbrev tr (g : SL2R) : SL2R := Matrix.SpecialLinearGroup.transpose g

lemma tr_apply (g : SL2R) (i j : Fin 2) : tr g i j = g j i := rfl

lemma tr_mul (g h : SL2R) : tr (g * h) = tr h * tr g := by
  ext i j
  simp only [tr_apply, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  ring

@[simp] lemma tr_one : tr 1 = 1 := by
  ext i j
  simp only [tr_apply, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> rfl

/-- **The transpose action** `tsmul g z = gᵀ • z = (a z + c) / (b z + d)` on `ℍ`. -/
def tsmul (g : SL2R) (z : ℍ) : ℍ := tr g • z

/-- The automorphy factor `jac g z = b z + d`. -/
def jac (g : SL2R) (z : ℂ) : ℂ := g 0 1 * z + g 1 1

lemma coe_tsmul (g : SL2R) (z : ℍ) :
    ((tsmul g z : ℍ) : ℂ) = (g 0 0 * (z : ℂ) + g 1 0) / jac g z := by
  rw [tsmul, coe_smul]; rfl

lemma jac_ne_zero (g : SL2R) (z : ℍ) : jac g z ≠ 0 :=
  denom_ne_zero' (tr g) z

lemma jac_eq_denom (g : SL2R) (z : ℍ) :
    jac g z = UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ (tr g)) z := by
  simp [jac, UpperHalfPlane.denom]

@[simp] lemma tsmul_one (z : ℍ) : tsmul 1 z = z := by simp [tsmul]

@[simp] lemma jac_one (z : ℂ) : jac 1 z = 1 := by simp [jac]

/-- **Right action** `tsmul (g h) = tsmul h ∘ tsmul g`. -/
lemma tsmul_mul (g h : SL2R) (z : ℍ) : tsmul (g * h) z = tsmul h (tsmul g z) := by
  rw [tsmul, tr_mul, mul_smul]; rfl

/-- **Cocycle identity** `jac (g h) z = jac g z · jac h (gᵀ • z)`. -/
lemma jac_mul (g h : SL2R) (z : ℍ) : jac (g * h) z = jac g z * jac h (tsmul g z) := by
  have hz := jac_ne_zero g z
  rw [coe_tsmul]
  simp only [jac, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two] at hz ⊢
  push_cast
  field_simp
  ring

/-- **Imaginary part** `Im (gᵀ • z) = Im z / |b z + d|²`. -/
lemma im_tsmul (g : SL2R) (z : ℍ) : (tsmul g z).im = z.im / Complex.normSq (jac g z) := by
  rw [tsmul, jac_eq_denom, show tr g • z = Matrix.SpecialLinearGroup.mapGL ℝ (tr g) • z from rfl,
    UpperHalfPlane.im_smul_eq_div_normSq]
  simp

lemma continuous_tsmul (g : SL2R) : Continuous (tsmul g) := continuous_const_smul (tr g)

lemma measurable_tsmul (g : SL2R) : Measurable (tsmul g) := (continuous_tsmul g).measurable

lemma continuous_jac (g : SL2R) : Continuous fun z : ℍ => jac g z := by
  unfold jac; fun_prop

lemma continuous_jac_zpow (g : SL2R) (k : ℤ) : Continuous fun z : ℍ => jac g z ^ k :=
  (continuous_jac g).zpow₀ k fun z => Or.inl (jac_ne_zero g z)

/-- `z ↦ gᵀ • z` preserves the invariant measure `μ_ℍ`. -/
lemma measurePreserving_tsmul (g : SL2R) :
    MeasurePreserving (tsmul g) (volume : Measure ℍ) volume :=
  measurePreserving_smul (tr g) volume

/-! ## The measure `μ_n = yⁿ dμ_ℍ` and unitarity -/

/-- The density `yⁿ` of `μ_n` with respect to `μ_ℍ`. -/
def wt (n : ℕ) (z : ℍ) : ℝ≥0∞ := ENNReal.ofReal (z.im ^ n)

lemma measurable_wt (n : ℕ) : Measurable (wt n) :=
  ENNReal.measurable_ofReal.comp ((UpperHalfPlane.continuous_im.pow n).measurable)

lemma wt_ne_zero (n : ℕ) (z : ℍ) : wt n z ≠ 0 := by
  rw [wt, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact pow_pos z.im_pos n

/-- **The measure `μ_n = yⁿ dμ_ℍ = y^{n-2} dx dy`** on `ℍ`. -/
def μn (n : ℕ) : Measure ℍ := (volume : Measure ℍ).withDensity (wt n)

lemma lintegral_μn (n : ℕ) {F : ℍ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂μn n = ∫⁻ z, wt n z * F z :=
  lintegral_withDensity_eq_lintegral_mul _ (measurable_wt n) hF

lemma μn_ac (n : ℕ) : μn n ≪ volume := withDensity_absolutelyContinuous _ _

lemma ac_μn (n : ℕ) : (volume : Measure ℍ) ≪ μn n :=
  withDensity_absolutelyContinuous' (measurable_wt n).aemeasurable
    (Eventually.of_forall (wt_ne_zero n))

lemma quasiMeasurePreserving_tsmul (n : ℕ) (g : SL2R) :
    QuasiMeasurePreserving (tsmul g) (μn n) (μn n) :=
  ((measurePreserving_tsmul g).quasiMeasurePreserving.mono_left (μn_ac n)).mono_right (ac_μn n)

/-- The Hilbert space `L²(ℍ, μ_n)`. -/
abbrev Hn (n : ℕ) := Lp ℂ 2 (μn n)

/-- **The pointwise identity behind unitarity**:
`yⁿ |b z + d|^{-2n} = Im (gᵀ • z)ⁿ`. -/
lemma wt_mul_enorm_jac (n : ℕ) (g : SL2R) (z : ℍ) (w : ℂ) :
    wt n z * ‖jac g z ^ (-(n : ℤ)) * w‖ₑ ^ (2 : ℝ) = wt n (tsmul g z) * ‖w‖ₑ ^ (2 : ℝ) := by
  have hj := jac_ne_zero g z
  have hns : 0 < Complex.normSq (jac g z) := Complex.normSq_pos.mpr hj
  simp only [wt, ← ofReal_norm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (pow_nonneg z.im_pos.le _), ← ENNReal.ofReal_mul
      (pow_nonneg (tsmul g z).im_pos.le _)]
  congr 1
  rw [im_tsmul, norm_mul, norm_zpow, mul_pow, ← Complex.normSq_eq_norm_sq, div_pow]
  rw [show (‖jac g z‖ ^ (-(n : ℤ))) ^ 2 = (Complex.normSq (jac g z) ^ n)⁻¹ by
    rw [Complex.normSq_eq_norm_sq, _root_.zpow_neg, zpow_natCast, inv_pow, ← pow_mul,
      ← pow_mul, mul_comm]]
  field_simp

/-- **The `L²` identity** behind unitarity: `∫⁻ |D_n(g) f|² dμ_n = ∫⁻ |f|² dμ_n`. -/
theorem lintegral_discrete (n : ℕ) (g : SL2R) (f : ℍ → ℂ) (hf : Measurable f) :
    ∫⁻ z : ℍ, ‖jac g z ^ (-(n : ℤ)) * f (tsmul g z)‖ₑ ^ (2 : ℝ) ∂μn n =
      ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂μn n := by
  have hf2 : Measurable fun z => ‖f z‖ₑ ^ (2 : ℝ) := hf.enorm.pow_const _
  have hF : Measurable fun z : ℍ => ‖jac g z ^ (-(n : ℤ)) * f (tsmul g z)‖ₑ ^ (2 : ℝ) :=
    ((continuous_jac_zpow g _).measurable.mul (hf.comp (measurable_tsmul g))).enorm.pow_const _
  rw [lintegral_μn n hF, lintegral_μn n hf2]
  simp only [wt_mul_enorm_jac]
  exact (measurePreserving_tsmul g).lintegral_comp ((measurable_wt n).mul hf2)

lemma aestronglyMeasurable_jac_zpow (n : ℕ) (g : SL2R) :
    AEStronglyMeasurable (fun z : ℍ => jac g z ^ (-(n : ℤ))) (μn n) :=
  (continuous_jac_zpow g _).aestronglyMeasurable

/-- The operator `D_n(g)` as a linear isometry of `L²(ℍ, μ_n)`. -/
def discreteIso (n : ℕ) (g : SL2R) : Hn n →ₗᵢ[ℂ] Hn n :=
  weightedCompL2 (μn n) (fun z : ℍ => jac g z ^ (-(n : ℤ))) (tsmul g)
    (aestronglyMeasurable_jac_zpow n g) (quasiMeasurePreserving_tsmul n g)
    (fun f hf => lintegral_discrete n g f hf)

lemma coeFn_discreteIso (n : ℕ) (g : SL2R) (f : Hn n) :
    discreteIso n g f =ᵐ[μn n] fun z : ℍ => jac g z ^ (-(n : ℤ)) * f (tsmul g z) :=
  coeFn_weightedCompL2 _ _ _ _ _ _ f

lemma discreteIso_one (n : ℕ) (f : Hn n) : discreteIso n 1 f = f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_discreteIso n 1 f] with z hz
  rw [hz]; simp

lemma discreteIso_mul (n : ℕ) (g h : SL2R) (f : Hn n) :
    discreteIso n (g * h) f = discreteIso n g (discreteIso n h f) := by
  rw [Lp.ext_iff]
  have h1 := coeFn_discreteIso n (g * h) f
  have h2 := coeFn_discreteIso n g (discreteIso n h f)
  have h3 := (quasiMeasurePreserving_tsmul n g).ae_eq_comp (coeFn_discreteIso n h f)
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  simp only [Function.comp_apply] at hz3
  rw [hz1, hz2, hz3, jac_mul, tsmul_mul, mul_zpow]; ring

/-- **The representation `D_n`** of `SL(2,ℝ)` on `L²(ℍ, μ_n)`. -/
def discreteAction (n : ℕ) : ContRepresentation ℂ SL2R (Hn n) :=
  .ofMonoidHom
    { toFun := fun g => (discreteIso n g).toContinuousLinearMap
      map_one' := by ext1 f; exact discreteIso_one n f
      map_mul' := fun g h => by ext1 f; exact discreteIso_mul n g h f }

lemma discreteAction_apply (n : ℕ) (g : SL2R) (f : Hn n) :
    discreteAction n g f = discreteIso n g f := rfl

/-- `D_n` acts by the explicit formula, almost everywhere. -/
theorem coeFn_discreteAction (n : ℕ) (g : SL2R) (f : Hn n) :
    discreteAction n g f =ᵐ[μn n] fun z : ℍ => jac g z ^ (-(n : ℤ)) * f (tsmul g z) :=
  coeFn_discreteIso n g f

/-- **Unitarity (norm form):** `‖D_n(g) f‖ = ‖f‖`. -/
theorem discreteAction_norm (n : ℕ) (g : SL2R) (f : Hn n) : ‖discreteAction n g f‖ = ‖f‖ :=
  (discreteIso n g).norm_map f

/-- **Unitarity:** `D_n(g)` preserves the inner product of `L²(ℍ, μ_n)`. -/
theorem discreteAction_inner (n : ℕ) (g : SL2R) (f f' : Hn n) :
    ⟪discreteAction n g f, discreteAction n g f'⟫_ℂ = ⟪f, f'⟫_ℂ :=
  (discreteIso n g).inner_map_map f f'

/-- **Each `D_n(g)` is a unitary operator** on `L²(ℍ, μ_n)`. -/
theorem discreteAction_mem_unitary (n : ℕ) (g : SL2R) :
    discreteAction n g ∈ unitary (Hn n →L[ℂ] Hn n) :=
  mem_unitary_of_inner _ (discreteAction_inner n) g

/-! ## Holomorphic classes -/

/-- The classes in `L²(ℍ, μ_n)` with a holomorphic representative. -/
def holoSubmodule (n : ℕ) : Submodule ℂ (Hn n) where
  carrier := {f | ∃ φ : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ ∧ f =ᵐ[μn n] φ}
  add_mem' := by
    rintro f f' ⟨φ, hφ, hf⟩ ⟨φ', hφ', hf'⟩
    refine ⟨φ + φ', hφ.add hφ', ?_⟩
    filter_upwards [Lp.coeFn_add f f', hf, hf'] with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.add_apply]
  zero_mem' := ⟨0, mdifferentiable_const, Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c f ⟨φ, hφ, hf⟩
    refine ⟨c • φ, hφ.const_smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hf] with z h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.smul_apply]

/-- `D_n(g)` of a holomorphic function is the weight-`n` slash of `gᵀ`, hence holomorphic. -/
lemma mdifferentiable_discrete (n : ℕ) (g : SL2R) {φ : ℍ → ℂ}
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : ℍ => jac g z ^ (-(n : ℤ)) * φ (tsmul g z) := by
  have hdet : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ (tr g)).det.val := by simp
  have h1 := mdifferentiable_denom_zpow (Matrix.SpecialLinearGroup.mapGL ℝ (tr g)) (-(n : ℤ))
  have h2 := hφ.comp (mdifferentiable_smul hdet)
  simp only [← jac_eq_denom] at h1
  exact h1.mul h2

/-- **`D_n` preserves the holomorphic classes.** -/
theorem discreteAction_mem_holoSubmodule (n : ℕ) (g : SL2R) {f : Hn n}
    (hf : f ∈ holoSubmodule n) : discreteAction n g f ∈ holoSubmodule n := by
  obtain ⟨φ, hφ, hfφ⟩ := hf
  refine ⟨_, mdifferentiable_discrete n g hφ, ?_⟩
  have h3 := (quasiMeasurePreserving_tsmul n g).ae_eq_comp hfφ
  filter_upwards [coeFn_discreteAction n g f, h3] with z h1 h2
  simp only [Function.comp_apply] at h2
  rw [h1, h2]

/-! ## Strong continuity

Matrix coefficients of continuous compactly supported functions are continuous, by the
parametric-integral theorem over the compact support. Since `μ_n` is a locally finite measure on a
σ-compact metric space, it is regular and `C_c` is dense in `L²(ℍ, μ_n)`; unitarity then gives
strong and joint continuity (`continuous_of_dense_coeff`, `continuous_action_of_norm`). -/

/-- `μ_n = yⁿ dμ_ℍ` is locally finite (its density is continuous). -/
instance instIsLocallyFiniteMeasure_μn (n : ℕ) : IsLocallyFiniteMeasure (μn n) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (UpperHalfPlane.continuous_im.pow n)

lemma continuous_tr : Continuous tr :=
  (continuous_subtype_val.matrix_transpose).subtype_mk _

/-- The action `(g, z) ↦ gᵀ • z` is jointly continuous. -/
lemma continuous_tsmul₂ : Continuous fun p : SL2R × ℍ => tsmul p.1 p.2 :=
  (continuous_tr.comp continuous_fst).smul continuous_snd

/-- The automorphy factor `(g, z) ↦ b z + d` is jointly continuous. -/
lemma continuous_jac₂ : Continuous fun p : SL2R × ℍ => jac p.1 p.2 := by
  have h : ∀ i j, Continuous fun p : SL2R × ℍ =>
      (((p.1 : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ) := fun i j =>
    Complex.continuous_ofReal.comp ((continuous_subtype_val.matrix_elem i j).comp continuous_fst)
  exact ((h 0 1).mul (UpperHalfPlane.continuous_coe.comp continuous_snd)).add (h 1 1)

/-- The integrand of the matrix coefficient `⟪D_n(g) φ, φ⟫`. -/
def discreteCoeff (n : ℕ) (φ : ℍ → ℂ) (g : SL2R) (z : ℍ) : ℂ :=
  conj (jac g z ^ (-(n : ℤ)) * φ (tsmul g z)) * φ z

/-- The matrix coefficient of a class with representative `φ` as an explicit integral. -/
lemma inner_discreteAction_eq (n : ℕ) {F : Hn n} {φ : ℍ → ℂ} (hF : F =ᵐ[μn n] φ) (g : SL2R) :
    ⟪discreteAction n g F, F⟫_ℂ = ∫ z, discreteCoeff n φ g z ∂μn n := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h3 := (quasiMeasurePreserving_tsmul n g).ae_eq_comp hF
  filter_upwards [coeFn_discreteAction n g F, hF, h3] with z hz1 hz2 hz3
  simp only [Function.comp_apply] at hz3
  rw [hz1, hz2, hz3, discreteCoeff, RCLike.inner_apply, mul_comm]

/-- For continuous compactly supported `φ`, the coefficient `g ↦ ∫ conj(D_n(g) φ) φ dμ_n` is
continuous. -/
theorem continuous_discreteCoeff (n : ℕ) {φ : ℍ → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Continuous fun g => ∫ z, discreteCoeff n φ g z ∂μn n := by
  have e : (fun g => ∫ z, discreteCoeff n φ g z ∂μn n) =
      fun g => ∫ z in tsupport φ, discreteCoeff n φ g z ∂μn n := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    simp [discreteCoeff, image_eq_zero_of_notMem_tsupport hz]
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ hφc.isCompact
  have hj : Continuous fun p : SL2R × ℍ => jac p.1 p.2 ^ (-(n : ℤ)) :=
    continuous_jac₂.zpow₀ _ fun p => Or.inl (jac_ne_zero p.1 p.2)
  exact (Complex.continuous_conj.comp (hj.mul (hφ.comp continuous_tsmul₂))).mul
    (hφ.comp continuous_snd)

/-- **Strong continuity of `D_n`**: `g ↦ D_n(g) f` is continuous for every `f ∈ L²(ℍ, μ_n)`. -/
theorem continuous_discreteAction (n : ℕ) (f : Hn n) :
    Continuous fun g => discreteAction n g f :=
  continuous_of_dense_coeff (discreteAction n) (discreteAction_norm n)
    (dense_hasCompactSupport_L2 (μn n)) (fun _ ⟨φ, hφ, hφc, hF⟩ => by
      rw [show (fun g => ⟪discreteAction n g _, _⟫_ℂ) = fun g => ∫ z, discreteCoeff n φ g z ∂μn n
        from funext (inner_discreteAction_eq n hF)]
      exact (continuous_discreteCoeff n hφ hφc).continuousAt) f

/-- **Joint continuity of `D_n`**: `(g, f) ↦ D_n(g) f` is continuous. -/
theorem continuous_discreteAction_action (n : ℕ) :
    Continuous fun p : SL2R × Hn n => discreteAction n p.1 p.2 :=
  continuous_action_of_norm (discreteAction n) (discreteAction_norm n) (continuous_discreteAction n)

end Lightlike.Lorentz.SL2R
