import Lightlike.Poincare.OneParticleRestricted

/-!
# The massless one-particle representations on `L²` of the light cone

For helicity `n/2` the induced representation acts on scalar wave functions on the forward light cone by
`(U(A) ψ)(P) = χ_n(W(A, A⁻¹ P)) ψ(A⁻¹ P)` (`helicityAct`), with the unimodular helicity character
`χ_n(W) = (W₀₀)ⁿ` of the Wigner element. The standard lift of the cone is not continuous, so the factor
`P ↦ χ_n(W(A, A⁻¹ P))` (`helMult`) is only measurable; it is unimodular, and multiplication by it is a linear isometry
of `L²` (`mulScalarL2`). For every invariant measure `μ` on the cone, `U(A)` is a unitary operator of `L²(μ)`
(`helL2E`), `U(AB) = U(A) U(B)` (`helL2_mul`), and with the translations `(T(a) ψ)(p) = e^{i p·a} ψ(p)`
(`translCone`), `V(a, A) = T(a) U(A)` is a unitary representation of `ℝ⁴ ⋊ SL(2,ℂ)` (`poincareCone_mul`).

Supporting results for the one-particle space; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz

namespace Lightlike.Poincare

noncomputable section

/-! ## Measurability of the standard lift of the cone -/

lemma measurable_alphaC : Measurable fun P : LightCone => alphaC P.1 :=
  (Complex.continuous_re.comp ((continuous_subtype_val : Continuous fun P : LightCone =>
    (P.1 : Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem 0 0)).measurable

lemma measurable_deltaC : Measurable fun P : LightCone => deltaC P.1 :=
  (Complex.continuous_re.comp ((continuous_subtype_val : Continuous fun P : LightCone =>
    (P.1 : Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem 1 1)).measurable

lemma measurable_entry01 : Measurable fun P : LightCone => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1 :=
  ((continuous_subtype_val : Continuous fun P : LightCone =>
    (P.1 : Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem 0 1).measurable

lemma measurable_coneLiftMat (i j : Fin 2) : Measurable fun P : LightCone => coneLiftMat P.1 i j := by
  have hs : MeasurableSet {P : LightCone | 0 < alphaC P.1} := measurableSet_lt measurable_const measurable_alphaC
  have ha : Measurable fun P : LightCone => ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_alphaC.div_const 2).sqrt)
  have hd : Measurable fun P : LightCone => ((Real.sqrt (deltaC P.1 / 2) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp ((measurable_deltaC.div_const 2).sqrt)
  have e : ∀ P : LightCone, coneLiftMat P.1 i j = if 0 < alphaC P.1 then
      (!![((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ), 0;
        starRingEnd ℂ ((P.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1) / (2 * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)),
        1 / ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) i j
      else (!![0, -1 / ((Real.sqrt (deltaC P.1 / 2) : ℝ) : ℂ);
        ((Real.sqrt (deltaC P.1 / 2) : ℝ) : ℂ), 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
    intro P
    unfold coneLiftMat
    split_ifs <;> rfl
  rw [show (fun P : LightCone => coneLiftMat P.1 i j) = _ from funext e]
  refine Measurable.ite hs ?_ ?_ <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue, Fin.mk_one]
  · exact ha
  · exact measurable_const
  · exact ((Complex.continuous_conj.measurable).comp measurable_entry01).div (measurable_const.mul ha)
  · exact measurable_const.div ha
  · exact measurable_const
  · exact measurable_const.div hd
  · exact hd
  · exact measurable_const

/-! ## The helicity factor -/

/-- The helicity factor `χ_n(W(A, A⁻¹ P)) = (W₀₀)ⁿ`. -/
def helMult (n : ℤ) (A : SL2C) (Q : LightCone) : ℂ :=
  ((wignerStab coneLift_smul A (A⁻¹ • Q)).1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^ n

lemma helicityAct_eq (n : ℤ) (A : SL2C) (ψ : LightCone → ℂ) (Q : LightCone) :
    helicityAct n A ψ Q = helMult n A Q * ψ (A⁻¹ • Q) := by
  simp [helicityAct, inducedActG, helicityChar, helMult]

lemma norm_helMult (n : ℤ) (A : SL2C) (Q : LightCone) : ‖helMult n A Q‖ = 1 :=
  norm_helicity n _

lemma helMult_entry (A : SL2C) (Q : LightCone) :
    ((wignerStab coneLift_smul A (A⁻¹ • Q)).1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      ((coneLiftMat Q.1).adjugate * (A : Matrix (Fin 2) (Fin 2) ℂ) * coneLiftMat (A⁻¹ • Q).1) 0 0 := by
  simp only [wignerStab, wignerG, smul_inv_smul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  rfl

lemma measurable_helMult (n : ℤ) (A : SL2C) : Measurable (helMult n A) := by
  have hL : ∀ i j, Measurable fun Q : LightCone => coneLiftMat Q.1 i j := measurable_coneLiftMat
  have hL' : ∀ i j, Measurable fun Q : LightCone => coneLiftMat (A⁻¹ • Q).1 i j := fun i j =>
    (measurable_coneLiftMat i j).comp (continuous_smul_lightCone A⁻¹).measurable
  have he : Measurable fun Q : LightCone =>
      ((coneLiftMat Q.1).adjugate * (A : Matrix (Fin 2) (Fin 2) ℂ) * coneLiftMat (A⁻¹ • Q).1) 0 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have := hL 0 0; have := hL 0 1; have := hL 1 0; have := hL 1 1
    have := hL' 0 0; have := hL' 1 0
    fun_prop
  have h : helMult n A = fun Q => ((coneLiftMat Q.1).adjugate * (A : Matrix (Fin 2) (Fin 2) ℂ) *
      coneLiftMat (A⁻¹ • Q).1) 0 0 ^ n := by
    funext Q; rw [helMult, helMult_entry]
  rw [h]
  exact he.pow_const n

/-! ## Multiplication by a unimodular function -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma memLp_mulScalar {c : X → ℂ} (hc : Measurable c) (h1 : ∀ x, ‖c x‖ = 1) (f : Lp ℂ 2 μ) :
    MemLp (fun x => c x * f x) 2 μ :=
  (Lp.memLp f).of_le (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => by rw [norm_mul, h1, one_mul])

/-- **Multiplication by a measurable unimodular function**, a linear isometry of `L²`. -/
def mulScalarL2 (c : X → ℂ) (hc : Measurable c) (h1 : ∀ x, ‖c x‖ = 1) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_mulScalar hc h1 f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_mulScalar hc h1 (f + g)).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((memLp_mulScalar hc h1 f).toLp _) ((memLp_mulScalar hc h1 g).toLp _),
      (memLp_mulScalar hc h1 f).coeFn_toLp, (memLp_mulScalar hc h1 g).coeFn_toLp] with x h1' h2 h3 h4 h5
    rw [h1', h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, mul_add]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [(memLp_mulScalar hc h1 (a • f)).coeFn_toLp, Lp.coeFn_smul a f,
      Lp.coeFn_smul a ((memLp_mulScalar hc h1 f).toLp _), (memLp_mulScalar hc h1 f).coeFn_toLp]
      with x h1' h2 h3 h4
    rw [h1', RingHom.id_apply, h3, Pi.smul_apply, h4, h2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  norm_map' f := by
    change ‖(memLp_mulScalar hc h1 f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable f) (Filter.Eventually.of_forall fun x => by rw [norm_mul, h1, one_mul])

lemma coeFn_mulScalarL2 {c : X → ℂ} (hc : Measurable c) (h1 : ∀ x, ‖c x‖ = 1) (f : Lp ℂ 2 μ) :
    (mulScalarL2 (μ := μ) c hc h1 f : X → ℂ) =ᵐ[μ] fun x => c x * f x :=
  (memLp_mulScalar hc h1 f).coeFn_toLp

/-! ## The helicity representation on `L²` -/

variable {ν : Measure LightCone}

/-- **The massless representation of helicity `n/2` on `L²(ν)`**, for an invariant measure `ν` on the cone. -/
def helL2 (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (A : SL2C) :
    Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ν :=
  (mulScalarL2 (helMult n A) (measurable_helMult n A) (norm_helMult n A)).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (fun Q : LightCone => A⁻¹ • Q) (hν A⁻¹))

lemma coeFn_helL2 (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (A : SL2C)
    (f : Lp ℂ 2 ν) : (helL2 n hν A f : LightCone → ℂ) =ᵐ[ν] fun Q => helMult n A Q * f (A⁻¹ • Q) := by
  have h1 := coeFn_mulScalarL2 (measurable_helMult n A) (norm_helMult n A)
    (Lp.compMeasurePreservingₗᵢ ℂ (fun Q : LightCone => A⁻¹ • Q) (hν A⁻¹) f)
  have h2 := Lp.coeFn_compMeasurePreserving f (hν A⁻¹)
  filter_upwards [h1, h2] with Q hQ1 hQ2
  rw [show helL2 n hν A f = mulScalarL2 (helMult n A) (measurable_helMult n A) (norm_helMult n A)
    (Lp.compMeasurePreservingₗᵢ ℂ (fun Q : LightCone => A⁻¹ • Q) (hν A⁻¹) f) from rfl, hQ1]
  congr 1

/-- **The group law on `L²` of the cone**: `U(A B) = U(A) U(B)`. -/
lemma helL2_mul (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (A B : SL2C)
    (f : Lp ℂ 2 ν) : helL2 n hν (A * B) f = helL2 n hν A (helL2 n hν B f) := by
  apply Lp.ext
  have h3 := (hν A⁻¹).quasiMeasurePreserving.ae_eq_comp (coeFn_helL2 n hν B f)
  filter_upwards [coeFn_helL2 n hν (A * B) f, coeFn_helL2 n hν A (helL2 n hν B f), h3] with Q hQ1 hQ2 hQ3
  rw [hQ1, hQ2]
  simp only [Function.comp_apply] at hQ3
  rw [hQ3]
  have h := congrFun (helicityAct_mul n A B (f : LightCone → ℂ)) Q
  rw [helicityAct_eq, helicityAct_eq, helicityAct_eq] at h
  exact h

lemma helL2_one (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν)
    (f : Lp ℂ 2 ν) : helL2 n hν 1 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_helL2 n hν 1 f] with Q hQ
  rw [hQ]
  have h := congrFun (helicityAct_one n (f : LightCone → ℂ)) Q
  rw [helicityAct_eq] at h
  rw [h]

/-- `U(A)` as a unitary operator of `L²` of the cone. -/
def helL2E (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (A : SL2C) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 ν :=
  LinearIsometryEquiv.ofSurjective (helL2 n hν A) fun f =>
    ⟨helL2 n hν A⁻¹ f, by rw [← helL2_mul, mul_inv_cancel, helL2_one]⟩

/-! ## Translations and the Poincaré representation on the cone -/

lemma continuous_pairing_cone (a : Transl) : Continuous fun Q : LightCone => pairing Q.1 a.1 :=
  Complex.continuous_re.comp ((continuous_mink_left a.1).comp continuous_subtype_val)

/-- The translations on `L²` of the cone: `(T(a) ψ)(p) = e^{i p·a} ψ(p)`. -/
def translCone (a : Transl) : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ν :=
  mulScalarL2 (fun Q : LightCone => Complex.exp (Complex.I * pairing Q.1 a.1))
    (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_pairing_cone a)))).measurable
    (fun Q => by
      rw [show Complex.I * (pairing Q.1 a.1 : ℂ) = (pairing Q.1 a.1 : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I])

lemma coeFn_translCone (a : Transl) (f : Lp ℂ 2 ν) :
    (translCone a f : LightCone → ℂ) =ᵐ[ν] fun Q => Complex.exp (Complex.I * pairing Q.1 a.1) * f Q :=
  coeFn_mulScalarL2 _ _ f

lemma helL2_translCone (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν)
    (A : SL2C) (b : Transl) (f : Lp ℂ 2 ν) :
    helL2 n hν A (translCone b f) = translCone (translAct A b) (helL2 n hν A f) := by
  apply Lp.ext
  have h3 := (hν A⁻¹).quasiMeasurePreserving.ae_eq_comp (coeFn_translCone b f)
  filter_upwards [coeFn_helL2 n hν A (translCone b f), coeFn_translCone (translAct A b) (helL2 n hν A f),
    coeFn_helL2 n hν A f, h3] with Q h1 h2 h4 h5
  simp only [Function.comp_apply] at h5
  rw [h1, h2, h4, h5]
  have : pairing (A⁻¹ • Q).1 b.1 = pairing Q.1 (translAct A b).1 := by
    have h := pairing_actP A (A⁻¹ • Q).1 b.1
    have hQ : actP A (A⁻¹ • Q).1 = Q.1 := by
      rw [← coe_smul_lightCone, smul_inv_smul]
    rw [hQ] at h
    exact h.symm
  rw [this]
  ring

lemma translCone_add (a b : Transl) (f : Lp ℂ 2 ν) : translCone (a + b) f = translCone a (translCone b f) := by
  apply Lp.ext
  filter_upwards [coeFn_translCone (ν := ν) (a + b) f, coeFn_translCone a (translCone b f),
    coeFn_translCone b f] with Q h1 h2 h3
  rw [h1, h2, h3, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [AddSubgroup.coe_add, pairing_add]
  push_cast
  ring

lemma translCone_zero (f : Lp ℂ 2 ν) : translCone 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translCone (ν := ν) 0 f] with Q h
  rw [h]
  simp [pairing, mink]

/-- **The massless unitary representation of `ℝ⁴ ⋊ SL(2,ℂ)`** of helicity `n/2`: `V(a, A) = T(a) U(A)`. -/
def poincareCone (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (a : Transl)
    (A : SL2C) : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ν :=
  (translCone a).comp (helL2 n hν A)

theorem poincareCone_mul (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν)
    (a b : Transl) (A B : SL2C) (f : Lp ℂ 2 ν) :
    poincareCone n hν a A (poincareCone n hν b B f) = poincareCone n hν (a + translAct A b) (A * B) f := by
  simp only [poincareCone, LinearIsometry.coe_comp, Function.comp_apply]
  rw [helL2_translCone, translCone_add, helL2_mul]

theorem poincareCone_one (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν)
    (f : Lp ℂ 2 ν) : poincareCone n hν 0 1 f = f := by
  simp only [poincareCone, LinearIsometry.coe_comp, Function.comp_apply, helL2_one, translCone_zero]

end

end Lightlike.Poincare
