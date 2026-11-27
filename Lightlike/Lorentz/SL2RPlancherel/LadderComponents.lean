module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.KKParseval
public import Lightlike.Lorentz.SL2RPlancherel.SmoothRight
public import Lightlike.Lorentz.ParamIntegral

/-!
# The ladder operators on the `K × K` components of a smooth function

For a `C¹` function `f = F ∘ (entries)` on `SL(2,ℝ)`, the right derivatives `A = dF F g H`,
`B = dF F g S` (`SmoothRight`) act on the `K × K` components `f_{m,n}` of `KKParseval` by the
ladder operators of `Ladder`: for `ξ ≠ 0`,
`(A + iB)_{m,n+2} = f_{m,n}' − ((n cosh ξ − m)/(2 sinh ξ)) f_{m,n}` (`kk_ladder_up`) and
`(A − iB)_{m,n−2} = f_{m,n}' + ((n cosh ξ − m)/(2 sinh ξ)) f_{m,n}` (`kk_ladder_down`).  The proof
differentiates under the integral sign in `ξ` (`hasDerivAt_kkIntegral`) and integrates by parts on
the torus of angles (`box_integral_dth`, `box_integral_dal`).  Layer 2c-i of the Plancherel
formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real Lightlike.Lorentz.SL2RPlancherel

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- **Integration by parts on the circle**: for a `C¹` function with `φ 1 = φ 0`,
`∫_0^1 e^{-2πi n x} φ'(x) dx = 2πi n ∫_0^1 e^{-2πi n x} φ(x) dx`. -/
lemma integral_ibp_periodic (n : ℤ) {φ φ' : ℝ → ℂ} (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hφ' : Continuous φ') (hper : φ 1 = φ 0) :
    ∫ x in Ioc (0 : ℝ) 1, Complex.exp (-(2 * π * Complex.I * n * x)) * φ' x =
      2 * π * Complex.I * n * ∫ x in Ioc (0 : ℝ) 1, Complex.exp (-(2 * π * Complex.I * n * x)) * φ x := by
  rw [← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * n * x)))
      (-(2 * π * Complex.I * n) * Complex.exp (-(2 * π * Complex.I * n * x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(2 * π * Complex.I * n * (x : ℂ))) (-(2 * π * Complex.I * n)) x := by
      have h0 := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (2 * π * Complex.I * n)).neg
      exact h0.congr_deriv (by simp)
    have := h1.cexp
    simpa [mul_comm] using this
  have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun x : ℝ => Complex.exp (-(2 * π * Complex.I * n * x))) (v := φ)
    (u' := fun x => -(2 * π * Complex.I * n) * Complex.exp (-(2 * π * Complex.I * n * x))) (v' := φ')
    (fun x _ => hu x) (fun x _ => hφ x)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (hφ'.intervalIntegrable _ _)
  have hu1 : Complex.exp (-(2 * π * Complex.I * n * ((1 : ℝ) : ℂ))) = 1 := by
    have : -(2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = ((-n : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  simp only [hu1, hper, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at this
  rw [this]
  simp only [neg_mul, intervalIntegral.integral_neg, sub_self, zero_sub, neg_neg]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext x; ring

/-- Iterated form of the Bochner integral over the box `(0,1]²`, for continuous integrands. -/
lemma integral_box_eq {G : (Fin 2 → ℝ) → ℂ} (hG : Continuous G) :
    ∫ x in box, G x = ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, G ![a, b] := by
  have hmp := volume_preserving_finTwoArrow ℝ
  have hbox : box = (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    ext x
    simp [box, Fin.forall_fin_two, MeasurableEquiv.finTwoArrow]
  have key := hmp.setIntegral_preimage_emb (MeasurableEquiv.finTwoArrow.measurableEmbedding)
    (fun p => G (MeasurableEquiv.finTwoArrow.symm p)) (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
  simp only [MeasurableEquiv.symm_apply_apply] at key
  rw [hbox, key, Measure.volume_eq_prod, setIntegral_prod]
  · rfl
  · have hc : Continuous fun p : ℝ × ℝ => G (MeasurableEquiv.finTwoArrow.symm p) :=
      hG.comp (continuous_pi fun i => by
        fin_cases i <;> simp [MeasurableEquiv.finTwoArrow] <;> fun_prop)
    have hI : IntegrableOn (fun p : ℝ × ℝ => G (MeasurableEquiv.finTwoArrow.symm p))
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) volume :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    rw [Measure.volume_eq_prod] at hI
    exact hI.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The character `e^{-2πi (m a + n b)}` of the torus. -/
def torusChar (m n : ℤ) (a b : ℝ) : ℂ :=
  Complex.exp (-(2 * π * Complex.I * (m * a + n * b)))

lemma torusChar_eq (m n : ℤ) (a b : ℝ) :
    torusChar m n a b = Complex.exp (-(2 * π * Complex.I * m * a)) *
      Complex.exp (-(2 * π * Complex.I * n * b)) := by
  unfold torusChar
  rw [← Complex.exp_add]
  congr 1
  ring

lemma torusChar_swap (m n : ℤ) (a b : ℝ) : torusChar n m b a = torusChar m n a b := by
  unfold torusChar
  congr 1
  ring

lemma continuous_torusChar (m n : ℤ) : Continuous fun p : ℝ × ℝ => torusChar m n p.1 p.2 := by
  unfold torusChar
  fun_prop

/-- **Integration by parts in the second angle** over the box. -/
lemma box_ibp_b (m n : ℤ) {G D : ℝ → ℝ → ℂ}
    (hG : ∀ a b, HasDerivAt (fun b => G a b) (D a b) b)
    (hD : Continuous fun p : ℝ × ℝ => D p.1 p.2) (hper : ∀ a, G a 1 = G a 0)
    (_hGc : Continuous fun p : ℝ × ℝ => G p.1 p.2) :
    ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, torusChar m n a b * D a b =
      2 * π * Complex.I * n * ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, torusChar m n a b * G a b := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun a _ => ?_
  simp only [torusChar_eq, mul_assoc (Complex.exp _) (Complex.exp _)]
  rw [integral_const_mul, integral_const_mul]
  have := integral_ibp_periodic n (φ := fun b => G a b) (φ' := fun b => D a b) (hG a)
    (hD.comp (continuous_const.prodMk continuous_id)) (hper a)
  rw [this]
  ring

/-- Fubini on the box for continuous integrands. -/
lemma box_swap {H : ℝ → ℝ → ℂ} (hH : Continuous fun p : ℝ × ℝ => H p.1 p.2) :
    ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, H a b =
      ∫ b in Ioc (0 : ℝ) 1, ∫ a in Ioc (0 : ℝ) 1, H a b := by
  apply integral_integral_swap
  have hI : IntegrableOn (fun p : ℝ × ℝ => H p.1 p.2) (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hH.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.prod_restrict]
  exact hI.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- **Integration by parts in the first angle** over the box. -/
lemma box_ibp_a (m n : ℤ) {G D : ℝ → ℝ → ℂ}
    (hG : ∀ a b, HasDerivAt (fun a => G a b) (D a b) a)
    (hD : Continuous fun p : ℝ × ℝ => D p.1 p.2) (hper : ∀ b, G 1 b = G 0 b)
    (hGc : Continuous fun p : ℝ × ℝ => G p.1 p.2) :
    ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, torusChar m n a b * D a b =
      2 * π * Complex.I * m * ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, torusChar m n a b * G a b := by
  have hsw := continuous_swap (X := ℝ) (Y := ℝ)
  rw [box_swap (H := fun a b => torusChar m n a b * D a b) ((continuous_torusChar m n).mul hD),
    box_swap (H := fun a b => torusChar m n a b * G a b) ((continuous_torusChar m n).mul hGc)]
  have := box_ibp_b n m (G := fun b a => G a b) (D := fun b a => D a b) (fun b a => hG a b)
    (hD.comp hsw) hper (hGc.comp hsw)
  simpa only [torusChar_swap] using this

lemma kakM_entries (α ξ θ : ℝ) : kakM α ξ θ =
    !![Real.cos α * Real.exp (ξ / 2) * Real.cos θ + Real.sin α * Real.exp (-(ξ / 2)) * (-Real.sin θ),
       Real.cos α * Real.exp (ξ / 2) * Real.sin θ + Real.sin α * Real.exp (-(ξ / 2)) * Real.cos θ;
       -Real.sin α * Real.exp (ξ / 2) * Real.cos θ + Real.cos α * Real.exp (-(ξ / 2)) * (-Real.sin θ),
       -Real.sin α * Real.exp (ξ / 2) * Real.sin θ + Real.cos α * Real.exp (-(ξ / 2)) * Real.cos θ] := by
  unfold kakM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_aR, Real.exp_neg]

/-- The entries of `k_α a(ξ) k_θ` are smooth in `(α, ξ, θ)`. -/
lemma contDiff_kakE : ContDiff ℝ ⊤ (fun p : ℝ × ℝ × ℝ => ent (kakM p.1 p.2.1 p.2.2)) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  simp only [ent, kakM_entries]
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- The `ξ`-derivative of `P(α, ξ, θ)`, in terms of right derivatives. -/
def dxi (F : Ent → ℂ) (α ξ θ : ℝ) : ℂ :=
  (Real.cos (2 * θ) : ℂ) * dF F (kakM α ξ θ) matH + (Real.sin (2 * θ) : ℂ) * dF F (kakM α ξ θ) matS

lemma measurableSet_box : MeasurableSet box := by
  have : box = Set.pi Set.univ (fun _ : Fin 2 => Ioc (0 : ℝ) 1) := by
    ext x; simp [box]
  rw [this]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

lemma volume_box_ne_top : volume box ≠ ⊤ := by
  have : box ⊆ Icc (0 : Fin 2 → ℝ) 1 := by
    intro x hx
    rw [mem_Icc]
    exact ⟨fun i => (hx i).1.le, fun i => by simpa using (hx i).2⟩
  exact ne_of_lt (lt_of_le_of_lt (measure_mono this) isCompact_Icc.measure_lt_top)

lemma kakP_eq (F : Ent → ℂ) (α ξ θ : ℝ) : kakP F α ξ θ = F (ent (kakM α ξ θ)) := rfl

/-- The smooth parametric integrand of the `K × K` component. -/
def kkPhi (F : Ent → ℂ) (m n : ℤ) (q : ℝ × ℝ) (ξ : ℝ) : ℂ :=
  torusChar m n q.1 q.2 * kakP F (2 * π * q.1) ξ (2 * π * q.2)

lemma contDiff_kkPhi {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (m n : ℤ) :
    ContDiff ℝ 1 (Function.uncurry (kkPhi F m n)) := by
  have hre : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have h1 : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => (p.1.1 : ℂ)) := hre.comp contDiff_fst.fst
  have h2 : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => (p.1.2 : ℂ)) := hre.comp contDiff_fst.snd
  have hchar : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => torusChar m n p.1.1 p.1.2) := by
    unfold torusChar
    refine Complex.contDiff_exp.comp ?_
    exact (contDiff_const.mul ((contDiff_const.mul h1).add (contDiff_const.mul h2))).neg
  have hpt : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => ((2 * π * p.1.1, p.2, 2 * π * p.1.2) : ℝ × ℝ × ℝ)) :=
    (contDiff_const.mul contDiff_fst.fst).prodMk (contDiff_snd.prodMk (contDiff_const.mul contDiff_fst.snd))
  have hk0 : ContDiff ℝ 1 (fun p : ℝ × ℝ × ℝ => ent (kakM p.1 p.2.1 p.2.2)) := contDiff_kakE.of_le le_top
  have hk := hk0.comp hpt
  have hfin : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => torusChar m n p.1.1 p.1.2 *
      F (ent (kakM (2 * π * p.1.1) p.2 (2 * π * p.1.2)))) := hchar.mul (hF.comp hk)
  have hfun : Function.uncurry (kkPhi F m n) = fun p : (ℝ × ℝ) × ℝ =>
      torusChar m n p.1.1 p.1.2 * F (ent (kakM (2 * π * p.1.1) p.2 (2 * π * p.1.2))) := by
    funext p
    rfl
  rw [hfun]
  exact hfin

/-- **Differentiation of the `K × K` component in `ξ`**: the derivative is the component of
`∂ξ P`, given by the right derivatives in the directions `H` and `S`. -/
theorem hasDerivAt_kkIntegral {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (m n : ℤ) (ξ : ℝ) :
    HasDerivAt (fun ξ => ∫ x in box, kkPhi F m n (x 0, x 1) ξ)
      (∫ x in box, torusChar m n (x 0) (x 1) * dxi F (2 * π * x 0) ξ (2 * π * x 1)) ξ := by
  have hΦ := contDiff_kkPhi hF m n
  have hp : Continuous fun x : Fin 2 → ℝ => ((x 0, x 1) : ℝ × ℝ) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hpR : ∀ᵐ a ∂(volume.restrict box), a ∈ box → ‖((a 0, a 1) : ℝ × ℝ)‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun a ha => ?_
    have h0 := ha 0
    have h1 := ha 1
    simp only [zero_add] at h0 h1
    rw [Prod.norm_def, max_le_iff]
    exact ⟨by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h0.1, h0.2],
      by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h1.1, h1.2]⟩
  have h0 : ∀ᵐ a ∂(volume.restrict box), a ∉ box → ∀ x, kkPhi F m n (a 0, a 1) x = 0 :=
    (ae_restrict_mem measurableSet_box).mono fun a ha hna => absurd ha hna
  have hmain := hasFDerivAt_parametric_integral (μ := volume.restrict box) hΦ
    hp.aestronglyMeasurable measurableSet_box (by rw [Measure.restrict_apply_self]; exact volume_box_ne_top)
    hpR h0 ξ
  have hd : ContDiff ℝ 0 (fun y : (ℝ × ℝ) × ℝ => fderiv ℝ (kkPhi F m n y.1) y.2) :=
    ContDiff.fderiv (f := fun (y : (ℝ × ℝ) × ℝ) (x : ℝ) => kkPhi F m n y.1 x) (g := Prod.snd)
      (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  have hint : Integrable (fun a : Fin 2 → ℝ => fderiv ℝ (kkPhi F m n (a 0, a 1)) ξ)
      (volume.restrict box) :=
    integrable_parametric (Ψ := fun q x => fderiv ℝ (kkPhi F m n q) x) hd.continuous
      hp.aestronglyMeasurable measurableSet_box
      (by rw [Measure.restrict_apply_self]; exact volume_box_ne_top) hpR
      (h0.mono fun a h0a ha x => fderiv_parametric_eq_zero (Φ := kkPhi F m n)
        (p := fun a : Fin 2 → ℝ => ((a 0, a 1) : ℝ × ℝ)) (S := box) h0a ha x) ξ
  have hder := hmain.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hint] at hder
  refine hder.congr_deriv (integral_congr_ae (Filter.Eventually.of_forall fun a => ?_))
  have h1 := hasDerivAt_kakP_xi (F := F) (hF.differentiable one_ne_zero) (2 * π * a 0) ξ (2 * π * a 1)
  have h2 := h1.const_mul (torusChar m n (a 0) (a 1))
  have h3 : HasDerivAt (fun ξ => kkPhi F m n (a 0, a 1) ξ)
      (torusChar m n (a 0) (a 1) * dxi F (2 * π * a 0) ξ (2 * π * a 1)) ξ := h2
  show (fderiv ℝ (kkPhi F m n (a 0, a 1)) ξ) 1 = _
  rw [fderiv_apply_one_eq_deriv]
  exact h3.deriv

/-- The `θ`-derivative of `P(α, ξ, θ)`. -/
def dth (F : Ent → ℂ) (α ξ θ : ℝ) : ℂ := dF F (kakM α ξ θ) matJ

/-- The `α`-derivative of `P(α, ξ, θ)`, in terms of right derivatives. -/
def dal (F : Ent → ℂ) (α ξ θ : ℝ) : ℂ :=
  (Real.cosh ξ : ℂ) * dF F (kakM α ξ θ) matJ -
    (2 * Real.sinh ξ : ℝ) * ((Real.cos (2 * θ) : ℂ) * dF F (kakM α ξ θ) matS -
      (Real.sin (2 * θ) : ℂ) * dF F (kakM α ξ θ) matH)

lemma continuous_kakM_entry (i k : Fin 2) :
    Continuous fun p : ℝ × ℝ × ℝ => kakM p.1 p.2.1 p.2.2 i k :=
  (continuous_apply k).comp ((continuous_apply i).comp contDiff_kakE.continuous)

lemma continuous_dF {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun p : ℝ × ℝ × ℝ => dF F (kakM p.1 p.2.1 p.2.2) X := by
  unfold dF
  have hf : Continuous fun p : ℝ × ℝ × ℝ => fderiv ℝ F (ent (kakM p.1 p.2.1 p.2.2)) :=
    (hF.continuous_fderiv one_ne_zero).comp contDiff_kakE.continuous
  have hx : Continuous fun p : ℝ × ℝ × ℝ => ent (kakM p.1 p.2.1 p.2.2 * X) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [ent, Matrix.mul_apply, Fin.sum_univ_two]
    have := continuous_kakM_entry
    fun_prop
  exact hf.clm_apply hx

lemma rot_two_pi : rot (2 * π) = 1 := by
  have := rot_periodic 0
  simpa using this

lemma kakP_two_pi_left (F : Ent → ℂ) (ξ θ : ℝ) : kakP F (2 * π) ξ θ = kakP F 0 ξ θ := by
  unfold kakP
  rw [rot_two_pi, rot_zero]

lemma kakP_two_pi_right (F : Ent → ℂ) (α ξ : ℝ) : kakP F α ξ (2 * π) = kakP F α ξ 0 := by
  unfold kakP
  rw [rot_two_pi, rot_zero]

lemma continuous_kakP {F : Ent → ℂ} (hF : Continuous F) :
    Continuous fun p : ℝ × ℝ × ℝ => kakP F p.1 p.2.1 p.2.2 :=
  hF.comp contDiff_kakE.continuous

lemma continuous_kakPoint (ξ : ℝ) :
    Continuous fun p : ℝ × ℝ => ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ) :=
  (continuous_const.mul continuous_fst).prodMk
    (continuous_const.prodMk (continuous_const.mul continuous_snd))

/-- **`∫ e · ∂θ P = i n · component`**. -/
theorem box_integral_dth {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (m n : ℤ) (ξ : ℝ) :
    ∫ x in box, torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1) =
      Complex.I * n * ∫ x in box, kkPhi F m n (x 0, x 1) ξ := by
  have h2π : (2 * π : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hGc : Continuous fun p : ℝ × ℝ => kakP F (2 * π * p.1) ξ (2 * π * p.2) :=
    Continuous.comp (g := fun q : ℝ × ℝ × ℝ => kakP F q.1 q.2.1 q.2.2)
      (f := fun p : ℝ × ℝ => ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ))
      (continuous_kakP hF.continuous) (continuous_kakPoint ξ)
  have hDc : Continuous fun p : ℝ × ℝ => (2 * π : ℂ) * dth F (2 * π * p.1) ξ (2 * π * p.2) :=
    continuous_const.mul (Continuous.comp
      (g := fun q : ℝ × ℝ × ℝ => dF F (kakM q.1 q.2.1 q.2.2) matJ)
      (f := fun p : ℝ × ℝ => ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ))
      (continuous_dF hF matJ) (continuous_kakPoint ξ))
  have hper : ∀ a, kakP F (2 * π * a) ξ (2 * π * 1) = kakP F (2 * π * a) ξ (2 * π * 0) := by
    intro a
    rw [mul_one, mul_zero]
    exact kakP_two_pi_right F _ ξ
  have hG : ∀ a b, HasDerivAt (fun b => kakP F (2 * π * a) ξ (2 * π * b))
      ((2 * π : ℂ) * dth F (2 * π * a) ξ (2 * π * b)) b := by
    intro a b
    have h1 := hasDerivAt_kakP_theta (F := F) (hF.differentiable one_ne_zero) (2 * π * a) ξ (2 * π * b)
    have h2 := h1.scomp b ((hasDerivAt_id b).const_mul (2 * π))
    refine h2.congr_deriv ?_
    simp [dth, Complex.real_smul]
  have key := box_ibp_b m n (G := fun a b => kakP F (2 * π * a) ξ (2 * π * b))
    (D := fun a b => (2 * π : ℂ) * dth F (2 * π * a) ξ (2 * π * b)) hG hDc hper hGc
  have hp : Continuous fun x : Fin 2 → ℝ => ((x 0, x 1) : ℝ × ℝ) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hc1 : Continuous fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1) := by
    have h : Continuous fun p : ℝ × ℝ =>
        torusChar m n p.1 p.2 * dth F (2 * π * p.1) ξ (2 * π * p.2) :=
      (continuous_torusChar m n).mul (Continuous.comp
        (g := fun q : ℝ × ℝ × ℝ => dF F (kakM q.1 q.2.1 q.2.2) matJ)
        (f := fun p : ℝ × ℝ => ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ))
        (continuous_dF hF matJ) (continuous_kakPoint ξ))
    exact h.comp hp
  have hc2 : Continuous fun x : Fin 2 → ℝ => kkPhi F m n (x 0, x 1) ξ := by
    have h : Continuous fun p : ℝ × ℝ => torusChar m n p.1 p.2 * kakP F (2 * π * p.1) ξ (2 * π * p.2) :=
      (continuous_torusChar m n).mul hGc
    exact h.comp hp
  rw [integral_box_eq hc1, integral_box_eq hc2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at *
  have e1 : ∀ a b : ℝ, torusChar m n a b * ((2 * π : ℂ) * dth F (2 * π * a) ξ (2 * π * b)) =
      (2 * π : ℂ) * (torusChar m n a b * dth F (2 * π * a) ξ (2 * π * b)) := fun a b => by ring
  simp only [e1, integral_const_mul] at key
  change _ = _ * ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, torusChar m n a b * kakP F (2 * π * a) ξ (2 * π * b)
  apply mul_left_cancel₀ h2π
  rw [key]
  ring

lemma continuous_dal {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (ξ : ℝ) :
    Continuous fun p : ℝ × ℝ => dal F (2 * π * p.1) ξ (2 * π * p.2) := by
  have hJ := continuous_dF hF matJ
  have hS := continuous_dF hF matS
  have hH := continuous_dF hF matH
  have hc : ∀ (g : ℝ × ℝ × ℝ → ℂ), Continuous g →
      Continuous fun p : ℝ × ℝ => g ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ) :=
    fun g hg => hg.comp (continuous_kakPoint ξ)
  have hJ' := hc _ hJ
  have hS' := hc _ hS
  have hH' := hc _ hH
  unfold dal
  have h2 : Continuous fun p : ℝ × ℝ => (Real.cos (2 * (2 * π * p.2)) : ℂ) := by fun_prop
  have h3 : Continuous fun p : ℝ × ℝ => (Real.sin (2 * (2 * π * p.2)) : ℂ) := by fun_prop
  exact (continuous_const.mul hJ').sub (continuous_const.mul ((h2.mul hS').sub (h3.mul hH')))

/-- **`∫ e · ∂α P = i m · component`**. -/
theorem box_integral_dal {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (m n : ℤ) (ξ : ℝ) :
    ∫ x in box, torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1) =
      Complex.I * m * ∫ x in box, kkPhi F m n (x 0, x 1) ξ := by
  have h2π : (2 * π : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hGc : Continuous fun p : ℝ × ℝ => kakP F (2 * π * p.1) ξ (2 * π * p.2) :=
    Continuous.comp (g := fun q : ℝ × ℝ × ℝ => kakP F q.1 q.2.1 q.2.2)
      (f := fun p : ℝ × ℝ => ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ))
      (continuous_kakP hF.continuous) (continuous_kakPoint ξ)
  have hDc : Continuous fun p : ℝ × ℝ => (2 * π : ℂ) * dal F (2 * π * p.1) ξ (2 * π * p.2) :=
    continuous_const.mul (continuous_dal hF ξ)
  have hper : ∀ b, kakP F (2 * π * 1) ξ (2 * π * b) = kakP F (2 * π * 0) ξ (2 * π * b) := by
    intro b
    rw [mul_one, mul_zero]
    exact kakP_two_pi_left F ξ _
  have hG : ∀ a b, HasDerivAt (fun a => kakP F (2 * π * a) ξ (2 * π * b))
      ((2 * π : ℂ) * dal F (2 * π * a) ξ (2 * π * b)) a := by
    intro a b
    have h1 := hasDerivAt_kakP_alpha (F := F) (hF.differentiable one_ne_zero) (2 * π * a) ξ (2 * π * b)
    have h2 := h1.scomp a ((hasDerivAt_id a).const_mul (2 * π))
    refine h2.congr_deriv ?_
    simp [dal, Complex.real_smul]
  have key := box_ibp_a m n (G := fun a b => kakP F (2 * π * a) ξ (2 * π * b))
    (D := fun a b => (2 * π : ℂ) * dal F (2 * π * a) ξ (2 * π * b)) hG hDc hper hGc
  have hp : Continuous fun x : Fin 2 → ℝ => ((x 0, x 1) : ℝ × ℝ) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hc1 : Continuous fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1) := by
    have h : Continuous fun p : ℝ × ℝ =>
        torusChar m n p.1 p.2 * dal F (2 * π * p.1) ξ (2 * π * p.2) :=
      (continuous_torusChar m n).mul (continuous_dal hF ξ)
    exact h.comp hp
  have hc2 : Continuous fun x : Fin 2 → ℝ => kkPhi F m n (x 0, x 1) ξ := by
    have h : Continuous fun p : ℝ × ℝ => torusChar m n p.1 p.2 * kakP F (2 * π * p.1) ξ (2 * π * p.2) :=
      (continuous_torusChar m n).mul hGc
    exact h.comp hp
  rw [integral_box_eq hc1, integral_box_eq hc2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at *
  have e1 : ∀ a b : ℝ, torusChar m n a b * ((2 * π : ℂ) * dal F (2 * π * a) ξ (2 * π * b)) =
      (2 * π : ℂ) * (torusChar m n a b * dal F (2 * π * a) ξ (2 * π * b)) := fun a b => by ring
  simp only [e1, integral_const_mul] at key
  change _ = _ * ∫ a in Ioc (0 : ℝ) 1, ∫ b in Ioc (0 : ℝ) 1, torusChar m n a b * kakP F (2 * π * a) ξ (2 * π * b)
  apply mul_left_cancel₀ h2π
  rw [key]
  ring

lemma torusChar_add_two (m n : ℤ) (a b : ℝ) :
    torusChar m (n + 2) a b = torusChar m n a b *
      ((Real.cos (2 * (2 * π * b)) : ℂ) - Complex.I * (Real.sin (2 * (2 * π * b)) : ℂ)) := by
  have h : torusChar m (n + 2) a b = torusChar m n a b *
      Complex.exp (((-(2 * (2 * π * b)) : ℝ) : ℂ) * Complex.I) := by
    unfold torusChar
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc : Complex.cos (((-(2 * (2 * π * b)) : ℝ)) : ℂ) = ((Real.cos (2 * (2 * π * b)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_neg]
  have hs : Complex.sin (((-(2 * (2 * π * b)) : ℝ)) : ℂ) = -((Real.sin (2 * (2 * π * b)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin, Real.sin_neg, Complex.ofReal_neg]
  rw [h, Complex.exp_mul_I, hc, hs]
  ring

lemma torusChar_sub_two (m n : ℤ) (a b : ℝ) :
    torusChar m (n - 2) a b = torusChar m n a b *
      ((Real.cos (2 * (2 * π * b)) : ℂ) + Complex.I * (Real.sin (2 * (2 * π * b)) : ℂ)) := by
  have h : torusChar m (n - 2) a b = torusChar m n a b *
      Complex.exp ((((2 * (2 * π * b)) : ℝ) : ℂ) * Complex.I) := by
    unfold torusChar
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc : Complex.cos (((2 * (2 * π * b) : ℝ)) : ℂ) = ((Real.cos (2 * (2 * π * b)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cos]
  have hs : Complex.sin (((2 * (2 * π * b) : ℝ)) : ℂ) = ((Real.sin (2 * (2 * π * b)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sin]
  rw [h, Complex.exp_mul_I, hc, hs]
  ring

lemma continuous_dth {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (ξ : ℝ) :
    Continuous fun p : ℝ × ℝ => dth F (2 * π * p.1) ξ (2 * π * p.2) :=
  Continuous.comp (g := fun q : ℝ × ℝ × ℝ => dF F (kakM q.1 q.2.1 q.2.2) matJ)
    (f := fun p : ℝ × ℝ => ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ))
    (continuous_dF hF matJ) (continuous_kakPoint ξ)

lemma continuous_dxi {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (ξ : ℝ) :
    Continuous fun p : ℝ × ℝ => dxi F (2 * π * p.1) ξ (2 * π * p.2) := by
  have hc : ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      Continuous fun p : ℝ × ℝ => dF F (kakM (2 * π * p.1) ξ (2 * π * p.2)) X := fun X =>
    Continuous.comp (g := fun q : ℝ × ℝ × ℝ => dF F (kakM q.1 q.2.1 q.2.2) X)
      (f := fun p : ℝ × ℝ => ((2 * π * p.1, ξ, 2 * π * p.2) : ℝ × ℝ × ℝ))
      (continuous_dF hF X) (continuous_kakPoint ξ)
  unfold dxi
  have h2 : Continuous fun p : ℝ × ℝ => (Real.cos (2 * (2 * π * p.2)) : ℂ) := by fun_prop
  have h3 : Continuous fun p : ℝ × ℝ => (Real.sin (2 * (2 * π * p.2)) : ℂ) := by fun_prop
  exact (h2.mul (hc matH)).add (h3.mul (hc matS))

/-- A continuous function is integrable over the box. -/
lemma integrableOn_box_of_continuous {G : (Fin 2 → ℝ) → ℂ} (hG : Continuous G) :
    IntegrableOn G box := by
  have hI : IntegrableOn G (Icc (0 : Fin 2 → ℝ) 1) :=
    hG.continuousOn.integrableOn_compact isCompact_Icc
  refine hI.mono_set ?_
  intro x hx
  rw [mem_Icc]
  exact ⟨fun i => (hx i).1.le, fun i => by simpa using (hx i).2⟩

lemma continuous_tc_mul (m n : ℤ) {H : ℝ × ℝ → ℂ} (hH : Continuous H) :
    Continuous fun x : Fin 2 → ℝ => torusChar m n (x 0) (x 1) * H (x 0, x 1) := by
  have hp : Continuous fun x : Fin 2 → ℝ => ((x 0, x 1) : ℝ × ℝ) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  exact ((continuous_torusChar m n).mul hH).comp hp

/-- The pointwise form of the raising operator: `e^{-2πi(m a + (n+2) b)} (A + iB)` is
`e^{-2πi(m a + n b)}` times `∂ξP + i (cosh ξ ∂θP − ∂αP) / (2 sinh ξ)`. -/
lemma ladder_pointwise (F : Ent → ℂ) (m n : ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) (a b : ℝ) :
    torusChar m (n + 2) a b * (dF F (kakM (2 * π * a) ξ (2 * π * b)) matH +
        Complex.I * dF F (kakM (2 * π * a) ξ (2 * π * b)) matS) =
      torusChar m n a b * dxi F (2 * π * a) ξ (2 * π * b) +
        (Complex.I / (2 * Real.sinh ξ : ℝ)) *
          ((Real.cosh ξ : ℂ) * (torusChar m n a b * dth F (2 * π * a) ξ (2 * π * b)) -
            torusChar m n a b * dal F (2 * π * a) ξ (2 * π * b)) := by
  have hsh : (Real.sinh ξ : ℂ) ≠ 0 := by
    have : Real.sinh ξ ≠ 0 := fun h => hξ (Real.sinh_eq_zero.mp h)
    exact_mod_cast this
  rw [torusChar_add_two]
  unfold dxi dal dth
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  generalize torusChar m n a b = T
  generalize dF F (kakM (2 * π * a) ξ (2 * π * b)) matH = A
  generalize dF F (kakM (2 * π * a) ξ (2 * π * b)) matS = B
  generalize dF F (kakM (2 * π * a) ξ (2 * π * b)) matJ = C
  generalize ((Real.cos (2 * (2 * π * b)) : ℝ) : ℂ) = c
  generalize ((Real.sin (2 * (2 * π * b)) : ℝ) : ℂ) = s
  generalize ((Real.sinh ξ : ℝ) : ℂ) = sh at hsh ⊢
  generalize ((Real.cosh ξ : ℝ) : ℂ) = ch
  field_simp
  linear_combination (-(2 * T * s * B * sh)) * Complex.I_sq

/-- The pointwise form of the lowering operator: `e^{-2πi(m a + (n-2) b)} (A - iB)` is
`e^{-2πi(m a + n b)}` times `∂ξP - i (cosh ξ ∂θP − ∂αP) / (2 sinh ξ)`. -/
lemma ladder_pointwise_down (F : Ent → ℂ) (m n : ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) (a b : ℝ) :
    torusChar m (n - 2) a b * (dF F (kakM (2 * π * a) ξ (2 * π * b)) matH -
        Complex.I * dF F (kakM (2 * π * a) ξ (2 * π * b)) matS) =
      torusChar m n a b * dxi F (2 * π * a) ξ (2 * π * b) -
        (Complex.I / (2 * Real.sinh ξ : ℝ)) *
          ((Real.cosh ξ : ℂ) * (torusChar m n a b * dth F (2 * π * a) ξ (2 * π * b)) -
            torusChar m n a b * dal F (2 * π * a) ξ (2 * π * b)) := by
  have hsh : (Real.sinh ξ : ℂ) ≠ 0 := by
    have : Real.sinh ξ ≠ 0 := fun h => hξ (Real.sinh_eq_zero.mp h)
    exact_mod_cast this
  rw [torusChar_sub_two]
  unfold dxi dal dth
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  generalize torusChar m n a b = T
  generalize dF F (kakM (2 * π * a) ξ (2 * π * b)) matH = A
  generalize dF F (kakM (2 * π * a) ξ (2 * π * b)) matS = B
  generalize dF F (kakM (2 * π * a) ξ (2 * π * b)) matJ = C
  generalize ((Real.cos (2 * (2 * π * b)) : ℝ) : ℂ) = c
  generalize ((Real.sin (2 * (2 * π * b)) : ℝ) : ℂ) = s
  generalize ((Real.sinh ξ : ℝ) : ℂ) = sh at hsh ⊢
  generalize ((Real.cosh ξ : ℝ) : ℂ) = ch
  field_simp
  linear_combination (-(2 * T * s * B * sh)) * Complex.I_sq


/-- **The raising operator on the `K × K` components** (layer 2c-i).  For `F` of class `C¹` on the
entries and `ξ ≠ 0`, the `(m, n+2)`-component of `A + iB`, where `A` and `B` are the right
derivatives of `F` in the directions `H` and `S`, is
`f_{m,n}'(ξ) − ((n cosh ξ − m) / (2 sinh ξ)) f_{m,n}(ξ)`. -/
theorem kk_ladder_up {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (m n : ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∫ x in box, torusChar m (n + 2) (x 0) (x 1) *
        (dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matH +
          Complex.I * dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matS) =
      deriv (fun ξ => ∫ x in box, kkPhi F m n (x 0, x 1) ξ) ξ -
        (((n : ℝ) * Real.cosh ξ - m) / (2 * Real.sinh ξ) : ℝ) *
          ∫ x in box, kkPhi F m n (x 0, x 1) ξ := by
  have hsh : (Real.sinh ξ : ℂ) ≠ 0 := by
    have : Real.sinh ξ ≠ 0 := fun h => hξ (Real.sinh_eq_zero.mp h)
    exact_mod_cast this
  have hI1 : Integrable (fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dxi F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    integrableOn_box_of_continuous (continuous_tc_mul m n (continuous_dxi hF ξ))
  have hI2 : Integrable (fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    integrableOn_box_of_continuous (continuous_tc_mul m n (continuous_dth hF ξ))
  have hI3 : Integrable (fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    integrableOn_box_of_continuous (continuous_tc_mul m n (continuous_dal hF ξ))
  have hpt : ∀ x : Fin 2 → ℝ, torusChar m (n + 2) (x 0) (x 1) *
        (dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matH +
          Complex.I * dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matS) =
      torusChar m n (x 0) (x 1) * dxi F (2 * π * x 0) ξ (2 * π * x 1) +
        (Complex.I / (2 * Real.sinh ξ : ℝ)) *
          ((Real.cosh ξ : ℂ) * (torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1)) -
            torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1)) :=
    fun x => ladder_pointwise F m n hξ (x 0) (x 1)
  simp_rw [hpt]
  have hS : Integrable (fun x : Fin 2 → ℝ =>
      (Real.cosh ξ : ℂ) * (torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1)) -
        torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    (hI2.const_mul _).sub hI3
  rw [integral_add hI1 (hS.const_mul _), integral_const_mul,
    integral_sub (hI2.const_mul _) hI3, integral_const_mul,
    (hasDerivAt_kkIntegral hF m n ξ).deriv, box_integral_dth hF m n ξ, box_integral_dal hF m n ξ]
  generalize (∫ x in box, kkPhi F m n (x 0, x 1) ξ) = K
  generalize deriv (fun ξ => ∫ x in box, kkPhi F m n (x 0, x 1) ξ) ξ = K'
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast,
    Complex.ofReal_ofNat]
  generalize ((Real.sinh ξ : ℝ) : ℂ) = sh at hsh ⊢
  generalize ((Real.cosh ξ : ℝ) : ℂ) = ch
  field_simp
  linear_combination (K * (ch * n - m)) * Complex.I_sq

/-- **The lowering operator on the `K × K` components** (layer 2c-i).  For `F` of class `C¹` on the
entries and `ξ ≠ 0`, the `(m, n-2)`-component of `A - iB`, where `A` and `B` are the right
derivatives of `F` in the directions `H` and `S`, is
`f_{m,n}'(ξ) + ((n cosh ξ − m) / (2 sinh ξ)) f_{m,n}(ξ)`. -/
theorem kk_ladder_down {F : Ent → ℂ} (hF : ContDiff ℝ 1 F) (m n : ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ∫ x in box, torusChar m (n - 2) (x 0) (x 1) *
        (dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matH -
          Complex.I * dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matS) =
      deriv (fun ξ => ∫ x in box, kkPhi F m n (x 0, x 1) ξ) ξ +
        (((n : ℝ) * Real.cosh ξ - m) / (2 * Real.sinh ξ) : ℝ) *
          ∫ x in box, kkPhi F m n (x 0, x 1) ξ := by
  have hsh : (Real.sinh ξ : ℂ) ≠ 0 := by
    have : Real.sinh ξ ≠ 0 := fun h => hξ (Real.sinh_eq_zero.mp h)
    exact_mod_cast this
  have hI1 : Integrable (fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dxi F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    integrableOn_box_of_continuous (continuous_tc_mul m n (continuous_dxi hF ξ))
  have hI2 : Integrable (fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    integrableOn_box_of_continuous (continuous_tc_mul m n (continuous_dth hF ξ))
  have hI3 : Integrable (fun x : Fin 2 → ℝ =>
      torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    integrableOn_box_of_continuous (continuous_tc_mul m n (continuous_dal hF ξ))
  have hpt : ∀ x : Fin 2 → ℝ, torusChar m (n - 2) (x 0) (x 1) *
        (dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matH -
          Complex.I * dF F (kakM (2 * π * x 0) ξ (2 * π * x 1)) matS) =
      torusChar m n (x 0) (x 1) * dxi F (2 * π * x 0) ξ (2 * π * x 1) -
        (Complex.I / (2 * Real.sinh ξ : ℝ)) *
          ((Real.cosh ξ : ℂ) * (torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1)) -
            torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1)) :=
    fun x => ladder_pointwise_down F m n hξ (x 0) (x 1)
  simp_rw [hpt]
  have hS : Integrable (fun x : Fin 2 → ℝ =>
      (Real.cosh ξ : ℂ) * (torusChar m n (x 0) (x 1) * dth F (2 * π * x 0) ξ (2 * π * x 1)) -
        torusChar m n (x 0) (x 1) * dal F (2 * π * x 0) ξ (2 * π * x 1)) (volume.restrict box) :=
    (hI2.const_mul _).sub hI3
  rw [integral_sub hI1 (hS.const_mul _), integral_const_mul,
    integral_sub (hI2.const_mul _) hI3, integral_const_mul,
    (hasDerivAt_kkIntegral hF m n ξ).deriv, box_integral_dth hF m n ξ, box_integral_dal hF m n ξ]
  generalize (∫ x in box, kkPhi F m n (x 0, x 1) ξ) = K
  generalize deriv (fun ξ => ∫ x in box, kkPhi F m n (x 0, x 1) ξ) ξ = K'
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_intCast,
    Complex.ofReal_ofNat]
  generalize ((Real.sinh ξ : ℝ) : ℂ) = sh at hsh ⊢
  generalize ((Real.cosh ξ : ℝ) : ℂ) = ch
  field_simp
  linear_combination (-(K * (ch * n - m))) * Complex.I_sq

/-- The `K × K` component of `f = F ∘ ent` is the box integral of `kkPhi`. -/
lemma kkCoeff_eq (F : Ent → ℂ) (m n : ℤ) (ξ : ℝ) :
    kkCoeff (fun g : SL2R => F (ent (g : Matrix (Fin 2) (Fin 2) ℝ))) ![m, n] ξ =
      ∫ x in box, kkPhi F m n (x 0, x 1) ξ := by
  unfold kkCoeff kkProfile kkPhi kakP torusChar
  simp [Fin.sum_univ_two]

end Lightlike.Lorentz.SL2R
