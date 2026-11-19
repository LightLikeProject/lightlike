import Lightlike.OperatorAlgebras.MomentumAdjoint

/-!
# Boundary values and the boundary form of the momentum on `L²(0, 1)`

For primitives `Y = c + ∫₀ˣ g`, `Z = d + ∫₀ˣ k` with `g, k` integrable on `[0, 1]`: integration by parts
`∫₀¹ (conj g · Z + conj Y · k) = conj Y(1) Z(1) - conj Y(0) Z(0)` (`integral_conj_mul_add_eq`), through Mathlib's absolutely continuous functions.
A vector `y` of the domain of the adjoint has the continuous representative `bvRep y = c + ∫₀ˣ i A† y` and the boundary values `bv0 y`, `bv1 y`;
the boundary form is `⟪A† y, z⟫ - ⟪y, A† z⟫ = i (conj y(1) z(1) - conj y(0) z(0))` (`boundary_form_momentum`), and the affine functions
`linVec a b` realize every pair of boundary values (`bv_linVec`), so `bv0`, `bv1` are linear functionals (`bv0L`, `bv1L`). Bonneau, Faraut and
Valent's form of `D_max` (Appendix A.3, read: absolutely continuous on `[0, 1]` with derivative in `L²`) is `mem_adjoint_iff_ac`.
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

/-- The primitive of a complex function integrable on `[0, 1]` is absolutely continuous on `[0, 1]`. -/
lemma ac_primitive {h : ℝ → ℂ} (hh : IntervalIntegrable h volume 0 1) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in (0 : ℝ)..x, h t) 0 1 := by
  have hr := (intervalIntegrable_re_part hh).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hi := (intervalIntegrable_im_part hh).absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hr' := Complex.isometry_ofReal.lipschitzWith.comp_absolutelyContinuousOnInterval hr
  have hi' := (Complex.isometry_ofReal.lipschitzWith.comp_absolutelyContinuousOnInterval hi).const_smul Complex.I
  refine (hr'.add hi').congr fun x hx => ?_
  have hsub : IntervalIntegrable h volume 0 x := hh.mono_set (uIcc_subset_uIcc left_mem_uIcc hx)
  simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (intervalIntegrable_ofReal_comp (intervalIntegrable_re_part hsub))
      ((intervalIntegrable_ofReal_comp (intervalIntegrable_im_part hsub)).const_mul _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  beta_reduce
  linear_combination Complex.re_add_im (h t)

/-- **Integration by parts for two primitives**: `∫₀¹ (conj g · Z + conj Y · k) = conj Y(1) Z(1) - conj Y(0) Z(0)` for `Y = c + ∫₀ˣ g` and
`Z = d + ∫₀ˣ k`. -/
theorem integral_conj_mul_add_eq {g k : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 1) (hk : IntervalIntegrable k volume 0 1)
    (c d : ℂ) :
    let Y : ℝ → ℂ := fun x => c + ∫ t in (0 : ℝ)..x, g t
    let Z : ℝ → ℂ := fun x => d + ∫ t in (0 : ℝ)..x, k t
    ∫ x in (0 : ℝ)..1, ((starRingEnd ℂ) (g x) * Z x + (starRingEnd ℂ) (Y x) * k x) =
      (starRingEnd ℂ) (Y 1) * Z 1 - (starRingEnd ℂ) (Y 0) * Z 0 := by
  intro Y Z
  have hconst : ∀ e : ℂ, AbsolutelyContinuousOnInterval (fun _ : ℝ => e) 0 1 := fun e =>
    (contDiff_const (c := e)).contDiffOn.absolutelyContinuousOnInterval
  have hY : AbsolutelyContinuousOnInterval Y 0 1 := (hconst c).add (ac_primitive hg)
  have hZ : AbsolutelyContinuousOnInterval Z 0 1 := (hconst d).add (ac_primitive hk)
  have hYc : AbsolutelyContinuousOnInterval (fun x => (starRingEnd ℂ) (Y x)) 0 1 :=
    Complex.isometry_conj.lipschitzWith.comp_absolutelyContinuousOnInterval hY
  have hF : AbsolutelyContinuousOnInterval (fun x => (starRingEnd ℂ) (Y x) * Z x) 0 1 := hYc.smul hZ
  have hYcont : ContinuousOn Y (uIcc 0 1) := hY.continuousOn
  have hZcont : ContinuousOn Z (uIcc 0 1) := hZ.continuousOn
  have hint : IntervalIntegrable (fun x => (starRingEnd ℂ) (g x) * Z x + (starRingEnd ℂ) (Y x) * k x) volume 0 1 :=
    ((intervalIntegrable_conj_comp hg).mul_continuousOn hZcont).add (hk.continuousOn_mul (Complex.continuous_conj.comp_continuousOn hYcont))
  have hQ := ac_primitive hint
  have hK := hF.sub hQ
  have hder : ∀ᵐ x, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt (fun x => (starRingEnd ℂ) (Y x) * Z x -
      ∫ t in (0 : ℝ)..x, ((starRingEnd ℂ) (g t) * Z t + (starRingEnd ℂ) (Y t) * k t)) 0 x := by
    filter_upwards [hg.ae_hasDerivAt_integral, hk.ae_hasDerivAt_integral, hint.ae_hasDerivAt_integral] with x h1 h2 h3 hx
    have dY : HasDerivAt Y (g x) x := (h1 hx 0 left_mem_uIcc).const_add c
    have dZ : HasDerivAt Z (k x) x := (h2 hx 0 left_mem_uIcc).const_add d
    have dYc : HasDerivAt (fun x => (starRingEnd ℂ) (Y x)) ((starRingEnd ℂ) (g x)) x := dY.star
    have dF := dYc.mul dZ
    have dQ := h3 hx 0 left_mem_uIcc
    convert dF.sub dQ using 1
    ring
  obtain ⟨C, hC⟩ := hK.const_of_ae_hasDerivAt_zero hder
  have e1 := hC 1 right_mem_uIcc
  have e0 := hC 0 left_mem_uIcc
  simp only [Pi.sub_apply, integral_same, sub_zero] at e1 e0
  rw [← e0] at e1
  linear_combination -e1

/-- The absolutely continuous representative `x ↦ c + ∫₀ˣ i A† y` of `y ∈ D(A†)`, with its constant chosen. -/
noncomputable def bvConst (y : (momentumMin†).domain) : ℂ := Classical.choose (adjoint_eq_primitive y y.2)

lemma bvConst_spec (y : (momentumMin†).domain) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      (y : L2I) x = bvConst y + ∫ t in (0 : ℝ)..x, Complex.I * (momentumMin† y : L2I) t :=
  Classical.choose_spec (adjoint_eq_primitive y y.2)

/-- The representative of `y ∈ D(A†)`. -/
noncomputable def bvRep (y : (momentumMin†).domain) (x : ℝ) : ℂ :=
  bvConst y + ∫ t in (0 : ℝ)..x, Complex.I * (momentumMin† y : L2I) t

/-- The boundary values `y(0)`, `y(1)` of `y ∈ D(A†)`. -/
noncomputable def bv0 (y : (momentumMin†).domain) : ℂ := bvRep y 0
noncomputable def bv1 (y : (momentumMin†).domain) : ℂ := bvRep y 1

lemma bv0_eq (y : (momentumMin†).domain) : bv0 y = bvConst y := by simp [bv0, bvRep]

/-- The constant of the representative is determined: two constants with the same primitive part agree. -/
lemma const_unique {c c' : ℂ} {F : ℝ → ℂ} {y : ℝ → ℂ}
    (h : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), y x = c + F x)
    (h' : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), y x = c' + F x) : c = c' := by
  have hne : ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; simp
  have : (ae ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))).NeBot := ae_neBot.mpr hne
  obtain ⟨x, hx, hx'⟩ := (h.and h').exists
  have := hx.symm.trans hx'
  exact add_right_cancel this

lemma rep_ae (y : (momentumMin†).domain) :
    (y : L2I) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] bvRep y := bvConst_spec y

lemma intervalIntegrable_I_mul (w : L2I) : IntervalIntegrable (fun t => Complex.I * w t) volume 0 1 :=
  intervalIntegrable_of_integrableOn ((integrable_L2I w).const_mul _)

lemma continuousOn_rep (y : (momentumMin†).domain) : ContinuousOn (bvRep y) (Icc 0 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_I_mul (momentumMin† y : L2I))
    (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
  rw [uIcc_of_le zero_le_one] at h
  exact continuousOn_const.add h

/-- The `L²` inner product with a vector of `D(A†)` through its representative. -/
lemma inner_eq_integral_rep (u : L2I) (z : (momentumMin†).domain) :
    ⟪u, (z : L2I)⟫_ℂ = ∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (u x) * bvRep z x := by
  rw [MeasureTheory.L2.inner_def, ← integral_Ioo_eq]
  refine integral_congr_ae ?_
  filter_upwards [rep_ae z] with x hx
  rw [hx]; simp [RCLike.inner_apply, mul_comm]

lemma inner_rep_eq_integral (y : (momentumMin†).domain) (u : L2I) :
    ⟪(y : L2I), u⟫_ℂ = ∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (bvRep y x) * u x := by
  rw [MeasureTheory.L2.inner_def, ← integral_Ioo_eq]
  refine integral_congr_ae ?_
  filter_upwards [rep_ae y] with x hx
  rw [hx]; simp [RCLike.inner_apply, mul_comm]

/-- **The boundary form of the momentum** (integration by parts on `D(A†)`):
`⟪A† y, z⟫ - ⟪y, A† z⟫ = i (conj y(1) z(1) - conj y(0) z(0))`. -/
theorem boundary_form_momentum (y z : (momentumMin†).domain) :
    ⟪(momentumMin† y : L2I), (z : L2I)⟫_ℂ - ⟪(y : L2I), (momentumMin† z : L2I)⟫_ℂ =
      Complex.I * ((starRingEnd ℂ) (bv1 y) * bv1 z - (starRingEnd ℂ) (bv0 y) * bv0 z) := by
  set wy : L2I := momentumMin† y
  set wz : L2I := momentumMin† z
  have hibp := integral_conj_mul_add_eq (intervalIntegrable_I_mul wy) (intervalIntegrable_I_mul wz) (bvConst y) (bvConst z)
  simp only at hibp
  have hY : ∀ x, bvConst y + ∫ t in (0 : ℝ)..x, Complex.I * wy t = bvRep y x := fun x => rfl
  have hZ : ∀ x, bvConst z + ∫ t in (0 : ℝ)..x, Complex.I * wz t = bvRep z x := fun x => rfl
  simp only [hY, hZ] at hibp
  rw [inner_eq_integral_rep, inner_rep_eq_integral, bv0, bv1, bv0, bv1, ← hibp, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub]
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [map_mul, Complex.conj_I]
    linear_combination ((starRingEnd ℂ) (wy x) * bvRep z x - (starRingEnd ℂ) (bvRep y x) * wz x) * Complex.I_sq
  · exact ((intervalIntegrable_of_integrableOn (integrable_conj_comp (integrable_L2I wy))).mul_continuousOn
      (by rw [uIcc_of_le zero_le_one]; exact continuousOn_rep z))
  · exact (intervalIntegrable_of_integrableOn (integrable_L2I wz)).continuousOn_mul
      (Complex.continuous_conj.comp_continuousOn (by rw [uIcc_of_le zero_le_one]; exact continuousOn_rep y))

/-- Almost every point of `[0, 1]` lies in `(0, 1)`: a statement almost everywhere on `(0, 1)` holds almost everywhere on `(0, x]`, `x ≤ 1`. -/
lemma ae_uIoc_of_ae_Ioo {P : ℝ → Prop} (h : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), P t) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ∀ᵐ t, t ∈ uIoc (0 : ℝ) x → P t := by
  have h1 := (ae_restrict_iff' measurableSet_Ioo).mp h
  have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
    rw [ae_iff]; simp
  filter_upwards [h1, h2] with t ht ht1 htI
  rw [uIoc_of_le hx.1] at htI
  exact ht ⟨htI.1, lt_of_le_of_ne (htI.2.trans hx.2) ht1⟩

/-- **The boundary values of a primitive in `D(A†)`**: if `y = c + ∫₀ˣ g` almost everywhere, then `y(0) = c` and `y(1) = c + ∫₀¹ g`. -/
theorem bv_of_primitive (y g : L2I) (c : ℂ)
    (hy : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), y x = c + ∫ t in (0 : ℝ)..x, g t)
    (hyd : y ∈ (momentumMin†).domain) :
    bv0 ⟨y, hyd⟩ = c ∧ bv1 ⟨y, hyd⟩ = c + ∫ t in (0 : ℝ)..1, g t := by
  obtain ⟨h, hA⟩ := mem_adjoint_of_primitive y g c hy
  have hA' : (momentumMin† ⟨y, hyd⟩ : L2I) = (-Complex.I) • g := hA
  have hsm := Lp.coeFn_smul (-Complex.I) g
  have hint : ∀ x ∈ Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..x, Complex.I * (momentumMin† ⟨y, hyd⟩ : L2I) t = ∫ t in (0 : ℝ)..x, g t := by
    intro x hx
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo hsm hx] with t ht htI
    rw [hA', ht htI]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]; simp
  have hc : bvConst ⟨y, hyd⟩ = c := by
    refine const_unique (F := fun x => ∫ t in (0 : ℝ)..x, g t) (y := y) ?_ hy
    filter_upwards [bvConst_spec ⟨y, hyd⟩, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx, hint x ⟨hxI.1.le, hxI.2.le⟩]
  refine ⟨by rw [bv0_eq, hc], ?_⟩
  rw [bv1, bvRep, hc, hint 1 ⟨zero_le_one, le_rfl⟩]

/-- The constant function `e` as a vector of `L²(0, 1)`. -/
noncomputable def constL2 (e : ℂ) : L2I := (memLp_const e).toLp (fun _ => e)

lemma constL2_ae (e : ℂ) : (constL2 e : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] fun _ => e :=
  MemLp.coeFn_toLp _

/-- The affine function `a + (b - a) x` as a vector of `L²(0, 1)`. -/
noncomputable def linVec (a b : ℂ) : L2I :=
  (MemLp.of_bound (C := ‖a‖ + ‖b - a‖)
    ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      calc ‖a + (b - a) * (x : ℂ)‖ ≤ ‖a‖ + ‖b - a‖ * ‖(x : ℂ)‖ := (norm_add_le _ _).trans (by rw [norm_mul])
        _ ≤ ‖a‖ + ‖b - a‖ * 1 := by
          gcongr; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]; exact hx.2.le
        _ = ‖a‖ + ‖b - a‖ := by ring)).toLp (fun x : ℝ => a + (b - a) * (x : ℂ))

lemma linVec_ae (a b : ℂ) :
    (linVec a b : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] fun x : ℝ => a + (b - a) * (x : ℂ) :=
  MemLp.coeFn_toLp _

lemma linVec_primitive (a b : ℂ) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), linVec a b x = a + ∫ t in (0 : ℝ)..x, constL2 (b - a) t := by
  filter_upwards [linVec_ae a b, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [hx]
  congr 1
  have : ∫ t in (0 : ℝ)..x, constL2 (b - a) t = ∫ t in (0 : ℝ)..x, (b - a) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo (constL2_ae (b - a)) ⟨hxI.1.le, hxI.2.le⟩] with t ht htI
    exact ht htI
  rw [this, intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  ring

lemma linVec_mem (a b : ℂ) : linVec a b ∈ (momentumMin†).domain :=
  (mem_adjoint_of_primitive _ _ a (linVec_primitive a b)).1

/-- **A vector of `D(A†)` with prescribed boundary values** `y(0) = a`, `y(1) = b`. -/
lemma bv_linVec (a b : ℂ) : bv0 ⟨linVec a b, linVec_mem a b⟩ = a ∧ bv1 ⟨linVec a b, linVec_mem a b⟩ = b := by
  obtain ⟨h0, h1⟩ := bv_of_primitive _ _ a (linVec_primitive a b) (linVec_mem a b)
  refine ⟨h0, ?_⟩
  rw [h1]
  have : ∫ t in (0 : ℝ)..1, constL2 (b - a) t = b - a := by
    rw [show (∫ t in (0 : ℝ)..1, constL2 (b - a) t) = ∫ t in (0 : ℝ)..1, (b - a) from
      intervalIntegral.integral_congr_ae (by
        filter_upwards [ae_uIoc_of_ae_Ioo (constL2_ae (b - a)) ⟨zero_le_one, le_rfl⟩] with t ht htI
        exact ht htI)]
    simp
  rw [this]; ring

/-- The test vector with `y(0) = a`, `y(1) = b`, as an element of `D(A†)`. -/
noncomputable def linD (a b : ℂ) : (momentumMin†).domain := ⟨linVec a b, linVec_mem a b⟩

/-- `y(1)` through the boundary form against `linD 0 1`; linear in `y`. -/
lemma bv1_eq (y : (momentumMin†).domain) :
    bv1 y = Complex.I * (⟪((linD 0 1 : (momentumMin†).domain) : L2I), (momentumMin† y : L2I)⟫_ℂ -
      ⟪(momentumMin† (linD 0 1) : L2I), (y : L2I)⟫_ℂ) := by
  have hb := boundary_form_momentum y (linD 0 1)
  obtain ⟨h0, h1⟩ := bv_linVec 0 1
  have h0' : bv0 (linD 0 1) = 0 := h0
  have h1' : bv1 (linD 0 1) = 1 := h1
  rw [h0', h1', mul_one, mul_zero, sub_zero] at hb
  have hc := congrArg (starRingEnd ℂ) hb
  simp only [map_sub, inner_conj_symm, map_mul, Complex.conj_I, Complex.conj_conj] at hc
  linear_combination (-Complex.I) * hc + (bv1 y) * Complex.I_sq

/-- `y(0)` through the boundary form against `linD 1 0`; linear in `y`. -/
lemma bv0_eq' (y : (momentumMin†).domain) :
    bv0 y = -Complex.I * (⟪((linD 1 0 : (momentumMin†).domain) : L2I), (momentumMin† y : L2I)⟫_ℂ -
      ⟪(momentumMin† (linD 1 0) : L2I), (y : L2I)⟫_ℂ) := by
  have hb := boundary_form_momentum y (linD 1 0)
  obtain ⟨h0, h1⟩ := bv_linVec 1 0
  have h0' : bv0 (linD 1 0) = 1 := h0
  have h1' : bv1 (linD 1 0) = 0 := h1
  rw [h0', h1', mul_one, mul_zero, zero_sub] at hb
  have hc := congrArg (starRingEnd ℂ) hb
  simp only [map_sub, inner_conj_symm, map_mul, map_neg, Complex.conj_I, Complex.conj_conj] at hc
  linear_combination Complex.I * hc + (bv0 y) * Complex.I_sq

/-- The boundary value `y(1)` as a linear functional on `D(A†)`. -/
noncomputable def bv1L : (momentumMin†).domain →ₗ[ℂ] ℂ where
  toFun := bv1
  map_add' y y' := by rw [bv1_eq, bv1_eq, bv1_eq, LinearPMap.map_add]; simp only [Submodule.coe_add, inner_add_right]; ring
  map_smul' c y := by rw [bv1_eq, bv1_eq, LinearPMap.map_smul]; simp only [Submodule.coe_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]; ring

/-- The boundary value `y(0)` as a linear functional on `D(A†)`. -/
noncomputable def bv0L : (momentumMin†).domain →ₗ[ℂ] ℂ where
  toFun := bv0
  map_add' y y' := by rw [bv0_eq', bv0_eq', bv0_eq', LinearPMap.map_add]; simp only [Submodule.coe_add, inner_add_right]; ring
  map_smul' c y := by rw [bv0_eq', bv0_eq', LinearPMap.map_smul]; simp only [Submodule.coe_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]; ring

/-- **The fundamental theorem of calculus for complex absolutely continuous functions** on `[0, 1]`: `f x = f 0 + ∫₀ˣ f'`. -/
lemma ac_eq_primitive {f : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    f x = f 0 + ∫ t in (0 : ℝ)..x, deriv f t := by
  have hfx : AbsolutelyContinuousOnInterval f 0 x :=
    hf.mono (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le zero_le_one]; exact hx))
  have hr : AbsolutelyContinuousOnInterval (fun t => (f t).re) 0 x :=
    Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hfx
  have hi : AbsolutelyContinuousOnInterval (fun t => (f t).im) 0 x :=
    Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hfx
  have er := hr.integral_deriv_eq_sub
  have ei := hi.integral_deriv_eq_sub
  have hdiff : ∀ᵐ t, t ∈ uIcc (0 : ℝ) x → HasDerivAt f (((deriv (fun t => (f t).re) t : ℝ) : ℂ) +
      ((deriv (fun t => (f t).im) t : ℝ) : ℂ) * Complex.I) t := by
    filter_upwards [hr.ae_differentiableAt, hi.ae_differentiableAt] with t h1 h2 ht
    have d1 := (h1 ht).hasDerivAt.ofReal_comp
    have d2 := ((h2 ht).hasDerivAt.ofReal_comp).mul_const Complex.I
    have := d1.add d2
    convert this using 1
    funext s
    exact (Complex.re_add_im (f s)).symm
  have hint : ∫ t in (0 : ℝ)..x, deriv f t =
      ∫ t in (0 : ℝ)..x, (((deriv (fun t => (f t).re) t : ℝ) : ℂ) + ((deriv (fun t => (f t).im) t : ℝ) : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hdiff] with t ht htI
    exact (ht (uIoc_subset_uIcc htI)).deriv
  rw [hint, intervalIntegral.integral_add (intervalIntegrable_ofReal_comp hr.intervalIntegrable_deriv)
    ((intervalIntegrable_ofReal_comp hi.intervalIntegrable_deriv).mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, er, ei]
  apply Complex.ext <;> simp

/-- **`D(A†) = D_max`**, in the source's form (Bonneau-Faraut-Valent, Appendix A.3): `y ∈ D(A†)` iff `y` agrees almost everywhere on `(0, 1)`
with a function `f` absolutely continuous on `[0, 1]` whose derivative is in `L²(0, 1)`. -/
theorem mem_adjoint_iff_ac (y : L2I) :
    y ∈ (momentumMin†).domain ↔ ∃ f : ℝ → ℂ, AbsolutelyContinuousOnInterval f 0 1 ∧
      MemLp (deriv f) 2 ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) ∧
      (y : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] f := by
  rw [mem_adjoint_iff_primitive]
  constructor
  · rintro ⟨c, g, hg⟩
    have hgi : IntervalIntegrable (fun t => g t) volume 0 1 := intervalIntegrable_of_integrableOn (integrable_L2I g)
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
      (contDiff_const (c := c)).contDiffOn.absolutelyContinuousOnInterval
    refine ⟨fun x => c + ∫ t in (0 : ℝ)..x, g t, hconst.add (ac_primitive hgi), ?_, hg⟩
    have hder : deriv (fun x => c + ∫ t in (0 : ℝ)..x, g t) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] g := by
      have h := (ae_restrict_iff' measurableSet_Ioo).mpr (hgi.ae_hasDerivAt_integral.mono fun x hx hxI =>
        hx (Ioo_subset_Icc_self.trans (uIcc_of_le (zero_le_one' ℝ)).symm.subset hxI) 0 left_mem_uIcc)
      filter_upwards [h] with x hx
      exact (hx.const_add c).deriv
    exact (Lp.memLp g).ae_eq hder.symm
  · rintro ⟨f, hf, hdf, hyf⟩
    refine ⟨f 0, hdf.toLp _, ?_⟩
    have hco := MemLp.coeFn_toLp hdf
    filter_upwards [hyf, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx, ac_eq_primitive hf ⟨hxI.1.le, hxI.2.le⟩]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo hco ⟨hxI.1.le, hxI.2.le⟩] with t ht htI
    exact (ht htI).symm

end Lightlike.OperatorAlgebras
