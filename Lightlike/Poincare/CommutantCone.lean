import Lightlike.Poincare.MulOperatorL2
import Lightlike.Poincare.ConeContinuity
import Lightlike.Poincare.CommutantPVM

/-!
# The commutant of the translations on `L²` of the light cone

On `L²(ν)` of the forward light cone (`ν` σ-finite) a bounded operator `B` commuting with every translation commutes
with every Schwartz function of the momentum (`commute_bcfMul_schwartz_cone`, Fourier inversion and Fubini), with the
indicator of every open set (`commute_indL2_isOpen`: an open set of the cone is the momentum preimage of an open set
of `ℝ⁴`, `exists_open_momCE`) and then of every Borel set (`commute_indL2_cone`, the `π`-`λ` theorem), and it is the
multiplication by a measurable function (`exists_mulField_of_commute_transl_cone`).

Supporting results for the irreducibility of the massless one-particle representations; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology BoundedContinuousFunction SchwartzMap Real
open scoped InnerProductSpace FourierTransform ContDiff ComplexConjugate

namespace Lightlike.Poincare

noncomputable section

/-! ## Momenta of the cone -/

/-- The momentum of a point of the cone. -/
def momC (Q : LightCone) : Fin 4 → ℝ := ![coord0 Q.1, coordV Q.1 0, coordV Q.1 1, coordV Q.1 2]

/-- The momentum, in `MomSpace`. -/
def momCE (Q : LightCone) : MomSpace := WithLp.toLp 2 (momC Q)

lemma continuous_momC : Continuous momC := by
  have hval : Continuous fun Q : LightCone => (Q.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have h0 : Continuous fun Q : LightCone => coord0 Q.1 :=
    Complex.continuous_re.comp (((hval.matrix_elem 0 0).add (hval.matrix_elem 1 1)).div_const 2)
  have hV : ∀ k, Continuous fun Q : LightCone => coordV Q.1 k := fun k =>
    (continuous_apply k).comp (continuous_coordV.comp hval)
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact h0
  · exact hV 0
  · exact hV 1
  · exact hV 2

lemma continuous_momCE : Continuous momCE := (PiLp.continuous_toLp 2 _).comp continuous_momC

lemma momH_momC (Q : LightCone) : momH (coord0 Q.1) (coordV Q.1) = Q.1 := momH_coords Q.2.1.1

lemma pairing_eq_minkowski_cone (Q : LightCone) (a : Transl) :
    pairing Q.1 a.1 = minkowski (momC Q) (tcoords a) := by
  have ha : (a.1 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]; exact a.2
  have h := mink_momH (coord0 Q.1) (coord0 a.1) (coordV Q.1) (coordV a.1)
  rw [momH_momC, momH_coords ha] at h
  rw [pairing, h, Complex.ofReal_re]
  simp [minkowski, momC, tcoords]

lemma pairing_freqTransl_cone (Q : LightCone) (ξ : MomSpace) :
    pairing Q.1 (freqTransl ξ).1 = 2 * π * ⟪ξ, momCE Q⟫_ℝ := by
  rw [pairing_eq_minkowski_cone]
  simp only [minkowski, tcoords, freqTransl, coord0_momH, coordV_momH, momC, momCE,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, star_trivial]
  ring

/-- The Schwartz function `φ` of the momentum, on the cone. -/
def schwartzMomC (φ : 𝓢(MomSpace, ℂ)) : LightCone →ᵇ ℂ :=
  φ.toBoundedContinuousFunction.compContinuous ⟨momCE, continuous_momCE⟩

lemma schwartzMomC_apply (φ : 𝓢(MomSpace, ℂ)) (Q : LightCone) : schwartzMomC φ Q = φ (momCE Q) := rfl

variable {ν : Measure LightCone}

/-- **Fourier inversion against the translations** on the cone. -/
theorem inner_bcfMul_schwartz_cone [SFinite ν] (φ : 𝓢(MomSpace, ℂ)) (u v : Lp ℂ 2 ν) :
    ⟪u, bcfMul (schwartzMomC φ) v⟫_ℂ = ∫ ξ, (𝓕 φ) ξ * ⟪u, translCone (freqTransl ξ) v⟫_ℂ := by
  have hinv : ∀ p : MomSpace, φ p = ∫ ξ, Complex.exp (↑(2 * π * ⟪ξ, p⟫_ℝ) * Complex.I) • (𝓕 φ) ξ := by
    intro p
    have h := congrFun (φ.continuous.fourierInv_fourier_eq (φ.integrable (μ := volume))
      ((𝓕 φ).integrable (μ := volume))) p
    rw [← h, fourierInv_eq', fourier_coe]
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) u v
  set F : LightCone × MomSpace → ℂ := fun z =>
    Complex.exp (↑(2 * π * ⟪z.2, momCE z.1⟫_ℝ) * Complex.I) * (𝓕 φ) z.2 * ⟪u z.1, v z.1⟫_ℂ
  have hF : Integrable F (ν.prod volume) := by
    have hprod := hint.mul_prod ((𝓕 φ).integrable (μ := volume))
    refine hprod.mono ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have hc : Continuous fun z : LightCone × MomSpace =>
          Complex.exp (↑(2 * π * ⟪z.2, momCE z.1⟫_ℝ) * Complex.I) * (𝓕 φ) z.2 := by
        have : Continuous fun z : LightCone × MomSpace => ⟪z.2, momCE z.1⟫_ℝ :=
          continuous_snd.inner (continuous_momCE.comp continuous_fst)
        exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul this)).mul
          continuous_const)).mul ((𝓕 φ).continuous.comp continuous_snd)
      exact hc.aestronglyMeasurable.mul (hint.1.comp_fst)
    · simp only [F, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      rw [mul_comm]
  have hL : ⟪u, bcfMul (schwartzMomC φ) v⟫_ℂ = ∫ Q, ∫ ξ, F (Q, ξ) ∂volume ∂ν := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_bcfMul (μ := ν) (schwartzMomC φ) v] with Q hQ
    rw [hQ, inner_smul_right, schwartzMomC_apply, hinv, ← integral_mul_const]
    rfl
  have hR : ∫ ξ, (𝓕 φ) ξ * ⟪u, translCone (freqTransl ξ) v⟫_ℂ = ∫ ξ, ∫ Q, F (Q, ξ) ∂ν ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [MeasureTheory.L2.inner_def]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_translCone (ν := ν) (freqTransl ξ) v] with Q hQ
    rw [hQ, ← smul_eq_mul (Complex.exp _), inner_smul_right, pairing_freqTransl_cone]
    simp only [F]
    rw [show Complex.I * (↑(2 * π * ⟪ξ, momCE Q⟫_ℝ) : ℂ) = ↑(2 * π * ⟪ξ, momCE Q⟫_ℝ) * Complex.I by ring]
    ring
  rw [hL, hR, integral_integral_swap hF]

/-- **An operator commuting with the translations of the cone commutes with every Schwartz function of the
momentum.** -/
theorem commute_bcfMul_schwartz_cone [SFinite ν] (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hB : ∀ a f, B (translCone a f) = translCone a (B f)) (φ : 𝓢(MomSpace, ℂ)) (f : Lp ℂ 2 ν) :
    B (bcfMul (schwartzMomC φ) f) = bcfMul (schwartzMomC φ) (B f) := by
  refine ext_inner_left ℂ fun u => ?_
  rw [← ContinuousLinearMap.adjoint_inner_left, inner_bcfMul_schwartz_cone, inner_bcfMul_schwartz_cone]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [ContinuousLinearMap.adjoint_inner_left, hB]

/-! ## Indicators of open and Borel sets -/

/-- **An open set of the cone is the momentum preimage of an open set of `ℝ⁴`.** -/
lemma exists_open_momCE {U : Set LightCone} (hU : IsOpen U) : ∃ V : Set MomSpace, IsOpen V ∧ momCE ⁻¹' V = U := by
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
  have hg : Continuous fun p : MomSpace => momH (p 0) ![p 1, p 2, p 3] := by
    have hc : ∀ i, Continuous fun p : MomSpace => p i := fun i => (PiLp.continuous_apply 2 _ i)
    unfold momH
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine ⟨(fun p : MomSpace => momH (p 0) ![p 1, p 2, p 3]) ⁻¹' U', hU'.preimage hg, ?_⟩
  ext Q
  simp only [Set.mem_preimage]
  have e : momH ((momCE Q) 0) ![(momCE Q) 1, (momCE Q) 2, (momCE Q) 3] = Q.1 := by
    have : (![(momCE Q) 1, (momCE Q) 2, (momCE Q) 3] : Fin 3 → ℝ) = coordV Q.1 := by
      funext i; fin_cases i <;> rfl
    rw [this]
    exact momH_momC Q
  rw [e]

/-- **`B` commutes with the indicator of every open set of the cone.** -/
theorem commute_indL2_isOpen [SFinite ν] (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hB : ∀ a f, B (translCone a f) = translCone a (B f)) {U : Set LightCone} (hU : IsOpen U) (v : Lp ℂ 2 ν) :
    B (indL2 U hU.measurableSet v) = indL2 U hU.measurableSet (B v) := by
  obtain ⟨V, hV, hVU⟩ := exists_open_momCE hU
  obtain ⟨f, hfs, hf, hfr⟩ := hV.exists_contDiff_support_eq (n := ⊤)
  have hf0 : ∀ p, 0 ≤ f p := fun p => (hfr ⟨p, rfl⟩).1
  set h : ℕ → LightCone → ℂ := fun k Q => smoothApproxFun f k (momCE Q)
  have hm : ∀ k, Measurable (h k) := fun k =>
    ((smoothApproxFun_contDiff hf k).continuous.comp continuous_momCE).measurable
  have hb : ∀ k Q, ‖h k Q‖ ≤ 1 := fun k Q => norm_smoothApproxFun_le f k _
  have hlim : ∀ Q, Tendsto (fun k => h k Q) atTop (𝓝 (U.indicator (fun _ => (1 : ℂ)) Q)) := by
    intro Q
    have h1 := tendsto_smoothApproxFun hf0 (momCE Q)
    have h2 : (Function.support f).indicator (fun _ => (1 : ℂ)) (momCE Q) = U.indicator (fun _ => (1 : ℂ)) Q := by
      rw [hfs]
      by_cases hQ : Q ∈ U
      · rw [Set.indicator_of_mem (show momCE Q ∈ V by rw [← hVU] at hQ; exact hQ), Set.indicator_of_mem hQ]
      · rw [Set.indicator_of_notMem (show momCE Q ∉ V from fun h => hQ (hVU ▸ h)), Set.indicator_of_notMem hQ]
    rw [h2] at h1
    exact h1
  have hcomm : ∀ k (w : Lp ℂ 2 ν), mulOp (h k) (hm k) (hb k) w = bcfMul (schwartzMomC (smoothApprox hf k)) w :=
    fun k w => mulOp_eq_bcfMul (schwartzMomC (smoothApprox hf k)) (hb k) w
  have t1 := tendsto_mulOp (μ := ν) hm hb (measurable_const.indicator hU.measurableSet)
    (norm_indicator_one_le U) hlim v
  have t2 := tendsto_mulOp (μ := ν) hm hb (measurable_const.indicator hU.measurableSet)
    (norm_indicator_one_le U) hlim (B v)
  have t1' := (B.continuous.tendsto _).comp t1
  refine tendsto_nhds_unique t1' (t2.congr fun k => ?_)
  simp only [Function.comp_apply]
  rw [hcomm, hcomm, commute_bcfMul_schwartz_cone B hB]

/-- **`B` commutes with the indicator of every Borel set of the cone** (Dynkin's `π`-`λ` theorem). -/
theorem commute_indL2_cone [SFinite ν] (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hB : ∀ a f, B (translCone a f) = translCone a (B f)) {S : Set LightCone} (hS : MeasurableSet S)
    (v : Lp ℂ 2 ν) : B (indL2 S hS v) = indL2 S hS (B v) := by
  -- the predicate is closed under complements and intersections
  have hcompl : ∀ {T : Set LightCone} (hT : MeasurableSet T),
      (∀ v, B (indL2 (μ := ν) T hT v) = indL2 T hT (B v)) → ∀ v, B (indL2 (μ := ν) Tᶜ hT.compl v) =
        indL2 Tᶜ hT.compl (B v) := by
    intro T hT h v
    rw [indL2_compl hT, indL2_compl hT, map_sub, h]
  have hinter : ∀ {T T' : Set LightCone} (hT : MeasurableSet T) (hT' : MeasurableSet T'),
      (∀ v, B (indL2 (μ := ν) T hT v) = indL2 T hT (B v)) → (∀ v, B (indL2 (μ := ν) T' hT' v) = indL2 T' hT' (B v)) →
      ∀ v, B (indL2 (μ := ν) (T ∩ T') (hT.inter hT') v) = indL2 (T ∩ T') (hT.inter hT') (B v) := by
    intro T T' hT hT' h h' v
    rw [indL2_inter hT hT', indL2_inter hT hT', h, h']
  have hunion : ∀ {T T' : Set LightCone} (hT : MeasurableSet T) (hT' : MeasurableSet T'),
      (∀ v, B (indL2 (μ := ν) T hT v) = indL2 T hT (B v)) → (∀ v, B (indL2 (μ := ν) T' hT' v) = indL2 T' hT' (B v)) →
      ∀ v, B (indL2 (μ := ν) (T ∪ T') (hT.union hT') v) = indL2 (T ∪ T') (hT.union hT') (B v) := by
    intro T T' hT hT' h h' v
    have e : T ∪ T' = (Tᶜ ∩ T'ᶜ)ᶜ := by rw [← Set.compl_union, compl_compl]
    rw [indL2_congr e (hT.union hT') (hT.compl.inter hT'.compl).compl]
    exact hcompl (hT.compl.inter hT'.compl) (hinter hT.compl hT'.compl (hcompl hT h) (hcompl hT' h')) v
  revert v
  refine MeasurableSpace.induction_on_inter (C := fun S hS => ∀ v, B (indL2 (μ := ν) S hS v) =
    indL2 S hS (B v)) (BorelSpace.measurable_eq (α := LightCone)) isPiSystem_isOpen ?_ ?_ ?_ ?_ S hS
  · intro v
    rw [indL2_empty, indL2_empty, map_zero]
  · intro U hU v
    exact commute_indL2_isOpen B hB hU v
  · intro T hT h
    exact hcompl hT h
  · intro E _ hE h v
    -- the partial unions
    have hacc : ∀ N, MeasurableSet (Set.accumulate E N) := fun N =>
      MeasurableSet.biUnion (Set.to_countable _) fun i _ => hE i
    have hN : ∀ N, ∀ v, B (indL2 (μ := ν) (Set.accumulate E N) (hacc N) v) =
        indL2 (Set.accumulate E N) (hacc N) (B v) := by
      intro N
      induction N with
      | zero =>
        intro v
        rw [indL2_congr (Set.accumulate_zero_nat E) (hacc 0) (hE 0)]
        exact h 0 v
      | succ N ih =>
        intro v
        rw [indL2_congr (Set.accumulate_succ E N) (hacc (N + 1)) ((hacc N).union (hE (N + 1)))]
        exact hunion (hacc N) (hE (N + 1)) ih (h (N + 1)) v
    have t1 := tendsto_indL2_iUnion (μ := ν) hacc (Set.monotone_accumulate) v
    have t2 := tendsto_indL2_iUnion (μ := ν) hacc (Set.monotone_accumulate) (B v)
    have t1' := (B.continuous.tendsto _).comp t1
    have hlim := tendsto_nhds_unique t1' (t2.congr fun N => (hN N v).symm)
    rw [indL2_congr Set.iUnion_accumulate (MeasurableSet.iUnion hacc) (MeasurableSet.iUnion hE)] at hlim
    exact hlim

/-! ## The multiplication function -/

lemma exists_posWeight_cone [SigmaFinite ν] :
    ∃ w : LightCone → ℝ, (∀ Q, 0 < w Q) ∧ Measurable w ∧ MemLp (fun Q => (w Q : ℂ)) 2 ν := by
  obtain ⟨g, hgpos, hgm, hgint⟩ := exists_pos_lintegral_lt_of_sigmaFinite ν (ε := 1) one_ne_zero
  have hwm : Measurable fun Q => Real.sqrt (g Q) := (NNReal.continuous_coe.measurable.comp hgm).sqrt
  have hae : AEStronglyMeasurable (fun Q => ((Real.sqrt (g Q) : ℝ) : ℂ)) ν :=
    (Complex.continuous_ofReal.measurable.comp hwm).aestronglyMeasurable
  refine ⟨fun Q => Real.sqrt (g Q), fun Q => Real.sqrt_pos.2 (by exact_mod_cast hgpos Q), hwm, ?_⟩
  change eLpNorm _ 2 ν < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hae]
  have hint : ∫⁻ Q, ‖((Real.sqrt (g Q) : ℝ) : ℂ)‖ₑ ^ (2 : ENNReal).toReal ∂ν < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun Q => ?_)) (hgint.trans ENNReal.one_lt_top)
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hint.ne

/-- **An operator commuting with the indicator multiplications of the cone is a multiplication**: `(B f)(Q) =
m(Q) f(Q)` almost everywhere, with `m` measurable. -/
theorem exists_mulField_of_commute_ind [SigmaFinite ν] (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hI : ∀ (S : Set LightCone) (hS : MeasurableSet S) v, B (indL2 S hS v) = indL2 S hS (B v)) :
    ∃ M : LightCone → ℂ, Measurable M ∧ ∀ f : Lp ℂ 2 ν, (B f : LightCone → ℂ) =ᵐ[ν] fun Q => M Q * f Q := by
  obtain ⟨w, hwpos, hwm, hwL⟩ := exists_posWeight_cone (ν := ν)
  set W : Lp ℂ 2 ν := hwL.toLp _
  have hW : (W : LightCone → ℂ) =ᵐ[ν] fun Q => (w Q : ℂ) := hwL.coeFn_toLp
  set M : LightCone → ℂ := fun Q => (B W : LightCone → ℂ) Q / (w Q : ℂ)
  have hMm : Measurable M :=
    (Lp.stronglyMeasurable (B W)).measurable.div (Complex.continuous_ofReal.measurable.comp hwm)
  refine ⟨M, hMm, ?_⟩
  -- the vectors on which `B` is the multiplication by `M`
  let K : Submodule ℂ (Lp ℂ 2 ν) :=
    { carrier := {f | (B f : LightCone → ℂ) =ᵐ[ν] fun Q => M Q * f Q}
      add_mem' := fun {f g} hf hg => by
        change (⇑(B (f + g)) : LightCone → ℂ) =ᵐ[ν] _
        rw [map_add]
        filter_upwards [hf, hg, Lp.coeFn_add (B f) (B g), Lp.coeFn_add f g] with Q h1 h2 h3 h4
        rw [h3, Pi.add_apply, h1, h2, h4, Pi.add_apply, mul_add]
      zero_mem' := by
        change (⇑(B 0) : LightCone → ℂ) =ᵐ[ν] _
        rw [map_zero]
        filter_upwards [Lp.coeFn_zero ℂ 2 ν] with Q h
        rw [h, Pi.zero_apply, mul_zero]
      smul_mem' := fun c f hf => by
        change (⇑(B (c • f)) : LightCone → ℂ) =ᵐ[ν] _
        rw [map_smul]
        filter_upwards [hf, Lp.coeFn_smul c (B f), Lp.coeFn_smul c f] with Q h1 h2 h3
        rw [h2, Pi.smul_apply, h1, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  have hKc : IsClosed (K : Set (Lp ℂ 2 ν)) := by
    refine IsSeqClosed.isClosed fun f g hf hlim => ?_
    obtain ⟨ns, hns, hns_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    have hB' : Tendsto (fun i => B (f (ns i))) atTop (𝓝 (B g)) :=
      (B.continuous.tendsto g).comp (hlim.comp hns.tendsto_atTop)
    obtain ⟨ns', hns', hns'_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hB').exists_seq_tendsto_ae
    have hall : ∀ᵐ Q ∂ν, ∀ k, (B (f k) : LightCone → ℂ) Q = M Q * f k Q := ae_all_iff.2 fun k => hf k
    change (⇑(B g) : LightCone → ℂ) =ᵐ[ν] _
    filter_upwards [hns_ae, hns'_ae, hall] with Q h1 h2 h3
    have h1' : Tendsto (fun i => f (ns (ns' i)) Q) atTop (𝓝 (g Q)) := h1.comp hns'.tendsto_atTop
    have h4 := (tendsto_const_nhds (x := M Q)).mul h1'
    refine tendsto_nhds_unique h2 (h4.congr fun i => ?_)
    exact (h3 _).symm
  -- the generators `1_S w`
  have hgen : ∀ (S : Set LightCone) (hS : MeasurableSet S), indL2 S hS W ∈ K := by
    intro S hS
    change (⇑(B (indL2 S hS W)) : LightCone → ℂ) =ᵐ[ν] _
    rw [hI]
    filter_upwards [coeFn_indL2 (μ := ν) hS (B W), coeFn_indL2 (μ := ν) hS W, hW] with Q h1 h2 h3
    rw [h1, h2]
    by_cases hQ : Q ∈ S
    · rw [Set.indicator_of_mem hQ, Set.indicator_of_mem hQ, h3]
      have hw0 : (w Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hwpos Q).ne'
      simp only [M]
      field_simp
    · rw [Set.indicator_of_notMem hQ, Set.indicator_of_notMem hQ, mul_zero]
  -- density
  have hdense : (Submodule.span ℂ {f | ∃ (S : Set LightCone) (hS : MeasurableSet S), f = indL2 S hS W}).topologicalClosure
      = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro u hu
    rw [Submodule.mem_orthogonal] at hu
    have hint : Integrable (fun Q => (w Q : ℂ) * u Q) ν := by
      have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) W u
      refine h.congr ?_
      filter_upwards [hW] with Q h2
      rw [h2, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]
    have h0 : (fun Q => (w Q : ℂ) * u Q) =ᵐ[ν] 0 := by
      refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hint.integrableOn) (fun s hs _ => ?_)
      have h := hu _ (Submodule.subset_span ⟨s, hs, rfl⟩)
      rw [MeasureTheory.L2.inner_def] at h
      rw [← h, ← integral_indicator hs]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_indL2 (μ := ν) hs W, hW] with Q h1 h2
      rw [h1]
      by_cases hQ : Q ∈ s
      · rw [Set.indicator_of_mem hQ, Set.indicator_of_mem hQ, h2, RCLike.inner_apply, Complex.conj_ofReal,
          mul_comm]
      · rw [Set.indicator_of_notMem hQ, Set.indicator_of_notMem hQ, inner_zero_left]
    apply Lp.ext
    filter_upwards [h0, Lp.coeFn_zero ℂ 2 ν] with Q hQ h0Q
    rw [h0Q]
    have hw0 : (w Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hwpos Q).ne'
    exact (mul_eq_zero.1 hQ).resolve_left hw0
  have hle : (Submodule.span ℂ {f | ∃ (S : Set LightCone) (hS : MeasurableSet S), f = indL2 S hS W}).topologicalClosure
      ≤ K := Submodule.topologicalClosure_minimal _
    (Submodule.span_le.2 fun f ⟨S, hS, hf⟩ => hf ▸ hgen S hS) hKc
  rw [hdense] at hle
  exact fun f => hle Submodule.mem_top

/-- **An operator commuting with the translations of the cone is a multiplication** by a measurable function. -/
theorem exists_mulField_of_commute_transl_cone [SigmaFinite ν] (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hB : ∀ a f, B (translCone a f) = translCone a (B f)) :
    ∃ M : LightCone → ℂ, Measurable M ∧ ∀ f : Lp ℂ 2 ν, (B f : LightCone → ℂ) =ᵐ[ν] fun Q => M Q * f Q :=
  exists_mulField_of_commute_ind B fun _ hS v => commute_indL2_cone B hB hS v

end

end Lightlike.Poincare
