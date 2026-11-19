import Lightlike.Poincare.ConeNull

/-!
# The massless one-particle representations are strongly continuous

For every invariant measure `ν` on the light cone, finite on compacts, the representation
`V(a, A) = T(a) U(A)` of `ℝ⁴ ⋊ SL(2,ℂ)` on `L²(ν)` with helicity `n/2` is strongly continuous
(`continuous_poincareCone`). The helicity factor `χ_n(W(A, A⁻¹ P))` is discontinuous on the half-line `P₀₀ = 0`,
where the standard lift jumps, but that half-line is `ν`-null (`measure_alphaC_eq_zero`); off it the standard lift
is continuous (`continuousAt_coneLift`) and the factor tends to `1` as `A → 1` (`tendsto_helMult`), so dominated
convergence applies to compactly supported continuous wave functions, which are dense.

Supporting results for the one-particle space; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology
open scoped ComplexOrder

namespace Lightlike.Poincare

noncomputable section

local instance (k : ℕ) : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin k → Fin k → ℂ))

local instance (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))

local instance : TopologicalSpace.PseudoMetrizableSpace SL2C :=
  Topology.IsInducing.subtypeVal.pseudoMetrizableSpace

local instance : TopologicalSpace.PseudoMetrizableSpace Transl :=
  Topology.IsInducing.subtypeVal.pseudoMetrizableSpace

local instance : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℂ))

/-! ## The cone is locally compact -/

lemma isLocallyClosed_lightConeH : IsLocallyClosed LightConeH := by
  have h1 : IsClosed {P : Matrix (Fin 2) (Fin 2) ℂ | P.PosSemidef} := Matrix.posSemidef_is_closed
  have h2 : IsClosed {P : Matrix (Fin 2) (Fin 2) ℂ | P.det = 0} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  have h3 : IsOpen {P : Matrix (Fin 2) (Fin 2) ℂ | P ≠ 0} := isOpen_ne
  have e : LightConeH = ({P : Matrix (Fin 2) (Fin 2) ℂ | P.PosSemidef} ∩ {P | P.det = 0}) ∩ {P | P ≠ 0} := by
    ext P; simp [LightConeH, and_assoc]
  rw [e]
  exact (h1.inter h2).isLocallyClosed.inter h3.isLocallyClosed

instance locallyCompactSpace_lightCone : LocallyCompactSpace LightCone :=
  isLocallyClosed_lightConeH.locallyCompactSpace

/-- Continuous compactly supported functions approximate every element of `L²` of the cone. -/
lemma exists_continuous_close_cone {ν : Measure LightCone} [IsFiniteMeasureOnCompacts ν] (f : Lp ℂ 2 ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : LightCone → ℂ, Continuous g ∧ HasCompactSupport g ∧ ∃ hg : MemLp g 2 ν, dist f (hg.toLp g) < ε := by
  obtain ⟨g, hgc, hle, hgcont, hgm⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε)
  refine ⟨g, hgcont, hgc, hgm, ?_⟩
  rw [Lp.dist_def]
  have he : eLpNorm (⇑f - ⇑(hgm.toLp g)) 2 ν = eLpNorm (⇑f - g) 2 ν :=
    eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hgm.coeFn_toLp)
  rw [he]
  calc (eLpNorm (⇑f - g) 2 ν).toReal ≤ ε / 2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hle
    _ < ε := by linarith

/-! ## The standard lift off the half-line `P₀₀ = 0` -/

lemma continuous_alphaC_cone : Continuous fun P : LightCone => alphaC P.1 :=
  Complex.continuous_re.comp ((continuous_subtype_val : Continuous fun P : LightCone =>
    (P.1 : Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem 0 0)

lemma continuousAt_coneLift {Q : LightCone} (hQ : 0 < alphaC Q.1) :
    Tendsto (fun P : LightCone => ((coneLift P : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) (𝓝 Q)
      (𝓝 ((coneLift Q : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hev : ∀ᶠ P in 𝓝 Q, 0 < alphaC P.1 := continuous_alphaC_cone.continuousAt.eventually (lt_mem_nhds hQ)
  have hs : Continuous fun P : LightCone => ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_alphaC_cone.div_const 2).sqrt)
  have hs0 : ((Real.sqrt (alphaC Q.1 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by linarith)).ne'
  have h01 : Continuous fun P : LightCone => starRingEnd ℂ ((P.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1) :=
    continuous_star.comp ((continuous_subtype_val : Continuous fun P : LightCone =>
      (P.1 : Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem 0 1)
  set F : LightCone → Matrix (Fin 2) (Fin 2) ℂ := fun P =>
    !![((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ), 0;
       starRingEnd ℂ (P.1 0 1) / (2 * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)),
       1 / ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)] with hF
  have hFc : ContinuousAt F Q := by
    have e1 : ContinuousAt (fun P : LightCone =>
        starRingEnd ℂ (P.1 0 1) / (2 * ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ))) Q :=
      h01.continuousAt.div (continuous_const.mul hs).continuousAt (mul_ne_zero two_ne_zero hs0)
    have e2 : ContinuousAt (fun P : LightCone => 1 / ((Real.sqrt (alphaC P.1 / 2) : ℝ) : ℂ)) Q :=
      continuousAt_const.div hs.continuousAt hs0
    refine (tendsto_pi_nhds (f := fun P => (F P : Fin 2 → Fin 2 → ℂ)) (g := F Q)).2 fun i =>
      (tendsto_pi_nhds (f := fun P => (F P : Fin 2 → Fin 2 → ℂ) i) (g := F Q i)).2 fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa [F] using hs.continuousAt.tendsto
    · simp [F]
    · simpa [F] using e1.tendsto
    · simpa [F] using e2.tendsto
  have heq : (fun P : LightCone => ((coneLift P : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) =ᶠ[𝓝 Q] F := by
    filter_upwards [hev] with P hP
    change coneLiftMat P.1 = F P
    rw [coneLiftMat, if_pos hP]
  have hQF : ((coneLift Q : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = F Q := by
    change coneLiftMat Q.1 = F Q
    rw [coneLiftMat, if_pos hQ]
  rw [hQF]
  exact hFc.tendsto.congr' heq.symm

/-- **The helicity factor tends to `1`** as `A → 1`, off the half-line `P₀₀ = 0`. -/
lemma tendsto_helMult (n : ℤ) {Q : LightCone} (hQ : 0 < alphaC Q.1) :
    Tendsto (fun A : SL2C => helMult n A Q) (𝓝 1) (𝓝 1) := by
  have hact : Tendsto (fun A : SL2C => A⁻¹ • Q) (𝓝 1) (𝓝 Q) := by
    have h := ((continuous_smul_cone_left Q).comp continuous_inv).tendsto (1 : SL2C)
    simpa [Function.comp_def] using h
  have hL : Tendsto (fun A : SL2C => ((coneLift (A⁻¹ • Q) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) (𝓝 1)
      (𝓝 ((coneLift Q : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) := (continuousAt_coneLift hQ).comp hact
  have hA : Tendsto (fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ)) (𝓝 1) (𝓝 1) := by
    have h := (continuous_subtype_val : Continuous fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ)).tendsto
      (1 : SL2C)
    rw [Matrix.SpecialLinearGroup.coe_one] at h
    exact h
  have hW : Tendsto (fun A : SL2C => (((coneLift Q)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) *
      (A : Matrix (Fin 2) (Fin 2) ℂ) * ((coneLift (A⁻¹ • Q) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) (𝓝 1) (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (((coneLift Q)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ))).mul hA).mul hL
    have e : (((coneLift Q)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * 1 * ((coneLift Q : SL2C) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [Matrix.mul_one]
      change ((((coneLift Q)⁻¹ * coneLift Q : SL2C)) : Matrix (Fin 2) (Fin 2) ℂ) = 1
      rw [inv_mul_cancel]
      rfl
    rw [e] at h
    exact h
  have hM : Tendsto (fun A : SL2C => ((wignerStab coneLift_smul A (A⁻¹ • Q)).1 :
      Matrix (Fin 2) (Fin 2) ℂ) 0 0) (𝓝 1) (𝓝 1) := by
    have h : Tendsto (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (𝓝 1) (𝓝 1) := by
      have := ((continuous_id (X := Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem 0 0).tendsto 1
      simp only [id] at this
      rw [Matrix.one_apply_eq] at this
      exact this
    have h' := h.comp hW
    have e : ∀ A : SL2C, ((wignerStab coneLift_smul A (A⁻¹ • Q)).1 : Matrix (Fin 2) (Fin 2) ℂ) =
        (((coneLift Q)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * (A : Matrix (Fin 2) (Fin 2) ℂ) *
          ((coneLift (A⁻¹ • Q) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) := by
      intro A
      change (((coneLift (A • (A⁻¹ • Q)))⁻¹ * A * coneLift (A⁻¹ • Q) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = _
      rw [smul_inv_smul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact h'.congr fun A => by simp only [Function.comp_apply]; rw [e]
  have hz : ContinuousAt (fun z : ℂ => z ^ n) 1 := continuousAt_zpow₀ 1 n (Or.inl one_ne_zero)
  have h := hz.tendsto.comp hM
  rw [_root_.one_zpow] at h
  exact h

/-! ## Strong continuity -/

variable {ν : Measure LightCone}

/-- The wave function `V(a, A) g`. -/
def coneVal (n : ℤ) (g : LightCone → ℂ) (x : Transl × SL2C) (Q : LightCone) : ℂ :=
  Complex.exp (Complex.I * pairing Q.1 x.1.1) * (helMult n x.2 Q * g (x.2⁻¹ • Q))

lemma coeFn_poincareCone (n : ℤ) (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν)
    {g : LightCone → ℂ} (hg : MemLp g 2 ν) (x : Transl × SL2C) :
    (poincareCone n hν x.1 x.2 (hg.toLp g) : LightCone → ℂ) =ᵐ[ν] coneVal n g x := by
  have h1 := coeFn_translCone (ν := ν) x.1 (helL2 n hν x.2 (hg.toLp g))
  have h2 := coeFn_helL2 n hν x.2 (hg.toLp g)
  have h3 := (hν x.2⁻¹).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
  filter_upwards [h1, h2, h3] with Q e1 e2 e3
  change (translCone x.1 (helL2 n hν x.2 (hg.toLp g)) : LightCone → ℂ) Q = _
  rw [e1, e2]
  simp only [Function.comp_apply] at e3
  rw [e3]
  rfl

lemma tendsto_poincareCone_one (n : ℤ) [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν)
    {g : LightCone → ℂ} (hgc : Continuous g) (hgs : HasCompactSupport g) (hg : MemLp g 2 ν) :
    Tendsto (fun x : Transl × SL2C => poincareCone n hν x.1 x.2 (hg.toLp g)) (𝓝 (0, 1)) (𝓝 (hg.toLp g)) := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  set K : Set LightCone := (fun p : SL2C × LightCone => p.1 • p.2) '' (nearOne ×ˢ tsupport g)
  have hK : IsCompact K := (isCompact_nearOne.prod hgs).image continuous_smul_cone
  have hK_meas : MeasurableSet K := hK.isClosed.measurableSet
  have h1K : tsupport g ⊆ K := fun Q hQ => ⟨(1, Q), ⟨one_mem_nearOne, hQ⟩, by simp⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hcongr : ∀ x : Transl × SL2C, eLpNorm (⇑(poincareCone n hν x.1 x.2 (hg.toLp g)) - ⇑(hg.toLp g)) 2 ν =
      eLpNorm (fun Q => coneVal n g x Q - g Q) 2 ν := fun x =>
    eLpNorm_congr_ae ((coeFn_poincareCone n hν hg x).sub hg.coeFn_toLp)
  simp only [hcongr]
  have hmeas : ∀ x : Transl × SL2C, Measurable fun Q => coneVal n g x Q - g Q := by
    intro x
    refine Measurable.sub ?_ hgc.measurable
    refine Measurable.mul ?_ ((measurable_helMult n x.2).mul
      (hgc.comp (continuous_smul_cone_right x.2⁻¹)).measurable)
    exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_pairing_cone x.1)))).measurable
  have hzero : ∀ x : Transl × SL2C, x.2 ∈ nearOne → ∀ Q, Q ∉ K → coneVal n g x Q = 0 := by
    intro x hx Q hQ
    have hnot : x.2⁻¹ • Q ∉ tsupport g := fun h => hQ ⟨(x.2, x.2⁻¹ • Q), ⟨hx, h⟩, by simp⟩
    simp [coneVal, image_eq_zero_of_notMem_tsupport hnot]
  have hlim : Tendsto (fun x : Transl × SL2C => ∫⁻ Q, ‖coneVal n g x Q - g Q‖ₑ ^ (2 : ℝ) ∂ν)
      (𝓝 (0, 1)) (𝓝 (∫⁻ _, 0 ∂ν)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence'
      (K.indicator fun _ => (ENNReal.ofReal (2 * C)) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => ((hmeas x).enorm.pow_const _).aemeasurable
    · have hev : ∀ᶠ x in 𝓝 ((0 : Transl), (1 : SL2C)), x.2 ∈ nearOne :=
        continuous_snd.continuousAt.preimage_mem_nhds nearOne_mem_nhds
      filter_upwards [hev] with x hx
      refine Filter.Eventually.of_forall fun Q => ?_
      by_cases hQ : Q ∈ K
      · rw [Set.indicator_of_mem hQ]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖coneVal n g x Q - g Q‖ ≤ ‖coneVal n g x Q‖ + ‖g Q‖ := norm_sub_le _ _
          _ ≤ C + C := by
            refine add_le_add ?_ (hC Q)
            simp only [coneVal, norm_mul, norm_helMult, one_mul]
            rw [show Complex.I * (pairing Q.1 x.1.1 : ℂ) = (pairing Q.1 x.1.1 : ℂ) * Complex.I by ring,
              Complex.norm_exp_ofReal_mul_I, one_mul]
            exact hC _
          _ = 2 * C := by ring
      · rw [Set.indicator_of_notMem hQ, hzero x hx Q hQ,
          image_eq_zero_of_notMem_tsupport (fun h => hQ (h1K h))]
        simp
    · rw [lintegral_indicator_const hK_meas]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hK.measure_lt_top.ne
    · have hae : ∀ᵐ Q ∂ν, 0 < alphaC Q.1 := by
        have h0 := measure_alphaC_eq_zero hν
        rw [ae_iff]
        refine measure_mono_null (fun Q hQ => ?_) h0
        simp only [Set.mem_setOf_eq, not_lt] at hQ ⊢
        have hnn : 0 ≤ alphaC Q.1 := by
          have := (Q.2.1.diag_nonneg (i := 0))
          rw [alphaC]
          exact (Complex.nonneg_iff.1 this).1
        linarith
      filter_upwards [hae] with Q hQ
      have hph : Tendsto (fun x : Transl × SL2C => Complex.exp (Complex.I * pairing Q.1 x.1.1)) (𝓝 (0, 1))
          (𝓝 1) := by
        have hc : Continuous fun x : Transl × SL2C => Complex.exp (Complex.I * pairing Q.1 x.1.1) :=
          Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
            ((continuous_pairing_right Q.1).comp continuous_fst)))
        have h := hc.tendsto (0, 1)
        have h0 : pairing Q.1 (0 : Transl).1 = 0 := by
          change (mink Q.1 0).re = 0
          simp [mink]
        rw [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
        exact h
      have hhel : Tendsto (fun x : Transl × SL2C => helMult n x.2 Q) (𝓝 (0, 1)) (𝓝 1) :=
        (tendsto_helMult n hQ).comp (continuous_snd.tendsto ((0 : Transl), (1 : SL2C)))
      have hgx : Tendsto (fun x : Transl × SL2C => g (x.2⁻¹ • Q)) (𝓝 (0, 1)) (𝓝 (g Q)) := by
        have h := (hgc.comp ((continuous_smul_cone_left Q).comp (continuous_inv.comp continuous_snd))).tendsto
          ((0 : Transl), (1 : SL2C))
        simpa [Function.comp_def] using h
      have h := ((hph.mul (hhel.mul hgx)).sub_const (g Q))
      rw [one_mul, one_mul, sub_self] at h
      have h' := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp h)
      rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h'
      exact h'
  rw [lintegral_zero] at hlim
  have hlim2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hlim2
  refine hlim2.congr' (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hmeas x).aestronglyMeasurable]
  norm_num

/-- **The massless one-particle representations are strongly continuous**, for every invariant s-finite measure on
the cone finite on compacts. -/
theorem continuous_poincareCone (n : ℤ) [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (f : Lp ℂ 2 ν) :
    Continuous fun x : Transl × SL2C => poincareCone n hν x.1 x.2 f := by
  refine continuous_of_approx (fun x : Transl × SL2C => poincareCone n hν x.1 x.2) f fun ε hε => ?_
  obtain ⟨g, hgc, hgs, hg, hd⟩ := exists_continuous_close_cone f hε
  refine ⟨hg.toLp g, hd, continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  have hh : Continuous fun x : Transl × SL2C =>
      ((-translAct x₀.2⁻¹ x₀.1 + translAct x₀.2⁻¹ x.1 : Transl), x₀.2⁻¹ * x.2) := by
    have h1 : Continuous fun x : Transl × SL2C => translAct x₀.2⁻¹ x.1 := by
      apply continuous_induced_rng.2
      show Continuous fun x : Transl × SL2C => actP x₀.2⁻¹ x.1.1
      unfold actP
      exact (continuous_const.matrix_mul (continuous_subtype_val.comp continuous_fst)).matrix_mul
        continuous_const
    have h2 : Continuous fun x : Transl × SL2C => (-translAct x₀.2⁻¹ x₀.1 + translAct x₀.2⁻¹ x.1 : Transl) :=
      (continuous_const (y := -translAct x₀.2⁻¹ x₀.1)).add h1
    have h3 : Continuous fun x : Transl × SL2C => x₀.2⁻¹ * x.2 :=
      (continuous_const (y := x₀.2⁻¹)).mul continuous_snd
    exact h2.prodMk h3
  have hh0 : ((-translAct x₀.2⁻¹ x₀.1 + translAct x₀.2⁻¹ x₀.1 : Transl), x₀.2⁻¹ * x₀.2) = (0, 1) := by
    rw [neg_add_cancel, inv_mul_cancel]
  have hlaw : ∀ x : Transl × SL2C, poincareCone n hν x₀.1 x₀.2
      (poincareCone n hν (-translAct x₀.2⁻¹ x₀.1 + translAct x₀.2⁻¹ x.1) (x₀.2⁻¹ * x.2) (hg.toLp g)) =
        poincareCone n hν x.1 x.2 (hg.toLp g) := by
    intro x
    rw [poincareCone_mul]
    congr 2
    · rw [translAct_add, translAct_neg, ← translAct_mul, ← translAct_mul, mul_inv_cancel, translAct_one,
        translAct_one]
      abel
    · rw [← mul_assoc, mul_inv_cancel, one_mul]
  have ht := tendsto_poincareCone_one n hν hgc hgs hg
  rw [← hh0] at ht
  have ht' := ht.comp (hh.tendsto x₀)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero] at ht'
  refine ht'.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [← hlaw x, ← hlaw x₀, neg_add_cancel, inv_mul_cancel, poincareCone_one, ← map_sub,
    LinearIsometry.norm_map]

end

end Lightlike.Poincare
