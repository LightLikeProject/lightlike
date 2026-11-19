import Lightlike.Poincare.OneParticle

/-!
# Strong continuity of the Poincaré representation on the mass shell

For an invariant measure `μ` on the mass shell, finite on compacts, the unitary representation
`V(a, A) = T(a) U(A)` of `ℝ⁴ ⋊ SL(2,ℂ)` on `L²(μ; ℂ^{n+1})` is strongly continuous: `(a, A) ↦ V(a, A) ψ` is
continuous for every `ψ` (`continuous_poincareL2`).

The proof: for a continuous compactly supported `ψ` the map is continuous at the identity by dominated convergence
(the supports of `V(a, A) ψ` for `A` near `1` stay in a compact set), hence everywhere by the group law; such `ψ` are
dense in `L²` (the shell is homeomorphic to `ℝ³` by the chart, so `μ` is regular), and the operators are
isometries.

Supporting results for the one-particle space; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2 Filter Topology

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

/-- The chart of the mass shell as a homeomorphism `ℝ³ ≃ H_m`. -/
def shellHomeo {m : ℝ} (hm : 0 < m) : (Fin 3 → ℝ) ≃ₜ MassShell m where
  toFun := chartInv hm
  invFun := fun P => coordV P.1
  left_inv := coordV_chartInv hm
  right_inv := chartInv_coordV hm
  continuous_toFun := continuous_chartInv hm
  continuous_invFun := continuous_coordV_shell

lemma locallyCompactSpace_massShell {m : ℝ} (hm : 0 < m) : LocallyCompactSpace (MassShell m) :=
  (shellHomeo hm).symm.isClosedEmbedding.locallyCompactSpace

/-- **Continuity from a dense set**: a family of linear isometries that is continuous on vectors approximating `f`
is continuous on `f`. -/
lemma continuous_of_approx {G H : Type*} [TopologicalSpace G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (U : G → H →ₗᵢ[ℂ] H) (f : H) (happ : ∀ ε > 0, ∃ d, dist f d < ε ∧ Continuous fun g => U g d) :
    Continuous fun g => U g f := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨d, hd, hc⟩ := happ ε hε
  refine ⟨fun g => U g d, hc, fun g => hεu ?_⟩
  rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map, ← dist_eq_norm]
  exact hd

variable {m : ℝ} {μ : Measure (MassShell m)}

/-- Continuous compactly supported functions approximate every element of `L²`. -/
lemma exists_continuous_close (hm : 0 < m) [IsFiniteMeasureOnCompacts μ] {n : ℕ} (f : Lp (Spinor n) 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : MassShell m → Spinor n, Continuous g ∧ HasCompactSupport g ∧ ∃ hg : MemLp g 2 μ, dist f (hg.toLp g) < ε := by
  haveI := locallyCompactSpace_massShell hm
  obtain ⟨g, hgc, hle, hgcont, hgm⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top
    (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε)
  refine ⟨g, hgcont, hgc, hgm, ?_⟩
  rw [Lp.dist_def]
  have he : eLpNorm (⇑f - ⇑(hgm.toLp g)) 2 μ = eLpNorm (⇑f - g) 2 μ :=
    eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hgm.coeFn_toLp)
  rw [he]
  calc (eLpNorm (⇑f - g) 2 μ).toReal ≤ ε / 2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hle
    _ < ε := by linarith

/-! ## Continuity of the pieces -/

lemma continuous_shellAct_joint : Continuous fun p : SL2C × MassShell m => shellAct p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  have hA : Continuous fun p : SL2C × MassShell m => ((p.1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hP : Continuous fun p : SL2C × MassShell m => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_snd
  exact (hA.matrix_mul hP).matrix_mul hA.matrix_conjTranspose

lemma continuous_wigField_A (hm : 0 < m) (n : ℕ) (Q : MassShell m) :
    Continuous fun A : SL2C => wigField hm n A Q := by
  have hinv : Continuous fun A : SL2C => A⁻¹ := continuous_inv
  have hs : Continuous fun A : SL2C => shellAct A⁻¹ Q := by
    apply continuous_induced_rng.2
    show Continuous fun A : SL2C => actP A⁻¹ Q.1
    unfold actP
    have hA : Continuous fun A : SL2C => ((A⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
      continuous_subtype_val.comp hinv
    exact (hA.matrix_mul continuous_const).matrix_mul hA.matrix_conjTranspose
  have hmat : Continuous fun A : SL2C =>
      ((((stdLift hm Q)⁻¹ * A * stdLift hm (shellAct A⁻¹ Q) : SL2C)) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp (((continuous_const (y := (stdLift hm Q)⁻¹)).mul continuous_id).mul
      ((continuous_stdLift hm).comp hs))
  have e : ∀ A : SL2C, ((wignerSU2 hm A (shellAct A⁻¹ Q) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((((stdLift hm Q)⁻¹ * A * stdLift hm (shellAct A⁻¹ Q) : SL2C)) : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro A
    have hQ : shellAct A (shellAct A⁻¹ Q) = Q := by rw [← shellAct_mul, mul_inv_cancel, shellAct_one]
    simp only [wignerSU2, wigner, hQ]
  have hw : Continuous fun A : SL2C => wignerSU2 hm A (shellAct A⁻¹ Q) := by
    apply continuous_induced_rng.2
    have h : (Subtype.val ∘ fun A : SL2C => wignerSU2 hm A (shellAct A⁻¹ Q)) = fun A : SL2C =>
        ((((stdLift hm Q)⁻¹ * A * stdLift hm (shellAct A⁻¹ Q) : SL2C)) : Matrix (Fin 2) (Fin 2) ℂ) :=
      funext e
    rw [h]
    exact hmat
  exact continuous_induced_rng.2 ((continuous_spinRep (n := n)).comp hw)

lemma mink_comm (P X : Matrix (Fin 2) (Fin 2) ℂ) : mink P X = mink X P := by
  simp only [mink, add_comm P X]
  ring

lemma continuous_pairing_right (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun a : Transl => pairing P a.1 := by
  have h : Continuous fun X : Matrix (Fin 2) (Fin 2) ℂ => mink P X := by
    simp only [mink_comm P]
    exact continuous_mink_left P
  exact Complex.continuous_re.comp (h.comp continuous_subtype_val)

/-- The pointwise form of `V(a, A) g`. -/
def poincVal (hm : 0 < m) (n : ℕ) (g : MassShell m → Spinor n) (x : Transl × SL2C) (Q : MassShell m) : Spinor n :=
  Complex.exp (Complex.I * pairing Q.1 x.1.1) • uAct (wigField hm n x.2 Q) (g (shellAct x.2⁻¹ Q))

lemma continuous_poincVal_x (hm : 0 < m) (n : ℕ) {g : MassShell m → Spinor n} (hg : Continuous g)
    (Q : MassShell m) : Continuous fun x : Transl × SL2C => poincVal hm n g x Q := by
  unfold poincVal
  refine Continuous.smul (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp ((continuous_pairing_right Q.1).comp continuous_fst)))) ?_
  exact continuous_uAct.comp (((continuous_wigField_A hm n Q).comp continuous_snd).prodMk
    (hg.comp (continuous_shellAct_joint.comp ((continuous_inv.comp continuous_snd).prodMk continuous_const))))

lemma continuous_poincVal_Q (hm : 0 < m) (n : ℕ) {g : MassShell m → Spinor n} (hg : Continuous g)
    (x : Transl × SL2C) : Continuous (poincVal hm n g x) := by
  unfold poincVal
  refine Continuous.smul (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp ((continuous_mink_left x.1.1).comp continuous_subtype_val))))) ?_
  exact continuous_uAct.comp ((continuous_wigField hm n x.2).prodMk (hg.comp (continuous_shellAct x.2⁻¹)))

lemma poincVal_one (hm : 0 < m) (n : ℕ) (g : MassShell m → Spinor n) (Q : MassShell m) :
    poincVal hm n g (0, 1) Q = g Q := by
  simp [poincVal, pairing, mink, wigField_one, uAct_one, shellAct_one]

lemma coeFn_poincareL2 (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ)
    {g : MassShell m → Spinor n} (hg : MemLp g 2 μ) (x : Transl × SL2C) :
    (poincareL2 hm n hμ x.1 x.2 (hg.toLp g) : MassShell m → Spinor n) =ᵐ[μ] poincVal hm n g x := by
  have h2 := (hμ x.2⁻¹).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
  filter_upwards [coeFn_translL2 n x.1 (inducedL2 hm n hμ x.2 (hg.toLp g)),
    coeFn_inducedL2 hm n hμ x.2 (hg.toLp g), h2] with Q e1 e2 e3
  simp only [Function.comp_apply] at e3
  simp only [poincareL2, LinearIsometry.coe_comp, Function.comp_apply]
  rw [e1, e2, e3]
  rfl

/-! ## The compact neighbourhood of `1` -/

/-- Matrices of `SL(2,ℂ)` entrywise within `1` of the identity. -/
def nearOne : Set SL2C := Subtype.val ⁻¹' (Set.pi Set.univ fun i : Fin 2 => Set.pi Set.univ fun j : Fin 2 =>
  Metric.closedBall ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j) 1)

lemma one_mem_nearOne : (1 : SL2C) ∈ nearOne :=
  fun _ _ _ _ => Metric.mem_closedBall_self zero_le_one

lemma isCompact_nearOne : IsCompact nearOne := by
  have hcl : Topology.IsClosedEmbedding (Subtype.val : SL2C → Matrix (Fin 2) (Fin 2) ℂ) := by
    refine Topology.IsClosedEmbedding.subtypeVal ?_
    exact isClosed_eq (continuous_id.matrix_det) continuous_const
  exact hcl.isCompact_preimage (isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _)

lemma nearOne_mem_nhds : nearOne ∈ 𝓝 (1 : SL2C) := by
  refine continuous_subtype_val.continuousAt.preimage_mem_nhds ?_
  refine set_pi_mem_nhds Set.finite_univ fun i _ => set_pi_mem_nhds Set.finite_univ fun j _ => ?_
  exact Metric.closedBall_mem_nhds _ one_pos

/-! ## Continuity at the identity on compactly supported functions -/

lemma tendsto_poincareL2_one (hm : 0 < m) {n : ℕ} [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ)
    {g : MassShell m → Spinor n} (hgc : Continuous g) (hgs : HasCompactSupport g) (hg : MemLp g 2 μ) :
    Tendsto (fun x : Transl × SL2C => poincareL2 hm n hμ x.1 x.2 (hg.toLp g)) (𝓝 (0, 1)) (𝓝 (hg.toLp g)) := by
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  set K : Set (MassShell m) := (fun p : SL2C × MassShell m => shellAct p.1 p.2) '' (nearOne ×ˢ tsupport g)
  have hK : IsCompact K := (isCompact_nearOne.prod hgs).image continuous_shellAct_joint
  have hK_meas : MeasurableSet K := hK.isClosed.measurableSet
  have h1K : tsupport g ⊆ K := fun Q hQ => ⟨(1, Q), ⟨one_mem_nearOne, hQ⟩, by simp [shellAct_one]⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hcongr : ∀ x : Transl × SL2C, eLpNorm (⇑(poincareL2 hm n hμ x.1 x.2 (hg.toLp g)) - ⇑(hg.toLp g)) 2 μ =
      eLpNorm (fun Q => poincVal hm n g x Q - g Q) 2 μ := fun x =>
    eLpNorm_congr_ae ((coeFn_poincareL2 hm n hμ hg x).sub hg.coeFn_toLp)
  simp only [hcongr]
  have hcont : ∀ x, Continuous fun Q => poincVal hm n g x Q - g Q := fun x =>
    (continuous_poincVal_Q hm n hgc x).sub hgc
  have hzero : ∀ x : Transl × SL2C, x.2 ∈ nearOne → ∀ Q, Q ∉ K → poincVal hm n g x Q = 0 := by
    intro x hx Q hQ
    have hnot : shellAct x.2⁻¹ Q ∉ tsupport g := fun h => hQ ⟨(x.2, shellAct x.2⁻¹ Q), ⟨hx, h⟩, by
      simp only; rw [← shellAct_mul, mul_inv_cancel, shellAct_one]⟩
    simp [poincVal, image_eq_zero_of_notMem_tsupport hnot, uAct]
  have hlim : Tendsto (fun x : Transl × SL2C => ∫⁻ Q, ‖poincVal hm n g x Q - g Q‖ₑ ^ (2 : ℝ) ∂μ)
      (𝓝 (0, 1)) (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence'
      (K.indicator fun _ => (ENNReal.ofReal (2 * C)) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => ((hcont x).measurable.enorm.pow_const _).aemeasurable
    · have hev : ∀ᶠ x in 𝓝 ((0 : Transl), (1 : SL2C)), x.2 ∈ nearOne :=
        continuous_snd.continuousAt.preimage_mem_nhds nearOne_mem_nhds
      filter_upwards [hev] with x hx
      refine Filter.Eventually.of_forall fun Q => ?_
      by_cases hQ : Q ∈ K
      · rw [Set.indicator_of_mem hQ]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖poincVal hm n g x Q - g Q‖ ≤ ‖poincVal hm n g x Q‖ + ‖g Q‖ := norm_sub_le _ _
          _ ≤ C + C := by
            refine add_le_add ?_ (hC Q)
            simp only [poincVal, norm_smul, norm_uAct]
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
    · refine Filter.Eventually.of_forall fun Q => ?_
      have h := ((continuous_poincVal_x hm n hgc Q).tendsto (0, 1)).sub_const (g Q)
      rw [poincVal_one, sub_self] at h
      have h' := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp h)
      rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h'
      exact h'
  rw [lintegral_zero] at hlim
  have hlim2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hlim2
  refine hlim2.congr' (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hcont x).aestronglyMeasurable]
  norm_num

/-! ## Strong continuity -/

lemma translAct_neg (A : SL2C) (a : Transl) : translAct A (-a) = -translAct A a := by
  apply Subtype.ext
  simp [translAct, actP]

lemma translAct_one (a : Transl) : translAct 1 a = a := Subtype.ext (by simp [translAct, actP])

lemma continuous_translAct : Continuous fun p : SL2C × Transl => translAct p.1 p.2 := by
  refine Continuous.subtype_mk ?_ _
  have hA : Continuous fun p : SL2C × Transl => ((p.1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have ha : Continuous fun p : SL2C × Transl => (p.2.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_snd
  exact (hA.matrix_mul ha).matrix_mul hA.matrix_conjTranspose

/-- **The representation is strongly continuous**: `(a, A) ↦ V(a, A) ψ` is continuous for every `ψ ∈ L²`. -/
theorem continuous_poincareL2 (hm : 0 < m) {n : ℕ} [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (f : Lp (Spinor n) 2 μ) :
    Continuous fun x : Transl × SL2C => poincareL2 hm n hμ x.1 x.2 f := by
  refine continuous_of_approx (fun x : Transl × SL2C => poincareL2 hm n hμ x.1 x.2) f fun ε hε => ?_
  obtain ⟨g, hgc, hgs, hg, hd⟩ := exists_continuous_close hm f hε
  refine ⟨hg.toLp g, hd, continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  -- move the continuity at the identity to `x₀` by the group law
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
  have hlaw : ∀ x : Transl × SL2C, poincareL2 hm n hμ x₀.1 x₀.2
      (poincareL2 hm n hμ (-translAct x₀.2⁻¹ x₀.1 + translAct x₀.2⁻¹ x.1) (x₀.2⁻¹ * x.2) (hg.toLp g)) =
        poincareL2 hm n hμ x.1 x.2 (hg.toLp g) := by
    intro x
    rw [poincareL2_mul]
    congr 2
    · rw [translAct_add, translAct_neg, ← translAct_mul, ← translAct_mul, mul_inv_cancel, translAct_one,
        translAct_one]
      abel
    · rw [← mul_assoc, mul_inv_cancel, one_mul]
  have ht := tendsto_poincareL2_one hm hμ hgc hgs hg
  rw [← hh0] at ht
  have ht' := ht.comp (hh.tendsto x₀)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero] at ht'
  refine ht'.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [← hlaw x, ← hlaw x₀, neg_add_cancel, inv_mul_cancel, poincareL2_one, ← map_sub, LinearIsometry.norm_map]

end

end Lightlike.Poincare
