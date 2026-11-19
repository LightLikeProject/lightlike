import Lightlike.Poincare.OneOrbit
import Lightlike.Poincare.IrreducibleMassive

/-!
# The momentum measure on a mass shell is absolutely continuous

For a representation `V` of `ℝ⁴ ⋊ SL(2,ℂ)` whose momentum measure `P` is carried by the mass shell `p² = m²`,
`p⁰ > 0`, every set that is null for the image of the Haar measure of `SL(2,ℂ)` on the shell has projection `0`
(`momPVM_eq_zero_of_null`). Proof: `‖P(S) V(0, A) ψ‖² = ⟨ψ, P(A⁻¹ · S) ψ⟩`, and integrating over `A` (Tonelli,
the right invariance of the Haar measure) gives `0`; so `P(S) V(0, A) ψ = 0` for almost every `A`, hence for every
`A` by strong continuity, in particular for `A = 1`.

Supporting results for the imprimitivity theorem; no catalogue entry.
-/

open scoped InnerProductSpace ComplexOrder
open Filter Topology MeasureTheory Matrix Lightlike.Lorentz Lightlike.OperatorAlgebras.Spectral
  Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Poincare

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The momentum coordinates of a point of the shell: `J (tcoords P)`. -/
def shellCoords {m : ℝ} (P : MassShell m) : Fin 4 → ℝ :=
  flipJ ![coord0 P.1, coordV P.1 0, coordV P.1 1, coordV P.1 2]

lemma continuous_shellCoords {m : ℝ} : Continuous (shellCoords (m := m)) := by
  refine continuous_flipJ.comp (continuous_pi fun i => ?_)
  have hval : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have h0 : Continuous fun P : MassShell m => coord0 P.1 :=
    Complex.continuous_re.comp (((hval.matrix_elem 0 0).add (hval.matrix_elem 1 1)).div_const 2)
  have hV' : ∀ k, Continuous fun P : MassShell m => coordV P.1 k := fun k =>
    (continuous_apply k).comp (continuous_coordV.comp hval)
  fin_cases i
  · exact h0
  · exact hV' 0
  · exact hV' 1
  · exact hV' 2

/-- The point of the shell with momentum coordinates `p`, for `p` on the shell. -/
def shellPoint {m : ℝ} {p : Fin 4 → ℝ} (hp : p ∈ shellSet m) : MassShell m := ⟨(hermOf (flipJ p)).1, hp⟩

lemma dualAct_inv_eq {m : ℝ} {p : Fin 4 → ℝ} (hp : p ∈ shellSet m) (A : SL2C) :
    dualAct A⁻¹ p = shellCoords (shellAct A (shellPoint hp)) := by
  simp only [dualAct, inv_inv, shellCoords]
  congr 1

lemma haar_preimage_shellAct {m : ℝ} (hm : 0 < m) (Q : MassShell m) {T : Set (MassShell m)}
    (hT : MeasurableSet T) : SL2C.haar ((fun A : SL2C => shellAct A Q) ⁻¹' T) = shellMeasure hm T := by
  have e : (fun A : SL2C => shellAct A Q) ⁻¹' T = (fun A => A * stdLift hm Q) ⁻¹' (orbitMap hm ⁻¹' T) := by
    ext A
    show shellAct A Q ∈ T ↔ orbitMap hm (A * stdLift hm Q) ∈ T
    rw [orbitMap_mul, orbitMap_stdLift]
  rw [e, measure_preimage_mul_right, shellMeasure, Measure.map_apply (continuous_orbitMap hm).measurable hT]

variable {V : Transl → SL2C → (H ≃ₗᵢ[ℂ] H)} (hV : IsPoincareRep V)
include hV

lemma assoc_toReal_eq_norm_sq (P : ProjectionValuedMeasure (Fin 4 → ℝ) H) {T : Set (Fin 4 → ℝ)}
    (hT : MeasurableSet T) (ψ : H) : ((P.assoc ψ) T).toReal = ‖P T ψ‖ ^ 2 := by
  rw [ProjectionValuedMeasure.assoc_apply _ _ hT]
  have hP := P.isStarProjection_apply T
  have h1 : ⟪ψ, P T ψ⟫_ℂ = ⟪P T ψ, P T ψ⟫_ℂ := by
    have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hP.isSelfAdjoint) ψ (P T ψ)
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [← ContinuousLinearMap.mul_apply, hP.isIdempotentElem.eq] at hs
    exact hs.symm
  rw [h1, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `‖P(S) V(0, A) ψ‖ = ‖P(A⁻¹ · S) ψ‖`. -/
lemma norm_momPVM_V {S : Set (Fin 4 → ℝ)} (hS : MeasurableSet S) (A : SL2C) (ψ : H) :
    ‖momPVMRep hV S (V 0 A ψ)‖ = ‖momPVMRep hV (dualAct A⁻¹ ⁻¹' S) ψ‖ := by
  have hcov := covariant_jointSpectralMeasure (translRep_eq_integral hV) (V 0 A⁻¹)
    (fun x => tcoords (translAct A⁻¹ (hermOf x))) (dualAct A⁻¹) (continuous_dualAct A⁻¹).measurable
    (sum_mul_dualAct A⁻¹) (covariance_translRep hV A⁻¹) hS (V 0 A ψ)
  have hinv : V 0 A⁻¹ (V 0 A ψ) = ψ := by
    rw [hV.map_mul, translAct_zero', add_zero, inv_mul_cancel, hV.map_one]
  rw [hinv] at hcov
  rw [← hcov, LinearIsometryEquiv.norm_map]

/-- **Absolute continuity**: a set of momenta that is null for the image of the Haar measure on the shell has
projection `0`. -/
theorem momPVM_eq_zero_of_null {m : ℝ} (hm : 0 < m) (hshell : momPVMRep hV (shellSet m) = 1)
    {S : Set (Fin 4 → ℝ)} (hS : MeasurableSet S) (h0 : shellMeasure hm (shellCoords ⁻¹' S) = 0) :
    momPVMRep hV S = 0 := by
  set P := momPVMRep hV
  have hshellm : MeasurableSet (shellSet m) := by
    have e : shellSet m = (momSet fun M => M.PosSemidef) ∩
        {p | ((hermOf (flipJ p) : Matrix (Fin 2) (Fin 2) ℂ)).det = ((m ^ 2 : ℝ) : ℂ)} := by
      ext p
      simp only [shellSet, momSet, MassShellH, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨hpd, hd⟩; exact ⟨hpd.posSemidef, hd⟩
      · rintro ⟨hpsd, hd⟩
        refine ⟨hpsd.posDef_iff_det_ne_zero.2 ?_, hd⟩
        rw [hd]
        exact_mod_cast (pow_pos hm 2).ne'
    rw [e]
    exact isClosed_momSet_psd.measurableSet.inter
      (isClosed_eq continuous_momMat.matrix_det continuous_const).measurableSet
  ext ψ
  rw [ContinuousLinearMap.zero_apply]
  -- `P` of the complement of the shell vanishes
  have hempty : P (∅ : Set (Fin 4 → ℝ)) = 0 := by
    ext v
    have hsum : Summable (fun _ : ℕ => P (∅ : Set (Fin 4 → ℝ)) v) :=
      (P.hasSum_apply (fun _ : ℕ => (∅ : Set (Fin 4 → ℝ))) (fun _ => MeasurableSet.empty)
        (by intro _ _ _; simp) v).summable
    exact (summable_const_iff (a := P (∅ : Set (Fin 4 → ℝ)) v)).mp hsum
  have hPc : P (shellSet m)ᶜ = 0 := by
    have h := P.apply_inter hshellm hshellm.compl
    rw [Set.inter_compl_self, hempty, hshell, one_mul] at h
    exact h.symm
  have hcompl : P.assoc ψ (shellSet m)ᶜ = 0 := by
    have h1 := assoc_toReal_eq_norm_sq hV P hshellm.compl ψ
    rw [hPc, ContinuousLinearMap.zero_apply, norm_zero] at h1
    exact (ENNReal.toReal_eq_zero_iff _).1 (by rw [h1]; norm_num) |>.resolve_right (measure_ne_top _ _)
  -- Tonelli
  have hcont2 : Continuous fun z : SL2C × (Fin 4 → ℝ) => dualAct z.1⁻¹ z.2 := by
    have ht : Continuous fun a : Transl => tcoords a := by
      refine continuous_pi fun i => ?_
      have hval : Continuous fun a : Transl => (a.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
      have h0 : Continuous fun a : Transl => coord0 a.1 :=
        Complex.continuous_re.comp (((hval.matrix_elem 0 0).add (hval.matrix_elem 1 1)).div_const 2)
      have hV' : ∀ k, Continuous fun a : Transl => coordV a.1 k := fun k =>
        (continuous_apply k).comp (continuous_coordV.comp hval)
      fin_cases i
      · exact h0
      · exact hV' 0
      · exact hV' 1
      · exact hV' 2
    have h := continuous_flipJ.comp (ht.comp (continuous_translAct.comp (continuous_fst.prodMk
      (continuous_hermOf.comp (continuous_flipJ.comp continuous_snd)))))
    refine h.congr fun z => ?_
    simp [dualAct]
  have hF : Measurable fun z : SL2C × (Fin 4 → ℝ) => S.indicator (fun _ => (1 : ENNReal)) (dualAct z.1⁻¹ z.2) :=
    (measurable_const.indicator hS).comp hcont2.measurable
  have e1 : ∀ A : SL2C, P.assoc ψ (dualAct A⁻¹ ⁻¹' S) =
      ∫⁻ p, S.indicator (fun _ => (1 : ENNReal)) (dualAct A⁻¹ p) ∂(P.assoc ψ) := by
    intro A
    have hm' : MeasurableSet (dualAct A⁻¹ ⁻¹' S) := (continuous_dualAct A⁻¹).measurable hS
    rw [← lintegral_indicator_one hm']
    refine lintegral_congr fun p => ?_
    by_cases hp : dualAct A⁻¹ p ∈ S
    · rw [Set.indicator_of_mem (show p ∈ dualAct A⁻¹ ⁻¹' S from hp), Set.indicator_of_mem hp]; rfl
    · rw [Set.indicator_of_notMem (show p ∉ dualAct A⁻¹ ⁻¹' S from hp), Set.indicator_of_notMem hp]
  have hint : ∫⁻ A, P.assoc ψ (dualAct A⁻¹ ⁻¹' S) ∂SL2C.haar = 0 := by
    simp_rw [e1]
    rw [lintegral_lintegral_swap (f := fun (A : SL2C) (p : Fin 4 → ℝ) =>
      S.indicator (fun _ => (1 : ENNReal)) (dualAct A⁻¹ p)) hF.aemeasurable]
    have hae : ∀ᵐ p ∂(P.assoc ψ), p ∈ shellSet m := by
      rw [ae_iff]
      exact hcompl
    refine (lintegral_eq_zero_iff' (hF.lintegral_prod_left'.aemeasurable)).2 ?_
    filter_upwards [hae] with p hp
    have e2 : (fun A : SL2C => S.indicator (fun _ => (1 : ENNReal)) (dualAct A⁻¹ p)) =
        ((fun A : SL2C => shellAct A (shellPoint hp)) ⁻¹' (shellCoords ⁻¹' S)).indicator (fun _ => 1) := by
      funext A
      rw [dualAct_inv_eq hp A]
      by_cases h : shellCoords (shellAct A (shellPoint hp)) ∈ S
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show A ∈ _ from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show A ∉ _ from h)]
    have hc : Continuous fun A : SL2C => shellAct A (shellPoint hp) := by
      refine Continuous.subtype_mk ?_ _
      unfold actP
      have h1 : Continuous fun A : SL2C => ((A : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
      exact (h1.matrix_mul continuous_const).matrix_mul h1.matrix_conjTranspose
    have hmeas : MeasurableSet ((fun A : SL2C => shellAct A (shellPoint hp)) ⁻¹' (shellCoords ⁻¹' S)) :=
      (continuous_shellCoords.comp hc).measurable hS
    rw [Pi.zero_apply, e2, lintegral_indicator_const hmeas, one_mul,
      haar_preimage_shellAct hm _ (continuous_shellCoords.measurable hS), h0]
  -- almost every `A`, then every `A`
  have hae : ∀ᵐ A ∂SL2C.haar, P S (V 0 A ψ) = 0 := by
    have hmeasA : AEMeasurable (fun A : SL2C => P.assoc ψ (dualAct A⁻¹ ⁻¹' S)) SL2C.haar := by
      have h := hF.lintegral_prod_right' (ν := P.assoc ψ)
      exact h.aemeasurable.congr (Filter.Eventually.of_forall fun A => (e1 A).symm)
    have h := (lintegral_eq_zero_iff' hmeasA).1 hint
    filter_upwards [h] with A hA
    have h1 := assoc_toReal_eq_norm_sq hV P ((continuous_dualAct A⁻¹).measurable hS) ψ
    rw [show (P.assoc ψ) (dualAct A⁻¹ ⁻¹' S) = 0 from hA, ENNReal.toReal_zero] at h1
    have h2 : ‖P S (V 0 A ψ)‖ = 0 := by
      rw [norm_momPVM_V hV hS A ψ]
      nlinarith [norm_nonneg (P (dualAct A⁻¹ ⁻¹' S) ψ)]
    exact norm_eq_zero.1 h2
  have hZ : IsOpen {A : SL2C | ¬ P S (V 0 A ψ) = 0} := by
    have hc : Continuous fun A : SL2C => P S (V 0 A ψ) :=
      (P S).continuous.comp ((hV.continuous ψ).comp (continuous_const.prodMk continuous_id))
    exact (isClosed_eq hc continuous_const).isOpen_compl
  have hnull : SL2C.haar {A : SL2C | ¬ P S (V 0 A ψ) = 0} = 0 := ae_iff.1 hae
  have hempty' := (hZ.measure_eq_zero_iff SL2C.haar).1 hnull
  have h1 : (1 : SL2C) ∉ {A : SL2C | ¬ P S (V 0 A ψ) = 0} := by rw [hempty']; exact Set.notMem_empty _
  simp only [Set.mem_setOf_eq, not_not] at h1
  rwa [hV.map_one] at h1

end

end Lightlike.Poincare
