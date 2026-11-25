import Lightlike.Poincare.OrbitMeasureClass

/-!
# The momentum measure on a mass shell is equivalent to the invariant measure

`momPVM_eq_zero_of_null` (`OrbitMeasureClass.lean`) says that a set of momenta that is null for the invariant
measure on the shell has projection `0`. The converse (`shellMeasure_eq_zero_of_momPVM_eq_zero`): if the projection
of a set `S` of momenta is `0`, the set is null for the invariant measure. Proof: for `ψ ≠ 0`, Tonelli gives
`∫ ‖P(A⁻¹ S) ψ‖² dA = ‖ψ‖² · ν(S)` (the right-hand side is the Haar measure of `{A | A⁻¹ p ∈ S}` for `p` on the
shell, which is `ν(S)`), while the covariance `‖P(A⁻¹ S) ψ‖ = ‖P(S) V(0, A) ψ‖` makes the left-hand side `0`.

So the projection-valued measure of a nonzero representation carried by the shell has exactly the null sets of the
invariant measure `ν` of the shell: this is step 2 of the converse of the Wigner classification
(`docs/notes/g1-055-converse-scope.md`).

Supporting results; no catalogue entry.
-/

open scoped InnerProductSpace ComplexOrder
open Filter Topology MeasureTheory Matrix Lightlike.Lorentz Lightlike.OperatorAlgebras.Spectral
  Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Poincare

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Transl → SL2C → (H ≃ₗᵢ[ℂ] H)} (hV : IsPoincareRep V)
include hV

/-- **The converse of absolute continuity**: a set of momenta with projection `0` is null for the invariant
measure of the shell. -/
theorem shellMeasure_eq_zero_of_momPVM_eq_zero {m : ℝ} (hm : 0 < m) (hshell : momPVMRep hV (shellSet m) = 1)
    [Nontrivial H] {S : Set (Fin 4 → ℝ)} (hS : MeasurableSet S) (h0 : momPVMRep hV S = 0) :
    shellMeasure hm (shellCoords ⁻¹' S) = 0 := by
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
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : H)
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
  -- the integral over `A`
  have hzero : ∫⁻ A, P.assoc ψ (dualAct A⁻¹ ⁻¹' S) ∂SL2C.haar = 0 := by
    refine (lintegral_eq_zero_iff' ?_).2 (Filter.Eventually.of_forall fun A => ?_)
    · have h := hF.lintegral_prod_right' (ν := P.assoc ψ)
      exact h.aemeasurable.congr (Filter.Eventually.of_forall fun A => (e1 A).symm)
    · have h1 := assoc_toReal_eq_norm_sq hV P ((continuous_dualAct A⁻¹).measurable hS) ψ
      have h2 : ‖P (dualAct A⁻¹ ⁻¹' S) ψ‖ = 0 := by
        rw [← norm_momPVM_V hV hS A ψ, h0]
        simp
      rw [h2] at h1
      have := (ENNReal.toReal_eq_zero_iff _).1 (by rw [h1]; norm_num)
      exact this.resolve_right (measure_ne_top _ _)
  simp_rw [e1] at hzero
  rw [lintegral_lintegral_swap (f := fun (A : SL2C) (p : Fin 4 → ℝ) =>
      S.indicator (fun _ => (1 : ENNReal)) (dualAct A⁻¹ p)) hF.aemeasurable] at hzero
  have hae : ∀ᵐ p ∂(P.assoc ψ), p ∈ shellSet m := by
    rw [ae_iff]
    exact hcompl
  have hconst : ∀ᵐ p ∂(P.assoc ψ), ∫⁻ A, S.indicator (fun _ => (1 : ENNReal)) (dualAct A⁻¹ p) ∂SL2C.haar =
      shellMeasure hm (shellCoords ⁻¹' S) := by
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
    rw [e2, lintegral_indicator_const hmeas, one_mul,
      haar_preimage_shellAct hm _ (continuous_shellCoords.measurable hS)]
  rw [lintegral_congr_ae hconst, lintegral_const, mul_eq_zero] at hzero
  rcases hzero with h | h
  · exact h
  · exfalso
    have huniv := assoc_toReal_eq_norm_sq hV P MeasurableSet.univ ψ
    rw [P.apply_univ, h] at huniv
    simp at huniv
    exact hψ (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 huniv.symm))

/-- **The null sets of the momentum measure on a mass shell are those of the invariant measure**: a measurable set
`S` of momenta has projection `0` if and only if `S` is null for the invariant measure `ν` of the shell. -/
theorem momPVM_eq_zero_iff {m : ℝ} (hm : 0 < m) (hshell : momPVMRep hV (shellSet m) = 1) [Nontrivial H]
    {S : Set (Fin 4 → ℝ)} (hS : MeasurableSet S) :
    momPVMRep hV S = 0 ↔ shellMeasure hm (shellCoords ⁻¹' S) = 0 :=
  ⟨shellMeasure_eq_zero_of_momPVM_eq_zero hV hm hshell hS, momPVM_eq_zero_of_null hV hm hshell hS⟩

end

end Lightlike.Poincare
