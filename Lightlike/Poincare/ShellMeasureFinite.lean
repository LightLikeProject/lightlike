module

public import Lightlike.Poincare.InducedUnitary
public import Lightlike.Poincare.LittleGroupsH

/-!
# The mass-shell measure is finite on compact sets and nonzero

The invariant measure `shellMeasure` on the mass shell (the image of the Haar measure of `SL(2,ℂ)` under the orbit map
`g ↦ g • (m · 1)`) is finite on compact sets (`isFiniteMeasureOnCompacts_shellMeasure`): the orbit map is proper,
since `g = L(g • q) · (L(g • q)⁻¹ g)` with the continuous standard lift `L` and `L(g • q)⁻¹ g` in the compact little
group `SU(2)`. It is nonzero (`shellMeasure_ne_zero`). So the unitarity of the induced action
(`lintegral_normSq_inducedAct`) is a statement about a genuine, locally finite invariant measure.

Supporting lemmas; no catalogue entry.
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory Lightlike.Lorentz Topology
open scoped ComplexOrder

namespace Lightlike.Poincare

lemma continuous_trN {m : ℝ} : Continuous fun P : MassShell m => trN m P.1 := by
  unfold trN normP
  have h : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have h2 : Continuous fun P : MassShell m => ((1 / m : ℝ) : ℂ) • (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    fun_prop
  exact Complex.continuous_re.comp h2.matrix_trace

lemma continuous_stdLift {m : ℝ} (hm : 0 < m) : Continuous (stdLift hm) := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun P : MassShell m => stdLiftMat m P.1
  unfold stdLiftMat
  have h : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  have hs : Continuous fun P : MassShell m => (((1 / Real.sqrt (trN m P.1 + 2)) : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Continuous.div continuous_const
      (Real.continuous_sqrt.comp (continuous_trN.add continuous_const)) fun P => ?_)
    have := (trace_normP hm P.2).2
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  have h2 : Continuous fun P : MassShell m => normP m P.1 + 1 := by
    unfold normP
    fun_prop
  exact hs.smul h2

/-- The little group of the rest momentum in `SL(2,ℂ)`. -/
def restStab (m : ℝ) : Set SL2C := {g | actP g ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (m : ℂ) • 1}

lemma isCompact_restStab {m : ℝ} (hm : 0 < m) : IsCompact (restStab m) := by
  have hclosed : IsClosed (restStab m) := isClosed_eq (continuous_actP _) continuous_const
  have hK : IsCompact {g : SL2C | ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1} := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : SL2C → Matrix (Fin 2) (Fin 2) ℂ) :=
      (isClosed_eq (continuous_id.matrix_det) continuous_const).isClosedEmbedding_subtypeVal
    have hB : IsCompact (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
        Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    have hset : {g : SL2C | ∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ≤ 1} =
        Subtype.val ⁻¹' (Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
          Metric.closedBall (0 : ℂ) 1 : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
      ext g
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [hset]
    exact hemb.isCompact_preimage hB
  refine hK.of_isClosed_subset hclosed fun g hg i j => ?_
  have hu := (actP_rest_eq_iff hm.ne' g).1 hg
  have hrow := congrFun (congrFun hu i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Fin.sum_univ_two] at hrow
  have hn : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn, hn] at hrow
  have hrow' : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i 1‖ ^ 2 = 1 := by
    exact_mod_cast hrow
  have hj : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 ≤ 1 := by
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
      nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i 0‖, sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) ℂ) i 1‖]
  nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) i j)]

/-- The orbit map is proper: preimages of compact sets are compact. -/
lemma isCompact_preimage_orbitMap {m : ℝ} (hm : 0 < m) {C : Set (MassShell m)} (hC : IsCompact C) :
    IsCompact (orbitMap hm ⁻¹' C) := by
  have himg : IsCompact ((fun x : MassShell m × SL2C => stdLift hm x.1 * x.2) '' (C ×ˢ restStab m)) :=
    (hC.prod (isCompact_restStab hm)).image
      (((continuous_stdLift hm).comp continuous_fst).mul continuous_snd)
  refine himg.of_isClosed_subset ((isClosed_of_closure_subset ?_).preimage (continuous_orbitMap hm)) ?_
  · exact hC.isClosed.closure_subset
  · intro g hg
    refine ⟨(orbitMap hm g, (stdLift hm (orbitMap hm g))⁻¹ * g), ⟨hg, ?_⟩, by simp⟩
    show actP _ _ = _
    rw [actP_mul]
    have h1 : actP g ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (orbitMap hm g).1 := rfl
    rw [h1, ← stdLift_act_rest hm (orbitMap hm g), ← actP_mul, inv_mul_cancel, actP_one]

/-- **The mass-shell measure is finite on compact sets.** -/
instance isFiniteMeasureOnCompacts_shellMeasure {m : ℝ} (hm : 0 < m) :
    IsFiniteMeasureOnCompacts (shellMeasure hm) where
  lt_top_of_isCompact C hC := by
    rw [shellMeasure, Measure.map_apply (continuous_orbitMap hm).measurable hC.isClosed.measurableSet]
    exact (isCompact_preimage_orbitMap hm hC).measure_lt_top

/-- **The mass-shell measure is nonzero.** -/
theorem shellMeasure_ne_zero {m : ℝ} (hm : 0 < m) : shellMeasure hm ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure (MassShell m) => μ Set.univ) h
  simp only [shellMeasure, Measure.map_apply (continuous_orbitMap hm).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
  exact (isOpen_univ.measure_pos SL2C.haar Set.univ_nonempty).ne' this
