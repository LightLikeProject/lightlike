import Lightlike.Poincare.ConeL2
import Lightlike.Poincare.IrreducibleMassive

/-!
# Null sets of invariant measures on the light cone

Every `SL(2,ℂ)`-invariant s-finite measure `ν` on the forward light cone has the null sets of the image `coneHaar` of
the Haar measure under the orbit map `A ↦ A • K`, `K = diag(2, 0)`: `ν(S) · haar(SL(2,ℂ)) = coneHaar(S) · ν(cone)`
(`measure_mul_haar_univ_cone`, Tonelli, with the standard lift as a section). The set `{A : A₀₀ = 0}` is Haar-null
(`haar_entry00_eq_zero`: its right translates by the rotations `u_θ`, `0 ≤ θ < π`, are pairwise disjoint and have
the same measure), so the half-line `P₀₀ = 0` of the cone, where the standard lift is discontinuous, is `ν`-null for
every such `ν` (`measure_alphaC_eq_zero`).

Supporting results for the massless one-particle representations; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology

namespace Lightlike.Poincare

noncomputable section

local instance (k : ℕ) : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin k → Fin k → ℂ))

local instance (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))

/-! ## The Tonelli comparison -/

lemma continuous_smul_cone : Continuous fun z : SL2C × LightCone => z.1 • z.2 := by
  apply continuous_induced_rng.2
  change Continuous fun z : SL2C × LightCone => actP z.1 z.2.1
  unfold actP
  have h1 : Continuous fun z : SL2C × LightCone => ((z.1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun z : SL2C × LightCone => (z.2.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_snd
  exact (h1.matrix_mul h2).matrix_mul h1.matrix_conjTranspose

lemma continuous_smul_cone_left (P : LightCone) : Continuous fun A : SL2C => A • P := by
  apply continuous_induced_rng.2
  change Continuous fun A : SL2C => actP A P.1
  unfold actP
  have h1 : Continuous fun A : SL2C => ((A : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  exact (h1.matrix_mul continuous_const).matrix_mul h1.matrix_conjTranspose

lemma continuous_smul_cone_right (A : SL2C) : Continuous fun P : LightCone => A • P := by
  apply continuous_induced_rng.2
  change Continuous fun P : LightCone => actP A P.1
  unfold actP
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const

/-- The orbit map `A ↦ A • K`. -/
def coneOrbit (A : SL2C) : LightCone := A • coneBase

lemma continuous_coneOrbit : Continuous coneOrbit := continuous_smul_cone_left coneBase

/-- The image of the Haar measure under the orbit map. -/
def coneHaar : Measure LightCone := Measure.map coneOrbit SL2C.haar

lemma indicator_one_comp_cone {α : Type*} (f : α → LightCone) (S : Set LightCone) :
    (fun x => S.indicator (fun _ => (1 : ENNReal)) (f x)) = (f ⁻¹' S).indicator (fun _ => 1) := by
  funext x
  by_cases h : f x ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ f ⁻¹' S from h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ f ⁻¹' S from h)]

/-- **`ν(S) · haar(G) = coneHaar(S) · ν(cone)`** for every invariant s-finite measure `ν` on the cone. -/
lemma measure_mul_haar_univ_cone {ν : Measure LightCone} [SFinite ν]
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) {S : Set LightCone}
    (hS : MeasurableSet S) : ν S * SL2C.haar Set.univ = coneHaar S * ν Set.univ := by
  have hF : Measurable fun z : SL2C × LightCone => S.indicator (fun _ => (1 : ENNReal)) (z.1 • z.2) :=
    (measurable_const.indicator hS).comp continuous_smul_cone.measurable
  have h1 : ∫⁻ A, ∫⁻ P, S.indicator (fun _ => (1 : ENNReal)) (A • P) ∂ν ∂SL2C.haar =
      ν S * SL2C.haar Set.univ := by
    have : ∀ A : SL2C, ∫⁻ P, S.indicator (fun _ => (1 : ENNReal)) (A • P) ∂ν = ν S := by
      intro A
      rw [indicator_one_comp_cone (fun P : LightCone => A • P),
        lintegral_indicator_const ((continuous_smul_cone_right A).measurable hS), one_mul,
        (hν A).measure_preimage hS.nullMeasurableSet]
    simp_rw [this, lintegral_const]
  have h2 : ∫⁻ P, ∫⁻ A, S.indicator (fun _ => (1 : ENNReal)) (A • P) ∂SL2C.haar ∂ν =
      coneHaar S * ν Set.univ := by
    have : ∀ P : LightCone, ∫⁻ A, S.indicator (fun _ => (1 : ENNReal)) (A • P) ∂SL2C.haar = coneHaar S := by
      intro P
      have e : (fun A : SL2C => A • P) ⁻¹' S = (fun A => A * coneLift P) ⁻¹' (coneOrbit ⁻¹' S) := by
        ext A
        show A • P ∈ S ↔ coneOrbit (A * coneLift P) ∈ S
        rw [coneOrbit, mul_smul, coneLift_smul]
      rw [indicator_one_comp_cone (fun A : SL2C => A • P),
        lintegral_indicator_const ((continuous_smul_cone_left P).measurable hS), one_mul, e,
        measure_preimage_mul_right, coneHaar, Measure.map_apply continuous_coneOrbit.measurable hS]
    simp_rw [this, lintegral_const]
  rw [← h1, ← h2]
  exact lintegral_lintegral_swap (f := fun (A : SL2C) (P : LightCone) =>
    S.indicator (fun _ => (1 : ENNReal)) (A • P)) hF.aemeasurable

lemma absolutelyContinuous_coneHaar {ν : Measure LightCone} [SFinite ν]
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) : ν ≪ coneHaar := by
  refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
  have h := measure_mul_haar_univ_cone hν hS
  rw [h0, zero_mul, SL2C.haar_univ] at h
  exact (mul_eq_zero.1 h).resolve_right ENNReal.top_ne_zero

lemma coneHaar_absolutelyContinuous {ν : Measure LightCone} [SFinite ν]
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (hν0 : ν ≠ 0) : coneHaar ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
  have h := measure_mul_haar_univ_cone hν hS
  rw [h0, zero_mul] at h
  exact (mul_eq_zero.1 h.symm).resolve_right (Measure.measure_univ_ne_zero.2 hν0)

/-! ## The half-line `P₀₀ = 0` is null -/

/-- The rotation `[[cos θ, −sin θ], [sin θ, cos θ]]`. -/
def rotSL (θ : ℝ) : SL2C :=
  ⟨!![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)], by
    rw [Matrix.det_fin_two_of]
    have h := Real.cos_sq_add_sin_sq θ
    have : ((Real.cos θ : ℂ)) ^ 2 + ((Real.sin θ : ℂ)) ^ 2 = 1 := by exact_mod_cast h
    linear_combination this⟩

/-- **The set `{A : A₀₀ = 0}` is Haar-null.** -/
theorem haar_entry00_eq_zero : SL2C.haar {A : SL2C | (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0} = 0 := by
  set Z := {A : SL2C | (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0}
  have hc : Continuous fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    (continuous_subtype_val : Continuous fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem 0 0
  have hZm : MeasurableSet Z := (isClosed_eq hc continuous_const).measurableSet
  set E : Set.Ico (0 : ℝ) Real.pi → Set SL2C := fun θ => (fun A => A * rotSL θ.1) ⁻¹' Z
  have hEm : ∀ θ, MeasurableSet (E θ) := fun θ => (measurable_mul_const _) hZm
  have hEmeas : ∀ θ, SL2C.haar (E θ) = SL2C.haar Z := fun θ => measure_preimage_mul_right _ _ _
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro θ θ' hne
    refine Set.disjoint_left.2 fun A h1 h2 => ?_
    simp only [E, Z, Set.mem_preimage, Set.mem_setOf_eq] at h1 h2
    change ((A : Matrix (Fin 2) (Fin 2) ℂ) * (rotSL θ.1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 0 at h1
    change ((A : Matrix (Fin 2) (Fin 2) ℂ) * (rotSL θ'.1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 0 at h2
    simp only [rotSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const] at h1 h2
    -- the two rows `(cos θ, sin θ)` and `(cos θ', sin θ')` are independent
    have hsin : Real.sin (θ'.1 - θ.1) ≠ 0 ∨ Real.sin (θ.1 - θ'.1) ≠ 0 := by
      rcases lt_or_gt_of_ne (fun h => hne (Subtype.ext h)) with h | h
      · left; exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [θ'.2.2, θ.2.1])).ne'
      · right; exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [θ.2.2, θ'.2.1])).ne'
    have hs : Real.sin (θ'.1 - θ.1) ≠ 0 := by
      rcases hsin with h | h
      · exact h
      · rw [show θ.1 - θ'.1 = -(θ'.1 - θ.1) by ring, Real.sin_neg, neg_ne_zero] at h; exact h
    have hsC : ((Real.sin (θ'.1 - θ.1) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
    have hsub : ((Real.sin (θ'.1 - θ.1) : ℝ) : ℂ) = (Real.sin θ'.1 : ℂ) * Real.cos θ.1 -
        (Real.cos θ'.1 : ℂ) * Real.sin θ.1 := by
      rw [Real.sin_sub]; push_cast; ring
    have ha : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * ((Real.sin (θ'.1 - θ.1) : ℝ) : ℂ) = 0 := by
        rw [hsub]; linear_combination (Real.sin θ'.1 : ℂ) * h1 - (Real.sin θ.1 : ℂ) * h2
      exact (mul_eq_zero.1 this).resolve_right hsC
    have hb : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      have : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * ((Real.sin (θ'.1 - θ.1) : ℝ) : ℂ) = 0 := by
        rw [hsub]; linear_combination (Real.cos θ.1 : ℂ) * h2 - (Real.cos θ'.1 : ℂ) * h1
      exact (mul_eq_zero.1 this).resolve_right hsC
    have hdet := A.2
    rw [Matrix.det_fin_two, ha, hb] at hdet
    simp at hdet
  by_contra hZ
  have hpos : 0 < SL2C.haar Z := pos_iff_ne_zero.2 hZ
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion (μ := SL2C.haar) hEm hdisj
  have huniv : {θ : Set.Ico (0 : ℝ) Real.pi | 0 < SL2C.haar (E θ)} = Set.univ := by
    ext θ; simp [hEmeas θ, hpos]
  rw [huniv] at hc
  have hcount : (Set.Ico (0 : ℝ) Real.pi).Countable := by
    have := hc.image (fun θ : Set.Ico (0 : ℝ) Real.pi => θ.1)
    rwa [Set.image_univ, Subtype.range_coe] at this
  have h0 := hcount.measure_zero (volume : Measure ℝ)
  rw [Real.volume_Ico, ENNReal.ofReal_eq_zero] at h0
  linarith [Real.pi_pos]

lemma alphaC_coneOrbit (A : SL2C) :
    alphaC (coneOrbit A).1 = 2 * Complex.normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  change (((A : Matrix (Fin 2) (Fin 2) ℂ) * masslessH * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) 0 0).re = _
  rw [masslessH_eq_diagonal]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply, Complex.mul_re]
  ring

lemma coneHaar_alphaC_eq_zero : coneHaar {P : LightCone | alphaC P.1 = 0} = 0 := by
  have hm : MeasurableSet {P : LightCone | alphaC P.1 = 0} :=
    measurable_alphaC (measurableSet_singleton 0)
  rw [coneHaar, Measure.map_apply continuous_coneOrbit.measurable hm]
  have e : coneOrbit ⁻¹' {P : LightCone | alphaC P.1 = 0} =
      {A : SL2C | (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0} := by
    ext A
    simp only [Set.mem_preimage, Set.mem_setOf_eq, alphaC_coneOrbit]
    constructor
    · intro h
      have : Complex.normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) = 0 := by linarith
      exact Complex.normSq_eq_zero.1 this
    · intro h; rw [h]; simp
  rw [e]
  exact haar_entry00_eq_zero

/-- **The half-line `P₀₀ = 0` is null for every invariant s-finite measure on the cone.** -/
theorem measure_alphaC_eq_zero {ν : Measure LightCone} [SFinite ν]
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) :
    ν {P : LightCone | alphaC P.1 = 0} = 0 :=
  absolutelyContinuous_coneHaar hν coneHaar_alphaC_eq_zero

end

end Lightlike.Poincare
