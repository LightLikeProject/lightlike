import Lightlike.CausalSets.Sprinkling

/-!
# The Myrheim–Meyer relation probability in `1 + 1` dimensions

Two independent uniform points of the causal diamond of `ℝ^{1+1}` are causally related with
probability `1/2`, so an ordered pair `x ≺ y` has probability `1/4` (`relProb_one`), and `n`
uniform points have `n (n - 1) / 4` relations in expectation (`expected_relations_diamond_one`).
This is the case of spacetime dimension `2` of the Myrheim–Meyer count
`⟨R⟩ = n (n - 1) Γ(D + 1) Γ(D / 2) / (4 Γ(3 D / 2))`, which at `D = 2` is `n (n - 1) / 4`.
**Scope.** Only the dimension `D = 2` is proved here; the formula in general dimension, and the
value `1/20` at `D = 4`, are open proof tasks (`T-CS2-P2`, `T-CS2-P3`). The comparison of the
formula with the sources is pending: they have not been read at a location.

The proof passes to light-cone coordinates `(t + x, t - x)`, in which the diamond is the unit square
and the causal order is the coordinatewise order; two independent coordinates are ordered with
probability `1/2` by the symmetry of the swap. This is part of a bridge between Lorentzian geometry
and causal sets: the relation is the causal order of Minkowski space
(`Lightlike/CausalSets/ConeOrder.lean`).

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open MeasureTheory
open Lightlike

namespace Lightlike.CausalSets


/-- The diagonal is null for a product of an atomless measure on `ℝ` with itself. -/
lemma prod_diag_null (μ : Measure ℝ) [SigmaFinite μ] [NullSingletonClass μ] :
    (μ.prod μ) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
  simp [Set.preimage]

/-- Two independent points of an atomless probability measure on `ℝ` are ordered with
probability `1/2`. -/
lemma prod_le_half (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    (μ.prod μ) {p : ℝ × ℝ | p.1 ≤ p.2} = 1 / 2 := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hS' : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  have hsw : (μ.prod μ) {p : ℝ × ℝ | p.2 ≤ p.1} = (μ.prod μ) {p : ℝ × ℝ | p.1 ≤ p.2} := by
    have hsp := Measure.prod_swap (μ := μ) (ν := μ)
    calc (μ.prod μ) {p : ℝ × ℝ | p.2 ≤ p.1} = (μ.prod μ) (Prod.swap ⁻¹' {p : ℝ × ℝ | p.1 ≤ p.2}) := rfl
      _ = (Measure.map Prod.swap (μ.prod μ)) {p : ℝ × ℝ | p.1 ≤ p.2} :=
          (Measure.map_apply measurable_swap hS).symm
      _ = _ := by rw [hsp]
  have hunion : (μ.prod μ) ({p : ℝ × ℝ | p.1 ≤ p.2} ∪ {p : ℝ × ℝ | p.2 ≤ p.1}) = 1 := by
    have : ({p : ℝ × ℝ | p.1 ≤ p.2} ∪ {p : ℝ × ℝ | p.2 ≤ p.1}) = Set.univ := by
      ext p; simp [le_total]
    rw [this]; simp
  have hinter : (μ.prod μ) ({p : ℝ × ℝ | p.1 ≤ p.2} ∩ {p : ℝ × ℝ | p.2 ≤ p.1}) = 0 := by
    have : ({p : ℝ × ℝ | p.1 ≤ p.2} ∩ {p : ℝ × ℝ | p.2 ≤ p.1}) = {p : ℝ × ℝ | p.1 = p.2} := by
      ext p; simp [le_antisymm_iff]
    rw [this]; exact prod_diag_null μ
  have := measure_union_add_inter (μ := μ.prod μ) {p : ℝ × ℝ | p.1 ≤ p.2} hS'
  rw [hunion, hinter, hsw, add_zero] at this
  have h2 : (2 : ENNReal) * (μ.prod μ) {p : ℝ × ℝ | p.1 ≤ p.2} = 1 := by rw [two_mul]; exact this.symm
  exact (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2 h2

/-- The probability that two independent points of a cube are ordered coordinatewise. -/
lemma pi_prod_le (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ] (n : ℕ) :
    ((Measure.pi fun _ : Fin n => μ).prod (Measure.pi fun _ : Fin n => μ))
      {p | ∀ i, p.1 i ≤ p.2 i} = (1 / 2) ^ n := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => μ) (fun _ => μ)
  have := hmp.measure_preimage_equiv {p : (Fin n → ℝ) × (Fin n → ℝ) | ∀ i, p.1 i ≤ p.2 i}
  rw [← this]
  have hpre : (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) ⁻¹'
      {p : (Fin n → ℝ) × (Fin n → ℝ) | ∀ i, p.1 i ≤ p.2 i} =
      Set.pi Set.univ (fun _ => {q : ℝ × ℝ | q.1 ≤ q.2}) := by
    ext z; simp [MeasurableEquiv.arrowProdEquivProdArrow]
  rw [hpre, Measure.pi_pi]
  simp [prod_le_half μ]


/-- The light-cone coordinates `(t, x) ↦ (t + x, t - x)`. -/
noncomputable def lc : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' !![1, 1; 1, -1]

lemma lc_apply (x : Fin 2 → ℝ) : lc x 0 = x 0 + x 1 ∧ lc x 1 = x 0 - x 1 := by
  simp [lc, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

lemma lc_det : LinearMap.det lc = -2 := by
  rw [lc, LinearMap.det_toLin']; simp [Matrix.det_fin_two]; norm_num

lemma spatialSq_one (v : Fin 2 → ℝ) : spatialSq v = v 1 ^ 2 := by simp [spatialSq]

lemma coneLE_one_iff (x y : Fin 2 → ℝ) :
    coneLE x y ↔ ∀ i, lc x i ≤ lc y i := by
  rw [coneLE_iff_spatial, spatialSq_one, Fin.forall_fin_two]
  obtain ⟨a0, a1⟩ := lc_apply x
  obtain ⟨b0, b1⟩ := lc_apply y
  rw [a0, a1, b0, b1]
  simp only [Pi.sub_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have := abs_le_of_sq_le_sq' h2 h1
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by nlinarith⟩

/-- The unit square in light-cone coordinates. -/
def lcSquare : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

lemma diamond_one_eq : diamond 1 = lc ⁻¹' lcSquare := by
  ext x
  have h1 := coneLE_one_iff 0 x
  have h2 := coneLE_one_iff x (diamondTop 1)
  obtain ⟨a0, a1⟩ := lc_apply x
  obtain ⟨b0, b1⟩ := lc_apply (diamondTop 1)
  obtain ⟨c0, c1⟩ := lc_apply (0 : Fin 2 → ℝ)
  simp only [diamond, Set.mem_ofPred_eq, h1, h2, Fin.forall_fin_two, a0, a1, b0, b1, c0, c1,
    Set.mem_preimage, lcSquare, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  simp [diamondTop]
  constructor <;> intro h <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [h.1, h.2]

lemma volume_sq : volume lcSquare = 1 := by
  rw [lcSquare, volume_pi_pi]; simp

lemma map_lc : Measure.map lc (volume : Measure (Fin 2 → ℝ)) = ENNReal.ofReal (1 / 2) • volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (by rw [lc_det]; norm_num), lc_det]
  norm_num

lemma lc_measurable : Measurable (lc : (Fin 2 → ℝ) → (Fin 2 → ℝ)) := lc.continuous_of_finiteDimensional.measurable

lemma measurableSet_lcSquare : MeasurableSet lcSquare :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

lemma volume_diamond_one : volume (diamond 1) = ENNReal.ofReal (1 / 2) := by
  rw [diamond_one_eq, ← Measure.map_apply lc_measurable measurableSet_lcSquare, map_lc]
  simp [volume_sq]

lemma map_diamondMeasure_one :
    (diamondMeasure 1).map lc = Measure.pi (fun _ : Fin 2 => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hc : ENNReal.ofReal (1 / 2) ≠ 0 := by simp
  have hc' : ENNReal.ofReal (1 / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold diamondMeasure regionMeasure ProbabilityTheory.cond
  rw [volume_diamond_one, Measure.map_smul, diamond_one_eq,
    ← Measure.restrict_map lc_measurable measurableSet_lcSquare, map_lc, Measure.restrict_smul,
    smul_smul, ENNReal.inv_mul_cancel hc hc', one_smul]
  · exact Measure.restrict_pi_pi (fun _ : Fin 2 => (volume : Measure ℝ)) (fun _ => Set.Icc (0 : ℝ) 1)
  · exact lc_measurable.aemeasurable

/-- The uniform probability measure on the unit interval. -/
noncomputable abbrev unitMeasure : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := ⟨by simp⟩

/-- The uniform probability measure on the unit square in light-cone coordinates. -/
noncomputable abbrev lcMeasure : Measure (Fin 2 → ℝ) := Measure.pi (fun _ : Fin 2 => unitMeasure)

lemma lcMeasure_diag :
    (lcMeasure.prod lcMeasure) {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2} = 0 := by
  have hm : MeasurableSet {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2} :=
    isClosed_diagonal.measurableSet
  rw [Measure.prod_apply hm]
  have : ∀ a : Fin 2 → ℝ, lcMeasure (Prod.mk a ⁻¹' {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2}) = 0 := by
    intro a
    have : Prod.mk a ⁻¹' {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 = q.2} = {a} := by
      ext b; simp [eq_comm]
    rw [this]
    simp [lcMeasure]
  simp

lemma lc_injective : Function.Injective (lc : (Fin 2 → ℝ) → (Fin 2 → ℝ)) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  obtain ⟨a0, a1⟩ := lc_apply x
  obtain ⟨b0, b1⟩ := lc_apply y
  rw [a0, b0] at h0
  rw [a1, b1] at h1
  ext i; fin_cases i <;> simp <;> linarith

/-- **The Myrheim–Meyer probability in `1 + 1` dimensions**: two uniform points of the causal
diamond are related with probability `1/4`. -/
theorem relProb_one : relProb 1 = 1 / 4 := by
  set T : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {q | (∀ i, q.1 i ≤ q.2 i) ∧ q.1 ≠ q.2} with hT
  have hset : {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLT p.1 p.2} = (Prod.map lc lc) ⁻¹' T := by
    ext p
    simp only [coneLT, Set.mem_ofPred_eq, hT, Set.mem_preimage, Prod.map_fst, Prod.map_snd,
      coneLE_one_iff, ne_eq, lc_injective.eq_iff]
  have hTm : MeasurableSet T := by
    have h1 : MeasurableSet {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | ∀ i, q.1 i ≤ q.2 i} := by
      have : {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | ∀ i, q.1 i ≤ q.2 i} =
          ⋂ i, {q | q.1 i ≤ q.2 i} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le ((measurable_pi_apply i).comp measurable_fst)
          ((measurable_pi_apply i).comp measurable_snd)
    exact h1.inter isClosed_diagonal.measurableSet.compl
  rw [relProb_eq]
  rw [hset, ← Measure.map_apply (lc_measurable.prodMap lc_measurable) hTm,
    ← Measure.map_prod_map _ _ lc_measurable lc_measurable, map_diamondMeasure_one]
  have hTeq : T = {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | ∀ i, q.1 i ≤ q.2 i} \
      {q | q.1 = q.2} := by ext; simp [hT]
  rw [hTeq, measure_sdiff_null lcMeasure_diag]
  have := pi_prod_le unitMeasure 2
  simp only [lcMeasure] at *
  rw [this]
  simp [ENNReal.toReal_pow]
  norm_num

/-- **Expected number of relations in `1 + 1` dimensions**: `n` uniform points of the causal
diamond have `n (n - 1) / 4` pairs `x ≺ y` in expectation (the case `D = 2` of the Myrheim–Meyer
count). -/
theorem expected_relations_diamond_one (n : ℕ) :
    ∫ ω, (relCount {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLT p.1 p.2} ω : ℝ)
        ∂Measure.pi (fun _ : Fin n => diamondMeasure 1) = (n : ℝ) * (n - 1) / 4 := by
  rw [expected_relations_diamond, relProb_one]; ring

end Lightlike.CausalSets
