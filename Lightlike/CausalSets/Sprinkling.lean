import Lightlike.CausalSets.ConeOrder
import Lightlike.CausalSets.Expected

/-!
# Sprinkling into a causal diamond

A *sprinkling* of `n` points into a region of Minkowski space is a sample of `n` independent uniform
points; the induced causal order on the sample is a causal set. This file is the second half of the
bridge between Lorentzian geometry and causal sets: the order on the sample is the causal order
`coneLE` of Minkowski space (`Lightlike/CausalSets/ConeOrder.lean`), which is the causal future of
the Lorentzian interface of `Lightlike/Spacetime/Causal/`.

The region is the **causal diamond** `diamond d` of Minkowski space `ℝ^{d+1}`: the points in the
causal future of the origin and in the causal past of the point `(1, 0, …, 0)`. `diamondMeasure d`
is the uniform probability measure on it. The theorem `expected_relations_diamond` says that `n`
uniform points of the diamond have `n (n - 1) p` related pairs in expectation, with `p`
(`relProb d`) the probability that two uniform points are related; the value of `p`
(Myrheim–Meyer: `Γ(D + 1) Γ(D / 2) / (4 Γ(3 D / 2))` in the dimension `D = d + 1`) is the subject of
`Lightlike/CausalSets/Myrheim.lean`. No Poisson process is used: the number of points is fixed.

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* L. Bombelli, J. Lee, D. Meyer, R. D. Sorkin, *Space-time as a causal set*, Phys. Rev. Lett. 59
  (1987) 521.
-/

open MeasureTheory

namespace Lightlike.CausalSets

variable {d : ℕ}

/-- The **top** of the standard causal diamond: the point `(1, 0, …, 0)`. -/
def diamondTop (d : ℕ) : Fin (d + 1) → ℝ := Pi.single 0 1

/-- The **causal diamond** of Minkowski space `ℝ^{d+1}` between the origin and `(1, 0, …, 0)`:
the points in the causal future of the origin and in the causal past of the top. -/
def diamond (d : ℕ) : Set (Fin (d + 1) → ℝ) := {x | coneLE 0 x ∧ coneLE x (diamondTop d)}

/-- The strict causal relation of Minkowski space: `x` is in the causal future of `y ≠ x`. -/
def coneLT (x y : Fin (d + 1) → ℝ) : Prop := coneLE x y ∧ x ≠ y

/-- The uniform probability measure on a region `A` of Minkowski space (the normalised Lebesgue
measure on `A`; the zero measure when `A` has measure `0` or `∞`, which is a junk value excluded
by the hypotheses of the theorems). -/
noncomputable def regionMeasure (A : Set (Fin (d + 1) → ℝ)) : Measure (Fin (d + 1) → ℝ) :=
  ProbabilityTheory.cond volume A

/-- The **related-pair probability** of a region `A`: the probability that two independent uniform
points `x`, `y` of `A` satisfy `x ≺ y` (`coneLT x y`). -/
noncomputable def regionRelProb (A : Set (Fin (d + 1) → ℝ)) : ℝ :=
  ((regionMeasure A).prod (regionMeasure A) {p | coneLT p.1 p.2}).toReal

/-- The uniform probability measure on the diamond. -/
noncomputable def diamondMeasure (d : ℕ) : Measure (Fin (d + 1) → ℝ) :=
  regionMeasure (diamond d)

/-- The **related-pair probability** of the diamond: the probability that two independent uniform
points `x`, `y` of the diamond satisfy `x ≺ y` (`coneLT x y`). -/
noncomputable def relProb (d : ℕ) : ℝ := regionRelProb (diamond d)

lemma relProb_eq (d : ℕ) :
    relProb d = ((diamondMeasure d).prod (diamondMeasure d) {p | coneLT p.1 p.2}).toReal := rfl

lemma diamond_subset_box (d : ℕ) : diamond d ⊆ Set.pi Set.univ (fun _ => Set.Icc (-1) 1) := by
  intro x ⟨h1, h2⟩
  rw [coneLE_iff_spatial] at h1 h2
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero] at h1
  have h0 : x 0 ≤ 1 := by
    have := h2.1; simp [diamondTop] at this; linarith
  have hsp : ∀ j : Fin d, (x j.succ) ^ 2 ≤ (x 0) ^ 2 := fun j =>
    (Finset.single_le_sum (f := fun i : Fin d => x i.succ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)).trans h1.2
  intro i _
  refine Fin.cases ?_ (fun j => ?_) i
  · constructor <;> linarith [h1.1]
  · have := abs_le_of_sq_le_sq' (hsp j) (by linarith [h1.1])
    constructor <;> linarith [this.1, this.2]

lemma diamond_isClosed (d : ℕ) : IsClosed (diamond d) := by
  have : diamond d = {x | 0 ≤ (x - 0) 0} ∩ {x | minkowskiForm (d + 1) (x - 0) (x - 0) ≤ 0} ∩
      ({x | 0 ≤ (diamondTop d - x) 0} ∩
        {x | minkowskiForm (d + 1) (diamondTop d - x) (diamondTop d - x) ≤ 0}) := by
    ext x; simp only [diamond, coneLE, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [this]
  simp only [minkowskiForm_apply]
  refine ((IsClosed.inter ?_ ?_).inter (IsClosed.inter ?_ ?_)) <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

lemma diamond_measurableSet (d : ℕ) : MeasurableSet (diamond d) :=
  (diamond_isClosed d).measurableSet

lemma volume_diamond_lt_top (d : ℕ) : volume (diamond d) < ⊤ :=
  (measure_mono (diamond_subset_box d)).trans_lt (by
    rw [volume_pi_pi]; simp)

/-- The diamond contains a ball around its centre `(1/2, 0, …, 0)`. -/
lemma ball_subset_diamond (d : ℕ) :
    Metric.ball ((1 / 2 : ℝ) • diamondTop d) (1 / (4 * (d + 1))) ⊆ diamond d := by
  intro x hx
  rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hx
  set r : ℝ := 1 / (4 * (d + 1)) with hr
  have hr0 : 0 < r := by positivity
  have hrd : (d : ℝ) * r ≤ 1 / 4 := by
    rw [hr, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hr4 : r ≤ 1 / 4 := by
    rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have h0 := hx 0
  have hs : ∀ j : Fin d, |x j.succ| < r := fun j => by
    have := hx j.succ
    simpa [diamondTop, Real.dist_eq, Pi.single_apply, Fin.succ_ne_zero] using this
  have ht : |x 0 - 1 / 2| < r := by
    simpa [diamondTop, Real.dist_eq] using h0
  have hx0 := abs_lt.1 ht
  have hsp : spatialSq x ≤ (d : ℝ) * r ^ 2 := by
    calc spatialSq x = ∑ j : Fin d, x j.succ ^ 2 := rfl
      _ ≤ ∑ _j : Fin d, r ^ 2 :=
        Finset.sum_le_sum fun j _ => (sq_le_sq' (abs_lt.1 (hs j)).1.le (abs_lt.1 (hs j)).2.le)
      _ = d * r ^ 2 := by simp
  have key : (d : ℝ) * r ^ 2 ≤ (1 / 2 - r) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hrd hr0.le]
  have hpos : 0 ≤ 1 / 2 - r := by linarith
  have e1 : spatialSq x ≤ (x 0) ^ 2 := by
    calc spatialSq x ≤ (1 / 2 - r) ^ 2 := hsp.trans key
      _ ≤ (x 0) ^ 2 := pow_le_pow_left₀ hpos (by linarith) 2
  have e2 : spatialSq x ≤ (1 - x 0) ^ 2 := by
    calc spatialSq x ≤ (1 / 2 - r) ^ 2 := hsp.trans key
      _ ≤ (1 - x 0) ^ 2 := pow_le_pow_left₀ hpos (by linarith) 2
  refine ⟨?_, ?_⟩
  · rw [coneLE_iff_spatial]
    simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
    exact ⟨by linarith, by simpa [spatialSq] using e1⟩
  · rw [coneLE_iff_spatial]
    have : spatialSq (diamondTop d - x) = spatialSq x := by
      simp [spatialSq, diamondTop, Fin.succ_ne_zero]
    simp only [Pi.sub_apply, diamondTop, Pi.single_eq_same] at *
    refine ⟨by linarith, ?_⟩
    simpa [diamondTop, spatialSq, Pi.single_apply, Fin.succ_ne_zero, sq] using e2

lemma volume_diamond_pos (d : ℕ) : 0 < volume (diamond d) :=
  (Metric.measure_ball_pos volume _ (by positivity)).trans_le
    (measure_mono (ball_subset_diamond d))

instance diamondMeasure_isProbability (d : ℕ) : IsProbabilityMeasure (diamondMeasure d) :=
  ProbabilityTheory.cond_isProbabilityMeasure_of_finite (volume_diamond_pos d).ne'
    (volume_diamond_lt_top d).ne

lemma coneLT_measurableSet (d : ℕ) : MeasurableSet {p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) |
    coneLT p.1 p.2} := by
  have h1 : IsClosed {p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) | coneLE p.1 p.2} := by
    have : {p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) | coneLE p.1 p.2} =
        {p | 0 ≤ (p.2 - p.1) 0} ∩ {p | minkowskiForm (d + 1) (p.2 - p.1) (p.2 - p.1) ≤ 0} := rfl
    rw [this]
    simp only [minkowskiForm_apply]
    exact (isClosed_le (by fun_prop) (by fun_prop)).inter (isClosed_le (by fun_prop) (by fun_prop))
  have h2 : MeasurableSet {p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  exact h1.measurableSet.inter h2

/-- **Expected number of relations of a sprinkling into a region.** `n` independent uniform points
of a region `A` of Minkowski space `ℝ^{d+1}` of finite positive volume have, in expectation,
`n (n - 1) p` pairs `x ≺ y` of points in the causal relation, where `p = regionRelProb A` is the
probability that two uniform points of `A` are related. -/
theorem expected_relations_region {A : Set (Fin (d + 1) → ℝ)} (hA0 : volume A ≠ 0)
    (hA : volume A ≠ ⊤) (n : ℕ) :
    ∫ ω, (relCount {p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) | coneLT p.1 p.2} ω : ℝ)
        ∂Measure.pi (fun _ : Fin n => regionMeasure A) = (n : ℝ) * (n - 1) * regionRelProb A := by
  have : IsProbabilityMeasure (regionMeasure A) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hA0 hA
  exact expected_relCount _ (coneLT_measurableSet d)

/-- **Expected number of relations of a sprinkling into the diamond.** `n` independent uniform
points of the causal diamond of `ℝ^{d+1}` have, in expectation, `n (n - 1) p` pairs `x ≺ y` of
points in the causal relation of Minkowski space, where `p = relProb d` is the probability that two
uniform points of the diamond are related. -/
theorem expected_relations_diamond (d n : ℕ) :
    ∫ ω, (relCount {p : (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ) | coneLT p.1 p.2} ω : ℝ)
        ∂Measure.pi (fun _ : Fin n => diamondMeasure d) = (n : ℝ) * (n - 1) * relProb d :=
  expected_relations_region (volume_diamond_pos d).ne' (volume_diamond_lt_top d).ne n

end Lightlike.CausalSets
