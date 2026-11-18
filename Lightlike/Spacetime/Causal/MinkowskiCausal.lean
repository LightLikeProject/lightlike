import Lightlike.Spacetime.Causal.Ladder
import Lightlike.Spacetime.Minkowski

/-!
# Causal structure of Minkowski space

Minkowski space `ℝ^{d+1}` with the constant metric `η` of `Lightlike/Spacetime/Minkowski.lean` is
time oriented by the constant field `∂₀` (`minkowskiOrientation`). A straight line with a
future-directed timelike direction is a future-directed timelike curve
(`isFutureTimelikeCurve_line`), so `x + v ∈ I⁺(x)` (`line_mem_chronFuture`).

## Main definitions

* `Causal.minkowskiOrientation d`: the time orientation `∂₀`.
* `Causal.isFutureTimelikeCurve_line`: affine timelike curves are timelike curves.

## References

* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1 (causal
  structure of Minkowski space).
-/

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {d : ℕ}

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 200000 in
/-- The constant field `∂₀` is a time orientation of Minkowski space `ℝ^{d+1}`. -/
def minkowskiOrientation (d : ℕ) : TimeOrientation (minkowskiMetric (d + 1)) where
  X _ := Pi.single 0 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := (Pi.single 0 1 : Fin (d + 1) → ℝ))
    simp [TangentSpace]
  timelike x := by
    show minkowskiForm (d + 1) (Pi.single 0 1) (Pi.single 0 1) < 0
    rw [minkowskiForm_eq]
    simp


set_option synthInstance.maxHeartbeats 200000 in
/-- A straight line in the model space is locally Lipschitz. -/
lemma isLocallyLipschitzOn_line {d : ℕ} (x v : Fin (d + 1) → ℝ) (s : Set ℝ) :
    IsLocallyLipschitzOn (I := 𝓘(ℝ, Fin (d + 1) → ℝ)) (fun t : ℝ => x + t • v) s := by
  intro t ht
  refine ⟨‖v‖₊, Set.univ, Filter.univ_mem, fun _ _ => ?_, ?_⟩
  · simp
  · have : LipschitzWith ‖v‖₊ (fun t : ℝ => x + t • v) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      simp [dist_eq_norm, ← sub_smul, norm_smul, mul_comm]
    simpa using this

/-- The velocity of a straight line is its direction (on an interval with nonempty interior). -/
lemma velocity_line {d : ℕ} (x v : Fin (d + 1) → ℝ) {a b : ℝ} (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) :
    velocity 𝓘(ℝ, Fin (d + 1) → ℝ) (fun t : ℝ => x + t • v) (Icc a b) t = v ∧
      MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin (d + 1) → ℝ) (fun t : ℝ => x + t • v) (Icc a b) t := by
  have hd : HasDerivWithinAt (fun t : ℝ => x + t • v) v (Icc a b) t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x |>.hasDerivWithinAt
  have hu : UniqueDiffWithinAt ℝ (Icc a b) t := uniqueDiffOn_Icc hab t ht
  refine ⟨?_, ?_⟩
  · rw [velocity, mfderivWithin_eq_fderivWithin, hd.hasFDerivWithinAt.fderivWithin hu]
    exact one_smul ℝ v
  · rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    exact hd.differentiableWithinAt


set_option synthInstance.maxHeartbeats 200000 in
/-- A straight line whose direction is future-directed timelike for `∂₀` is a future-directed
timelike curve on a nondegenerate interval. -/
theorem isFutureTimelikeCurve_line (x v : Fin (d + 1) → ℝ) {a b : ℝ} (hab : a < b)
    (hv : minkowskiForm (d + 1) v v < 0 ∧ minkowskiForm (d + 1) v (Pi.single 0 1) < 0) :
    IsFutureTimelikeCurve (minkowskiOrientation d) (fun t : ℝ => x + t • v) (Icc a b) := by
  have hX : minkowskiForm (d + 1) v (Pi.single 0 1) ≠ 0 := hv.2.ne
  set ε : ℝ := -minkowskiForm (d + 1) v v / (minkowskiForm (d + 1) v (Pi.single 0 1)) ^ 2 with hε
  have hεpos : 0 < ε := div_pos (by linarith [hv.1]) (by positivity)
  have hεeq : minkowskiForm (d + 1) v v ≤ -ε * (minkowskiForm (d + 1) v (Pi.single 0 1)) ^ 2 := by
    have h2 : ε * (minkowskiForm (d + 1) v (Pi.single 0 1)) ^ 2 =
        -minkowskiForm (d + 1) v v := by
      rw [hε]; field_simp
    linarith
  have key : ∀ (P : ∀ y : Fin (d + 1) → ℝ, TangentSpace 𝓘(ℝ, Fin (d + 1) → ℝ) y → Prop)
      {a b : ℝ}, a < b → (∀ y, P y v) →
      IsCurveWith (I := 𝓘(ℝ, Fin (d + 1) → ℝ)) P (fun t : ℝ => x + t • v) (Icc a b) := by
    intro P a b hab hP
    refine ⟨ordConnected_Icc, isLocallyLipschitzOn_line x v _, ?_⟩
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    obtain ⟨h1, h2⟩ := velocity_line x v hab ht
    refine ⟨h2, ?_⟩
    rw [h1]
    exact hP _
  refine ⟨key _ hab fun _ => hv, fun c d' hcd hsub => ⟨ε, hεpos, ?_⟩⟩
  exact key _ hcd fun _ => ⟨hεeq, hv.2⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- `x + v` is in the chronological future of `x` for a future-directed timelike `v`. -/
theorem line_mem_chronFuture (x v : Fin (d + 1) → ℝ)
    (hv : minkowskiForm (d + 1) v v < 0 ∧ minkowskiForm (d + 1) v (Pi.single 0 1) < 0) :
    x + v ∈ chronFuture (minkowskiOrientation d) x :=
  ⟨fun t => x + t • v, 0, 1, zero_lt_one, isFutureTimelikeCurve_line x v zero_lt_one hv, by simp, by simp⟩

end Lightlike.Causal
