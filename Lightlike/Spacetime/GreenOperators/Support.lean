import Mathlib
import Lightlike.Spacetime.GreenOperators.Advanced
import Lightlike.Spacetime.Causal.MinkowskiGH

/-!
# Support of the retarded and advanced solutions on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For `f` of class `C²` with compact support, the retarded solution of the massless wave equation
is supported in the causal future of the support of `f`, and the advanced one in the causal
past (`retardedSol_ne_zero`, `advancedSol_ne_zero`): this is finite propagation speed.
The causal relation of `ℝ × ℝ` with coordinates `(t, x)` is `causalLE2 q p : |x_p - x_q| ≤ t_p - t_q`;
it agrees with the cone order `coneLE` of the Minkowski files (`coneLE_iff_causalLE2`) and with
the causal future of `minkowskiOrientation 1` (`retardedSol_mem_causalFuture`).

This is a supporting result; no catalogue entry.
-/

open Set

namespace Lightlike.GreenOperators

/-- `p` is in the causal future of `q` in `1+1` Minkowski space (coordinates `(t, x)`). -/
def causalLE2 (q p : ℝ × ℝ) : Prop := |p.2 - q.2| ≤ p.1 - q.1

/-- `causalLE2` is the cone order of `ℝ^{1+1}`. -/
lemma coneLE_iff_causalLE2 (q p : ℝ × ℝ) :
    Lightlike.CausalSets.coneLE ![q.1, q.2] ![p.1, p.2] ↔ causalLE2 q p := by
  rw [Lightlike.CausalSets.coneLE_iff_spatial, causalLE2]
  simp only [spatialSq, Fin.sum_univ_one, Pi.sub_apply]
  simp only [Fin.succ_zero_eq_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sq_abs (p.2 - q.2)]
  constructor
  · rintro ⟨h1, h2⟩
    exact abs_le_of_sq_le_sq (by simpa using h2) h1
  · intro h
    exact ⟨(abs_nonneg _).trans h, by simpa using pow_le_pow_left₀ (abs_nonneg _) h 2⟩

/-- `causalLE2 q p` iff `q` is below `p` in both null coordinates `t - x`, `t + x`. -/
lemma causalLE2_iff (q p : ℝ × ℝ) :
    causalLE2 q p ↔ q.1 - q.2 ≤ p.1 - p.2 ∧ q.1 + q.2 ≤ p.1 + p.2 := by
  unfold causalLE2
  rw [abs_le]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Finite propagation speed, retarded case**: if the retarded solution is nonzero at `p`, then
`f` is nonzero at some point of the causal past of `p`. -/
theorem retardedSol_ne_zero {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : retardedSol f p ≠ 0) :
    ∃ q, f q ≠ 0 ∧ causalLE2 q p := by
  by_contra hcon
  push Not at hcon
  apply h
  apply quadPrim_eq_zero
  intro q hq
  simp only [Pi.smul_apply, smul_eq_mul, nullSource]
  have h1 : q.1 ≤ p.1 - p.2 := hq.1
  have h2 : q.2 ≤ p.1 + p.2 := hq.2
  have := hcon (nullPt q.1 q.2)
  rw [mul_eq_zero]
  right
  by_contra hne
  apply this hne
  rw [causalLE2_iff]
  simp only [nullPt]
  constructor <;> linarith

/-- **Finite propagation speed, advanced case**: if the advanced solution is nonzero at `p`, then
`f` is nonzero at some point of the causal future of `p`. -/
theorem advancedSol_ne_zero {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : advancedSol f p ≠ 0) :
    ∃ q, f q ≠ 0 ∧ causalLE2 p q := by
  obtain ⟨q', hq', hc⟩ := retardedSol_ne_zero h
  refine ⟨timeRevL q', hq', ?_⟩
  rw [causalLE2_iff] at hc ⊢
  simp only [timeRevL_apply] at hc ⊢
  constructor <;> linarith [hc.1, hc.2]

/-- The retarded solution is supported in the causal future of the support of `f`, stated with the
causal future of `minkowskiOrientation 1`. -/
theorem retardedSol_mem_causalFuture {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : retardedSol f p ≠ 0) :
    ∃ q, f q ≠ 0 ∧
      ![p.1, p.2] ∈ Lightlike.Causal.causalFuture (Lightlike.Causal.minkowskiOrientation 1) ![q.1, q.2] := by
  obtain ⟨q, hq, hc⟩ := retardedSol_ne_zero h
  refine ⟨q, hq, ?_⟩
  rw [Lightlike.Causal.mem_causalFuture_iff, coneLE_iff_causalLE2]
  exact hc

end Lightlike.GreenOperators
