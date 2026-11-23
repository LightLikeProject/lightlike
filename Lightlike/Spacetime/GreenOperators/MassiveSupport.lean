import Mathlib
import Lightlike.Spacetime.GreenOperators.MassiveAdvanced
import Lightlike.Spacetime.GreenOperators.Support

/-!
# Finite propagation speed for the massive Green operators on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For every mass `m`, the retarded solution `massiveSol m f` of `kgOp m u = f` is nonzero at `p` only if
`f` is nonzero somewhere in the causal past of `p` (`massiveSol_ne_zero`), and the advanced one only
if `f` is nonzero somewhere in the causal future (`massiveAdvancedSol_ne_zero`).  This extends the
massless statements `retardedSol_ne_zero`, `advancedSol_ne_zero` to every mass.

This is a supporting result; no catalogue entry.
-/

open Set MeasureTheory
open scoped Convolution

namespace Lightlike.GreenOperators

/-- **Finite propagation speed, massive retarded case**: if `massiveSol m f` is nonzero at `p`, then
`f` is nonzero at some point of the causal past of `p`. -/
theorem massiveSol_ne_zero {m : ℝ} {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (h : massiveSol m f p ≠ 0) :
    ∃ q, f q ≠ 0 ∧ causalLE2 q p := by
  by_contra hcon
  push Not at hcon
  apply h
  unfold massiveSol riemannSol
  simp only [Function.comp]
  rw [convolution_def]
  have : (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (riemannKernel (-m ^ 2 / 4) t)
        (((-(1 / 4 : ℝ)) • nullSource f) (toNull p - t))) = fun _ => 0 := by
    funext t
    by_cases ht : (0 : ℝ × ℝ) ≤ t
    · have ht1 : (0 : ℝ) ≤ t.1 := ht.1
      have ht2 : (0 : ℝ) ≤ t.2 := ht.2
      have hf0 : f (nullPt (toNull p - t).1 (toNull p - t).2) = 0 := by
        by_contra hne
        apply hcon _ hne
        rw [causalLE2_iff]
        simp only [nullPt, toNull_apply, Prod.fst_sub, Prod.snd_sub]
        constructor <;> linarith
      simp only [Prod.fst_sub, Prod.snd_sub] at hf0
      simp [nullSource, hf0]
    · simp [riemannKernel, ht]
  rw [this, integral_zero]

/-- **Finite propagation speed, massive advanced case**: if `massiveAdvancedSol m f` is nonzero at
`p`, then `f` is nonzero at some point of the causal future of `p`. -/
theorem massiveAdvancedSol_ne_zero {m : ℝ} {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : massiveAdvancedSol m f p ≠ 0) : ∃ q, f q ≠ 0 ∧ causalLE2 p q := by
  obtain ⟨q', hq', hc⟩ := massiveSol_ne_zero h
  refine ⟨timeRevL q', hq', ?_⟩
  rw [causalLE2_iff] at hc ⊢
  simp only [timeRevL_apply] at hc ⊢
  constructor <;> linarith [hc.1, hc.2]

/-- The massive retarded solution is supported in the causal future of the support of `f`, stated with
the causal future of `minkowskiOrientation 1`. -/
theorem massiveSol_mem_causalFuture {m : ℝ} {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (h : massiveSol m f p ≠ 0) :
    ∃ q, f q ≠ 0 ∧
      ![p.1, p.2] ∈ Lightlike.Causal.causalFuture (Lightlike.Causal.minkowskiOrientation 1)
        ![q.1, q.2] := by
  obtain ⟨q, hq, hc⟩ := massiveSol_ne_zero h
  refine ⟨q, hq, ?_⟩
  rw [Lightlike.Causal.mem_causalFuture_iff, coneLE_iff_causalLE2]
  exact hc

end Lightlike.GreenOperators
