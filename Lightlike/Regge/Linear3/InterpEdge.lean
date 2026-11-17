import Mathlib

/-!
# Christiansen's degrees of freedom of the Regge interpolant

For a field `h` of symmetric matrices on `ℝ³`, the degree of freedom of the edge from `x` to `y` is
`μ_e (h) = ∫₀¹ (y - x)ᵀ h (x + t (y - x)) (y - x) dt` (Christiansen 2011, eq. (5)): the first variation
of the squared length of the edge for the metric `δ + ε h`, integrated along the straight edge (it is
*not* the first variation of the geodesic distance of `δ + ε h`; the two have the same first
variation at `ε = 0`, which is not formalized here). It does not depend on the orientation of the edge
(`muE_comm`) and is invariant under translations that preserve `h` (`muE_translate`).

## Main results

* `muE`: the degree of freedom.
* `muE_comm`, `muE_translate`: orientation and translation invariance.

**Limits.** Fields on all of `ℝ³`; no smoothness is needed for these two lemmas.
-/

open Real MeasureTheory intervalIntegral Matrix
namespace Lightlike.Regge.Linear3

/-- **Christiansen's degree of freedom** `μ_e (h) = ∫₀¹ (y - x)ᵀ h (x + t (y - x)) (y - x) dt` of the
edge from `x` to `y` (eq. (5) of Christiansen 2011) for a field `hf` of symmetric matrices. -/
noncomputable def muE (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (y - x) ⬝ᵥ (hf (x + t • (y - x)) *ᵥ (y - x))

/-- `μ_e` does not depend on the orientation of the edge. -/
theorem muE_comm (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    muE hf x y = muE hf y x := by
  unfold muE
  have h1 : ∀ t : ℝ, (x - y) ⬝ᵥ (hf (y + t • (x - y)) *ᵥ (x - y)) =
      (y - x) ⬝ᵥ (hf (x + (1 - t) • (y - x)) *ᵥ (y - x)) := fun t => by
    have e1 : y + t • (x - y) = x + (1 - t) • (y - x) := by
      funext i; simp; ring
    have e2 : x - y = -(y - x) := by abel
    rw [e1, e2, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  simp only [h1]
  have := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => (y - x) ⬝ᵥ (hf (x + t • (y - x)) *ᵥ (y - x))) (a := 0) (b := 1) 1
  simpa using this.symm

/-- `μ_e` of a field invariant under the translation `e` is invariant under translating the edge. -/
theorem muE_translate (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 3 → ℝ)
    (hper : ∀ p, hf (p + e) = hf p) (x y : Fin 3 → ℝ) : muE hf (x + e) (y + e) = muE hf x y := by
  unfold muE
  congr 1
  funext t
  have e1 : (y + e) - (x + e) = y - x := by abel
  have e2 : x + e + t • (y - x) = (x + t • (y - x)) + e := by abel
  rw [e1, e2, hper]

end Lightlike.Regge.Linear3
