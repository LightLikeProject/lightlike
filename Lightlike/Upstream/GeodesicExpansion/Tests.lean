import Lightlike.Upstream.GeodesicExpansion.Final
import Mathlib

/-!
# Trust checks for the fifth-order expansion of the squared distance

For the Euclidean metric the jet `distJet` is `|w|²` (all derivative terms vanish), and on a convex
open set Mathlib's `riemannianEDist` of the Euclidean bundle has square `|y - x|²`, so the
expansion theorem holds with error `0`. Also the axioms of the two main theorems are printed.
-/

open Matrix Set Filter Topology Metric MeasureTheory Manifold Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ}

/-- For the Euclidean metric every derivative term of the jet vanishes: `distJet = |w|²`. -/
theorem distJet_euclid (x w : Fin n → ℝ) : distJet euclid x w = eNormSq w := by
  have hpd : ∀ (k : Fin n) (i j : Fin n) (y : Fin n → ℝ),
      pd k (fun z => (euclid z : Matrix (Fin n) (Fin n) ℝ) i j) y = 0 := by
    intro k i j y
    simp [pd, euclid]
  have hpd2 : ∀ (k l : Fin n) (i j : Fin n) (y : Fin n → ℝ),
      pd l (pd k (fun z => (euclid z : Matrix (Fin n) (Fin n) ℝ) i j)) y = 0 := by
    intro k l i j y
    have : pd k (fun z => (euclid z : Matrix (Fin n) (Fin n) ℝ) i j) = fun _ => 0 :=
      funext (hpd k i j)
    rw [this]
    simp [pd]
  have hchr : chr euclid x w w = 0 := by
    ext i
    simp [chr, christoffel, hpd]
  have hd : dmat euclid x w = 0 := by
    ext i j
    simp only [dmat, hpd, mul_zero, Finset.sum_const_zero, Matrix.of_apply, Matrix.zero_apply]
  have hdd : ddmat euclid x w w = 0 := by
    ext i j
    simp only [ddmat, hpd2, mul_zero, Finset.sum_const_zero, Matrix.of_apply, Matrix.zero_apply]
  simp [distJet, hd, hdd, hchr, euclid, eNormSq]

/-- **Trust check.** On a convex open set the Euclidean metric gives, through the Mathlib
Riemannian structure, `riemannianEDist² = |y - x|² = distJet euclid x (y - x)`: the expansion has
vanishing remainder. -/
theorem riemannianEDist_sq_euclid {U : TopologicalSpace.Opens (Fin n → ℝ)}
    (hconv : Convex ℝ (U : Set (Fin n → ℝ))) (x y : U) :
    letI := (isRiemMetric_euclid (n := n) U.isOpen).riemannianBundle
    (riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y).toReal ^ 2 =
      distJet euclid (x : Fin n → ℝ) ((y : Fin n → ℝ) - x) := by
  let := (isRiemMetric_euclid (n := n) U.isOpen).riemannianBundle
  rw [← (isRiemMetric_euclid (n := n) U.isOpen).chartDist_eq_toReal_riemannianEDist x y,
    chartDist_euclid U.isOpen hconv x.2 y.2, distJet_euclid]
  refine Real.sq_sqrt ?_
  unfold eNormSq dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

#print axioms IsRiemMetric.riemannianEDist_sq_expansion
#print axioms IsRiemMetric.riemannianEDist_sq_expansion_midpoint
#print axioms riemannianEDist_sq_euclid

end Lightlike.Upstream.GeodesicExpansion
