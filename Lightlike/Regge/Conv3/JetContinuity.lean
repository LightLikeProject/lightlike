import Lightlike.Regge.Conv3.TrueLength
import Lightlike.Regge.Conv3.JetCurvature
import Lightlike.Regge.Conv3.JetSlice

/-!
# The jet of a smooth metric depends continuously on the base point

For a coordinate metric on `U`, the first and second partial derivatives of the entries, the Christoffel
symbols, and hence the three parts `incQ`, `incC`, `incR` of the squared lengths of the star at a
hinge midpoint `v`, are continuous functions of `v ∈ U` (`continuousOn_incQ`, `continuousOn_incC`,
`continuousOn_incR`). This is what turns the pointwise jet estimates into estimates uniform on a compact
set of hinge midpoints.

## Main results

* `continuousOn_incQ`, `continuousOn_incC`, `continuousOn_incR`: continuity of the star data.
* `continuousOn_christoffel`: continuity of the Christoffel symbols.

**Limits.** Continuity only; no modulus of continuity is given.
-/

open Real Matrix Lightlike Filter Topology Metric Set
open scoped ContDiff
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)}

/-- The partial derivatives of the entries of a coordinate metric are smooth on `U`. -/
theorem contDiffOn_pd (hg : IsCoordMetric g U) (k i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun y => pd k (fun z => g z i j) y) U := by
  have := (hg.smooth i j).fderiv_of_isOpen hg.isOpen (m := ∞) (by simp)
  unfold pd
  exact this.clm_apply contDiffOn_const

/-- The entries of a coordinate metric are continuous on `U`. -/
theorem continuousOn_g (hg : IsCoordMetric g U) (i j : Fin 3) :
    ContinuousOn (fun y => g y i j) U := (hg.smooth i j).continuousOn

/-- The first partial derivatives of the entries are continuous on `U`. -/
theorem continuousOn_pd (hg : IsCoordMetric g U) (k i j : Fin 3) :
    ContinuousOn (fun y => pd k (fun z => g z i j) y) U := (contDiffOn_pd hg k i j).continuousOn

/-- The second partial derivatives of the entries are continuous on `U`. -/
theorem continuousOn_pd2 (hg : IsCoordMetric g U) (k l i j : Fin 3) :
    ContinuousOn (fun y => pd l (fun z => pd k (fun w => g w i j) z) y) U := by
  have := (contDiffOn_pd hg k i j).fderiv_of_isOpen hg.isOpen (m := ∞) (by simp)
  unfold pd
  exact (this.clm_apply contDiffOn_const).continuousOn

/-- The Christoffel symbols are continuous on `U`. -/
theorem continuousOn_christoffel (hg : IsCoordMetric g U) (a j k : Fin 3) :
    ContinuousOn (fun y => christoffel g a j k y) U := by
  unfold christoffel
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun l _ => ?_)
  refine ((cdo_inv g hg a l).continuousOn).mul ?_
  exact (((continuousOn_pd hg j l k).add (continuousOn_pd hg k l j)).sub (continuousOn_pd hg l j k))

/-- `edgeQ` is continuous in the base point. -/
theorem continuousOn_edgeQ (hg : IsCoordMetric g U) (Δ : Fin 3 → ℝ) :
    ContinuousOn (fun v => edgeQ g v Δ) U := by
  simp only [edgeQ, dotProduct, Matrix.mulVec]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact (continuousOn_g hg i j).mul continuousOn_const

/-- `edgeC` is continuous in the base point. -/
theorem continuousOn_edgeC (hg : IsCoordMetric g U) (s Δ : Fin 3 → ℝ) :
    ContinuousOn (fun v => edgeC g v s Δ) U := by
  simp only [edgeC, dmat, dotProduct, Matrix.mulVec, Matrix.of_apply]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
  refine continuousOn_finsetSum _ fun j _ => ?_
  refine (continuousOn_finsetSum _ fun k _ => ?_).mul continuousOn_const
  exact continuousOn_const.mul (continuousOn_pd hg k i j)

/-- `edgeR` is continuous in the base point. -/
theorem continuousOn_edgeR (hg : IsCoordMetric g U) (s Δ : Fin 3 → ℝ) :
    ContinuousOn (fun v => edgeR g v s Δ) U := by
  have hdd : ∀ u u' : Fin 3 → ℝ, ∀ i j : Fin 3,
      ContinuousOn (fun v => ddmat g v u u' i j) U := fun u u' i j => by
    simp only [ddmat, Matrix.of_apply]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun l _ => ?_
    exact (continuousOn_const.mul continuousOn_const).mul (continuousOn_pd2 hg k l i j)
  have hq : ∀ u u' : Fin 3 → ℝ, ContinuousOn (fun v => Δ ⬝ᵥ (ddmat g v u u' *ᵥ Δ)) U := fun u u' => by
    simp only [dotProduct, Matrix.mulVec]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
    exact continuousOn_finsetSum _ fun j _ => (hdd u u' i j).mul continuousOn_const
  have hch : ∀ i, ContinuousOn (fun v => chr g v Δ Δ i) U := fun i => by
    simp only [chr]
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ => ?_
    exact ((continuousOn_christoffel hg i j k).mul continuousOn_const).mul continuousOn_const
  have hgc : ContinuousOn (fun v => chr g v Δ Δ ⬝ᵥ (g v *ᵥ chr g v Δ Δ)) U := by
    simp only [dotProduct, Matrix.mulVec]
    refine continuousOn_finsetSum _ fun i _ => (hch i).mul ?_
    exact continuousOn_finsetSum _ fun j _ => (continuousOn_g hg i j).mul (hch j)
  unfold edgeR
  exact (((hq s s).const_smul (1 / 2 : ℝ)).add ((hq Δ Δ).const_smul (1 / 24 : ℝ))).sub
    (hgc.const_smul (1 / 12 : ℝ))

/-- `incQ` is continuous in the base point. -/
theorem continuousOn_incQ (hg : IsCoordMetric g U) (σ h : Fin 6) :
    ContinuousOn (fun v => incQ g v σ h) U := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i <;> simp only [incQ, incVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Fin.reduceFinMk, Fin.isValue] <;> exact continuousOn_edgeQ hg _

/-- `incC` is continuous in the base point. -/
theorem continuousOn_incC (hg : IsCoordMetric g U) (σ h : Fin 6) :
    ContinuousOn (fun v => incC g v σ h) U := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i <;> simp only [incC, incVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Fin.reduceFinMk, Fin.isValue] <;> exact continuousOn_edgeC hg _ _

/-- `incR` is continuous in the base point. -/
theorem continuousOn_incR (hg : IsCoordMetric g U) (σ h : Fin 6) :
    ContinuousOn (fun v => incR g v σ h) U := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i <;> simp only [incR, incVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, Fin.reduceFinMk, Fin.isValue] <;> exact continuousOn_edgeR hg _ _

end Lightlike.Regge.Conv3
