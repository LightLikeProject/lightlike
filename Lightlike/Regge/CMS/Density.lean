import Mathlib
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Regge.Geodesic.Metric

/-!
# The curvature density is Lipschitz on a compact set (RC6b)

For a Riemannian metric `g` on an open set `U` and a compact `K ⊆ U`, the density
`x ↦ (R(x) / 2) √det g(x)` (half the scalar curvature times the Riemannian volume density) is
smooth on `U` and therefore Lipschitz on `K`. In two dimensions `R / 2` is the Gauss curvature.
-/

open Set
open scoped ContDiff

namespace Lightlike.CMS

variable {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}

/-- The scalar curvature is smooth on the domain of a coordinate metric. -/
theorem contDiffOn_scalarCurvature (hg : IsCoordMetric g U) :
    ContDiffOn ℝ ∞ (scalarCurvature g) U := by
  have hΓ := hg.contDiffOn_christoffel
  have hR : ∀ ρ σ μ ν, ContDiffOn ℝ ∞ (riemann g ρ σ μ ν) U := by
    intro ρ σ μ ν
    unfold riemann
    refine ContDiffOn.add (ContDiffOn.sub (contDiffOn_pd (hΓ _ _ _) hg.isOpen _)
      (contDiffOn_pd (hΓ _ _ _) hg.isOpen _)) ?_
    exact ContDiffOn.sum fun l _ => ((hΓ _ _ _).mul (hΓ _ _ _)).sub ((hΓ _ _ _).mul (hΓ _ _ _))
  unfold scalarCurvature ricci
  exact ContDiffOn.sum fun σ _ => ContDiffOn.sum fun ν _ =>
    (hg.contDiffOn_inv σ ν).mul (ContDiffOn.sum fun ρ _ => hR _ _ _ _)

/-- A `C^∞` function on an open set is Lipschitz on each compact subset. -/
theorem lipschitzOn_of_contDiffOn {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    (hU : IsOpen U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : NNReal, LipschitzOnWith L ψ K := by
  have : LocallyLipschitzOn K ψ := by
    intro x hx
    have hc : ContDiffAt ℝ 1 ψ x :=
      ((hψ.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by exact_mod_cast le_top))
    obtain ⟨L, t, ht, hL⟩ := hc.exists_lipschitzOnWith
    exact ⟨L, t, nhdsWithin_le_nhds ht, hL⟩
  exact this.exists_lipschitzOnWith_of_compact hK

/-- **The curvature density is Lipschitz on a compact set**: `(R / 2) √det g` on `K ⊆ U`. -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.lipschitz_density
    (hg : Lightlike.Geodesic.IsRiemMetric g U) {K : Set (Fin 2 → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : NNReal, LipschitzOnWith L (fun x => scalarCurvature g x / 2 * Real.sqrt ((g x).det)) K := by
  have hdet : ContDiffOn ℝ ∞ (fun y => (g y).det) U :=
    contDiffOn_det_of_entries hg.coord.smooth
  have hpos : ∀ x ∈ U, (g x).det ≠ 0 := fun x hx =>
    (hg.coord.isUnit_det x hx).ne_zero
  have := ((contDiffOn_scalarCurvature hg.coord).div_const 2).mul (hdet.sqrt hpos)
  exact lipschitzOn_of_contDiffOn this hg.coord.isOpen hK hKU

end Lightlike.CMS
