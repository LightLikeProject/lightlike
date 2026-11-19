import Lightlike.Spacetime.EHManifold.GHYDomain
import Lightlike.Spacetime.EHManifold.RegionVariation

/-!
# The Gibbons–Hawking–York density of a metric given only near the boundary point (M16, step 3)

The Gibbons–Hawking–York density of a boundary at a point depends only on the germ of the metric there
(`ghyDensityOf_congr`, `ghyGraph_congr`), and the Palatini flux only on the germs of the metric and the
perturbation (`ehFlux_congr`). So `ghyGraph_add_smul` (the density of `g + t h` is affine in `t`, with slope minus
the Palatini flux through the graph, where `h` vanishes on the graph) holds for a metric and a perturbation smooth
and nondegenerate only on an open set containing the graph point (`ghyGraph_add_smul_loc`): retract them to a
small ball around the point (`ballRetract`), apply `ghyGraph_add_smul`, and compare germs. This is the form needed
for the chart components of a metric on a manifold.
-/

open MeasureTheory Set Filter Topology Matrix Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

section Germ

variable {g g' h h' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}

/-- The Gibbons–Hawking–York density at `x` depends only on the germ of the metric at `x`. -/
theorem ghyDensityOf_congr (hg : g =ᶠ[𝓝 x] g') (ν : Fin n → ℝ) (dν : Fin n → Fin n → ℝ) :
    ghyDensityOf g ν dν x = ghyDensityOf g' ν dν x := by
  have hc : ∀ μ α β, christoffel g μ α β x = christoffel g' μ α β x := fun μ α β =>
    (christoffel_eventuallyEq hg μ α β).eq_of_nhds
  unfold ghyDensityOf conormalHup
  simp only [hg.eq_of_nhds, hc]

/-- The Palatini flux at `x` depends only on the germs of the metric and the perturbation at `x`. -/
theorem ehFlux_congr (hg : g =ᶠ[𝓝 x] g') (hh : h =ᶠ[𝓝 x] h') (ρ : Fin n) :
    ehFlux g h ρ x = ehFlux g' h' ρ x := by
  unfold ehFlux
  rw [hg.eq_of_nhds, (Wvec_eventuallyEq hg hh ρ).eq_of_nhds]

end Germ

/-- The Gibbons–Hawking–York density of a graph at `y` depends only on the germ of the metric at the graph
point. -/
theorem ghyGraph_congr {g g' : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (y : Fin n → ℝ) (hg : g =ᶠ[𝓝 (graphPt γ i y)] g') :
    ghyGraph g γ i y = ghyGraph g' γ i y :=
  ghyDensityOf_congr hg _ _

/-- **`ghyGraph_add_smul` for a metric given near the graph point**: if `G` and `H` are smooth and symmetric on
an open set containing the graph point, `G` nondegenerate there, `H` vanishing on the graph near `y`, and the
graph not null for `G`, then the Gibbons–Hawking–York density of `G + t H` is affine in `t` with slope minus the
Palatini flux through the graph. -/
theorem ghyGraph_add_smul_loc {G H : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    (hG : ∀ a b, ContDiffOn ℝ ∞ (fun z => G z a b) U) (hH : ∀ a b, ContDiffOn ℝ ∞ (fun z => H z a b) U)
    (hGs : ∀ z a b, G z a b = G z b a) (hHs : ∀ z a b, H z a b = H z b a) (hdet : ∀ z ∈ U, (G z).det ≠ 0)
    (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 1 γ) (i : Fin (n + 1)) (y : Fin n → ℝ) (hy : graphPt γ i y ∈ U)
    (hbd : ∀ᶠ y' in 𝓝 y, H (graphPt γ i y') = 0)
    (hN : (∑ a, graphConormal γ i y a *
      ∑ b, (G (graphPt γ i y))⁻¹ a b * graphConormal γ i y b) ≠ 0) (t : ℝ) :
    ghyGraph (fun z => G z + t • H z) γ i y =
      ghyGraph G γ i y + t * (-∑ ρ, ehFlux G H ρ (graphPt γ i y) * graphConormal γ i y ρ) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU _ hy
  let φ : ContDiffBump (graphPt γ i y) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hballφ : ball (graphPt γ i y) φ.rOut ⊆ U := hball
  have hG' : ∀ a b, ContDiff ℝ ∞ (fun z => G (ballRetract φ z) a b) :=
    contDiff_comp_ballRetract φ fun a b => (hG a b).mono hballφ
  have hH' : ∀ a b, ContDiff ℝ ∞ (fun z => H (ballRetract φ z) a b) :=
    contDiff_comp_ballRetract φ fun a b => (hH a b).mono hballφ
  have hdet' : ∀ z, (G (ballRetract φ z)).det ≠ 0 := fun z => hdet _ (hballφ (ballRetract_mem φ z))
  have hxin : graphPt γ i y ∈ ball (graphPt γ i y) φ.rIn := mem_ball_self (half_pos hr)
  have eG : (fun z => G (ballRetract φ z)) =ᶠ[𝓝 (graphPt γ i y)] G := eventuallyEq_comp_ballRetract φ G hxin
  have eH : (fun z => H (ballRetract φ z)) =ᶠ[𝓝 (graphPt γ i y)] H := eventuallyEq_comp_ballRetract φ H hxin
  have eGt : (fun z => G (ballRetract φ z) + t • H (ballRetract φ z)) =ᶠ[𝓝 (graphPt γ i y)]
      (fun z => G z + t • H z) := (eG.and eH).mono fun z hz => by
    show G (ballRetract φ z) + t • H (ballRetract φ z) = G z + t • H z
    rw [show G (ballRetract φ z) = G z from hz.1, show H (ballRetract φ z) = H z from hz.2]
  have hcont : ContinuousAt (graphPt γ i) y := (continuous_graphPt γ hγ.continuous i).continuousAt
  have hbd' : ∀ᶠ y' in 𝓝 y, H (ballRetract φ (graphPt γ i y')) = 0 := by
    filter_upwards [hbd, hcont.preimage_mem_nhds (isOpen_ball.mem_nhds hxin)] with y' h1 h2
    rw [ballRetract_of_mem φ h2]
    exact h1
  have hN' : (∑ a, graphConormal γ i y a *
      ∑ b, (G (ballRetract φ (graphPt γ i y)))⁻¹ a b * graphConormal γ i y b) ≠ 0 := by
    rwa [ballRetract_of_mem φ hxin]
  have key := ghyGraph_add_smul (fun z => G (ballRetract φ z)) (fun z => H (ballRetract φ z)) hG' hH'
    (fun z a b => hGs _ a b) (fun z a b => hHs _ a b) γ hγ i y hbd' hN' t
  rw [ghyGraph_congr γ i y eGt.symm, ghyGraph_congr γ i y eG.symm]
  simp only [ehFlux_congr eG.symm eH.symm]
  exact key

end Lightlike
