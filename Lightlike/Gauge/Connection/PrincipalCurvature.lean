import Lightlike.Gauge.Connection.PrincipalConnection
import Lightlike.Gauge.LieConnection.LieGroupGauge

/-!
# The curvature of the glued connection (Svetlichny §4.9, eqs. (62), (63), p. 42)

Svetlichny defines the curvature of an invariant connection through its local principal gauge potentials: in a
trivialization over `U`, `F_U = dA_U + [A_U, A_U]` (eq. (62)), a `g`-valued 2-form on `U`, and on an overlap the local
curvatures are related by `F_V = g_VU F_U g_VU⁻¹ = Ad_{g_VU} F_U` (eq. (63)), the transition map of the adjoint
bundle `P ×_Ad g`, so that `F` is a `P ×_Ad g`-valued 2-form (p. 42).

Here, for the glued principal bundle over an open cover of a normed space `F` (the source's local form, as for (62)
and (64) in `LieGroupGauge.lean`), with local potentials `A_i` satisfying (38) (`IsCompatible`), the local curvatures
`lieCurvature (A i)` satisfy (63) on every overlap (`lieCurvature_transition`). The proof writes the `C³` transition
map `g_ij` near a point in the chart at the identity (`chart_form`) and applies the covariance (64)
(`lieCurvature_lieGaugeTransform`) to `A_j = Ad_{g_ij} A_i - dg_ij g_ij⁻¹`.
-/

open Set Filter
open scoped ContDiff Manifold Topology

universe u

namespace Lightlike.Gauge

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {G : Type u} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G]

omit [CompleteSpace E] [LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G] in
/-- The curvature depends only on the germ of the potential. -/
lemma lieCurvature_congr {A B : F → F →L[ℝ] E} {x₀ : F} (h : A =ᶠ[𝓝 x₀] B) (η ξ : F) :
    lieCurvature 𝓘(ℝ, E) G A x₀ η ξ = lieCurvature 𝓘(ℝ, E) G B x₀ η ξ := by
  unfold lieCurvature
  rw [h.fderiv_eq, h.eq_of_nhds]

omit [CompleteSpace E] in
/-- **A `C³` map into `G` in the chart at the identity**: near `x₀`, `g = g(x₀) · φ⁻¹(γ)` with
`γ = φ(g(x₀)⁻¹ g)` `C²` and `γ(x₀) = φ(1)`, the form required by `lieCurvature_lieGaugeTransform`. -/
lemma chart_form {g : F → G} {x₀ : F} (hg : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) (minSmoothness ℝ 3) g x₀) :
    ContDiffAt ℝ 2 (fun x => chart1 E G ((g x₀)⁻¹ * g x)) x₀ ∧
      chart1 E G ((g x₀)⁻¹ * g x₀) = chartOne E G ∧
      g =ᶠ[𝓝 x₀] fun x => g x₀ * (chart1 E G).symm (chart1 E G ((g x₀)⁻¹ * g x)) := by
  have hk : ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, E) (minSmoothness ℝ 3) (fun x => (g x₀)⁻¹ * g x) x₀ :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3)).contMDiffAt.comp x₀ hg
  have h1 : (g x₀)⁻¹ * g x₀ = 1 := inv_mul_cancel _
  have hsrc : (chart1 E G).source ∈ 𝓝 ((g x₀)⁻¹ * g x₀) := by
    rw [h1]; exact extChartAt_source_mem_nhds (1 : G)
  have hmem : ∀ᶠ x in 𝓝 x₀, (g x₀)⁻¹ * g x ∈ (chart1 E G).source := hk.continuousAt.preimage_mem_nhds hsrc
  have hch : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) (minSmoothness ℝ 3) (chart1 E G) ((g x₀)⁻¹ * g x₀) := by
    rw [h1]; exact contMDiffAt_extChartAt
  refine ⟨?_, by rw [h1], ?_⟩
  · have := (hch.comp x₀ hk)
    exact (contMDiffAt_iff_contDiffAt.1 this).of_le ((show (2 : ℕ∞ω) ≤ 3 by norm_num).trans le_minSmoothness)
  · filter_upwards [hmem] with x hx
    rw [(chart1 E G).left_inv hx, mul_inv_cancel_left]

namespace PrincipalCocycle

/-- **The transition formula for the curvature** (Svetlichny eq. (63), p. 42): on an overlap `U_i ∩ U_j`, the
local curvatures (62) of potentials satisfying (38) are related by `F_j = Ad_{g_ij} F_i`. -/
theorem lieCurvature_transition [ContinuousMul G] (c : PrincipalCocycle F G) {A : c.ι → F → F →L[ℝ] E}
    (hA : c.IsCompatible 𝓘(ℝ, F) A)
    (hg : ∀ i j, ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    {i j : c.ι} {x₀ : F} (hxi : x₀ ∈ c.U i) (hxj : x₀ ∈ c.U j) (hAd : DifferentiableAt ℝ (A i) x₀) (η ξ : F) :
    lieCurvature 𝓘(ℝ, E) G (A j) x₀ η ξ =
      adjointE 𝓘(ℝ, E) (c.g i j x₀) (lieCurvature 𝓘(ℝ, E) G (A i) x₀ η ξ) := by
  have hU : ((c.U i ⊓ c.U j : TopologicalSpace.Opens F) : Set F) ∈ 𝓝 x₀ :=
    (c.U i ⊓ c.U j).isOpen.mem_nhds ⟨hxi, hxj⟩
  obtain ⟨hγ, hγ0, hge⟩ := chart_form ((hg i j).contMDiffAt hU)
  have hev : A j =ᶠ[𝓝 x₀] lieGaugeTransform (c.g i j) (A i) :=
    Filter.eventually_of_mem hU fun x hx => hA i j x hx.1 hx.2
  rw [lieCurvature_congr hev]
  exact lieCurvature_lieGaugeTransform hγ hγ0 hge hAd η ξ

end PrincipalCocycle

end Lightlike.Gauge
