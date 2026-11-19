import Lightlike.GR.KruskalInextendible
import Lightlike.Geodesic.Gauss

/-!
# The Kruskal–Szekeres spacetime is inextendible

Gap row G1-020: **maximality of the Kruskal extension**. The Kruskal manifold `{X² - T² > -1} × S²` with the
Kruskal metric (`kruskalManifoldMetric`) has no extension to a connected Hausdorff Lorentzian manifold with a
smooth metric (`kruskal_isInextendible`, in the sense of `IsInextendible`).

Proof. In an extension, take a point `p` of the closure of the image that is not in the image (the image is
open and not everything, the target is connected). A normal chart at `p` (`exists_isNormalChart`) covers a
neighbourhood of `p`, which contains a point `q` of the image; the radial geodesic from `p` to `q`, reversed,
starts in the image and leaves it, which `IsLorentzianExtension.false_of_geodesic_kruskal` excludes.

The argument follows the outline in J. Sbierski, arXiv:1507.00601, Section 1.3: every inextendible geodesic of
the Kruskal manifold is complete or runs into the curvature singularity. Here the statement is smooth
(`C^∞`) inextendibility; the `C⁰`-inextendibility proved in that paper is stronger and is not formalized.
-/

open Matrix Real Set Filter Topology Manifold TopologicalSpace Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

open Lightlike.Geodesic

variable {M : ℝ}

/-- The Kruskal manifold is not empty. -/
lemma kruskalC_nonempty : (kruskalC).Nonempty := by
  refine ⟨![0, 1, 0, 0], ?_, ?_⟩
  · show 0 < rhoSq ![0, 1, 0, 0]
    simp [rhoSq]
  · show -1 < sC ![0, 1, 0, 0]
    simp [sC, rhoSq]

/-- **The Kruskal–Szekeres spacetime is inextendible** (maximality of the Kruskal extension). -/
theorem kruskal_isInextendible (hM : 0 < M) : IsInextendible (kruskalManifoldMetric M hM) := by
  intro M' _ _ _ _ g' ι hext
  haveI := hext.connected
  -- a boundary point of the image
  have hopen : IsOpen (range ι) := hext.isOpenEmbedding.isOpen_range
  obtain ⟨p, hpcl, hpn⟩ : ∃ p, p ∈ closure (range ι) ∧ p ∉ range ι := by
    by_contra hcon
    push Not at hcon
    have hclosed : IsClosed (range ι) := closure_subset_iff_isClosed.1 fun p hp => hcon p hp
    obtain ⟨z, hz⟩ := kruskalC_nonempty
    exact hext.proper (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨ι ⟨z, hz⟩, mem_range_self _⟩)
  set e := extChartAt 𝓘(ℝ, Fin 4 → ℝ) p with he
  have hG := g'.isCoordMetric_coordMetric p
  obtain ⟨ρ, φ, hφ⟩ := exists_isNormalChart hG (mem_extChartAt_target (I := 𝓘(ℝ, Fin 4 → ℝ)) p)
  have h0src : (0 : Fin 4 → ℝ) ∈ φ.source := by
    rw [hφ.source_eq]; exact mem_ball_self hφ.pos
  have hxt : e p ∈ φ.target := by
    rw [← hφ.map_zero]; exact φ.map_source h0src
  -- a point of the image in the normal neighbourhood
  have hW : e.source ∩ e ⁻¹' φ.target ∈ 𝓝 p :=
    inter_mem ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin 4 → ℝ)) p).mem_nhds
      (mem_extChartAt_source (I := 𝓘(ℝ, Fin 4 → ℝ)) p))
      ((continuousAt_extChartAt (I := 𝓘(ℝ, Fin 4 → ℝ)) p).preimage_mem_nhds
        (φ.open_target.mem_nhds hxt))
  obtain ⟨q, ⟨hqsrc, hqφ⟩, hqr⟩ := mem_closure_iff_nhds.1 hpcl _ hW
  set v := φ.symm (e q) with hv
  have hvsrc : v ∈ φ.source := φ.map_target hqφ
  have hvball : v ∈ ball (0 : Fin 4 → ℝ) ρ := by rw [← hφ.source_eq]; exact hvsrc
  have hφv : φ v = e q := φ.right_inv hqφ
  obtain ⟨γ, w, hγ0, -, hγ1, hγgeo, hγφ⟩ := hφ.geodesic v hvball
  -- the reversed geodesic
  have hrev := (hγgeo.scale (-1)).shift 1
  have hmem : ∀ t ∈ Ioo (-1 : ℝ) 2, t ∈ (fun t : ℝ => t - 1) ⁻¹' ((fun t : ℝ => -1 * t) ⁻¹' Ioo (-1) 2) :=
    fun t ht => ⟨by show -1 < -1 * (t - 1); linarith [ht.2], by show -1 * (t - 1) < 2; linarith [ht.1]⟩
  have hσ : IsGeodesicOn (g'.coordMetric p) (fun t => γ (-1 * (t - 1)))
      (fun t => (-1 : ℝ) • w (-1 * (t - 1))) (Ioo (-1) 2) :=
    ⟨fun t ht => hrev.pos t (hmem t ht), fun t ht => hrev.vel t (hmem t ht)⟩
  refine hext.false_of_geodesic_kruskal hM p hσ (fun s hs => ?_) ?_ ?_
  · -- the geodesic stays in the chart
    have hs' : -1 * (s - 1) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    show γ (-1 * (s - 1)) ∈ e.target
    rw [hγφ _ hs']
    refine hφ.target_subset (φ.map_source ?_)
    rw [hφ.source_eq, mem_ball_zero_iff, norm_smul]
    have h1 : ‖-1 * (s - 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; exact hs'
    calc ‖-1 * (s - 1)‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ < ρ := mem_ball_zero_iff.1 hvball
  · show e.symm (γ (-1 * (0 - 1))) ∈ range ι
    rw [show (-1 : ℝ) * (0 - 1) = 1 by norm_num, hγ1, hφv, e.left_inv hqsrc]
    exact hqr
  · show e.symm (γ (-1 * (1 - 1))) ∉ range ι
    rw [show (-1 : ℝ) * (1 - 1) = 0 by norm_num, hγ0,
      e.left_inv (mem_extChartAt_source (I := 𝓘(ℝ, Fin 4 → ℝ)) p)]
    exact hpn

end Lightlike
