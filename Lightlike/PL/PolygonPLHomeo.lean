import Lightlike.PL.PolygonBoundary
import Lightlike.PL.RealGeom
import Lightlike.PL.Relabel

/-!
# The region of a polygon is PL homeomorphic to a triangle

The triangulation of the region of a simple polygon is a geometric complex `K` in the plane that is
a PL ball, so stellar equivalent to a simplex. Stellar equivalent complexes are PL homeomorphic
(Lickorish, proof of Theorem 4.5) for the canonical realisations `K.real`; a geometric complex is
PL homeomorphic to its canonical realisation (`SComplex.isPLHomeo_real_geom`); and the simplex on
any three vertices is PL homeomorphic to the simplex on the vertices of a planar triangle
(`SComplex.PLHomeomorphic.of_isPLBallIn`). Composing gives a PL homeomorphism of the region onto a
triangle.

## Main results

* `Lightlike.PL.Polygon.polygon_plHomeo_triangle`
-/

open Set

namespace Lightlike.PL
namespace Polygon

/-- The standard planar triangle is affinely independent. -/
lemma affineIndependent_std_triangle :
    AffineIndependent ℝ ![((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro h
  rw [collinear_iff_of_mem (p₀ := ((0 : ℝ), (0 : ℝ))) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, hr⟩ := hv (1, 0) (by simp)
  obtain ⟨t, ht⟩ := hv (0, 1) (by simp)
  simp [Prod.ext_iff] at hr ht
  obtain ⟨h1, h2⟩ := hr
  obtain ⟨h3, h4⟩ := ht
  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · rw [h2] at h1; simp at h1
  · rw [h2] at h1; simp at h1
  · rw [h3] at h4; simp at h4
  · rw [h2] at h4; simp at h4

/-- **The region of a simple polygon is PL homeomorphic to a triangle.** The closed region bounded
by a simple closed polygon in the plane is the underlying set of a geometric complex that is
piecewise linearly homeomorphic to the triangle with vertices `(0,0)`, `(1,0)`, `(0,1)`. The
homeomorphism is not shown to map the polygon onto the boundary of the triangle. -/
theorem polygon_plHomeo_triangle {n : ℕ} (p : Polygon n) (hn : 3 ≤ n) (hs : p.IsSimple) :
    ∃ (K : SComplex (ℝ × ℝ)) (f : ℝ × ℝ → ℝ × ℝ), K.space = p.inside ∪ p.carrier ∧
      SComplex.IsPLHomeo K (SComplex.simplex {((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)}) f := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨T, hT, hU, hN, hB⟩ := exists_ball_triangulation n p hn hs
  obtain ⟨m, hm⟩ := hB
  set K := SComplex.closure T with hK
  -- the ball has dimension two
  have hex : ∃ t ∈ T, True := by
    obtain ⟨t, ht, -⟩ := SComplex.mem_closure.1 (hT.2.2.2 ⟨0, by omega⟩)
    exact ⟨t, ht, trivial⟩
  obtain ⟨t, ht, -⟩ := hex
  have hmax : K.maxCard = 3 := by
    refine le_antisymm (SComplex.maxCard_le fun s hs' => ?_) ?_
    · obtain ⟨t', ht', hst⟩ := SComplex.mem_closure.1 hs'
      exact (Finset.card_le_card hst).trans (hT.1 t' ht').1.le
    · have := SComplex.card_le_maxCard (K := K) (SComplex.mem_closure.2 ⟨t, ht, subset_rfl⟩)
      rwa [(hT.1 t ht).1] at this
  have hm2 : m = 2 := by
    have := hm.maxCard
    omega
  set B : Finset (ℝ × ℝ) := {((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} with hBdef
  have hBcard : B.card = m + 1 := by
    rw [hm2, hBdef]
    simp [Finset.card_insert_of_notMem, Prod.ext_iff]
  have hind : AffineIndependent ℝ ((↑) : B → ℝ × ℝ) := by
    have h1 := affineIndependent_std_triangle.range
    have hset : (B : Set (ℝ × ℝ)) = Set.range ![((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)] := by
      ext y
      simp [hBdef]
      tauto
    rwa [← hset] at h1
  have hKgeom : SComplex.IsGeom K := hT.2.1
  have hBgeom : SComplex.IsGeom (SComplex.simplex B) := SComplex.isGeom_simplex hind
  obtain ⟨f, hf⟩ := SComplex.PLHomeomorphic.of_isPLBallIn hm hBcard
  have h1 := (SComplex.isPLHomeo_real_geom hKgeom).symm
  have h2 := h1.trans hf
  have h3 := h2.trans (SComplex.isPLHomeo_real_geom hBgeom)
  exact ⟨K, _, hT.2.2.1, h3⟩

end Polygon

end Lightlike.PL
