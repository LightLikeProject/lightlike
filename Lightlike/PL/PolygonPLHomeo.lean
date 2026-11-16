import Lightlike.PL.PolygonBoundary
import Lightlike.PL.Image
import Lightlike.PL.StellarHomeo

/-!
# The region of a polygon is PL homeomorphic to a triangle

Sketch (not imported; statements only). The triangulation of the region of a simple polygon is a
geometric complex `K` in the plane that is a PL ball, so abstractly stellar equivalent to a
simplex. Stellar equivalent complexes are PL homeomorphic (`PLHomeomorphic.of_stellarEquivIn`), for
the canonical realisations `K.real`. The plan transports this to the plane:

1. For a geometric complex `K` in a real vector space `E` with vertex type `E`, the linear map
   `g : (E →₀ ℝ) → E`, `x ↦ ∑ x v • v`, is a PL homeomorphism from `K.real` onto `K`
   (`isPLHomeo_real_geom`): linear, hence piecewise linear, surjective onto `|K|`, and injective
   by uniqueness of barycentric coordinates in the geometric complex.
2. Relabel the vertices of the abstract simplex to those of a planar triangle (`PLHomeomorphic.map`
   along a permutation extending the bijection of the vertex sets).
3. Compose with `IsPLHomeo.symm` and `IsPLHomeo.trans` (`Lightlike/PL/Image.lean`).
-/

open Set

namespace Lightlike.PL
namespace Polygon

variable {n : ℕ}

/-- **The region of a simple polygon is PL homeomorphic to a triangle.** -/
theorem polygon_plHomeo_triangle (p : Polygon n) (hn : 3 ≤ n) (hs : p.IsSimple) :
    ∃ (K L : SComplex (ℝ × ℝ)) (f : ℝ × ℝ → ℝ × ℝ),
      K.space = p.inside ∪ p.carrier ∧ SComplex.IsPLHomeo K L f ∧
        ∃ a b c : ℝ × ℝ, AffineIndependent ℝ ![a, b, c] ∧
          L = SComplex.simplex {a, b, c} := by
  sorry

end Polygon

end Lightlike.PL
