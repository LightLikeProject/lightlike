import Mathlib
import Lightlike.Regge.Linearized.ThinKite

/-!
# Consistency of the linearized deficit is uniform over non-fat stars (polar gauge)

The perturbation `h = (x dy - y dx)²` of the flat plane (a constant-curvature direction
at the origin) gives, along an edge `p → q`, the integrated squared-length change
`∫ (x e₂ - y e₁)² dt = (p × q)²`, because `p(t) × (q - p) = p × q` is constant; spokes from the
origin get `0`. The first variation of the angle at the origin in the triangle `(0, p, q)`
is then `(p × q)² / (2 √D) = |p × q| / 2`, the area of the triangle, whatever its shape
(`√D = 2 |p × q|`).

So the linearized deficit at a vertex equals minus the area of its star: the
"curvature times area" law holds with a constant independent of the fatness of the star. In
contrast with `Lightlike.Regge.Linearized.kiteDeficit_hasDerivAt`, the unit sensitivity `-2/η` of
a thin kite is multiplied by data of size `η²`, which is why consistency of smooth data does not
fail at vertices of thin stars; non-fat triangulations fail through the uncontrolled
sensitivity to the data (stability), not through the vertex consistency estimate.
-/

open Real Lightlike.CMS

namespace Lightlike.Regge.Linearized

open Lightlike.Regge.Linear

/-- Cross product of two plane vectors. -/
def cross2 (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

/-- Squared length of a plane vector. -/
def sqn (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- The angle at the origin of the triangle `(0, p, q)` when the squared length of the outer edge
is perturbed by `ε (p × q)²` (polar-gauge data). -/
noncomputable def polarAngle (p q : ℝ × ℝ) (ε : ℝ) : ℝ :=
  triAngle (sqn p + ε * 0) (sqn q + ε * 0) (sqn (p - q) + ε * cross2 p q ^ 2)

/-- The discriminant of a triangle `(0, p, q)` is `4 (p × q)²`. -/
theorem disc_sqn (p q : ℝ × ℝ) : disc (sqn p) (sqn q) (sqn (p - q)) = 4 * cross2 p q ^ 2 := by
  unfold disc sqn cross2
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **Polar-gauge first variation equals the area.** For a nondegenerate triangle `(0, p, q)`
of any shape, the derivative of the angle at the origin in the polar-gauge perturbation is
`|p × q| / 2`, the area of the triangle. -/
theorem polarAngle_hasDerivAt (p q : ℝ × ℝ) (hp : p ≠ 0) (hq : q ≠ 0) (hk : cross2 p q ≠ 0) :
    HasDerivAt (polarAngle p q) (|cross2 p q| / 2) 0 := by
  have hpa : 0 < sqn p := by
    unfold sqn
    rcases eq_or_ne p.1 0 with h1 | h1
    · have : p.2 ≠ 0 := fun h2 => hp (Prod.ext h1 h2)
      positivity
    · positivity
  have hqa : 0 < sqn q := by
    unfold sqn
    rcases eq_or_ne q.1 0 with h1 | h1
    · have : q.2 ≠ 0 := fun h2 => hq (Prod.ext h1 h2)
      positivity
    · positivity
  have hD : 0 < disc (sqn p) (sqn q) (sqn (p - q)) := by
    rw [disc_sqn]; positivity
  have hder := hasDerivAt_triAngle (a := sqn p) (b := sqn q) (c := sqn (p - q)) (a₁ := 0) (b₁ := 0)
    (c₁ := cross2 p q ^ 2) hpa hqa hD
  have hroot : √(disc (sqn p) (sqn q) (sqn (p - q))) = 2 * |cross2 p q| := by
    rw [disc_sqn, show 4 * cross2 p q ^ 2 = (2 * cross2 p q) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_mul, abs_two]
  rw [hroot] at hder
  have habs : 0 < |cross2 p q| := abs_pos.mpr hk
  refine hder.congr_deriv ?_
  rw [← sq_abs (cross2 p q)]
  field_simp
  ring

/-- **Closed star in the polar gauge.** For any finite family of nondegenerate triangles
`(0, pᵢ, qᵢ)` around the origin (any shapes), the deficit `2π - Σ θᵢ` under the polar-gauge data
has derivative `-Σ |pᵢ × qᵢ| / 2`: minus the area of the star. -/
theorem polarStarDeficit_hasDerivAt {n : ℕ} (p q : Fin n → ℝ × ℝ) (hp : ∀ i, p i ≠ 0)
    (hq : ∀ i, q i ≠ 0) (hk : ∀ i, cross2 (p i) (q i) ≠ 0) :
    HasDerivAt (fun ε : ℝ => 2 * π - ∑ i, polarAngle (p i) (q i) ε)
      (-∑ i, |cross2 (p i) (q i)| / 2) 0 := by
  have hs := HasDerivAt.sum (u := Finset.univ) (A := fun i ε => polarAngle (p i) (q i) ε)
    (A' := fun i => |cross2 (p i) (q i)| / 2) (x := (0 : ℝ))
    (fun i _ => polarAngle_hasDerivAt (p i) (q i) (hp i) (hq i) (hk i))
  have := (hs.const_sub (2 * π))
  simpa [Finset.sum_div] using this

/-- **Thin kite, polar data.** The kite deficit under data `ε η²` (the polar-gauge size for
the four triangles `(1,0),(0,η)`) has derivative `-2 η`, which tends to `0` with `η`, while
the unit sensitivity is `-2/η` (`kiteDeficit_hasDerivAt`). -/
theorem kiteDeficit_polar_hasDerivAt (η : ℝ) (hη : 0 < η) :
    HasDerivAt (fun ε : ℝ => kiteDeficit η (ε * η ^ 2)) (-(2 * η)) 0 := by
  have h1 := kiteDeficit_hasDerivAt η hη
  have h2 : HasDerivAt (fun ε : ℝ => ε * η ^ 2) (η ^ 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (η ^ 2)
  have h3 := h1.scomp_of_eq (0 : ℝ) h2 (by simp)
  refine h3.congr_deriv ?_
  simp only [smul_eq_mul]
  field_simp

end Lightlike.Regge.Linearized
