import Mathlib
import Lightlike.Regge.CMS.Angle

/-!
# The first variation of a triangle angle

`triAngle a b c` is the angle opposite the side of squared length `c`, between the sides of squared
lengths `a` and `b`. For a nondegenerate triangle (`D = 4ab - (a + b - c)² > 0`) the angle is
differentiable in the three squared lengths, with partial derivatives
`∂c = 1/√D`, `∂a = -(a - b + c)/(2a√D)`, `∂b = -(b - a + c)/(2b√D)`; here `√D = 4 ·` area.
-/

open Real Lightlike.CMS

namespace Lightlike.Regge.Linear

/-- The discriminant `D = 4ab - (a + b - c)²` of a triangle with squared sides `a, b, c`
(`D = 16 ·` area²). -/
def disc (a b c : ℝ) : ℝ := 4 * a * b - (a + b - c) ^ 2

/-- **First variation of a triangle angle.** Along the line of squared lengths
`(a + ε a₁, b + ε b₁, c + ε c₁)` the angle has derivative at `ε = 0` equal to
`(2 c₁ - (a - b + c) a₁ / a - (b - a + c) b₁ / b) / (2 √D)`. -/
theorem hasDerivAt_triAngle {a b c a₁ b₁ c₁ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hD : 0 < disc a b c) :
    HasDerivAt (fun ε : ℝ => triAngle (a + ε * a₁) (b + ε * b₁) (c + ε * c₁))
      ((2 * c₁ - (a - b + c) * a₁ / a - (b - a + c) * b₁ / b) / (2 * √(disc a b c))) 0 := by
  have hab : 0 < a * b := mul_pos ha hb
  have hsq : 0 < √(a * b) := Real.sqrt_pos.mpr hab
  have hA : HasDerivAt (fun ε : ℝ => a + ε * a₁) a₁ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const a₁).const_add a
  have hB : HasDerivAt (fun ε : ℝ => b + ε * b₁) b₁ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const b₁).const_add b
  have hC : HasDerivAt (fun ε : ℝ => c + ε * c₁) c₁ 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const c₁).const_add c
  have hP : HasDerivAt (fun ε : ℝ => (a + ε * a₁) * (b + ε * b₁)) (a₁ * b + a * b₁) 0 := by
    convert hA.mul hB using 1; simp
  have hS : HasDerivAt (fun ε : ℝ => √((a + ε * a₁) * (b + ε * b₁)))
      ((a₁ * b + a * b₁) / (2 * √(a * b))) 0 := by
    have := hP.sqrt (by simpa using hab.ne')
    simpa using this
  have hN : HasDerivAt (fun ε : ℝ => (a + ε * a₁) + (b + ε * b₁) - (c + ε * c₁))
      (a₁ + b₁ - c₁) 0 := hA.add hB |>.sub hC
  have hQ : HasDerivAt (fun ε : ℝ => ((a + ε * a₁) + (b + ε * b₁) - (c + ε * c₁)) /
      (2 * √((a + ε * a₁) * (b + ε * b₁)))) _ 0 :=
    hN.div (hS.const_mul 2) (by simpa using hsq.ne')
  have hx : ((a + b - c) / (2 * √(a * b))) ^ 2 < 1 := by
    have h4 : (2 * √(a * b)) ^ 2 = 4 * (a * b) := by
      rw [mul_pow, Real.sq_sqrt hab.le]; ring
    rw [div_pow, h4, div_lt_one (by positivity)]
    unfold disc at hD; nlinarith
  have hne1 : (a + b - c) / (2 * √(a * b)) ≠ 1 := fun h => by rw [h] at hx; simp at hx
  have hne2 : (a + b - c) / (2 * √(a * b)) ≠ -1 := fun h => by rw [h] at hx; simp at hx
  have hne1' : (a + 0 * a₁ + (b + 0 * b₁) - (c + 0 * c₁)) / (2 * √((a + 0 * a₁) * (b + 0 * b₁)))
      ≠ 1 := by simpa using hne1
  have hne2' : (a + 0 * a₁ + (b + 0 * b₁) - (c + 0 * c₁)) / (2 * √((a + 0 * a₁) * (b + 0 * b₁)))
      ≠ -1 := by simpa using hne2
  have := HasDerivAt.scomp (0:ℝ) (hasDerivAt_arccos hne2' hne1') hQ
  convert this using 1
  · ext ε; simp [triAngle]
  · simp only [add_zero, zero_mul]
    have h4 : 1 - ((a + b - c) / (2 * √(a * b))) ^ 2 = disc a b c / (4 * (a * b)) := by
      have : (2 * √(a * b)) ^ 2 = 4 * (a * b) := by
        rw [mul_pow, Real.sq_sqrt hab.le]; ring
      rw [div_pow, this, disc]; field_simp
    rw [h4, Real.sqrt_div hD.le, show (4 * (a * b)) = (2 * √(a * b)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt hab.le]; ring, Real.sqrt_sq (by positivity)]
    have hsD : 0 < √(disc a b c) := Real.sqrt_pos.mpr hD
    have hs2 : √(a * b) ^ 2 = a * b := Real.sq_sqrt hab.le
    simp only [smul_eq_mul]
    field_simp
    rw [hs2]
    ring

end Lightlike.Regge.Linear
