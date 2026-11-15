import Mathlib
import Lightlike.Regge.Dihedral

/-!
# The first variation of a dihedral angle in the squared lengths

For a tetrahedron `pqrs` with squared edge lengths `a = pq², b = pr², c = qr², d = ps², e = qs²,
f = rs²`, the dihedral angle at `pq` is `arccos (cosSq a b c d e f)`, where
`cosSq = Nn / √(Pp a b c · Pp a d e)` is the formula of `Lightlike.PR.cosDihedral` written in the
squared lengths. Along a line of squared lengths `(a + ε a₁, …, f + ε f₁)` the angle is
differentiable at `ε = 0` with an explicit derivative, as long as the angle is neither `0` nor `π`
and both faces at the edge are non-degenerate.

## Main results

* `cosDihedral_sqrt`: `cosDihedral` of the square roots is `cosSq`.
* `hasDerivAt_dihSq`: the derivative of the dihedral angle along a line of squared lengths.
-/

open Real Lightlike.PR

namespace Lightlike.Regge.Conv3

/-- The numerator of the cosine of the dihedral angle at `pq`, in squared lengths. -/
noncomputable def Nn (a b c d e f : ℝ) : ℝ :=
  (b + d - f) / 2 - (b + a - c) * (d + a - e) / (4 * a)

/-- The squared height of `r` over the line `pq`, in squared lengths (`= disc / 4a`). -/
noncomputable def Pp (a b c : ℝ) : ℝ := b - (b + a - c) ^ 2 / (4 * a)

/-- The cosine of the dihedral angle at `pq` from the squared lengths. -/
noncomputable def cosSq (a b c d e f : ℝ) : ℝ := Nn a b c d e f / √(Pp a b c * Pp a d e)

/-- The dihedral angle at `pq` from the squared lengths. -/
noncomputable def dihSq (a b c d e f : ℝ) : ℝ := arccos (cosSq a b c d e f)

/-- `cosDihedral` of the square roots of the squared lengths is `cosSq`. -/
theorem cosDihedral_sqrt {a b c d e f : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) :
    cosDihedral (√a) (√b) (√c) (√d) (√e) (√f) = cosSq a b c d e f := by
  have h1 : (√a) ^ 2 = a := sq_sqrt ha.le
  have h2 : (√b) ^ 2 = b := sq_sqrt hb
  have h3 : (√c) ^ 2 = c := sq_sqrt hc
  have h4 : (√d) ^ 2 = d := sq_sqrt hd
  have h5 : (√e) ^ 2 = e := sq_sqrt he
  have h6 : (√f) ^ 2 = f := sq_sqrt hf
  have hs : √a ≠ 0 := (sqrt_pos.mpr ha).ne'
  unfold cosDihedral cosSq Nn Pp
  simp only [h1, h2, h3, h4, h5, h6]
  have e1 : (b + a - c) / (2 * √a) * ((d + a - e) / (2 * √a)) = (b + a - c) * (d + a - e) / (4 * a) := by
    rw [div_mul_div_comm, show 2 * √a * (2 * √a) = 4 * a by nlinarith [h1]]
  have e2 : ((b + a - c) / (2 * √a)) ^ 2 = (b + a - c) ^ 2 / (4 * a) := by
    rw [div_pow, mul_pow, h1]; ring
  have e3 : ((d + a - e) / (2 * √a)) ^ 2 = (d + a - e) ^ 2 / (4 * a) := by
    rw [div_pow, mul_pow, h1]; ring
  rw [e1, e2, e3]

/-- Derivative of `u / √(v w)` at `0`. -/
theorem hasDerivAt_div_sqrt {u v w : ℝ → ℝ} {u' v' w' : ℝ} (hu : HasDerivAt u u' 0)
    (hv : HasDerivAt v v' 0) (hw : HasDerivAt w w' 0) (hv0 : 0 < v 0) (hw0 : 0 < w 0) :
    HasDerivAt (fun ε => u ε / √(v ε * w ε))
      ((u' * √(v 0 * w 0) - u 0 * ((v' * w 0 + v 0 * w') / (2 * √(v 0 * w 0)))) /
        √(v 0 * w 0) ^ 2) 0 := by
  have hp : 0 < v 0 * w 0 := mul_pos hv0 hw0
  have hs := (hv.mul hw).sqrt hp.ne'
  exact hu.div hs (sqrt_pos.mpr hp).ne'

/-- Derivative of `arccos (u / √(v w))` at `0`, when the value is not `±1`. -/
theorem hasDerivAt_arccos_div_sqrt {u v w : ℝ → ℝ} {u' v' w' : ℝ} (hu : HasDerivAt u u' 0)
    (hv : HasDerivAt v v' 0) (hw : HasDerivAt w w' 0) (hv0 : 0 < v 0) (hw0 : 0 < w 0)
    (h1 : u 0 / √(v 0 * w 0) ≠ 1) (h2 : u 0 / √(v 0 * w 0) ≠ -1) :
    HasDerivAt (fun ε => arccos (u ε / √(v ε * w ε)))
      (-(1 / √(1 - (u 0 / √(v 0 * w 0)) ^ 2)) *
        ((u' * √(v 0 * w 0) - u 0 * ((v' * w 0 + v 0 * w') / (2 * √(v 0 * w 0)))) /
          √(v 0 * w 0) ^ 2)) 0 := by
  have := (hasDerivAt_arccos h2 h1).scomp (0 : ℝ) (hasDerivAt_div_sqrt hu hv hw hv0 hw0)
  convert this using 1
  all_goals first | rfl | (simp only [smul_eq_mul]; ring)

/-- The derivative of `Nn` along the line `(a + ε a₁, …, f + ε f₁)`. -/
noncomputable def Nn' (a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) : ℝ :=
  (b₁ + d₁ - f₁) / 2 -
    (((b₁ + a₁ - c₁) * (d + a - e) + (b + a - c) * (d₁ + a₁ - e₁)) * (4 * a) -
      (b + a - c) * (d + a - e) * (4 * a₁)) / (4 * a) ^ 2

/-- The derivative of `Pp` along the line `(a + ε a₁, b + ε b₁, c + ε c₁)`. -/
noncomputable def Pp' (a b c a₁ b₁ c₁ : ℝ) : ℝ :=
  b₁ - (2 * (b + a - c) * (b₁ + a₁ - c₁) * (4 * a) - (b + a - c) ^ 2 * (4 * a₁)) / (4 * a) ^ 2

private lemma hasDerivAt_lin (x x₁ : ℝ) : HasDerivAt (fun ε : ℝ => x + ε * x₁) x₁ 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x₁).const_add x

theorem hasDerivAt_Nn {a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun ε => Nn (a + ε * a₁) (b + ε * b₁) (c + ε * c₁) (d + ε * d₁) (e + ε * e₁)
      (f + ε * f₁)) (Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁) 0 := by
  have hA := hasDerivAt_lin a a₁
  have hB := hasDerivAt_lin b b₁
  have hC := hasDerivAt_lin c c₁
  have hD := hasDerivAt_lin d d₁
  have hE := hasDerivAt_lin e e₁
  have hF := hasDerivAt_lin f f₁
  have h1 := ((hB.add hD).sub hF).div_const 2
  have h2 := (((hB.add hA).sub hC).mul ((hD.add hA).sub hE))
  have h3 := h2.div (hA.const_mul 4) (by simpa using ha)
  have := h1.sub h3
  convert this using 1
  · funext ε
    simp only [Nn, Pi.sub_apply, Pi.add_apply, Pi.div_apply, Pi.mul_apply]
  · simp only [Nn', Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
    simp

theorem hasDerivAt_Pp {a b c a₁ b₁ c₁ : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun ε => Pp (a + ε * a₁) (b + ε * b₁) (c + ε * c₁)) (Pp' a b c a₁ b₁ c₁) 0 := by
  have hA := hasDerivAt_lin a a₁
  have hB := hasDerivAt_lin b b₁
  have hC := hasDerivAt_lin c c₁
  have h2 := ((hB.add hA).sub hC).pow 2
  have h3 := h2.div (hA.const_mul 4) (by simpa using ha)
  have := hB.sub h3
  convert this using 1
  · funext ε
    simp only [Pp, Pi.sub_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply]
  · simp only [Pp', Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
    simp

/-- The derivative of `dihSq` along the line `(a + ε a₁, …, f + ε f₁)` at `ε = 0`, in closed form
(the chain rule through `arccos`, the quotient and the square root). -/
noncomputable def dihSq' (a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ) : ℝ :=
  -(1 / √(1 - (Nn a b c d e f / √(Pp a b c * Pp a d e)) ^ 2)) *
    ((Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ * √(Pp a b c * Pp a d e) -
        Nn a b c d e f * ((Pp' a b c a₁ b₁ c₁ * Pp a d e + Pp a b c * Pp' a d e a₁ d₁ e₁) /
          (2 * √(Pp a b c * Pp a d e)))) / √(Pp a b c * Pp a d e) ^ 2)

/-- **First variation of a dihedral angle in the squared edge lengths.** Along the line
`(a + ε a₁, …, f + ε f₁)` of squared lengths, the dihedral angle `dihSq` has the derivative
`dihSq'` at `ε = 0`, as long as the two faces at the edge are non-degenerate (`Pp > 0`) and the
angle is not `0` or `π`. -/
theorem hasDerivAt_dihSq {a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ} (ha : a ≠ 0)
    (hP1 : 0 < Pp a b c) (hP2 : 0 < Pp a d e)
    (h1 : cosSq a b c d e f ≠ 1) (h2 : cosSq a b c d e f ≠ -1) :
    HasDerivAt (fun ε => dihSq (a + ε * a₁) (b + ε * b₁) (c + ε * c₁) (d + ε * d₁)
      (e + ε * e₁) (f + ε * f₁)) (dihSq' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁) 0 := by
  have hN := hasDerivAt_Nn (a := a) (b := b) (c := c) (d := d) (e := e) (f := f)
    (a₁ := a₁) (b₁ := b₁) (c₁ := c₁) (d₁ := d₁) (e₁ := e₁) (f₁ := f₁) ha
  have hP := hasDerivAt_Pp (a := a) (b := b) (c := c) (a₁ := a₁) (b₁ := b₁) (c₁ := c₁) ha
  have hQ := hasDerivAt_Pp (a := a) (b := d) (c := e) (a₁ := a₁) (b₁ := d₁) (c₁ := e₁) ha
  have := hasDerivAt_arccos_div_sqrt hN hP hQ (by simpa using hP1) (by simpa using hP2)
    (by simpa [cosSq] using h1) (by simpa [cosSq] using h2)
  simpa [dihSq, cosSq, dihSq'] using this

end Lightlike.Regge.Conv3
