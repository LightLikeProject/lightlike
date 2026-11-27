import Lightlike.TuraevViro.QSixJ

/-!
# The quantum 6j symbol at a generic angle, and the generic Biedenharn–Elliott identity

At `q = e^{iθ}` the quantum integer is `[n]_θ = sin(nθ)/sin θ`; at `θ = π/r` it is `qnum r n`. This file
defines the q-Racah sum `racahG θ` with `[n]_θ` in place of `qnum r n` (term by term the same formula as
`qRacahSum`), the squared triangle coefficient `delta2G θ a b c = [s-a]! [s-b]! [s-c]! / [s+1]!`, and the
**generic Biedenharn–Elliott identity** `GenBE θ` in a form without square roots: the six triangle
coefficients that do not contain the summed colour are the same on both sides of `Model.BE` and are
divided out, and those that do contain it occur squared.

`GenBE θ a b c d e f p q r'` says: if the six triads `(a,d,p), (c,b,p), (c,f,q), (e,d,q), (e,a,r'), (b,f,r')` are
triangles, then

    Σ_x (-1)^((a+b+c+d+e+f+p+q+r'+x)/2) [x+1]_θ Δ²(a,b,x) Δ²(c,d,x) Δ²(e,f,x)
          · R(a,b,x,c,d,p) R(c,d,x,e,f,q) R(e,f,x,b,a,r')
      = Δ²(p,q,r') R(p,q,r',e,a,d) R(p,q,r',f,b,c),

the sum over every `x` for which `(a,b,x), (c,d,x), (e,f,x)` are triangles (no level bound), `R = racahG θ`,
`Δ² = delta2G θ`. The triad `(p,q,r')` is not assumed to be a triangle: its parity follows from the six, and if a
triangle inequality fails the summation range of `racahG θ p q r' e a d` is empty, so the right side is `0` (and the
left side vanishes too; this case is needed for `qBiedenharnElliott`, where the colours are unrestricted).

Numerical evidence (not proof; mpmath at 40 digits, 150 random tuples with colours `≤ 6`): `GenBE` holds at
`θ = 0.2137` (relative error `≤ 8.5e-40`; 120 further tuples with `(p,q,r')` not a triangle: both sides vanish, error `≤ 1e-36`), and the same sum restricted to the colours admissible at level
`r = 7` holds at `θ = π/7` (relative error `≤ 6.1e-41`). At `θ = π/r` the terms with a colour above the level
do not vanish one by one; they cancel in pairs `x ↔ 2r - 2 - x` in the limit `θ → π/r`.

Roles: `GenBE` is the interface between the Temperley–Lieb pentagon (which proves it at every `θ` with
`sin(nθ) ≠ 0` for the finitely many `n` involved) and the root-of-unity statement `qBiedenharnElliott`
(obtained from it by the limit `θ → π/r`).
-/

open Real Finset Lightlike.Pentagon

namespace Lightlike.TV

/-- The quantum integer `[n]_θ = sin(nθ)/sin θ` at `q = e^{iθ}`. -/
noncomputable def qnG (θ : ℝ) (n : ℕ) : ℝ := sin (n * θ) / sin θ

/-- The quantum factorial `[n]_θ! = Π_{k=1}^n [k]_θ`. -/
noncomputable def qfG (θ : ℝ) (n : ℕ) : ℝ := ∏ k ∈ range n, qnG θ (k + 1)

/-- `1/[u]_θ!` for `u ≥ 0`, else `0`. -/
noncomputable def invQFG (θ : ℝ) (u : ℤ) : ℝ := if 0 ≤ u then (qfG θ u.toNat)⁻¹ else 0

/-- The summand of the q-Racah formula at the angle `θ` (the same formula as `qRacahTerm`). -/
noncomputable def racahTermG (θ : ℝ) (α₁ α₂ α₃ α₄ β₁ β₂ β₃ : ℤ) (z : ℕ) : ℝ :=
  (-1 : ℝ) ^ z * qfG θ (z + 1) *
    (invQFG θ (z - α₁) * invQFG θ (z - α₂) * invQFG θ (z - α₃) * invQFG θ (z - α₄) *
      (invQFG θ (β₁ - z) * invQFG θ (β₂ - z) * invQFG θ (β₃ - z)))

/-- The q-Racah sum at the angle `θ` (the same formula and range as `qRacahSum`). -/
noncomputable def racahG (θ : ℝ) (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  ∑ z ∈ range (j₁ + j₂ + j₃ + j₄ + j₅ + j₆ + 1),
    racahTermG θ (((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ) (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ) (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)
      (((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ) (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ)
      (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ) z

/-- The squared triangle coefficient `Δ(a,b,c)² = [s-a]! [s-b]! [s-c]! / [s+1]!`, `s = (a+b+c)/2`. -/
noncomputable def delta2G (θ : ℝ) (a b c : ℕ) : ℝ :=
  qfG θ ((a + b + c) / 2 - a) * qfG θ ((a + b + c) / 2 - b) * qfG θ ((a + b + c) / 2 - c) /
    qfG θ ((a + b + c) / 2 + 1)

open Classical in
/-- The summand of the generic Biedenharn–Elliott identity at the middle colour `x` (zero unless the three
triads containing `x` are triangles). -/
noncomputable def genBETerm (θ : ℝ) (a b c d e f p q r' x : ℕ) : ℝ :=
  if Tri a b x ∧ Tri c d x ∧ Tri e f x then
    (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r' + x) / 2) * qnG θ (x + 1) *
      (delta2G θ a b x * delta2G θ c d x * delta2G θ e f x) *
      (racahG θ a b x c d p * racahG θ c d x e f q * racahG θ e f x b a r')
  else 0

/-- **The generic Biedenharn–Elliott identity** at the angle `θ`, for one tuple of colours, without square
roots (see the module docstring). The sum runs over `x ≤ a + b`, which contains every triangle `(a,b,x)`. -/
def GenBE (θ : ℝ) (a b c d e f p q r' : ℕ) : Prop :=
  Tri a d p → Tri c b p → Tri c f q → Tri e d q → Tri e a r' → Tri b f r' →
    ∑ x ∈ range (a + b + 1), genBETerm θ a b c d e f p q r' x =
      delta2G θ p q r' * racahG θ p q r' e a d * racahG θ p q r' f b c

end Lightlike.TV
