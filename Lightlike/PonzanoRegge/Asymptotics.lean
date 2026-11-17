module

public import Lightlike.PonzanoRegge.BiedenharnElliott
public import Mathlib

/-!
# The Ponzano–Regge asymptotic formula (statement)

For large spins the 6j symbol is governed by the Euclidean tetrahedron with edge lengths
`j + ½` (Ponzano–Regge 1968). This is the Ponzano–Regge form of Roberts' Theorem 1 (*Geom. Topol.*
3 (1999) 21); Roberts' theorem itself uses the unshifted tetrahedron, and the two forms are
equivalent by his §6.1 (Schläfli identity), an extra step that a proof here has to carry:

  `{6j}(λ j) ≈ cos(Σ_e (λ j_e + ½) θ_e + π/4) / √(12 π V)`,

with `V` the volume and `θ_e` the exterior dihedral angles. The phase is the **Regge action** of
the tetrahedron, discrete general relativity. This is the semiclassical link from the quantum
amplitude back to classical gravity.

This file **states** the formula precisely (`PonzanoReggeFormula`) and audits the geometry. The
proof is `Lightlike.Asymptotics.ponzanoReggeFormula` (Lightlike/Asymptotics/SaddleAssembly.lean), through
the large-spin asymptotics of the Racah sum.

* `vol2`: the squared volume from the six edge lengths (Euler–Tartaglia).
* `dihedral`: the interior dihedral angle at an edge, from the lengths.
* Audits: `vol2_regular` (`V² = ℓ⁶/72`) and `cos_dihedral_regular` (`cos φ = 1/3`).
* `PonzanoReggeFormula`: the asymptotic statement for every non-degenerate tetrahedron whose
  faces satisfy the triangle inequalities (`IsTriad`).

Labelling as everywhere in `PonzanoRegge/`: `j₁ = AB, j₂ = BC, j₃ = CA, j₄ = CD, j₅ = AD, j₆ = BD`;
the triads are the faces and the columns pair opposite edges.

Numerical evidence (`scripts/pr_asymptotics.py`):
* on three tetrahedra the normalised error falls like `1/λ`, to `≤ 0.003` at `λ ≈ 80`;
* dropping the `½` shift leaves an error of `0.28–0.54` that does not decay.
-/

@[expose] public section

open Real Filter Topology PhyslibAlpha.Sl2

namespace Lightlike.PR

/-- Squared volume of the tetrahedron with edge lengths `a = AB, b = BC, c = CA, d = CD, e = AD,
f = BD` (opposite pairs `(a,d), (b,e), (c,f)`), by the Euler–Tartaglia formula. -/
noncomputable def vol2 (a b c d e f : ℝ) : ℝ :=
  (a^2*d^2*(-a^2 - d^2 + b^2 + e^2 + c^2 + f^2) + b^2*e^2*(a^2 + d^2 - b^2 - e^2 + c^2 + f^2)
    + c^2*f^2*(a^2 + d^2 + b^2 + e^2 - c^2 - f^2)
    - a^2*b^2*c^2 - a^2*e^2*f^2 - d^2*b^2*f^2 - d^2*e^2*c^2) / 144

/-- Cosine of the interior dihedral angle at edge `PQ` (length `pq`) between the faces `PQR` and
`PQS`, from the lengths: project `R` and `S` orthogonally off the line `PQ`. -/
noncomputable def cosDihedral (pq pr qr ps qs rs : ℝ) : ℝ :=
  let ru := (pr^2 + pq^2 - qr^2) / (2 * pq)
  let su := (ps^2 + pq^2 - qs^2) / (2 * pq)
  ((pr^2 + ps^2 - rs^2) / 2 - ru * su) / Real.sqrt ((pr^2 - ru^2) * (ps^2 - su^2))

/-- The interior dihedral angle. -/
noncomputable def dihedral (pq pr qr ps qs rs : ℝ) : ℝ := Real.arccos (cosDihedral pq pr qr ps qs rs)

/-- The six exterior dihedral angles `π - φ_e` of the tetrahedron with lengths
`l = (AB, BC, CA, CD, AD, BD)`, in the same order. -/
noncomputable def extAngles (l : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let AB := l 0; let BC := l 1; let CA := l 2; let CD := l 3; let AD := l 4; let BD := l 5
  ![π - dihedral AB CA BC AD BD CD,   -- edge AB: faces ABC, ABD
    π - dihedral BC AB CA BD CD AD,   -- edge BC: faces BCA, BCD
    π - dihedral CA BC AB CD AD BD,   -- edge CA: faces CAB, CAD
    π - dihedral CD CA AD BC BD AB,   -- edge CD: faces CDA, CDB
    π - dihedral AD AB BD CA CD BC,   -- edge AD: faces ADB, ADC
    π - dihedral BD AB AD BC CD CA]   -- edge BD: faces BDA, BDC

/-- Edge lengths `λ j_e + ½`. -/
noncomputable def lengths (j : Fin 6 → ℕ) (lam : ℕ) : Fin 6 → ℝ := fun e => lam * j e + 1 / 2

/-- The Regge action `Σ_e ℓ_e θ_e`. -/
noncomputable def reggeAction (l : Fin 6 → ℝ) : ℝ := ∑ e, l e * extAngles l e

/-- The 6j symbol `{λj₁ λj₂ λj₃; λj₄ λj₅ λj₆}` (Physlib's `sixJSym` takes doubled spins). -/
noncomputable def sixJScaled (j : Fin 6 → ℕ) (lam : ℕ) : ℝ :=
  sixJSym (2 * lam * j 0) (2 * lam * j 1) (2 * lam * j 2) (2 * lam * j 3) (2 * lam * j 4)
    (2 * lam * j 5)

/-- The triangle inequalities for a triad `(a, b, c)`. -/
def IsTriad (a b c : ℕ) : Prop := c ≤ a + b ∧ a ≤ b + c ∧ b ≤ a + c

/-- **The Ponzano–Regge asymptotic formula**, in the Ponzano–Regge form (edge lengths `j + ½`): for
spins `j` whose four faces satisfy the triangle inequalities and that form a non-degenerate
Euclidean tetrahedron (`vol2 > 0`), `√(12πV) {6j}(λj) - cos(S_Regge + π/4) → 0`. Proven as
`Lightlike.Asymptotics.ponzanoReggeFormula`. Roberts' Theorem 1 uses the unshifted tetrahedron; the
two forms agree by his §6.1 (the Schläfli identity), but that equivalence is not proven here, and
Roberts' Minkowskian case (`vol2 < 0`) is not stated.

The triangle inequalities are needed: `vol2 > 0` does not imply them. For `j = (1, 1, 3, 1, 5, 3)`
`vol2 = 1.625 > 0`, but the face `(1, 1, 3)` is not a triangle, so the 6j symbol vanishes for every
`λ` while `cos(S_Regge + π/4)` does not tend to `0`. An exhaustive search over `j ∈ {0, …, 6}⁶`
found no tuple with the weak triangle inequalities and `vol2 > 0` that needs more.

The base spins `j` are integers: `sixJScaled` scales doubled spins as `2λj`, so tetrahedra with
half-integer base spins are not covered, unlike Roberts' theorem. -/
def PonzanoReggeFormula : Prop :=
  ∀ j : Fin 6 → ℕ,
    IsTriad (j 0) (j 1) (j 2) → IsTriad (j 0) (j 4) (j 5) → IsTriad (j 3) (j 1) (j 5) →
    IsTriad (j 3) (j 4) (j 2) →
    0 < vol2 (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) →
    Tendsto (fun lam : ℕ =>
      Real.sqrt (12 * π * Real.sqrt (vol2 (lengths j lam 0) (lengths j lam 1) (lengths j lam 2)
          (lengths j lam 3) (lengths j lam 4) (lengths j lam 5))) * sixJScaled j lam -
        Real.cos (reggeAction (lengths j lam) + π / 4)) atTop (𝓝 0)

/-! ## Audits of the geometry -/

/-- Regular tetrahedron: `V² = ℓ⁶/72`, i.e. `V = ℓ³/(6√2)`. -/
theorem vol2_regular (l : ℝ) : vol2 l l l l l l = l ^ 6 / 72 := by
  unfold vol2; ring

/-- Regular tetrahedron: the dihedral angle has `cos φ = 1/3`. -/
theorem cos_dihedral_regular {l : ℝ} (hl : 0 < l) : cosDihedral l l l l l l = 1 / 3 := by
  unfold cosDihedral
  simp only
  have h1 : (l ^ 2 + l ^ 2 - l ^ 2) / (2 * l) = l / 2 := by field_simp; ring
  rw [h1, show (l ^ 2 - (l / 2) ^ 2) * (l ^ 2 - (l / 2) ^ 2) = (3 * l ^ 2 / 4) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- A degenerate (flat) configuration has zero volume: four points on a line of lengths
`1, 1, 2` between consecutive and outer points. -/
theorem vol2_flat : vol2 1 1 2 1 3 2 = 0 := by
  unfold vol2; norm_num

end Lightlike.PR
