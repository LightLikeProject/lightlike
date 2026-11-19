# G3-063: CP¹ and CP³ as complex manifolds; lines of CP³ and the compactified complexified Minkowski space

Lean: `Lightlike/Geometry/ProjectiveSpace.lean` (general, no twistor names), `Lightlike/GR/TwistorKlein.lean` (on G3-061's
`ComplexMinkowski.lean`).

## Mathlib check

`Mathlib/LinearAlgebra/Projectivization/` (Basic, Subspace, Independence, Constructions, Action, PSL) is algebraic only: no topology, no
`ChartedSpace` on `ℙ K V`. `Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean` gives a set-level equivalence
`OnePoint K ≃ ℙ K (Fin 2 → K)` (the homeomorphism is a TODO there). Physlib and the repository: nothing.

## Sources read (pdftotext of the arXiv PDF)

T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196:
* §1.4, p. 9: "Let CP³ be the 3-dimensional complex projective space: this is the space of all complex lines through the origin in C⁴"
  (1.21); "we can chart CP³ by covering it with the coordinate patches U_i = {Z^A ∈ C⁴ | Z^i ≠ 0}; in U_i there are manifestly three
  well-defined complex coordinates given by taking (Z^i)⁻¹ Z^A"; PS ≅ M_C × CP¹ with λ a homogeneous coordinate on CP¹, p. 9.
* §1.4, pp. 9–10: points of M_C ↔ lines of PT (1.23)–(1.25).
* §2.3, p. 19: the bi-twistor X^AB of a point (2.25); footnote 2, p. 20: X^AB are homogeneous coordinates on CP⁵, X² = 0, "the quadric
  Q = {X ∈ CP⁵ | X² = 0} ... is something known as the Klein quadric, which represents points in Q as lines in a complex projective
  3-space, namely, twistor space"; p. 20: "IAB X^AB = 0, which defines a set of points 'at infinity' in the usual sense of conformal
  compactification"; (2.29) and p. 21: `I_AB X^AB = ⟨λ₁ λ₂⟩`, lines with `I_AB X^AB = 0` are the points at infinity.

## How each Lean statement matches

ProjectiveSpace.lean (any `n`):
* `instTopologicalSpace`: the quotient topology of `{v ≠ 0} ⊂ ℂⁿ⁺¹`; `continuous_proj`, `isOpenMap_proj` (proved: `π⁻¹(π O) = ⋃_c c • O`).
* `chart i`: Adamo's `U_i` with the coordinates `(Z^i)⁻¹ Z^A` (the coordinate `Z^i/Z^i = 1` omitted), an `OpenPartialHomeomorph` of the
  open `U_i` onto `ℂⁿ`: `isOpen_chartSet`, `continuousOn_chartFun` (through the open quotient map), `continuous_chartInv`,
  `chartInv_chartFun`, `chartFun_chartInv`.
* `instChartedSpace`, `isManifold`: `IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CP n)` (analytic transitions, `contDiffOn_transition`); `CP 1`, `CP 3`.
* `instT2Space` (the projector `v v†/|v|²` is a continuous injection into matrices), `instCompactSpace` (image of `{|v|² = 1}`).

TwistorKlein.lean:
* `Gr2` (lines of CP³ = 2-planes of ℂ⁴), `KleinQuadric ⊂ ℙ(ℂ⁶)`, `pluckerVec`, `kleinForm` (the Pfaffian, footnote 2).
* `pluckerVec_ne_zero_iff` (both directions), `pluckerVec_comb` (basis change multiplies by the determinant), `planeOf_pluckerVec`,
  `exists_pluckerVec_eq` (via `klein_decomposable`), `kleinEquiv : Gr2 ≃ KleinQuadric` (both directions: `fromKlein_toKlein`,
  `toKlein_fromKlein`).
* `isTwistorLine_iff`, `inf_infinityPlane_eq_bot_iff` (`X²³ = I_AB X^AB ≠ 0`), `compl_range_twistorLine` (**the complement of the affine
  chart is the set of lines meeting I**, as set equalities), `twistorLine_affine_chart` (the chart `ℂ⁴ → Gr2` is injective with image
  `{X²³ ≠ 0}`).

## Differences

1. Representation: lines of CP³ are 2-dimensional subspaces of ℂ⁴ (`Gr2`) and the line at infinity I is the plane `λ = 0`; Q is in ℙ(ℂ⁶)
   with coordinates `(X⁰¹, X⁰², X⁰³, X¹², X¹³, X²³)`.
2. Representation: the charts are Adamo's `U_i` with the redundant coordinate `Z^i/Z^i` dropped, for every `n` (Adamo: CP³).
