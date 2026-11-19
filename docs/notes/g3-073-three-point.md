# G3-073: three-particle special kinematics and three-point amplitudes fixed by little-group scaling

Lean: `Lightlike/GR/ThreePointAmplitude.lean` (on G3-072's `SpinorHelicity.lean`).

## Source read (pdftotext of arXiv:1308.1697v2)

H. Elvang, Y. Huang, *Scattering Amplitudes*:
* p. 18, §2.4: "if three lightlike vectors satisfy p₁ + p₂ + p₃ = 0, then ⟨12⟩[12] = 2p₁·p₂ = (p₁ + p₂)² = p₃² = 0" (2.56), "so either
  ⟨12⟩ or [12] must vanish. Suppose ⟨12⟩ is non-vanishing; then by (2.38) and the massless Weyl equation we have
  ⟨12⟩[23] = ⟨1|(p₁ + p₃)|3] = 0. So [23] = 0. Similarly, [13] = 0", hence an on-shell 3-point amplitude of massless particles depends
  on either angle or square brackets only.
* p. 27: little-group scaling (2.92). p. 28: amplitudes have weight `−2hᵢ` (2.93); the Ansatz `A₃ = c⟨12⟩^{x₁₂}⟨13⟩^{x₁₃}⟨23⟩^{x₂₃}`
  (2.94); "Little group scaling (2.93) fixes −2h₁ = x₁₂ + x₁₃, −2h₂ = x₁₂ + x₂₃, −2h₃ = x₁₃ + x₂₃" (2.95); the solution
  `x₁₂ = h₃ − h₁ − h₂` etc. (2.96): "the helicity structure uniquely fixes the 3-particle amplitude up to an overall constant".
* p. 29: `A₃(g₁⁻g₂⁻g₃⁺) = g_YM ⟨12⟩³/(⟨13⟩⟨23⟩)` (2.97); with square brackets "the scaling would have been the opposite",
  `g′ [13][23]/[12]³` (2.98), discarded by dimensional analysis and locality.

## How each Lean statement matches

* `Conserved3`, `conserved3_iff`: momentum conservation `Σ λᵢ λ̃ᵢᵀ = 0` is `p₁ + p₂ + p₃ = 0` for `pᵢ = nullMom λᵢ λ̃ᵢ`.
* `contract_conserved3`: `Σᵢ ⟨A i⟩[i B] = 0` (the contraction behind (2.38)); certificate found by a linear solve (sympy).
* `angleBr_mul_squareBr_conserved`: `⟨ij⟩[jk] = 0` for distinct `i, j, k` (p. 18); `angleBr_mul_squareBr_self_conserved`:
  `⟨ij⟩[ji] = 0` ((2.56)); `special_kinematics`: all angle brackets vanish or all square brackets vanish.
* `angleAnsatz` (2.94), `angleAnsatz_littleGroup` (its scaling), `angle_exponents_iff` ((2.95) ⟺ (2.96)), `angleAnsatz_weights_iff`
  (a nonzero ansatz has the weights `−2hᵢ` for all scalings iff its exponents are (2.96)); `squareAnsatz`,
  `squareAnsatz_littleGroup`, `square_exponents_iff` (the opposite exponents, (2.98)).
* Mass dimension (p. 29, (2.24), (2.99)): `angleAnsatz_dilation`, `squareAnsatz_dilation` (under `λᵢ ↦ sλᵢ`, `λ̃ᵢ ↦ sλ̃ᵢ`, so
  `pᵢ ↦ s²pᵢ`, each bracket gets `s²`: dimension 1); `HasMassDim`, `HasMassDim.unique`, `hasMassDim_angleAnsatz`,
  `hasMassDim_squareAnsatz`; `three_point_dimension`: with the little-group exponents the angle ansatz has dimension `−Σhᵢ` and the
  square ansatz `+Σhᵢ`; `gluon_mmp_massDim` ((2.97) has dimension 1), `gluon_mmp_square_massDim` ((2.98) has dimension −1);
  `three_point_selection`: under the hypothesis "the three-point amplitude has mass dimension 1", a nonzero angle ansatz with the
  weights `−2hᵢ` occurs iff `Σhᵢ = −1`, a nonzero square ansatz iff `Σhᵢ = +1`.
* Trust checks: `gluon_mmp_littleGroup` ((2.97) has the weights of `1⁻2⁻3⁺`), `gluon_mmp_square_littleGroup` ((2.98) too).

## Differences

1. Representation: as in G3-072 (complex momenta, spinors `Fin 2 → ℂ` with lower indices, brackets as functions of the spinors);
   helicities enter as `Hᵢ = 2hᵢ ∈ ℤ`; amplitudes are the monomial Ansätze (2.94) with integer exponents.
2. Representation: the physical input of p. 29 (locality: the three-point amplitude has mass dimension 1, the momentum
   dependence of the `AA∂A` vertex of `Tr F²`; (2.99)) is a stated hypothesis of `three_point_selection`; the dimension count
   and the selection are proved.
