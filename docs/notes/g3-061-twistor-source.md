# G3-061: complexified Minkowski space, its null cone and conformal compactification (twistor lines)

Lean: `Lightlike/GR/ComplexMinkowski.lean`.

## Source read (pdftotext of the arXiv PDF)

T. Adamo, *Lectures on twistor theory*, arXiv:1712.02196:
* section 1.2 "2-spinors in Minkowski space", p. 5: the spinor representation of a vector, (1.2); "the norm of a vector v^a with respect to
  the metric is encoded by the determinant of its spinor representation: η_ab v^a v^b = 2 det(v^{αα̇})" (1.3); "every (non-trivial) null vector
  in M_C can be written as v_null^{αα̇} = a^α ã^α̇ ... The converse is also obviously true" (1.4).
* section 1.3 "Real slices and spinor conjugations", p. 7: x^{αα̇} = (1/√2)[[x⁰ + x³, x¹ − ix²], [x¹ + ix², x⁰ − x³]] (1.12); Lorentzian real slice:
  "this corresponds to requiring x^{αα̇} to be Hermitian" (1.13).
* section 1.4 "Twistor space", pp. 9–10: homogeneous coordinates Z^A on CP³ (1.21), Z^A = (μ^α̇, λ_α) (1.22), the incidence relations
  μ^α̇ = x^{αα̇} λ_α (1.23); "the incidence relations ... define a complex plane C² ⊂ C⁴ ... a CP¹ ⊂ PT"; every linear embedding (1.24) put in the
  form (1.25) of the incidence relations; "lines in twistor space intersect if and only if their corresponding points in M_C are null separated"
  ((1.26)–(1.28)).
* section 2.3 "Conformal structures", pp. 19–21: the bi-twistor X^{AB} of a point (2.25), footnote 2 (p. 20): "X² = ε_ABCD X^AB X^CD = 0. So the
  quadric Q = {X ∈ CP⁵ | X² = 0} has four degrees of freedom. This is something known as the Klein quadric"; the infinity twistor I_AB (2.29),
  I_AB X^AB = ⟨λ₁λ₂⟩; lines meeting the infinity line are points at infinity (p. 21).

## How each Lean statement matches

* `spinorMat` = (1.12); `spinorEquiv` (M_C ≅ M₂(ℂ)) and `tensorEquiv` (ℂ² ⊗ ℂ² ≅ M₂(ℂ), `a ⊗ b ↦ a bᵀ`): the identification behind (1.2).
* `qC_eq_two_det` = (1.3) with the source's signature (+, −, −, −) (CONVENTION: the library's η is (−, +, +, +), i.e. −qC).
* `qC_eq_zero_iff`, `qC_eq_zero_iff_tmul` = (1.4) (both directions).
* `isHermitian_spinorMat_iff` = (1.13) (the real slice).
* `twistorLine`, `finrank_twistorLine` = "the incidence relations define a complex plane C² ⊂ C⁴" (1.23).
* `exists_twistorLine_eq` = (1.24)–(1.25), stated for 2-planes complementary to the plane at infinity λ = 0; `twistorLine_inf_infinity`,
  `twistorLine_injective`: M_C is the affine chart of the Grassmannian of 2-planes of ℂ⁴ (the compactification), points at infinity = planes meeting
  `infinityPlane` (p. 21; REPRESENTATION: the source uses the infinity twistor I_AB of (2.29) and lines of CP³; we use 2-planes of ℂ⁴ and the plane
  λ = 0, the same objects up to projectivization).
* `twistorLine_inf_ne_bot_iff` = (1.26)–(1.28).
* `plucker_klein`: Plücker coordinates lie on the Klein quadric (footnote 2, p. 20; Pfaffian form X⁰¹X²³ − X⁰²X¹³ + X⁰³X¹² = ε X X / 8).
  `plucker_twistorLine`: X²³ = 1 (I_AB X^AB = ⟨λ₁λ₂⟩ = 1) and X⁰¹ = qC x / 2 (the ½ x² entry of (2.25)).

## Not done

* The converse of `plucker_klein` (every point of the Klein quadric is a decomposable bivector) and the identification of the compactification with the
  Klein quadric as a variety (only the Plücker relation and the chart are formalized); the conformal structure on the compactification; Mathlib's
  `Module.Grassmannian` (quotient convention) is not used: we work with 2-dimensional submodules.
* The conformal group SU(2, 2) / SL(4, ℂ) action (next row G3-064).
