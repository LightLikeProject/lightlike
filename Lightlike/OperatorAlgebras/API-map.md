# Operator algebras and Hilbert-space representations

## Abstract (Alpha)

This API holds the definitions for unbounded self-adjoint operators and the Weyl relations. The operator
type is Mathlib's partially defined linear map, with its adjoint and self-adjointness. It adds strongly
continuous one-parameter unitary groups with their generators, for Stone's theorem, and Bogoliubov
transformations, Hilbert–Schmidt maps and Fock representations, for Shale's criterion. The theorems
themselves are open proof tasks, in `Tasks/OP/`.

## Content (Alpha)

A strongly continuous one-parameter unitary group is a family of unitaries `U t` with `U 0 = 1`,
`U (s + t) = U s ∘ U t` and `t ↦ U t ψ` continuous [1]. Its generator `A` is `-i d/dt U t ψ` at `0`, on
the vectors where the derivative exists, so that formally `U t = exp (i t A)` [1]. Stone's theorem says
that the generator is self-adjoint, that every self-adjoint operator is a generator, and that the group is
determined by it {1}. The phase group `exp (i λ t)` has the generator `λ`, and the generators of `λ = 1`
and `λ = -1` differ [2]. A Bogoliubov transformation of a complex Hilbert space `h` is a continuous
real-linear bijection that preserves the symplectic form `Im ⟪f, g⟫`, with a complex-linear part and an
antilinear part [3]. A representation of the Weyl relations is a family of unitaries `W f` with
`W f ∘ W g = exp (-i Im ⟪f, g⟫ / 2) W (f + g)`, and a Fock representation has a cyclic unit vector with the
vacuum expectation `exp (-‖f‖² / 4)` [3]. Shale's criterion says that a Bogoliubov transformation is
implemented by a unitary of the Fock representation exactly when its antilinear part is Hilbert–Schmidt {2}.
In one mode the squeezing has `|α|² - |β|² = 1` and the dilation `f ↦ 2 f` is not symplectic [4]. The
Fock space itself is not built here, and a Fock representation is characterized by its vacuum. The
unbounded spectral theorem is not in Mathlib. Stone's theorem and Shale's criterion are [TODO] here.

## Lean References

1. Lightlike/OperatorAlgebras/UnitaryGroup.lean - `OperatorAlgebras.UnitaryGroup`,
   `OperatorAlgebras.UnitaryGroup.generatorDomain`, `OperatorAlgebras.UnitaryGroup.generator`
2. Lightlike/OperatorAlgebras/TestsUnitaryGroup.lean - `OperatorAlgebras.phaseGroup`,
   `OperatorAlgebras.phaseGroup_domain`, `OperatorAlgebras.phaseGroup_generator`,
   `OperatorAlgebras.phaseGroup_generator_ne`
3. Lightlike/OperatorAlgebras/Weyl.lean - `OperatorAlgebras.symp`, `OperatorAlgebras.Bogoliubov`,
   `OperatorAlgebras.Bogoliubov.alphaPart`, `OperatorAlgebras.Bogoliubov.betaPart`,
   `OperatorAlgebras.IsHilbertSchmidt`, `OperatorAlgebras.CCRRep`, `OperatorAlgebras.FockRep`,
   `OperatorAlgebras.Implements`
4. Lightlike/OperatorAlgebras/TestsWeyl.lean - `OperatorAlgebras.squeezeMap`,
   `OperatorAlgebras.squeeze`, `OperatorAlgebras.squeeze_alpha`, `OperatorAlgebras.squeeze_beta`,
   `OperatorAlgebras.squeeze_norm_sq`, `OperatorAlgebras.dilation_not_symplectic`

## References

1. B. C. Hall, *Quantum Theory for Mathematicians*, Graduate Texts in Mathematics 267, Springer, 2013,
   Chapter 10 (Stone's theorem).
2. O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 2*, 2nd ed.,
   Springer, 1997, Chapter 5, after D. Shale, *Linear symmetries of free boson fields*, Trans. Amer. Math.
   Soc. 103 (1962) 149.
