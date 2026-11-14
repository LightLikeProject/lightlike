# Conventions

The conventions the library uses. A new definition should follow them, or state in its docstring
where and why it differs. Each entry names the file where the convention is fixed.

## Spacetime and curvature

- **Signature "mostly plus".** `η = diag(-1, +1, …, +1)` (Misner–Thorne–Wheeler, Wald), spacetime
  dimension `n`, coordinate index `0` is time (`Lightlike/Spacetime/Lorentzian.lean`).
- **Physlib uses the opposite signature.** Physlib's `minkowskiMatrix` is `diag(1, -1, …, -1)` on
  `Fin 1 ⊕ Fin d`. `Lightlike.Lorentz.reindex_minkowskiMatrix` (`Lightlike/Lorentz/Signature.lean`)
  proves that, reindexed to `Fin 4`, it is `-η`, so results can move between the two.
- **Curvature** (`Lightlike/Spacetime/Curvature.lean`), for a coordinate metric `g` on `ℝⁿ`:
  - Christoffel symbols `Γ^i_{jk} = ½ g^{il} (∂_j g_{lk} + ∂_k g_{lj} − ∂_l g_{jk})`;
  - Riemann tensor `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} − Γ^ρ_{νλ} Γ^λ_{μσ}`;
  - Ricci tensor `R_{σν} = R^ρ_{σρν}` (contraction of the first and third index);
  - scalar curvature `R = g^{σν} R_{σν}`.

  These are the sign conventions of Misner–Thorne–Wheeler; with them the round sphere has
  positive scalar curvature.

## Representation theory and recoupling

- **SU(2) and SL(2,ℂ)** are Mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ` and
  `Matrix.SpecialLinearGroup (Fin 2) ℂ`.
- **3j and 6j symbols** are Physlib's `threeJ` and `sixJSym`.
- **Phases.** Condon–Shortley: `J₊ |j m⟩ = √((j−m)(j+m+1)) |j m+1⟩` with a positive coefficient
  (`Lightlike/Spin4/Ladder.lean`, `Lightlike/Spin4/CGBridge.lean`).

## Turaev–Viro and quantum groups

- `q = e^{iπ/r}`, quantum integers `[n] = sin(nπ/r) / sin(π/r)` (`qnum`,
  `Lightlike/TuraevViro/QNumber.lean`).
- Colours are `0, …, r − 2` (doubled spins), admissible at level `r − 2` (`qAdm`: a triangle with
  perimeter at most `2(r − 2)`; `Lightlike/TuraevViro/QNumber.lean`,
  `Lightlike/TuraevViro/TuraevViro.lean`).
- The quantum 6j symbol `qSixJ` has the unitary normalisation of Kirillov–Reshetikhin and
  Turaev–Viro (`Lightlike/TuraevViro/QSixJ.lean`).

## Lean's junk values

Lean's total functions return a value outside their mathematical domain. A statement must not
hold only because of one of these:

| Expression | Value in Lean |
|---|---|
| `a / 0` | `0` |
| `(M : Matrix n n K)⁻¹` for singular `M` | `0` |
| `fderiv ℝ f x` for `f` not differentiable at `x` | `0` |
| `Real.sqrt x` for `x < 0` | `0` |
| `Real.log 0`, `Real.log x` for `x < 0` | `0`, `Real.log (-x)` |
| `a - b` on `ℕ` for `a < b` | `0` |
| `a / b` on `ℕ` | the floor of the quotient |

A definition that uses one of them states its domain in the docstring, and its theorems assume
that domain. The non-vacuity task of each milestone gives an example inside it.

## Definitions taken from Physlib

Theorems from Mathlib and Physlib are checked by Lean like those of this library, but their
definitions are taken on trust: a definition that did not mean what its name says would make the
theorems built on it be about the wrong object. Each Physlib definition the library uses is
checked here against independent values or known identities. Physlib is used at its Alpha tier,
which has no maintenance promise, so its names and statements can change between versions.

| Definition | What it is | How it is checked here |
|---|---|---|
| `sixJSym` | Wigner 6j symbol (doubled spins) | `Lightlike/Tests/SixJ.lean`: 14 values up to spin 5/2 against SymPy's `wigner_6j`; the Biedenharn–Elliott identity and orthogonality are proven for all spins |
| `threeJ` | Wigner 3j symbol | `Lightlike/Recoupling/Tests.lean`; orthogonality and completeness are proven (`sum_threeJ_mul_threeJ`, `sum_threeJ_complete`) |
| `PhyslibAlpha.Sl2` | irreducible `sl₂`-modules `V(n)` and their tensor products | `Lightlike/SU2/LieBridge.lean` proves that the derivative of the spin-`n/2` representation acts as `V(n)` (`dSpin_E`, `dSpin_F`, `dSpin_H`) |
| `cgCoefficient` | Clebsch–Gordan coefficients | `Lightlike/Spin4/CGBridge.lean` proves that they intertwine the SU(2) representations, are orthonormal and complete, and match `threeJ` (`cgMatrix_equivariant`, `cgMatrix_orth`, `cgMatrix_complete`, `cgMatrix_eq_threeJ`) |

Mathlib definitions are used as they are; where a Mathlib notion is compared with one of this
library (for example `SComplex.toPreAbstract` in `Lightlike/PL/Complex.lean`), the
comparison is a theorem.

## By area

Conventions of the areas that have them, in addition to those above. An area not listed has none
yet: its first definitions follow its sources and record their choices here.

- **Lorentzian and Riemannian geometry, cosmology, semiclassical gravity.** The signature and
  curvature conventions above. Physlib's FLRW files work with the scale factor and the Friedmann
  equations directly, without a metric tensor; milestone CO1 connects the two.
- **Perturbative quantum gravity.** The signature above; much of the amplitudes literature uses
  (+,−,−,−), so state the convention of each source.
- **Harmonic analysis on Lie groups.** SU(2) and SL(2,ℂ) are Mathlib's matrix groups; spins are
  doubled (spin `j` is the natural number `2j`); Condon–Shortley phases.
- **Operator algebras and quantum information.** Hilbert spaces and operators are Mathlib's;
  finite-dimensional quantum mechanics is in `Lightlike/QM/`.
- **PL topology, dynamical triangulations.** Simplicial complexes are finite sets of finite vertex
  sets closed under subsets (`Lightlike/PL/`); a face with `n + 1` vertices is `n`-dimensional.
- **Regge calculus.** Edge lengths `ℓ` are the variables; the deficit angle at an interior edge is
  `2π` minus the sum of the dihedral angles around it (`Lightlike/Regge/Complex.lean`).
- **Spin foams.** Spins are doubled; Spin(4) = SU(2) × SU(2), with irreducible representations
  labelled `(j₊, j₋)`.
