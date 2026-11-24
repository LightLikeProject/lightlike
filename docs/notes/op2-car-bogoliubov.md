# OP2, CAR half (G3-158): fermionic Bogoliubov transformations

Status: in progress. Done: Bogoliubov transformations of the CAR and their unitary implementability in finite dimensions.
Second part (`CARQuasiFree.lean`, branch opalg/op2-car-quasifree): Bogoliubov vacua, the pure quasi-free states. Not done: Wick's theorem beyond the two-point function.

Already on main (read, reused): the finite CAR in Jordan-Wigner form (`FiniteCAR`), uniqueness of its irreducible representations
(`CARUnique`, Dereziński Theorem 10), the exterior-algebra creation/annihilation operators (`FermionFock`), the Fock representation
over a Hilbert space with irreducibility (`FermiFockGeneral`, Theorem 28).

New (`OperatorAlgebras/CARBogoliubov.lean`, tests in `TestsCARBogoliubov.lean`), no source is claimed for the statements; they are
computed here:
* `bogAnn_bogCre_anticomm`, `bogAnn_anticomm`: for `bᵢ = ∑ⱼ (αᵢⱼ aⱼ + βᵢⱼ cⱼ)` the anticommutators are `(α α* + β β*)ᵢₖ` and `(α βᵀ + β αᵀ)ᵢₖ`;
* `isCARPairs_bog`: `α α* + β β* = 1`, `α βᵀ + β αᵀ = 0` give the CAR again (sufficiency of the conditions);
* `bog_inv`: the inverse transformation (the block matrix `[[α, β], [β̄, ᾱ]]` is unitary);
* `isCAROn_bogFam`, `isIrreducibleCAR_bogFam`: the transformed Majorana family is an irreducible CAR representation;
* `bogoliubov_implementable`: hence (uniqueness) a unitary `U` with `U φₖ = φ'ₖ U`, with no Shale condition in finite dimensions.
Tests: particle-hole swap; the one-mode conditions force `αβ = 0` (contrast `|α|² − |β|² = 1` for bosons); a two-mode mixing
`α = c·1`, `β = s·[[0,1],[-1,0]]`, `c² + s² = 1` with an implementing unitary on the 2-mode Jordan-Wigner space.

Not shown: the necessity of the conditions (that a CAR-preserving linear map has them), infinitely many modes (the fermionic Shale
criterion, `β` Hilbert-Schmidt, is not formalised), quasi-free states. No comparison with Dereziński Section 7 or Araki's papers is claimed.

## Quasi-free part (`CARQuasiFree.lean`, `TestsCARQuasiFree.lean`)
A vector `Ψ` with `bⱼ Ψ = 0` for all `j` (Bogoliubov vacuum) has `⟪aᵢΨ, aⱼΨ⟫ = (β*β)ᵢⱼ‖Ψ‖²`, `⟪cᵢΨ, cⱼΨ⟫ = (α*α)ᵢⱼ‖Ψ‖²`,
`⟪aᵢΨ, cⱼΨ⟫ = (β*α)ᵢⱼ‖Ψ‖²` (`bogVacuum_inner_a_a`, `_c_c`, `_a_c`); it exists for the Jordan-Wigner representation
(`exists_bogVacuum_jordanWigner`, `Ψ = UΩ`) and is unique up to a scalar (`bogVacuum_unique`, one-dimensional vacuum space of the
irreducible transformed representation). Two-mode test: occupation `s²δᵢⱼ`, pairing `-sc`. Not proved: Wick's formula for the higher
functions, mixed (non-pure) quasi-free states, the converse (every pure quasi-free state is a Bogoliubov vacuum).
