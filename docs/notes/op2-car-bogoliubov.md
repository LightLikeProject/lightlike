# OP2, CAR half (G3-158): fermionic Bogoliubov transformations

Status: in progress. Done: Bogoliubov transformations of the CAR and their unitary implementability in finite dimensions.
Not done: quasi-free states of the CAR algebra (the fermionic counterpart of `QuasiFreeState/`).

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
