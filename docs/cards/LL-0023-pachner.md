# Statement card: Pachner's theorem, stellar version (LL-0023)

| | |
|---|---|
| Result | `Lightlike.PL.SComplex.pachner`, entry LL-0023 (`main: true`, milestone PL2 item m1) |
| File | `Lightlike/PL/PachnerMain.lean`, line 840 (main at `eeba9873b`) |
| Source | W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geometry & Topology Monographs 2 (1999), arXiv:math/9911256, Theorem 5.9 (p. 315) |
| Card written | 27 Nov 2026, from the text of the paper (read) and the Lean files named below (read) |

## 1. The source theorem, word for word

> **Theorem 5.9** (Newman [9], Pachner [11], [12]) Two closed combinatorial n–manifolds are piecewise linearly homeomorphic if and only if they are bistellar equivalent.

The statements it depends on, also verbatim (the PDF text extraction writes `∈/` for `∉`):

> **Definition 2.2** A combinatorial n–ball is a simplicial complex B n piecewise linearly homeomorphic to ∆n . A combinatorial n–sphere is a simplicial complex S n piecewise linearly homeomorphic to ∂∆n+1 . A combinatorial n–manifold is a simplicial complex M such that, for every vertex v of M , lk (v, M ) is a combinatorial (n − 1)–ball or a combinatorial (n − 1)–sphere.

> **Definition 2.3** Suppose that A is an r–simplex in an abstract simplicial complex K and that lk (A, K) = ∂B for some (n − r)–simplex B ∉ K . The bistellar move κ(A, B) consists of changing K by removing A⋆∂B and inserting ∂A ⋆ B .

> **Definition 5.6** Combinatorial n–manifolds M1 and M2 are bistellar equivalent, written M1 ≈ M2 , if they are related by a sequence of bistellar moves and simplicial isomorphisms.

> **Definition 3.1** A stellar n–ball is a simplicial complex B n stellar equivalent to ∆n . A stellar n–sphere is a simplicial complex S n stellar equivalent to ∂∆n+1 . A stellar n–manifold is a simplicial complex M such that, for every vertex v of M , lk (v, M ) is a stellar (n − 1)–ball or a stellar (n − 1)–sphere.

> Suppose that A is any simplex in a simplicial complex K . The operation (A, a), of starring K at a point a in the interior of A, is the operation that changes K to K′ by removing st (A, K) and replacing it with a ⋆ ∂A ⋆ lk (A, K). […] In the abstract setting a is just a vertex not in K . This type of operation is called a stellar subdivision, the inverse operation (A, a)−1 that changes K′ to K is called a stellar weld. If simplicial complexes K1 and K2 are related by a sequence of starring operations (subdivisions or welds) and simplicial isomorphisms, they are called stellar equivalent, written K1 ∼ K2 .

> **Theorem 4.5** Two n–dimensional simplicial complexes are piecewise linearly homeomorphic if and only if they are stellar equivalent.

> The boundary ∂M of a stellar n–manifold M is all simplexes that have as link in M a stellar ball. It is not hard to see that this is a subcomplex and is a stellar (n − 1)–manifold without boundary. (p. 305)

The proof of Theorem 5.9 begins: "By Theorem 4.5 it is sufficient to prove that, if closed combinatorial n–manifolds M and M ′ are related by a stellar exchange, then they are bistellar equivalent." The paper does not define "closed" in the passages read; it is used here as "∂M is empty" (see difference 2).

## 2. The Lean statement, verbatim

```lean
theorem pachner {n : ℕ} {K L : SComplex V} (hK : IsClosedCombManifold n K) :
    StellarEquiv K L ↔ BistellarEquiv K L :=
  ⟨fun h => StellarEquivIn.bistellarEquivIn h (isMfdIn_false_iff.2 hK),
    BistellarEquiv.stellarEquiv⟩
```

in `namespace Lightlike.PL.SComplex` with `variable {V : Type*} [DecidableEq V]`. Its docstring: "Pachner's theorem, stellar version: closed combinatorial manifolds are stellar equivalent iff related by bistellar moves (no renamings of the vertices are needed). The closed combinatorial manifolds are the stellar ones of `Lightlike/PL/Manifold.lean` (Lickorish 1999, Definition 3.1). Lickorish's Theorem 5.9 (Newman, Pachner) has "PL homeomorphic" in place of "stellar equivalent"; that form is `pachner_plHomeomorphic`, from this theorem and Newman's theorem."

The PL form, in `Lightlike/PL/PachnerPL.lean` (catalogue entry on main, citing LL-0064 and LL-0023):

```lean
theorem pachner_plHomeomorphic {n : ℕ} {K L : SComplex V} (hK : IsClosedCombManifold n K)
    (h₀K : ∅ ∈ K) (h₀L : ∅ ∈ L) :
    PLHomeomorphic K L ↔ BistellarEquiv K L
```

## 3. Dictionary

| Lean | Meaning | Lickorish |
|---|---|---|
| `V`, `[DecidableEq V]` | the vertex type, with decidable equality | the vertices of an abstract simplicial complex |
| `SComplex V` | a structure: `faces : Finset (Finset V)` closed under subsets (`down`); the empty set is a face of every non-void complex | an abstract simplicial complex |
| `K.verts` | the elements of the faces of `K` | the vertices |
| `simplex A` | all subsets of `A` (`#A = n+1`: the n-simplex) | ∆n |
| `boundary A` | all proper subsets of `A`; for `#A = n+1` the (n−1)-sphere; `boundary` of a 0-simplex is `{∅}` | ∂A, ∂∆n+1 |
| `K.link σ` | faces `u` disjoint from `σ` with `σ ∪ u ∈ K`; void if `σ ∉ K` | lk (A, K) |
| `K.starAt A a` | faces of `K` not containing `A`, plus the cone from `a` over the faces `s` with `¬ A ⊆ s` and `A ∪ s ∈ K` | the stellar subdivision (A, a)K |
| `StellarStep K L` | `L = K.starAt A a` with `A ∈ K` nonempty and `a ∉ K.verts` | one starring |
| `StellarEquivIn K L` | `Relation.EqvGen StellarStep`: subdivisions and welds with new vertices in `V` | stellar equivalent (without the isomorphism steps) |
| `K.lift` | `K` with its vertices put into `V ⊕ ℕ` by `Sum.inl`: an unlimited supply of new vertices | none (Lickorish: "a is just a vertex not in K") |
| `StellarEquiv K L` | `StellarEquivIn K.lift L.lift` | K ∼ L |
| `IsBistellar K A B` | `A`, `B` nonempty, disjoint, `K.link A = boundary B`, `B ∉ K` | the hypotheses of Def 2.3 |
| `K.bistellar A B h` | faces of `K` not containing `A`, plus `t ∪ B` for the proper subsets `t` of `A` | κ(A, B): remove A⋆∂B, insert ∂A⋆B |
| `BistellarStep`, `BistellarEquivIn` | one move; `EqvGen` of moves and their inverses, vertices in `V` | the moves of Def 2.3 |
| `BistellarEquiv K L` | `BistellarEquivIn K.lift L.lift` | M1 ≈ M2 (Def 5.6, without the isomorphism steps) |
| `IsClosedCombManifoldIn n K` | every `v ∈ K.verts` has `A` with `#A = n+1` and `StellarEquivIn (K.link {v}) (boundary A)` | stellar n-manifold with all vertex links spheres (Def 3.1) |
| `IsClosedCombManifold n K` | `IsClosedCombManifoldIn n K.lift` | closed combinatorial n-manifold |
| `n` | the dimension (vertex links are (n−1)-spheres) | n |

## 4. Differences from the source

1. **Stellar equivalence in place of PL homeomorphism** (kind: REPRESENTATION, with the PL form proved separately). Lickorish's Theorem 4.5 says the two are the same for n-dimensional complexes; Lean has that as Newman's theorem (LL-0064, `StellarEquiv.of_plHomeomorphic`) and combines the two in `pachner_plHomeomorphic`. `pachner` is the stellar half only; it is what Lickorish's proof establishes after its first line.
2. **Manifold notion** (kind: REPRESENTATION). Lean's closed combinatorial manifold has every vertex link stellar equivalent to `∂Δⁿ`, i.e. a stellar sphere: Lickorish's Def 3.1 with ball links excluded. Lickorish's Theorem 5.9 uses Def 2.2 (PL balls and spheres) and "closed". PROXY: reading "closed" as "∂M = ∅", a vertex with ball link would lie in ∂M, and ∂M is a subcomplex (his remark on p. 305), so "closed" = "every vertex link is a sphere". The two readings of "sphere" agree by Theorem 4.5; Lean proves it as `isClosedCombManifold_iff_plHomeomorphic`.
3. **No isomorphism steps** (kind: REPRESENTATION). Def 5.6 and the definition of stellar equivalence list simplicial isomorphisms among the moves. Lean's `StellarEquiv` and `BistellarEquiv` have none; new vertices come from `V ⊕ ℕ`, and renamings are derived: `StellarEquiv.map_perm`, `IsClosedCombManifold.bistellarEquiv_map` (a closed combinatorial manifold is bistellar equivalent to its renaming by any `e : Equiv.Perm V`), and `IsClosedCombManifold.bistellarEquiv_of_iso`.
4. **Hypothesis only on `K`, and only for one direction.** `BistellarEquiv K L → StellarEquiv K L` holds for every `K`, `L` (`BistellarEquiv.stellarEquiv`). The other direction needs `hK`; that `L` is then also a closed combinatorial manifold is not assumed, it follows from stellar equivalence (`isMfdIn_iff_of_stellarEquivIn` in the proof).
5. **Dimension of the move** (kind: REPRESENTATION). Def 2.3 asks `A` to be an r-simplex and `B` an (n−r)-simplex. `IsBistellar` only asks both nonempty, so it is a wider relation than Def 2.3 on arbitrary complexes. PROXY: on a closed n-manifold the condition `link A = ∂B` fixes the dimension of `B`, so on the theorem's domain the two agree; the card does not prove this. The `←` direction of `pachner` holds for the wider relation (it does not use `hK`).
6. **Complexes with no vertices.** `IsClosedCombManifold n K` holds vacuously for such `K`, so the theorem covers them without a case split; Lickorish's statement is about manifolds with vertices.
7. **Proof shape.** Not a difference of statement: the file's header says it follows Lickorish's induction (proof of Theorem 5.9) on the commutation of exchanges (`exch_comm`, `exchStmt`) down to `bistellarEquivIn_starAt`.

## 5. Why each hypothesis is needed

- **`hK : IsClosedCombManifold n K`.** Used twice. (i) `bistellarEquivIn_starAt` starts by extracting from the manifold hypothesis, through `isMfdIn_main`, that the link of the face `A` being subdivided is stellar equivalent to the boundary of a simplex, which is what the bistellar rewriting of the stellar move works from. (ii) Stellar equivalence preserves the manifold property (`isMfdIn_iff_of_stellarEquivIn`, the local `hinv`), so every complex along a chain of stellar moves is again a manifold and the induction over the chain (`EqvGen`: `rel`, `refl`, `symm`, `trans`) can continue. Lickorish's theorem is about closed manifolds only; the card has not looked for a counterexample for a non-manifold `K`, so it does not claim the statement fails there.
- **`n`.** Free; it fixes the dimension of the vertex links ((n−1)-spheres).
- **`[DecidableEq V]`.** Needed to form `Finset (Finset V)` unions and filters in the definitions; no mathematical content.
- **No `Infinite V`.** The lifts to `V ⊕ ℕ` supply new vertices, so none is needed for `pachner` (the inner `bistellarEquivIn_starAt` takes `[Infinite V]`, and is applied to `V ⊕ ℕ`).

## 6. Trust checks

- **Axioms.** MEASURED (27 Nov 2026, `lake env lean` on the seed build of `eeba9873b`): `#print axioms Lightlike.PL.SComplex.pachner` and `…pachner_plHomeomorphic` both give `[propext, Classical.choice, Quot.sound]`. The repository's axiom audit covers every constant of the library; `TestsPachner.lean` is imported by `Lightlike.lean`.
- **Known values and wrong inputs** (`Lightlike/PL/TestsPachner.lean`, in the library build): `bistellarEquiv_octahedron` and the explicit four-move chain `bistellarChain_octahedron` (octahedron to the boundary of a tetrahedron; two 1–3 moves and two 2–2 flips, by `decide`); `not_bistellarEquiv_twoSpheres` and `not_bistellarEquiv_dim` (the boundary of a tetrahedron is not bistellar equivalent to two disjoint 2-spheres or to the boundary of a 4-simplex); `bistellarChain_rename` and `bistellarEquiv_map_octahedron` (renaming is a chain of bistellar moves, as `bistellarEquiv_map` predicts); `move3_S3`, `move4_K3` (the corollaries `pachner3`, `pachner4` on the tests of `PonzanoRegge/` and `FourD/`); `move3_cell16`, `move4_cross5` (independently built triangulations: the 16-cell and the 5-dimensional cross-polytope).
- **Non-vacuity of the PL form.** `PachnerPL.lean` ends with an `example`: the boundary of a triangle and its subdivision at a new vertex are bistellar equivalent.
- **Not done by this card.** The theorem is a main theorem of milestone PL2, not a comparator proof task, and the card did not re-run the build or the gate; the checks above are the file's own, listed as written in `TestsPachner.lean`'s header plus the measured axiom list.

## 7. One question for the reviewer

Is the relation `BistellarEquiv` (bistellar moves and inverses, with new vertices drawn from `V ⊕ ℕ` and no isomorphism step) the same relation as Lickorish's "bistellar equivalent" on isomorphism classes of complexes, given that renamings are derived (difference 3) and the manifold notion is the stellar one (difference 2)?
