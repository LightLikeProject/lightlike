# FT1: the exponential formula in the algebra of graphs (Borinsky, Theorem 2.4.1)

Status of 19 November 2026. Claim tags: MEASURED = checked in Lean or by reading the cited location; PROXY /
ASSUMPTION = stated as such.

## Source read

M. Borinsky, *Graphs in perturbation theory: Algebraic structure and asymptotics*, PhD thesis (2018),
arXiv:1807.02046v1, read with pdftotext on 19 November 2026 (printed page numbers):

* §2.1, Definitions 2.1.1-2.1.2, p. 10: a graph is a set of half-edges `H`, a set of vertices `V`, a map `ν : H → V`
  and an involution `ι` of `H`; the 2-cycles of `ι` are the edges, its fixed points the legs.
* §2.1, Definitions 2.1.6-2.1.7, p. 11: an isomorphism is a pair of bijections of the half-edges and of the vertices
  compatible with `ν` and `ι`; an automorphism is an isomorphism of a graph with itself.
* §2.3, Proposition 2.3.1, p. 15: the unlabelled graphs are the orbits of the labelled ones under relabelling, and
  `|Orb Γ|/(m! k!) = 1/|Aut Γ|` (orbit-stabilizer).
* §2.4.2, eqs. (2.4.5)-(2.4.6), p. 17: `X = Σ_Γ Γ/|Aut Γ|` in the algebra `G` of graphs with the disjoint union as
  product, and `X_c` the same sum over the connected graphs; Theorem 2.4.1, eq. (2.4.7), p. 18: `X = e^{X_c}`.
* Chapter 7, p. 117: `W(ħ, j) := ħ log Z(ħ, j)` generates the connected diagrams "as stated in Theorem 2.4.1".

## Formal statements and how they compare (MEASURED unless tagged)

All in `Lightlike/FieldTheory/ZeroDim/`.

* `HalfEdge.existsUnique_componentOn`, `HalfEdge.card_invOn_eq_sum` (Components.lean): on a fixed half-edge type
  `π : H → V`, a graph on the vertex set `S` is an involution of `H` fixing the half-edges off `S`; every vertex lies in
  exactly one closed connected vertex set, and splitting off the component of a vertex gives
  `#graphs(R) = Σ_{v₀ ∈ S ⊆ R} #connected(S) · #graphs(R \ S)`. Supporting lemmas, no statement of the source.
* `LGraph n k`, `isIso_iff_smul`, `mem_aut_iff`, `inv_card_aut` (GraphIso.lean): a labelled graph has half-edges
  `Fin n`, vertices `Fin k`, an attachment map and an involution (Defs. 2.1.1-2.1.2 with `H = Fin n`, `V = Fin k`).
  Isomorphisms (Def. 2.1.6) are exactly the relabellings by `S_n × S_k`, automorphisms (Def. 2.1.7) the stabilizer,
  and `1/|Aut Γ| = |orbit Γ|/(n! k!)` is Prop. 2.3.1 (no difference beyond the labels being `Fin`).
* `GAlg`, `mul`, `X`, `Xc`, `expXc` (GraphAlgebra.lean): a coefficient for every isomorphism class of every size
  `(n, k)`; the product is the disjoint union (`unionC`, well defined on classes by `union_smul`), finite in each
  grade. Difference, kind representation: Borinsky's `G` is spanned by the graphs; here an element is a function on all
  classes (formal sums with arbitrary coefficients), which contains `X` and `X_c`. `e^{X_c}` at a class with `k`
  vertices is the finite sum `Σ_{m ≤ k} X_c^m/m!`; the terms with `m > k` vanish because `X_c` has no empty graph.
* `expXc_eq_X` (GraphExp.lean): `e^{X_c} = X` at every class, Theorem 2.4.1. Route of the proof:
  1. `X(c) = lab c/(n! k!)` (`X_eq_lab`), with `lab c` the number of labelled graphs in the class `c`;
  2. `X_c^m(c) = [c has m components] · m! · lab c/(n! k!)` (`pow_Xc_eq`), by induction on `m`: unfolding one factor
     of the product, `X_c^{m+1}(c) = Σ_{j ≤ n, l ≤ k} m! · s(j, l)/(j! l! (n - j)! (k - l)!)`, where `s(j, l)` counts the
     pairs (connected class with `j` half-edges and `l` vertices, class with `m` components) whose union is `c`,
     weighted by their labelled copies;
  3. double counting the pairs (labelled graph, one of its components) (`card_mul_ncomp`): `(m + 1)` times the number
     of graphs of class `c` with `m + 1` components is `Σ_{B, A}` of the number with component `B` and half-edge set
     `A`, and each of these equals `s(|A|, |B|)` by cutting the graph at `B` and gluing it back (`card_split`, through
     `restrictL` and `glue`, GraphSplit.lean); grouping the sets by size gives the binomials, and
     `C(n, j) j! (n - j)! = n!` closes the induction (`count_identity`);
  4. the number of components is a class invariant and at most `k` (`ncomp_le`), so the sum for `e^{X_c}(c)` has the
     single term `m = ncomp`, which is `lab c/(n! k!) = X(c)`.
  Borinsky proves Theorem 2.4.1 with the same idea (a graph is the disjoint union of its components, ordered
  decompositions overcount by `m!`); the induction on `m` and the double count are this proof's own organisation.

## Attempt record

* Attempt 1, 19 November 2026: the route above. The first plan for step 3 was a derivation argument (the vertex count
  `D(Γ) = k(Γ) Γ` is a derivation of the product, `D X = (D X_c) X`, and uniqueness of the solution). It was replaced
  by the direct count because the derivation route needs the commutativity and associativity of the product on
  classes as separate theorems, while the count needs only the cut-and-glue bijection.
* Chapter 7, p. 117, `W = ħ log Z` for a general potential with a source, attempt 2 (19 November 2026; the first
  attempt is the four-valent vacuum case read through the vertex count, in the zero-dimensional field theory note).
  Route: (a) the generating function `gen w a = Σ_{n,k} (Σ_c a(c) w(c)) X^n Y^k` of a formal sum of graphs under a
  multiplicative weight is multiplicative, so `X = e^{X_c}` gives `gen w X = Σ_m (gen w X_c)^m/m!` coefficientwise
  (GraphEval.lean); (b) the half-edges are distributed over the vertices: `Σ_{f : Fin n → Fin k} ∏_v m_v |f⁻¹ v| =
  n! [x^n] ∏_v Σ_d m_v(d) x^d/d!`, by induction on `n` through the derivative (MapsEGF.lean); with the number
  `(n - 1)!!` of fixed-point-free involutions this is the sum of the Feynman weights `∏_v μ(deg v)` over the leg-free
  labelled graphs (GraphRules.lean); (c) the formal partition function with a source, `formalZ`, as the coefficients
  `(n - 1)!! [x^n] (Σ_d μ_d x^d/d!)^k / k!` of `X^n Y^k ~ ħ^{n/2 - k}` (`μ_1 = j`, `μ_d = λ_d`), is the sum over the
  leg-free graphs with `1/|Aut Γ|` (Proposition 3.1.1 with a source) and is `Σ_m (W/ħ)^m/m!` with `W/ħ` the sum over
  the connected ones. Not stated: Borinsky's shift by `x₀(j)` on p. 116 (the tree part and the `F`-term), which is a
  further identity, and the logarithm of the bivariate series (the log form is read through `log = exp⁻¹`).

## Open

* Borinsky's shift by `x₀(j)` (p. 116: `Z = e^{(-x₀²/2 + V(x₀) + x₀ j)/ħ} F[...]`, the tree part times the `F`-term,
  with `x₀ = V'(x₀) + j`) and the Legendre transform to the effective action (p. 117) are further identities; not
  started.
