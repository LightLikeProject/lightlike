# The EPRL vertex for γ > 1: from the coherent node to the Spin(4)⁵ integral of edge forms

Status: plan and derivation on paper. The statements below marked *proved* are in
`Lightlike/Asymptotics/EPRL/`; the rest is not yet formalized. Numerical evidence is labelled as such
and is not a proof.

## Sources and conventions

* EPRL, arXiv:0711.0146, Section III, eq. (27): for γ > 1 the simplicity constraint selects the lowest
  irreducible component, `k = j⁺ − j⁻`.
* Barrett–Dowdall–Fairbairn–Gomes–Hellmann, arXiv:0902.1170, Section 3.4, eqs. (16)–(19): the resolution
  of the identity on `SU(2)/U(1)` (16), the edge amplitude (17), the action (18) and the vertex as a
  Spin(4)⁵ integral with two points per edge (19). The structure map `J` is defined earlier in the
  paper; its page is not registered as a source location here.
* Doubled spins: `n = 2j⁺`, `m = 2j⁻`, `k = n − m ≥ 0`. `|k, g⟩ = D^k(g) e₀`. On `V_n ⊗ V_m` the form
  `B(u, w) = Σ ε_n(μ) ε_m(ν) u(μ,ν) w(−μ,−ν)` is the pairing of `k5Contract4`.

What the library claims from the sources: (i) for γ > 1 the map is the lowest component (EPRL (27));
(ii) the vertex is an integral over Spin(4)⁵ with extra `SU(2)/U(1)` points (BDFGH (17)–(19)). It does
not claim equality with (19): that equation is written in a convention that absorbs the phase of the
coherent points, and the factor `(−1)^{χ'}`, the signs `(−1)^{2j⁻}` and the constant `d_{j⁺}²` are not
compared. The `U(1)`-invariant integrand below is derived here, not printed in the source.

## Pieces

1. **Node (proved).** `eprlIntertwinerLow_homForm_cohInt`, `eprlCohNodeHigh_integral`: the image of the
   `SU(2)` coherent intertwiner is the Spin(4) average of the conjugates of the lifted rank-one tensor
   `⊗_l |k_l, g_l⟩`. The image is a superposition, not a product of coherent states.
2. **Leg amplitude (proved up to `c₀`).** `eprlMapLow_cohState`:
   `(⟨n,M| ⊗ ⟨m,M'|) Y_low |k,g⟩ = (−1)^m c₀ ⟨M|g⟩^k ⟨M|J M'⟩^m`, `c₀ = Y_low[(0,m),0]`. The closed value
   `c₀² = (k+1)/(n+1)` is numerical evidence only.
3. **Covariance of `B` (to do, about 40 lines).** For `A, A' ∈ SU(2)`,
   `B((A⊗A')u, (A⊗A')w) = B(u, w)`: `D^n(A)ᵀ W_n D^n(A) = W_n` for each factor, then the Kronecker mixed
   product. Docstring: "The edge pairing of the `K₅` contraction is invariant under the diagonal action."
   Limit: stated for `SU(2)` elements only.
4. **`k5Contract4_prod` (to do, about 25 lines).** For node tensors that are products over the four legs,
   the contraction is the product over the ten edges of `Σ_{μ,ν} ε_n(μ) ε_m(ν) f_src(μ,ν) f_tgt(−μ,−ν)`.
   A copy of `k5Contract_prod` with the pair of indices per edge.
5. **Fubini over Spin(4)⁵ (to do, about 30 lines).** `k5Contract4` of Haar integrals over `Spin4` is the
   integral over `Fin 5 → Spin4` of the contraction of the integrands, for continuous integrands
   (a copy of `k5Contract_integral`, reusing the Spin(4) measure of `EPRLFormula.lean`).
6. **Low lift of a product (to do, about 70 lines).** `eprlLiftLow (homForm (prodVec s))` is the outer
   product of the leg vectors `Y_low s_l`: the `γ > 1` analogue of `eprlLift_homForm_prod`, using the
   singlet intertwining and the equivariance of `Y_low`. This is the one non-trivial missing lemma.
7. **Edge form (to do, with 3 and the resolution of the identity).**
   `B(u, v) = (n+1)(m+1) ∫ dM dM' B(u, |M,M'⟩) ⟨M,M'|v⟩`, and with the leg amplitude the integrand is
   `F_e = c₀² conj(⟨P_a|J g_ab⟩)^k conj(⟨P_a|J P'_a⟩)^m ⟨P_b|g_ba⟩^k ⟨P_b|J P'_b⟩^m`,
   `P_x = (G_x⁺)⁻¹ M`, `P'_x = (G_x⁻)⁻¹ M'`. It is invariant under `M ↦ e^{ia}M`, `M' ↦ e^{ib}M'`
   because it contains the projectors `|M⟩⟨M|` and `|M'⟩⟨M'|`.
   Numerical evidence (not a proof): `scripts/spinfoam/eprl_high_check.py`, direct form against closed
   form for `(n,m) ∈ {(2,1), (3,1), (3,2), (4,1), (4,3)}`, agreement to 1e-13 with controls that fail.

## Target statement

`eprlCohHigh n m g = ∫_{Spin(4)⁵} ∏_e (m_e+1)(k_e+1) ∫ dM_e dM'_e F_e dG`, with the closed value of `c₀`
a follow-up; the vertex sum with coherent boundary data equals it up to the explicit per-edge sign
`(−1)^{m_e}`, which is kept and not compared with the source.

## Size and stopping rule

About 225 lines in total for pieces 3–7; if the assembly alone passes 300 lines, stop and report.

## Open

* The positivity and closed value of `c₀`.
* Whether the product of the two edge resolutions of the source and the single resolution here give the
  same integral term by term (they are both exact rewritings of one vertex; the comparison is not made).

## Draft: tightened limits text for the catalogue entries

Entry on the node and the vertex sum (`eprlCohNodeHigh_integral`, `eprlVertexHigh_coherent`):

* *Proves.* For every spin, with the same `SU(2)` elements on both chiral halves, the coherent node
  tensor of the lowest component is, at the projections of two components, `nodeSign` times the bridge
  signs times a matrix entry of the Spin(4) average of the lifted rank-one tensor, and the vertex sum with
  coherent boundary data is the `K₅` contraction of these node tensors.
* *Does not prove.* A `Spin(4)⁵` integral of edge forms; a factorization into `SU(2)` node tensors (false
  for this map: the image is a superposition); any comparison with the source's vertex equation, its
  signs `(−1)^{χ'}` and `(−1)^{2j⁻}`, or its constant `d_{j⁺}²`; any asymptotic statement.

Entry on the leg amplitude (`eprlMapLow_cohState`, `weight_of_equivariant`):

* *Proves.* `(⟨n,M| ⊗ ⟨m,M'|) Y_low |k,g⟩ = (−1)^m c₀ ⟨M|g⟩^k ⟨M|J M'⟩^m` with `c₀ = Y_low[(0,m),0]`.
* *Does not prove.* That `c₀ ≠ 0`, or its value `√((k+1)/(n+1))` (numerical evidence only); that the
  `U(1)`-invariant integrand of the vertex follows from it (derived on paper, checked numerically, not
  formalized); equality with the source's equation (19).
