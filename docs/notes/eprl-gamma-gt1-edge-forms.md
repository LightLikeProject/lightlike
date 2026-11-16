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

## Draft: Lean statements and docstrings for the remaining pieces (text only, not compiled)

Each is tied to the source equation it formalizes. `n m : Fin 10 → ℕ` are doubled spins, `k = n − m`.

**Piece 3, covariance of the edge pairing** (no source equation: this is the invariance of the singlet
pairing that underlies the edge sign of `k5Contract4`; the structure map `J` of BDFGH Section 3.3 is its
antilinear counterpart).

```lean
/-- **The edge pairing is invariant under the diagonal action**: for `A A' : SU2` and `u w` on
`V_n ⊗ V_m`, `B ((A ⊗ A') u) ((A ⊗ A') w) = B u w`, with `B` the pairing of `k5Contract4`
(`edgeSign n μ * edgeSign m ν`). Stated for `SU(2)` elements only. -/
theorem edgePair_invariant (n m : ℕ) (A A' : SU2) (u w : Idx n m → ℂ) :
    edgePair n m (act2 n m A A' *ᵥ u) (act2 n m A A' *ᵥ w) = edgePair n m u w
```

**Piece 4, regrouping by edges** (BDFGH Section 3.4, the product over edges `∏_{a<b}` in eq. (17) and the
sum over the ten edges in the action (18)).

```lean
/-- **Regrouping the `K₅` contraction by edges, for Spin(4)**: if every node tensor is a product over its
legs, `T_a(μ, ν) = ∏_l f_{a,l}(μ_l, ν_l)`, the contraction is the product over the ten edges of the
edge pairings `Σ_{μ,ν} ε_n(μ) ε_m(ν) f_src(μ,ν) f_tgt(−μ,−ν)`. -/
theorem k5Contract4_prod (n m : Fin 10 → ℕ) (f : Fin 5 → Fin 4 → ℤ → ℤ → ℂ) :
    k5Contract4 n m (fun a μ ν => ∏ l, f a l (μ l) (ν l)) = ∏ e, edgeForm n m e f
```

**Piece 5, Fubini over Spin(4)⁵** (BDFGH eq. (19): the integral `∫_{Spin(4)⁵} ∏_c dG_c` over the five
nodes).

```lean
/-- **Fubini for the Spin(4) `K₅` contraction**: if the node tensors are Haar integrals over Spin(4) of
continuous functions, the contraction is the integral over `Spin(4)⁵` of the contraction of the
integrands. -/
theorem k5Contract4_integral (n m : Fin 10 → ℕ) (G : Fin 5 → Spin4 → (Fin 4 → ℤ) → (Fin 4 → ℤ) → ℂ)
    (hG : ∀ a μ ν, Continuous fun X => G a X μ ν) :
    k5Contract4 n m (fun a μ ν => ∫ X, G a X μ ν ∂haarSpin4) =
      ∫ X : Fin 5 → Spin4, k5Contract4 n m (fun a => G a (X a)) ∂haarN5
```

**Piece 6, the low lift of a product** (BDFGH Section 3.4, Figure 4 and the paragraph before eq. (17): the
Clebsch–Gordan intertwiner injects into the lowest state `k = j⁺ − j⁻`; EPRL eq. (27)).

```lean
/-- **The `γ > 1` lift of a product of leg vectors is the outer product of the leg images**:
`eprlLiftLow (homForm (prodVec s))` is the tensor product over the legs of `Y_low s_l`, with the
singlet signs of the bridge. Not a product of coherent states when `s_l` are coherent. -/
theorem eprlLiftLow_homForm_prod (n m : Fin 4 → ℕ) (hmn : ∀ l, m l ≤ n l) (s : …) : …
```

**Piece 7, the edge form** (BDFGH eq. (16) for the resolution of the identity and eq. (17) for the edge
amplitude; the integrand is the derived `U(1)`-invariant one, not the printed one).

```lean
/-- **The edge amplitude as a sphere integral**: with `E = (n+1)(m+1)` and the resolution of the identity
on `V_n ⊗ V_m` by coherent states, `B u v = E ∫∫ B(u, |M,M'⟩) ⟨M,M'|v⟩ dM dM'`. -/
theorem edgePair_resolution …
/-- **The closed integrand** (`c₀` abstract): `⟨J u | M,M'⟩ ⟨M,M'| v⟩ = c₀² conj(⟨P_a|J g_ab⟩)^k …`. -/
theorem edgeIntegrand_eq …
```

Limits to carry in each docstring: exact at every spin; `c₀` abstract; no equality with eq. (19) and no
`(−1)^{χ'}`; the `U(1)`-invariant form is derived here.

## Draft: limits text for a combined PR of the robustness and the Plancherel changes

*Proved* (robustness change, task `T-SF5d`): a robust forcing set keeps forcing under every 2-4 move and,
if it does not contain the moved triangle, under the 3-3 move (Lemma X by blocking sets); robustness is
**not** kept by the 3-3 move in general, shown by an explicit 4-sphere with 20 simplices (kernel-checked
data, independently re-verified by a script). *Not proved*: the 2-4 counterexample (independent script
only; measured at 1 of 67,712 random 2-4 locations); whether the gauge set carried from the boundary of
the 5-simplex stays robust (robust in every sample, not proved); existence of a robust forcing gauge set on
every sphere reached from it. The task stays open. The change corrects the catalogue note and docstrings
on main that called robustness "conjecture, not claimed".

*Proved / documented* (Plancherel change, task `T-HA2`): a catalogue entry for `plancherel` and
`plancherel_trace` with the constant `16π⁴`; the constant is checked by hand on `K`-biinvariant functions
and numerically to 2e-7; the `1/(8π⁴)` of Perez–Rovelli (A11, A16) is four times too large in this
normalization. *Not proved*: the full `L²` theorem (smooth compactly supported functions only); the
section or equation of Knapp (1986, chapter II) and of Gelfand–Graev–Vilenkin (1966) behind the constant
are not located; Rühl's text is seen only through a quotation.

The change combines two related tasks; each keeps its own `Task:` line and has no `Closes` keyword.

## Sources check of the existing `sf9` catalogue entries

Method: `python scripts/sources.py check` (registry shape; passes: 226 references, 187 milestones, 97
results) and a read of the registry's verification record for the cited locations.

| Entry | Cited source location | What the registry verified | What it does not verify |
|---|---|---|---|
| `eprlVertex_coherent`, `k5Contract4_eprlCohNode` | BDFGH, Section 3.4 | the heading "3.4 Exponentiated expression for the four-simplex amplitude" exists in arXiv:0902.1170 | that eq. (17)–(19) say what the note says; the sign `(−1)^χ` of the 15j equation |
| `local_suppression`, `suppression_finite_max`, `coh15j_dichotomy`, `eprlCoh_exp_decay_of_no_gluing` | BDFGH, Section 4 | the heading "4 Asymptotic formula" exists | the exact theorem and its hypotheses; the entries are original statements about integrals, and the source is the context |
| `eprlCohNodeHigh_integral`, `eprlVertexHigh_coherent`, `eprlMapLow_cohState` | BDFGH, Section 3.4 (and EPRL, Section III, eq. (27) in the note) | heading only (EPRL "III. Euclidean theory" is registered) | the equation numbers (16)–(19) and (27) were read from the converted text, not registered; the J-map page is unregistered |

Update after registering the equations: the entries for the node, the vertex sum and the leg amplitude now
cite `eq. (27)` of EPRL (arXiv:0711.0146) and `eq. (16)`, `eq. (17)`, `eq. (19)` of BDFGH (arXiv:0902.1170).
`sources.py verify` finds each label in the full text with its keyword in the surrounding text:

| Location | Keyword found nearby | What the source says there |
|---|---|---|
| EPRL `eq. (27)` | "highest irreducible" | `k = j⁺ + j⁻` for `0 < γ < 1` (the highest irreducible of `H_(j⁺,j⁻)` under the diagonal `SU(2)`), `k = j⁺ − j⁻` for `γ > 1` |
| BDFGH `eq. (16)` | "resolution of the identity" | `1_j = d_j ∫_{SU(2)/U(1)} dn (projector onto the coherent state j,n)`, `d_j = 2j+1`, measure normalized to 1, arbitrary phase for each coherent state |
| BDFGH `eq. (17)` | "second resolution of the identity" | the edge amplitude `P_ab^{γ>1}` with the factor `(−1)^{2j⁻} d²_{j⁺}`, two points `m_ab`, `m_ba` per edge |
| BDFGH `eq. (19)` | "amplitude for" | `f₄ = (−1)^{χ'} ∏ (−1)^{2j⁻} d²_{j⁺} ∫_{Spin(4)⁵} ∏ dG_c ∫ ∏ dm_ab dm_ba e^{S_{γ>1}}` |

What this verifies: that the labelled equation exists in the source with that content nearby. What it does
not: that the library's statement equals the source's. The entries still claim only the context.

Finding before the registration, kept for the record: every `sf9` location verified that a *section exists*,
none an *equation*.

## Sources check of the `γ < 1` identification and of the suppression entries

Same method as above: `sources.py check` passes, and the registry records headings only
(BDFGH `Section 3.4` for the identification entry and `Section 4` for the two suppression entries). The
equations the entries stand next to, read from the full text of arXiv:0902.1170:

| Entry | Source statement it stands next to | What the source says |
|---|---|---|
| `eprlVertex_coherent`, `k5Contract4_eprlCohNode` (γ < 1) | eq. (14), with (13) and (15) | `f₄ = (−1)^{χ'} ∫_{Spin(4)⁵} ∏_a dG_a e^{S_{γ<1}}`, with the propagator `P_ab = ⟨−n_ab\|X⁻_ab\|n_ba⟩^{2j⁻} ⟨−n_ab\|X⁺_ab\|n_ba⟩^{2j⁺}` (13) and the action (15). Prefactor `(−1)^{χ'}` is the source's; the library's `eprlCoh` has no such sign. |
| `local_suppression`, `suppression_finite_max` | Theorem 1, part 3, eq. (22) | for boundary data that is neither a non-degenerate 4-geometry nor a vector geometry, `f₄(ψ_λ) = o(λ^{−M})` for all `M` |
| `coh15j_dichotomy`, `eprlCoh_exp_decay_of_no_gluing` | the same, and the sentence after the proof outline of Section 5 | exponential suppression of points where the modulus is below one; "all other points are exponentially suppressed" (near eq. (37)) |

Findings:

* The suppression entries prove an analytic mechanism (non-stationary phase with finitely many noncritical
  maxima, and a dichotomy for `SU(2)` data). The source's statement (22) is the geometric conclusion that
  non-Regge, non-vector boundary data is suppressed to `o(λ^{−M})`. The library does not prove that
  conclusion: the noncriticality of the maxima is a hypothesis, and for spins that are not areas of the
  boundary geometry it is not shown. The entries do not claim eq. (22).
* The identification entry matches the source's integral up to the source's prefactor `(−1)^{χ'}`, which
  the library does not carry and does not compare.
* Possible registration (not done; it changes the registry): `eq. (14)` with the keyword "re-expressed"
  for the identification entry, and `eq. (22)` with the keyword "supressed" (the source's spelling) for
  the two suppression entries as context. Each would verify the label with its content nearby, as for the
  `γ > 1` entries.

