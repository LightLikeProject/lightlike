# SF1 t1: published values of the Riemannian Barrett–Crane 10j symbol

Status: literature search done, values compared numerically, and three values proved in Lean
(27 Nov 2026): `Tests.bcVertex_half` (7/18), `Tests.bcVertex_one` (307/1500) and
`Tests.bcVertexBC_mixed` (−163/1728), in `Lightlike/SpinFoam/BarrettCraneValues.lean`; the numerical
check is `scripts/spin4/bc10j_check.py`. This note records what is published, the conventions, and which values the
library's `Lightlike.SpinFoam.BC.bcVertex` reproduces.

## Sources read

1. **J. D. Christensen and G. Egan, *An efficient algorithm for the Riemannian 10j symbols*,
   Class. Quantum Grav. 19 (2002) 1185, arXiv:gr-qc/0110045** (HTML rendering of v3, §§1–4 read).
   It gives the algorithm only, with no table of values. The only number in the text is a running
   time. Conventions, verbatim:
   - §2: "We use the convention that spins are non-negative half-integers." A spin `j` labels the
     Spin(4) representation `j ⊗ j`.
   - §2: "j_{1,i} are the spins on the edges joining vertex i to vertex i+1 (modulo 5)", and
     "j_{2,i} are the spins on the edges joining vertex i to vertex i+2 (modulo 5)".
   - §2: the vertices are Barrett–Crane intertwiners, "the unique intertwiners (up to a factor)
     between four balanced representations of Spin(4)". They are given by Barrett and Crane's
     formula, a sum over the internal spin `l` with weight `Δ_l`, where "Δ_l is the value of a loop
     in the spin-l representation, which is just (−1)^{2l}(2l+1)".
   - §2: "(These intertwiners are normalized so that the theta network in the numerator of equation
     (4) has value 1.)"
   - §3, eq. (2): the 10j symbol is `Σ_{l_0…l_4} (∏_k Δ_{l_k})` times the square of one decagonal
     SU(2) network.
2. **J. D. Christensen, *Riemannian 10j symbols*, sample table**: http://jdc.math.uwo.ca/spin-foams/10j-samples/riemannian,
   linked from the arXiv abstract page of gr-qc/0110045. Read in full. "The calculations below were
   done using the algorithm by Christensen and Egan". Three groups:
   - all ten spins equal, "The first column shows twice the spin, and the second column is the value
     of the regular 10j symbol" (2j = 0 … 300);
   - multiples of the ten spins "1 3/2 1/2 1 1/2 1/2 3/2 1/2 1 1";
   - multiples of "1 1 1 1 1 1/2 1/2 1/2 1/2 1/2"; "note that some answers are negative".
   The page states no normalisation or edge order of its own beyond the algorithm's.
3. **G. Egan, *Exact values of some regular Riemannian 10j symbols***: http://www.gregegan.net/SCIENCE/tenJ/tenJ.html,
   linked from the table page. Table "2j+1 | 10j symbol evaluation to 60 digits precision | Exact
   10j symbol evaluation". Rows used here: 2j+1 = 1: `1`; 2: `7 / 18`; 3: `307 / 1 500`;
   4: `9 263 / 73 500`; 5: `197 467 / 2 315 250`.
4. J. C. Baez, J. D. Christensen, G. Egan, *Asymptotics of 10j symbols*, arXiv:gr-qc/0208010, and
   J. C. Baez, J. D. Christensen, *Positivity of spin foam amplitudes*, arXiv:gr-qc/0110044. Their
   text has no Riemannian 10j values at named spins: the second has Lorentzian tables, the first
   fitted coefficients and figures. The second fixes the sign rule ("positive or negative
   depending on whether the sum of the ten spins is an integer or half-integer", abstract).

The search behind catalogue entry LL-0052 ("No published table of 10j values was found") missed the
author's table (2) and Egan's exact values (3).

## Conventions compared with the library

| Christensen–Egan | Library (`BarrettCrane.lean`) | Effect |
|---|---|---|
| spin `j`, half-integer | doubled spin `2j ∈ ℕ` | relabelling |
| BC intertwiner `Σ_l Δ_l ι^θ_l ⊗ ι^θ_l`, trivalent vertices with theta = 1 | `bcNode = Σ_i ι_i ⊗ ι_i`, `ι_i` orthonormal (`fourJ`) | The theta-normalised tree has norm² `±1/Δ_l`, so `Δ_l ι^θ ⊗ ι^θ = ±ι ⊗ ι`. PROXY: argument only; the numbers below agree. |
| sign: negative for a half-integer spin sum | `bcVertex ≥ 0` (`bcVertex_nonneg`); `bcVertexBC = (−1)^{Σ 2j_e} bcVertex` | Published value = `bcVertexBC`. |
| edges `j_{1,i}` (i, i+1), `j_{2,i}` (i, i+2) | edges `0:(0,1) 1:(0,2) 2:(0,3) 3:(0,4) 4:(1,2) 5:(1,3) 6:(1,4) 7:(2,3) 8:(2,4) 9:(3,4)` (`k5Spins`) | `j_{1,·}` → edges 0, 4, 7, 9, 3; `j_{2,·}` → edges 1, 5, 8, 2, 6. |

## Numerical comparison (MEASURED, numerical evidence, not proof)

The library's definition was evaluated directly in floating point: `fourJ` from the Wigner 3j
symbols (SymPy), `k5Legs` (a negated projection is a reversed index), and `edgeSign` on each edge.
Then `bcVertex = Σ_i k5Contract(j; ι_{i_a})²` (`k5Contract4_mul`), with numpy einsum over the ten
edge projections (`scripts/spin4/bc10j_check.py`).

| spins (Christensen–Egan order) | published | `bcVertexBC` (float) |
|---|---|---|
| all 0 | 1 | 1.000000000000000 |
| all 1/2 | 7/18 = 0.388888… | 0.388888888888889 |
| all 1 | 307/1500 = 0.2046666… | 0.204666666666667 |
| all 3/2 | 9263/73500 = 0.1260272108… | 0.126027210884354 |
| 1 3/2 1/2 1 1/2 · 1/2 3/2 1/2 1 1 (multiple 1) | 0.0416666666666666643537 | 0.041666666666667 |
| 1 1 1 1 1 · 1/2 1/2 1/2 1/2 1/2 (multiple 1) | −0.0943287037037036923959 | −0.094328703703704 |

The mixed rows read the ten input spins as `j_{1,0..4}` followed by `j_{2,0..4}`. This order is
PROXY, inferred from the paper's notation. The match of the mixed group-2 row supports it. The group-3 row
would be the same with the two groups of five exchanged, by the symmetry of `K₅`. The negative group-3 value
matches `bcVertexBC`, the sign-corrected vertex.

Wrong-input control: without the `√(k+1)` normalisation of the intertwiners, all spins `1/2` give
0.047839506172840 instead of 0.388888…, so the comparison separates the normalisations.

## What t1 can be in Lean

Candidates, smallest first (each would be a theorem in `Lightlike/SpinFoam/BarrettCraneTests.lean`):
- `bcVertex` with all ten spins `1/2` (doubled `1`) equals `7/18`: 32 channel tuples, each a 15j
  symbol of spin-½ legs with channels in {0, 1};
- all spins `1` equals `307/1500`;
- the negative mixed value, through `bcVertexBC`, giving `−163/1728` (now proved exactly; the table's
  `−0.0943287037037036923959` agrees to double precision).

The library already has the spin-0 value (`Tests.bcVertex_zero`, value 1) and the closed-loop and
triangle values, which are not 4-simplex values. Route: `bcVertex_eq_sum` reduces to 15j symbols,
then `fifteenJSimplex` values from the 6j formula (`Lightlike/Recoupling/FifteenJ.lean`) at doubled
spin 1, using the finite-case method of AGENTS.md: an integer table and kernel `decide`. This is not
started at the time of the search; it is now done for the three values above. The value at ten
spins 3/2 (1024 channel tuples) is beyond this kernel evaluation and is checked numerically only.
