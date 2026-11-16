import Lightlike.SpinFoam.Move33
import Lightlike.SpinFoam.Move24Global
import Lightlike.SpinFoam.Move15Global
import Lightlike.SpinFoam.GaugeChain
import Lightlike.SpinFoam.ForcingMoves
import Lightlike.SpinFoam.ForcingMove33
import Lightlike.SpinFoam.ForcingMove24
import Lightlike.SpinFoam.ForcingRobust
import Lightlike.Recoupling.Tests
import Lightlike.FourD.Tests
import Lightlike.Spin4.EPRLTests
import Lightlike.Spin4.Tests
import Lightlike.SpinFoam.EPRLTests
import Lightlike.SpinFoam.BarrettCraneTests

/-!
# Trust checks for the Ooguri vertex amplitude, the Pachner moves and the gauge rule

Each check states a value, a wrong input that gives another value, and a non-vacuity example in its
own docstring; this header keeps the values, the library results under test, the sources and the
numerical cross-checks. A check marked "numerical evidence" is not part of the proof.

## The vertex conventions (`Vertex.lean`)

`vertexContr_eq` proves for all colourings that the contraction of the canonical intertwiners with
`FourD`'s strand rule is the closed form `vertexAmp` (the 15j symbol `fifteenJSimplex` in the
pentagram order `(s₀, s₂, s₄, s₁, s₃)`, with signs), for both orientations. At the level of positions,
`vertexAmp s col = ampP J K` with `J p q = col (s∖{s_p, s_q})` and `K i = col (s∖{sᵢ})` holds by
definition.

| check | value | theorem |
|---|---|---|
| all spins `0` | `1` | `ampP_zero`, `vertexAmp_zero` |
| spins `½` on `{0,1}ᶜ, {0,3}ᶜ, {1,2}ᶜ, {2,3}ᶜ`, virtual spins `½` on the tetrahedra at positions `1, 2` | `1/2` | `ampP_cycle` |
| spins `½` on the three triangles and three tetrahedra through the edge of positions `0, 1` | `1/√2` | `ampP_tri` |

The last two values agree with the numerical contraction of the five intertwiners with the strand
rule, for both orientations (`scripts/spinfoam/vertex_check.py`; numerical evidence).
`tri_of_ampP_ne_zero` (`Ooguri.lean`) lists the ten triads that a nonzero vertex amplitude needs.
Wrong input: the 15j symbol with the identity labelling `(s₀, s₁, s₂, s₃, s₄)`, that is
`fifteenJSimplex` fed with the vertex order of `Complex4`, gives `0` on the cycle colouring
(`fifteenJSimplex_identity_labels`).

## The Pachner moves (`Move33.lean`, `Move24.lean`, `Move24Global.lean`, `Move15.lean`, `Move15Global.lean`)

The invariance theorems `amplitudeGF_move33`, `amplitudeGF_move24`, `amplitudeGF_move15` and the
gauge-fixed `amplitudeGF_move33_gauge` are applied to genuine complexes, with every cutoff
hypothesis checked by `decide +kernel`:

| move | complex | cutoffs | non-vacuity | gauge-fixed |
|---|---|---|---|---|
| 3-3 `{0,2,3} → {4,5,6}` (`isMove33`) | `Lightlike.FourD.Tests.K2` (34 triangles, 30 tetrahedra, 12 4-simplices) | `3` on the two inner triangles, `6` on every tetrahedron, `1` elsewhere (`cut33`) | `amplitudeGF_move33_example` | `amplitudeGF_move33_T33`, `amplitudeGF_move33_star1` (`star1`) |
| 2-4 `{0,1,2,3} → {5,6}` (`isMove24`) | `K1`, the 1-5 subdivision of `∂Δ⁵` | `cut24` | `amplitudeGF_move24_example` | `amplitudeGF_move24_gauge_example` (`T14`, `isGauge_T14`) |
| 1-5 `{0,1,2,3,4} → {6}` (`isMove15`) | `K0 = ∂Δ⁵` | `cut15`; the sixteen conditions `Cut15` | `amplitudeGF_move15_example` | `amplitudeGF_move15_gauge_example` (`starK0`, `isGauge_starK0`) |

The vertices of the removed simplex are read in sorted order through `orderEmbOfFin_unique`.
`T33` fixes every colourable face of `K2` at spin `0` except the removed triangle `{0,2,3}` and its
three tetrahedra.

## The gauge-fixed state sum

`amplitudeGFWith` takes an arbitrary vertex amplitude `a` (`amplitudeGF` is the case `a = ampP`), so
that a wrong amplitude can be run through the state sum.

| check | value | theorem |
|---|---|---|
| `∂Δ⁵`, every face outside the edge `{0,1}` fixed at `0`, cutoff `½` on the faces through it | `5` (`1 + 4`) | `amplitudeGF_sphere6_edge` |
| 3-3 move on `K2` with the gauge set `T33`, both sides | `1` | `amplitudeGF_T33` |
| the same with the wrong amplitude `ampBad` | `1` after, `3` before | `ampBad_breaks_move33` |
| `∂Δ⁵`, the ten triangles through a vertex, or ten with no common vertex | gauge rule holds; sum `1` for every cutoff | `isGauge_starT`, `amplitudeGF_starT`, `isGauge_twistT`, `amplitudeGF_twistT` |
| `K2`, the fifteen triangles through a vertex, before and after the 3-3 move | gauge rule holds; sum `1` | `isGauge_star1`, `amplitudeGF_K2_star1`, `amplitudeGF_K3_star1` |
| `gauge9`, `starT` without one triangle | breaks the rule (9 triangles, `E − V + 1 = 10`); sum `5` at cutoff `½` | `not_isGauge_gauge9`, `amplitudeGF_gauge9_one` |

`ampBad` is `ampP` plus `1` on the single colouring `(e34, 0)`, where `ampP` vanishes. Before the 3-3
move the colouring `colStar` (spin `½` on `{0,2,3}`) gives each of the three 4-simplices around that
triangle this colouring and adds `2 · 1³`; after the move only the zero colouring survives. So the
invariance `amplitudeGF_move33` depends on the vertex amplitude, not only on the combinatorics.

The first value agrees with the numerical state sum over all virtual spins
(`scripts/recoupling/ooguri_moves_check.py`; numerical evidence). On `∂Δ⁵` a set of ten triangles
obeys the gauge rule (`Ooguri.lean`) exactly when it forces all twenty triangles to spin `0`, for all
184756 such sets (numerical evidence).

## Inputs: the Pachner moves (`Lightlike/FourD/Pachner.lean`)

`Lightlike.FourD.Tests` computes the moves `K0 → K1 → K2 → K3` on `∂Δ⁵` and their inverses directly;
the two general theorems are checked against it:

| check | value | theorem | computed |
|---|---|---|---|
| the moves with `σ`, `τ` exchanged undo the three moves | `K1 → K0`, `K2 → K1`, `K3 → K2` | `pachner_move_move_predicts` | `pachner_move_move_direct` |
| Euler characteristic `euler4` of `K1`, `K2`, `K3` | `2` | `pachner_euler4_predicts` | `pachner_euler4_direct` |

Wrong inputs: repeating the 1-5 move on `K1` without exchanging `σ`, `τ` returns `K1`
(`pachner_repeat_fails`); without the signs `(-1)^k` the face count `f₀ + ⋯ + f₄` is `62` on `K0` and
`92` on `K1` (`pachner_unsigned_euler_fails`). `scripts/recoupling/ooguri_moves_check.py` repeats the
sequence independently (numerical evidence).

## Inputs from `Lightlike/Spin4`

| result | check | value | wrong input |
|---|---|---|---|
| EPRL injectivity (`eprlIntertwiner_injective_iff`, `Lightlike/Spin4/Fusion.lean`) | `γ = 1/3`, `J = (3,3,3,3)`: injective (`eprl_injective_iff_parity_predicts`; `injective_third` from `eprlIntertwiner_injective`). `γ = 1/2`, `J = (4,4,4,16)`: no SU(2) intertwiners, `Σ 2j⁺ = 21` odd, injective (`eprl_injective_iff_empty_predicts`, `eprl_injective_iff_empty_direct`) | | the parity-only criterion fails at `(4,4,4,16)` (`eprl_injective_parity_only_fails`; with `not_injective_counterexample` of `Lightlike.Spin4.Test`) |
| Clebsch–Gordan on the diagonal (`spin4_diag_clebschGordan`, `Lightlike/Spin4/ClebschGordan.lean`) | trace of `cgMat 1 1` at `diag(e^{iθ}, e^{−iθ})` | `2 cos 2θ + 2` (`cg_trace_half_half_predicts`, `cg_trace_half_half_direct`; `cg_trace_predicts` from `trace_eq_of_intertwine`; `card_cgIdx` of `Lightlike.Spin4.Test`) | off the diagonal the trace is `−4`, not `4` (`cg_offdiag_fails`) |
| double cover (`toSO4_eq_one_iff`, `Lightlike/Spin4/SO4.lean`) | `(−1,−1)` acts as the identity; `(1,−1)`, `(−1,1)` as `x ↦ −x`; `(i,1)`: `1 ↦ i`, `j ↦ k` (from `toSO4_apply`) | `so4_kernel_predicts`, `so4_half_kernel_predicts`, `so4_left_i_values` | "`toSO4` is injective" fails (`so4_trivial_kernel_fails`) |
| completeness (`spin4Rep_complete`, `Lightlike/Spin4/Completeness.lean`) | `vecRep` (the SO(4) matrix `toSO4Mat`) has labels `(½, ½)` | `completeness_vector_predicts`, `completeness_vector_labels`, `completeness_vector_direct` (`half_half_equiv_vector`) | `(3/2, 0)`, `(0, 3/2)` also have dimension 4 but are not equivalent to `vecRep` (`completeness_vector_wrong_labels`; the continuity hypothesis is needed: `Lightlike.Spin4.Test.spin4Rep_complete_needs_continuity`) |

The labels `label_half_four`, `label_half_sixteen`, `label_third_three` and `vecRep` (`continuous_vecRep`,
`vecRep_irreducible`) satisfy the hypotheses. Independent computations in
`scripts/recoupling/intertwiner_check.py` (sections 6–9: intertwiner counts, characters for doubled
`n, m ≤ 8`, the 64 pairs from the quaternion group, the torus characters) agree (numerical evidence).

## References

* `ooguri-1992`: the vertex amplitude and the state sum that these checks test.
* `kaminski-kisielowski-lewandowski-2011`, Theorem 2: the injectivity criterion that
  `eprlIntertwiner_injective_iff` extends.
* `edmonds-1957`, Ch. 3: the coupling of two angular momenta, `j₊ ⊗ j₋ = ⊕_{k} (j₊ + j₋ − k)`, that
  `spin4_diag_clebschGordan` proves on the diagonal SU(2).

The number of divergent spin sums, `E − V + 1` on a 4-sphere, which the gauge rule matches, is from
Bonzom–Smerlak, *Bubble divergences from cellular cohomology*, Lett. Math. Phys. 93, 295 (2010),
arXiv:1004.5196 (not in `sources.yaml`).
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.SpinFoam

/-- **Value check.** With all spins `0` the vertex amplitude is `1`. -/
theorem ampP_zero : ampP (fun _ _ => 0) (fun _ => 0) = 1 := by
  simp [ampP, fifteenJSimplex_zero]

/-- **Value check (any 4-simplex).** The vertex amplitude of the zero colouring is `1`. -/
theorem vertexAmp_zero {V : Type*} [LinearOrder V] (s : Finset V) (hs : #s = 5) :
    vertexAmp s hs (fun _ => 0) = 1 :=
  ampP_zero

/-- The triangle spins of the cycle colouring: `½` (doubled `1`) on `{0,1}ᶜ, {0,3}ᶜ, {1,2}ᶜ,
{2,3}ᶜ`. -/
def cycleJ : Fin 5 → Fin 5 → ℕ :=
  ![![0, 1, 0, 1, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 0, 0]]

/-- The virtual spins of the cycle colouring: `½` at positions `1` and `2`. -/
def cycleK : Fin 5 → ℕ := ![0, 1, 1, 0, 0]

@[simp] lemma cycleJ_01 : cycleJ 0 1 = 1 := rfl
@[simp] lemma cycleJ_02 : cycleJ 0 2 = 0 := rfl
@[simp] lemma cycleJ_03 : cycleJ 0 3 = 1 := rfl
@[simp] lemma cycleJ_04 : cycleJ 0 4 = 0 := rfl
@[simp] lemma cycleJ_12 : cycleJ 1 2 = 1 := rfl
@[simp] lemma cycleJ_13 : cycleJ 1 3 = 0 := rfl
@[simp] lemma cycleJ_14 : cycleJ 1 4 = 0 := rfl
@[simp] lemma cycleJ_23 : cycleJ 2 3 = 1 := rfl
@[simp] lemma cycleJ_24 : cycleJ 2 4 = 0 := rfl
@[simp] lemma cycleJ_34 : cycleJ 3 4 = 0 := rfl
@[simp] lemma cycleK_0 : cycleK 0 = 0 := rfl
@[simp] lemma cycleK_1 : cycleK 1 = 1 := rfl
@[simp] lemma cycleK_2 : cycleK 2 = 1 := rfl
@[simp] lemma cycleK_3 : cycleK 3 = 0 := rfl
@[simp] lemma cycleK_4 : cycleK 4 = 0 := rfl

/-- **Value check.** The vertex amplitude of the cycle colouring is `1/2` (numerically, the direct
contraction with the strand rule gives `0.5` for both orientations). -/
theorem ampP_cycle : ampP cycleJ cycleK = 1 / 2 := by
  have h := Lightlike.Recoupling.Tests.fifteenJSimplex_cycle
  simp only [ampP, cycleJ_01, cycleJ_02, cycleJ_03, cycleJ_04, cycleJ_12, cycleJ_13, cycleJ_14,
    cycleJ_23, cycleJ_24, cycleJ_34, cycleK_0, cycleK_1, cycleK_2, cycleK_3, cycleK_4, h]
  norm_num

/-- An intertwiner vanishes unless its first two spins and its virtual spin form a triad. -/
lemma fourJ_eq_zero_of_not_tri {j₁ j₂ j₃ j₄ k : ℕ} (h : ¬Tri j₁ j₂ k) (m₁ m₂ m₃ m₄ : ℤ) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  unfold fourJ
  rw [sum_eq_zero fun μ _ => by rw [threeJ_eq_zero_of_not (fun h' => h h'.1)]; ring, mul_zero]

/-- **Wrong input.** The 15j symbol with the identity labelling of the vertices (the vertex order
of `Complex4` fed directly to `fifteenJSimplex`) vanishes on the cycle colouring, where the vertex
amplitude is `1/2`: at the tetrahedron opposite `s₀` it couples the spins `½` and `0` to the
virtual spin `0`. -/
theorem fifteenJSimplex_identity_labels :
    fifteenJSimplex (cycleJ 0 1) (cycleJ 0 2) (cycleJ 0 3) (cycleJ 0 4) (cycleJ 1 2) (cycleJ 1 3)
      (cycleJ 1 4) (cycleJ 2 3) (cycleJ 2 4) (cycleJ 3 4) (cycleK 0) (cycleK 1) (cycleK 2)
      (cycleK 3) (cycleK 4) = 0 ∧ ampP cycleJ cycleK ≠ 0 := by
  refine ⟨?_, by rw [ampP_cycle]; norm_num⟩
  have hT : ¬Tri 1 0 0 := by unfold Tri; omega
  simp only [cycleJ_01, cycleJ_02, cycleJ_03, cycleJ_04, cycleJ_12, cycleJ_13, cycleJ_14,
    cycleJ_23, cycleJ_24, cycleJ_34, cycleK_0, cycleK_1, cycleK_2, cycleK_3, cycleK_4]
  unfold fifteenJSimplex
  have h0 : ∀ m₁ m₂ m₃ m₄ : ℤ, fourJ 1 0 1 0 0 m₁ m₂ m₃ m₄ = 0 :=
    fourJ_eq_zero_of_not_tri (j₃ := 1) (j₄ := 0) hT
  simp only [h0, zero_mul, mul_zero, sum_const_zero]

open Lightlike.FourD.Tests in
/-- The cutoffs of the non-vacuity check of the 3-3 move: `3` on the inner triangles `{0,2,3}` and
`{4,5,6}`, `6` on the tetrahedra, `1` on the other triangles. -/
def cut33 (f : Finset (Fin 8)) : ℕ :=
  if f = {0, 2, 3} ∨ f = {4, 5, 6} then 3 else if #f = 4 then 6 else 1

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the 3-3 invariance.** On the closed 4-sphere `K2` of the `FourD` tests, the
3-3 move `{0,2,3} → {4,5,6}` leaves the state sum with the cutoffs `cut33` unchanged; every
hypothesis of `amplitudeGF_move33` is checked by the kernel. -/
theorem amplitudeGF_move33_example :
    amplitudeGF (K2.move isMove33) ∅ cut33 = amplitudeGF K2 ∅ cut33 :=
  amplitudeGF_move33 K2 isMove33 (by decide) ∅ (by simp) cut33
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

open Lightlike.FourD.Tests in
/-- The cutoffs of the non-vacuity check of the 2-4 move: `12` on `{3,5,6}`, `24` on `{1,5,6}` and
`{2,5,6}`, `100` on the tetrahedra, `1` on the other faces. -/
def cut24 (f : Finset (Fin 8)) : ℕ :=
  if f = {3, 5, 6} then 12 else if f = {1, 5, 6} ∨ f = {2, 5, 6} then 24
  else if #f = 4 then 100 else 1

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the 2-4 invariance.** On `K1` (the 1-5 subdivision of `∂Δ⁵`), the 2-4 move
`{0,1,2,3} → {5,6}` leaves the state sum with the cutoffs `cut24` unchanged, the new triangle
`{0,5,6}` being fixed; every hypothesis of `amplitudeGF_move24` is checked by the kernel. -/
theorem amplitudeGF_move24_example :
    amplitudeGF (K1.move isMove24) {{0, 5, 6}} cut24 = amplitudeGF K1 ∅ cut24 := by
  have hσ : #({0, 1, 2, 3} : Finset (Fin 8)) = 4 := by decide
  have eo : ∀ k : Fin 4, ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ k = Fin.castLE (by omega) k := fun k => by
    have := Finset.orderEmbOfFin_unique (s := ({0, 1, 2, 3} : Finset (Fin 8))) hσ
      (f := fun k : Fin 4 => Fin.castLE (by omega) k)
      (fun k => by revert k; decide) (fun a b hab => hab)
    exact (congrFun this k).symm
  have e0 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 0 = 0 := by rw [eo]; rfl
  have e1 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 1 = 1 := by rw [eo]; rfl
  have e2 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 2 = 2 := by rw [eo]; rfl
  have e3 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 3 = 3 := by rw [eo]; rfl
  have h := amplitudeGF_move24 K1 isMove24 (σ := {0, 1, 2, 3}) (τ := {5, 6}) hσ ∅
    (by simp) cut24 (by decide +kernel) (by rw [e3]; decide +kernel)
    (by rw [e3, e2]; decide +kernel) (by rw [e3, e1]; decide +kernel)
    (by rw [e3, e2, e1]; decide +kernel)
  rw [e0] at h
  simpa using h

open Lightlike.FourD.Tests in
/-- A gauge set of `K1`: fourteen triangles (`#edges - #vertices + 1 = 20 - 7 + 1`) that collapse
with the edges onto the vertex `0`. The cone from one vertex is not a gauge set here, since `5` and
`6` are not adjacent; the collapse order is a certificate found by a search outside Lean. -/
def T14 : Finset (Finset (Fin 8)) :=
  {{1, 2, 4}, {0, 2, 4}, {1, 3, 6}, {0, 1, 2}, {0, 4, 5}, {0, 2, 5}, {1, 2, 6},
    {1, 3, 4}, {3, 4, 6}, {1, 2, 3}, {1, 4, 5}, {0, 3, 4}, {0, 3, 6}, {2, 3, 5}}

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the gauge rule on `K1`.** `T14` obeys the gauge rule: the vertices, the edges
and `T14` collapse onto the vertex `0`, each step checked by the kernel. -/
theorem isGauge_T14 : IsGauge K1 T14 :=
  ⟨by decide +kernel, collapsible_of_collapsesBy (v := 0)
    (l := [({3, 5}, {2, 3, 5}), ({0, 6}, {0, 3, 6}), ({0, 3}, {0, 3, 4}), ({1, 5}, {1, 4, 5}),
      ({2, 3}, {1, 2, 3}), ({4, 6}, {3, 4, 6}), ({3, 4}, {1, 3, 4}), ({2, 6}, {1, 2, 6}),
      ({2, 5}, {0, 2, 5}), ({4, 5}, {0, 4, 5}), ({0, 1}, {0, 1, 2}), ({1, 3}, {1, 3, 6}),
      ({0, 4}, {0, 2, 4}), ({1, 2}, {1, 2, 4}), ({3}, {3, 6}), ({6}, {1, 6}), ({5}, {0, 5}),
      ({1}, {1, 4}), ({4}, {2, 4}), ({2}, {0, 2})])
    (by decide +kernel)⟩

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the gauge-fixed 2-4 invariance.** On `K1` with the nonempty gauge set `T14`,
the 2-4 move `{0,1,2,3} → {5,6}` gives the gauge set `T14 ∪ {{0,5,6}}` of the moved complex and the
same state sum for the cutoffs `cut24`; every hypothesis of `amplitudeGF_move24_gauge` is checked
by the kernel. Only the equality of the two sums is shown, not their value. -/
theorem amplitudeGF_move24_gauge_example :
    IsGauge (K1.move isMove24) (insert {0, 5, 6} T14) ∧
      amplitudeGF (K1.move isMove24) (insert {0, 5, 6} T14) cut24 = amplitudeGF K1 T14 cut24 := by
  have hσ : #({0, 1, 2, 3} : Finset (Fin 8)) = 4 := by decide
  have eo : ∀ k : Fin 4, ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ k = Fin.castLE (by omega) k := fun k => by
    have := Finset.orderEmbOfFin_unique (s := ({0, 1, 2, 3} : Finset (Fin 8))) hσ
      (f := fun k : Fin 4 => Fin.castLE (by omega) k)
      (fun k => by revert k; decide) (fun a b hab => hab)
    exact (congrFun this k).symm
  have e0 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 0 = 0 := by rw [eo]; rfl
  have e1 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 1 = 1 := by rw [eo]; rfl
  have e2 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 2 = 2 := by rw [eo]; rfl
  have e3 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ 3 = 3 := by rw [eo]; rfl
  have h := amplitudeGF_move24_gauge K1 isMove24 (σ := {0, 1, 2, 3}) (τ := {5, 6}) hσ T14
    isGauge_T14 cut24 (by decide +kernel) (by rw [e3]; decide +kernel)
    (by rw [e3, e2]; decide +kernel) (by rw [e3, e1]; decide +kernel)
    (by rw [e3, e2, e1]; decide +kernel)
  rw [e0] at h
  simpa using h

open Lightlike.FourD.Tests in
/-- The cutoffs of the non-vacuity check of the 1-5 move: `3` on the triangles `{6,1,2}`, `{6,1,3}`
and `{6,2,3}`, `10` on the tetrahedra, `1` on the other faces. -/
def cut15 (f : Finset (Fin 8)) : ℕ :=
  if f = {6, 1, 2} ∨ f = {6, 1, 3} ∨ f = {6, 2, 3} then 3 else if #f = 4 then 10 else 1

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the 1-5 invariance.** On `K0 = ∂Δ⁵`, the 1-5 move `{0,1,2,3,4} → {6}` leaves
the state sum with the cutoffs `cut15` unchanged, the four new triangles `{6,0,j}` being fixed;
every hypothesis of `amplitudeGF_move15` is checked by the kernel. -/
theorem amplitudeGF_move15_example :
    amplitudeGF (K0.move isMove15) {{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} cut15 =
      amplitudeGF K0 ∅ cut15 := by
  have hσ : #({0, 1, 2, 3, 4} : Finset (Fin 8)) = 5 := by decide
  have eo : ∀ k : Fin 5, ({0, 1, 2, 3, 4} : Finset (Fin 8)).orderEmbOfFin hσ k =
      Fin.castLE (by omega) k := fun k => by
    have := Finset.orderEmbOfFin_unique (s := ({0, 1, 2, 3, 4} : Finset (Fin 8))) hσ
      (f := fun k : Fin 5 => Fin.castLE (by omega) k)
      (fun k => by revert k; decide) (fun a b hab => hab)
    exact (congrFun this k).symm
  have e : ⇑(({0, 1, 2, 3, 4} : Finset (Fin 8)).orderEmbOfFin hσ) =
      fun k : Fin 5 => Fin.castLE (by omega) k := funext eo
  have hcut : Move15.Cut15 cut15 (Move15.triV (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8))
      (Move15.teV (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8))
      (Move15.otV (fun k : Fin 5 => Fin.castLE (by omega) k)) := by
    unfold Move15.Cut15 Move15.triV Move15.teV Move15.otV
    decide +kernel
  have hg : Move15.gaugeTri (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8) ∪ ∅ =
      {{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} := by
    unfold Move15.gaugeTri
    decide +kernel
  have h := Move15.amplitudeGF_move15 K0 isMove15 (σ := {0, 1, 2, 3, 4}) (τ := {6}) hσ (v := 6) rfl ∅
    (by simp) cut15 (by rw [e]; exact hcut)
  rw [e, hg] at h
  exact h

open Lightlike.FourD.Tests in
/-- The ten triangles of `K0 = ∂Δ⁵` through the vertex `5`: the cone from `5` on the edges of the
opposite 4-simplex, the same set as `starT` with the vertex type `Fin 8`. -/
def starK0 : Finset (Finset (Fin 8)) := K0.tris.filter (5 ∈ ·)

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the gauge rule on `K0`.** `starK0` obeys the gauge rule: the vertices, the
edges and `starK0` collapse onto the vertex `5`. -/
theorem isGauge_starK0 : IsGauge K0 starK0 :=
  ⟨filter_subset _ _, collapsible_of_collapsesBy (v := 5)
    (l := [({0, 1}, {0, 1, 5}), ({0, 2}, {0, 2, 5}), ({0, 3}, {0, 3, 5}), ({0, 4}, {0, 4, 5}),
      ({1, 2}, {1, 2, 5}), ({1, 3}, {1, 3, 5}), ({1, 4}, {1, 4, 5}), ({2, 3}, {2, 3, 5}),
      ({2, 4}, {2, 4, 5}), ({3, 4}, {3, 4, 5}), ({0}, {0, 5}), ({1}, {1, 5}), ({2}, {2, 5}),
      ({3}, {3, 5}), ({4}, {4, 5})])
    (by decide +kernel)⟩

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the gauge-fixed 1-5 invariance.** On `K0 = ∂Δ⁵` with the ten gauge triangles
`starK0`, the 1-5 move `{0,1,2,3,4} → {6}` gives the gauge set `starK0` plus the four triangles
`{6,0,j}` of the moved complex and the same state sum for the cutoffs `cut15`; every hypothesis of
`amplitudeGF_move15_gauge` is checked by the kernel. Only the equality of the two sums is shown,
not their value. -/
theorem amplitudeGF_move15_gauge_example :
    IsGauge (K0.move isMove15) ({{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} ∪ starK0) ∧
      amplitudeGF (K0.move isMove15) ({{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} ∪ starK0) cut15 =
        amplitudeGF K0 starK0 cut15 := by
  have hσ : #({0, 1, 2, 3, 4} : Finset (Fin 8)) = 5 := by decide
  have eo : ∀ k : Fin 5, ({0, 1, 2, 3, 4} : Finset (Fin 8)).orderEmbOfFin hσ k =
      Fin.castLE (by omega) k := fun k => by
    have := Finset.orderEmbOfFin_unique (s := ({0, 1, 2, 3, 4} : Finset (Fin 8))) hσ
      (f := fun k : Fin 5 => Fin.castLE (by omega) k)
      (fun k => by revert k; decide) (fun a b hab => hab)
    exact (congrFun this k).symm
  have e : ⇑(({0, 1, 2, 3, 4} : Finset (Fin 8)).orderEmbOfFin hσ) =
      fun k : Fin 5 => Fin.castLE (by omega) k := funext eo
  have hcut : Move15.Cut15 cut15 (Move15.triV (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8))
      (Move15.teV (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8))
      (Move15.otV (fun k : Fin 5 => Fin.castLE (by omega) k)) := by
    unfold Move15.Cut15 Move15.triV Move15.teV Move15.otV
    decide +kernel
  have hg : Move15.gaugeTri (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8) =
      {{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} := by
    unfold Move15.gaugeTri
    decide +kernel
  have h := Move15.amplitudeGF_move15_gauge K0 isMove15 (σ := {0, 1, 2, 3, 4}) (τ := {6}) hσ
    (v := 6) rfl starK0 isGauge_starK0 cut15 (by rw [e]; exact hcut)
  rw [e, hg] at h
  exact h

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the forcing lemma for the 1-5 move.** On `K0 = ∂Δ⁵` the ten triangles
`starK0` force every triangle (each of the ten tetrahedra through the vertex `5` forces one triangle,
checked by the kernel). After the 1-5 move `{0,1,2,3,4} → {6}`, the set `starK0` plus the four
triangles `{6,0,j}` forces every triangle of the moved complex. This is the gauge set of
`amplitudeGF_move15_gauge_example`. -/
theorem forces_move15_example :
    Forces (K0.move isMove15) (K0.move isMove15).tris
      ({{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} ∪ starK0) := by
  have hσ : #({0, 1, 2, 3, 4} : Finset (Fin 8)) = 5 := by decide
  have hF : Forces K0 K0.tris starK0 := forces_of_forcesBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}),
      ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}),
      ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}),
      ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)
  have hg : Move15.gaugeTri (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8) =
      {{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} := by
    unfold Move15.gaugeTri
    decide +kernel
  have hsurj : ∀ x : Fin 8, x ∈ ({0, 1, 2, 3, 4} : Finset (Fin 8)) ↔
      ∃ j : Fin 5, (fun k : Fin 5 => (Fin.castLE (by omega) k : Fin 8)) j = x := by decide
  have h := Move15.forces_move15 isMove15 (σ := {0, 1, 2, 3, 4}) (τ := {6}) (v := 6) rfl hσ
    (a := fun k : Fin 5 => Fin.castLE (by omega) k) hsurj hF
  rwa [hg] at h

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the forcing characterization for the 3-3 move.** On `K2` (the boundary of the
5-simplex after a 1-5 and a 2-4 move) the fifteen triangles `T33` force every triangle, and so does
their closure under the tetrahedra that do not contain `{0,2,3}`: no forcing step needs the moved
triangle. After the 3-3 move `{0,2,3} → {4,5,6}` the same set forces every triangle of the new
complex. Every hypothesis of `Forcing33.forces_move33_iff` is checked by the kernel. -/
theorem forces_move33_example :
    Forces (K2.move isMove33) (K2.move isMove33).tris
      ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) := by
  have hσ : #({0, 2, 3} : Finset (Fin 8)) = 3 := by decide
  have hT : ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) ⊆ K2.tris := by decide +kernel
  have hσT : ({0, 2, 3} : Finset (Fin 8)) ∉ ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) := by decide
  have hF : Forces K2 K2.tris ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) := forces_of_forcesBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)
  have hS : ForcesIn (K2.tets.filter fun t => ¬ ({0, 2, 3} : Finset (Fin 8)) ⊆ t)
      (K2.tris.erase {0, 2, 3}) ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) := forcesIn_of_forcesInBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {2, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)
  exact (Forcing33.forces_move33_iff isMove33 hσ hT hσT hF).mpr hS

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the forcing characterization for the 2-4 move.** On `K1` (the boundary of the
5-simplex after a 1-5 move) the fourteen triangles `T24` force every triangle, and so does their
closure under the tetrahedra other than `{0,1,2,3}`. After the 2-4 move `{0,1,2,3} → {5,6}`, the set
`T24` together with the triangle `{0,5,6}` forces every triangle of the new complex `K2`. Every
hypothesis of `Forcing24.forces_move24_iff` is checked by the kernel. -/
theorem forces_move24_example :
    Forces K2 K2.tris (insert (insert 0 {5, 6}) ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8)))) := by
  have hσ : #({0, 1, 2, 3} : Finset (Fin 8)) = 4 := by decide
  have hT : ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) ⊆ K1.tris := by decide +kernel
  have hF : Forces K1 K1.tris ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) := forces_of_forcesBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)
  have hS : ForcesIn (K1.tets.filter fun t => ¬ ({0, 1, 2, 3} : Finset (Fin 8)) ⊆ t) K1.tris
      ({{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}} : Finset (Finset (Fin 8))) := forcesIn_of_forcesInBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)
  exact (Forcing24.forces_move24_iff isMove24 hσ (a := 0) (by decide) hT hF).mpr hS

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the robust 1-5 move.** On `K0 = ∂Δ⁵` the ten triangles `starK0` through the vertex
`5` force every triangle with any one of the fifteen tetrahedra removed (`Robust K0 starK0`, checked
by the kernel from explicit forcing steps for each removed tetrahedron). After the 1-5 move
`{0,1,2,3,4} → {6}`, the set `starK0` plus the four triangles `{6,0,j}` is robust for the moved
complex (`robust_move15`). -/
theorem robust_move15_example :
    Robust (K0.move isMove15) ({{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} ∪ starK0) := by
  have hσ : #({0, 1, 2, 3, 4} : Finset (Fin 8)) = 5 := by decide
  have hR : Robust K0 starK0 := robust_of_robustBy (L := [
    ({0, 1, 2, 3}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 2, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 2, 5}, [({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 3}, {0, 1, 2})]),
    ({0, 1, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 3}, {0, 1, 3})]),
    ({0, 1, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {0, 1, 4})]),
    ({0, 2, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 3}, {0, 2, 3})]),
    ({0, 2, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {0, 2, 4})]),
    ({0, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 3, 4}, {0, 3, 4})]),
    ({1, 2, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 3}, {1, 2, 3})]),
    ({1, 2, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {1, 2, 4})]),
    ({1, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 3, 4}, {1, 3, 4})]),
    ({2, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({0, 2, 3, 4}, {2, 3, 4})])])
    (by decide +kernel)
  have hg : Move15.gaugeTri (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8) =
      {{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} := by
    unfold Move15.gaugeTri
    decide +kernel
  have hsurj : ∀ x : Fin 8, x ∈ ({0, 1, 2, 3, 4} : Finset (Fin 8)) ↔
      ∃ j : Fin 5, (fun k : Fin 5 => (Fin.castLE (by omega) k : Fin 8)) j = x := by decide
  have h := Move15.robust_move15 isMove15 (σ := {0, 1, 2, 3, 4}) (τ := {6}) (v := 6) rfl hσ
    (a := fun k : Fin 5 => Fin.castLE (by omega) k) hsurj hR
  rwa [hg] at h

/-- The fourteen triangles of the 2-4 examples: the ten triangles `starK0` through the vertex `5` of `K0`
and the four triangles `{6, 0, j}` of the 1-5 move. -/
def T24 : Finset (Finset (Fin 8)) :=
  {{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}}

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the robust 2-4 move.** The fourteen triangles `T24` are robust for `K1` (the
boundary of the 5-simplex after a 1-5 move): they force every triangle with any one of the
twenty-five tetrahedra removed, checked by the kernel from explicit forcing steps. By
`forces_move24_of_robust`, together with the triangle `{0, 5, 6}` they force every triangle of `K2`, the
complex after the 2-4 move `{0,1,2,3} → {5,6}`. -/
theorem forces_move24_of_robust_example :
    Forces K2 K2.tris (insert (insert 0 {5, 6}) T24) := by
  have hσ : #({0, 1, 2, 3} : Finset (Fin 8)) = 4 := by decide
  have hT : T24 ⊆ K1.tris := by decide +kernel
  have hR : Robust K1 T24 := robust_of_robustBy (L := [
    ({0, 1, 2, 3}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 2, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 2, 5}, [({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 2, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 3}, {0, 1, 2})]),
    ({0, 1, 2, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 2, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 3}, {0, 1, 3})]),
    ({0, 1, 3, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {1, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {0, 1, 4})]),
    ({0, 1, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {1, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {2, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 3}, {0, 2, 3})]),
    ({0, 2, 3, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {2, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {0, 2, 4})]),
    ({0, 2, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({1, 3, 4, 6}, {3, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 3, 4}, {0, 3, 4})]),
    ({0, 3, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({1, 3, 4, 6}, {3, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 6}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 3, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 6}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 6}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 3, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({2, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 6}, {2, 3, 4})]),
    ({2, 3, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})])])
    (by decide +kernel)
  exact forces_move24_of_robust isMove24 hσ (a := 0) (by decide) hT hR

/-- The fifteen triangles of the 3-3 robust example: the ten triangles through the vertex `5` of `K0`,
the four triangles `{6, 0, j}` of the 1-5 move and the triangle `{0, 5, 6}` of the 2-4 move. -/
def T15 : Finset (Finset (Fin 8)) :=
  {{0, 1, 5}, {0, 1, 6}, {0, 2, 5}, {0, 2, 6}, {0, 3, 5}, {0, 3, 6}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}, {1, 2, 5}, {1, 3, 5}, {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}}

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the robust 3-3 move (Lemma X).** The fifteen triangles `T15` are robust for `K2`
(the boundary of the 5-simplex after a 1-5 and a 2-4 move): they force every triangle with any one of
the thirty tetrahedra removed, checked by the kernel from explicit forcing steps. The triangle
`{0, 2, 3}` is not in `T15`, so `Forcing33.forces_move33_of_robust` shows that `T15` forces every
triangle of the complex after the 3-3 move `{0,2,3} → {4,5,6}`. -/
theorem forces_move33_of_robust_example :
    Forces (K2.move isMove33) (K2.move isMove33).tris T15 := by
  have hσ : #({0, 2, 3} : Finset (Fin 8)) = 3 := by decide
  have hT : T15 ⊆ K2.tris := by decide +kernel
  have hσT : ({0, 2, 3} : Finset (Fin 8)) ∉ T15 := by decide
  have hR : Robust K2 T15 := robust_of_robustBy (L := [
    ({0, 1, 2, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 2, 5}, [({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 2, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {0, 1, 2})]),
    ({0, 1, 2, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 2, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 3, 4}, {0, 1, 3})]),
    ({0, 1, 3, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {1, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {1, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {0, 1, 4})]),
    ({0, 1, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {1, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 1, 5, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 5, 6}, {1, 5, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {2, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 2, 3, 4}, {0, 2, 3})]),
    ({0, 2, 3, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 3, 6}, {2, 3, 6}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 2, 4}, {0, 2, 4})]),
    ({0, 2, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 2, 5, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 2, 5, 6}, {2, 5, 6}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({1, 3, 4, 6}, {3, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({0, 1, 3, 4}, {0, 3, 4})]),
    ({0, 3, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({1, 3, 4, 6}, {3, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({0, 3, 5, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({1, 3, 5, 6}, {3, 5, 6}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 3, 4}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 3, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 6}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 3, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 6}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 2, 5, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 6}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 3, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({1, 3, 5, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({2, 3, 4, 5}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 6}, {2, 3, 4})]),
    ({2, 3, 4, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})]),
    ({2, 3, 5, 6}, [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 3, 6}, {1, 3, 6}), ({0, 1, 4, 5}, {0, 1, 4}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 3, 6}, {2, 3, 6}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}), ({0, 3, 4, 5}, {0, 3, 4}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}), ({2, 3, 4, 5}, {2, 3, 4})])])
    (by decide +kernel)
  exact Forcing33.forces_move33_of_robust isMove33 hσ hT hσT hR

open Lightlike.FourD.Tests in
/-- The cutoffs of the chain example: `3` on the triangles `{6,1,2}`, `{6,1,3}` and `{6,2,3}` (the
1-5 move asks for them), `40` on `{3,5,6}`, `100` on `{1,5,6}` and `{2,5,6}`, `1000` on the
tetrahedra and `1` on the other faces; the cutoff conditions of both moves hold. -/
def cutChain (f : Finset (Fin 8)) : ℕ :=
  if f = {6, 1, 2} ∨ f = {6, 1, 3} ∨ f = {6, 2, 3} then 3
  else if f = {3, 5, 6} then 40 else if f = {1, 5, 6} ∨ f = {2, 5, 6} then 100
  else if #f = 4 then 1000 else 1

open Lightlike.FourD.Tests in
/-- **Non-vacuity of the chain theorem.** On `∂Δ⁵` with the ten gauge triangles `starK0` and the
cutoffs `cutChain`, the 1-5 move `{0,1,2,3,4} → {6}` followed by the 2-4 move `{0,1,2,3} → {5,6}` is a
chain of two steps of `GFStep4`, and `amplitudeGF_eqvGen4` gives the equality of the state sums at
its two ends. The gauge set after the first step is the one that the second step needs
(`GFStep4.isGauge`); the cutoffs are not changed along the chain. -/
theorem amplitudeGF_chain_example :
    amplitudeGF (K1.move isMove24)
        (insert {0, 5, 6} ({{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} ∪ starK0)) cutChain =
      amplitudeGF K0 starK0 cutChain := by
  have hσ : #({0, 1, 2, 3, 4} : Finset (Fin 8)) = 5 := by decide
  have eo : ∀ k : Fin 5, ({0, 1, 2, 3, 4} : Finset (Fin 8)).orderEmbOfFin hσ k =
      Fin.castLE (by omega) k := fun k => by
    have := Finset.orderEmbOfFin_unique (s := ({0, 1, 2, 3, 4} : Finset (Fin 8))) hσ
      (f := fun k : Fin 5 => Fin.castLE (by omega) k)
      (fun k => by revert k; decide) (fun a b hab => hab)
    exact (congrFun this k).symm
  have e : ⇑(({0, 1, 2, 3, 4} : Finset (Fin 8)).orderEmbOfFin hσ) =
      fun k : Fin 5 => Fin.castLE (by omega) k := funext eo
  have hcut : Move15.Cut15 cutChain (Move15.triV (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8))
      (Move15.teV (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8))
      (Move15.otV (fun k : Fin 5 => Fin.castLE (by omega) k)) := by
    unfold Move15.Cut15 Move15.triV Move15.teV Move15.otV
    decide +kernel
  have hg : Move15.gaugeTri (fun k : Fin 5 => Fin.castLE (by omega) k) (6 : Fin 8) =
      {{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} := by
    unfold Move15.gaugeTri
    decide +kernel
  have s1 := GFStep4.move15 isMove15 hσ (v := 6) rfl isGauge_starK0 (cut := cutChain)
    (by rw [e]; exact hcut)
  rw [e, hg] at s1
  have hσ' : #({0, 1, 2, 3} : Finset (Fin 8)) = 4 := by decide
  have eo' : ∀ k : Fin 4, ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ' k =
      Fin.castLE (by omega) k := fun k => by
    have := Finset.orderEmbOfFin_unique (s := ({0, 1, 2, 3} : Finset (Fin 8))) hσ'
      (f := fun k : Fin 4 => Fin.castLE (by omega) k)
      (fun k => by revert k; decide) (fun a b hab => hab)
    exact (congrFun this k).symm
  have e0 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ' 0 = 0 := by rw [eo']; rfl
  have e1 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ' 1 = 1 := by rw [eo']; rfl
  have e2 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ' 2 = 2 := by rw [eo']; rfl
  have e3 : ({0, 1, 2, 3} : Finset (Fin 8)).orderEmbOfFin hσ' 3 = 3 := by rw [eo']; rfl
  have s2 := GFStep4.move24 isMove24 (σ := {0, 1, 2, 3}) (τ := {5, 6}) hσ'
    (T := {{6, 0, 1}, {6, 0, 2}, {6, 0, 3}, {6, 0, 4}} ∪ starK0)
    (s1.isGauge isGauge_starK0) (cut := cutChain) (by decide +kernel) (by rw [e3]; decide +kernel)
    (by rw [e3, e2]; decide +kernel) (by rw [e3, e1]; decide +kernel)
    (by rw [e3, e2, e1]; decide +kernel)
  rw [e0] at s2
  have := amplitudeGF_eqvGen4 (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ s1)
    (Relation.EqvGen.rel _ _ s2))
  simpa using this.symm

/-! ## Trust checks of the gauge-fixed state sum

The state sum with an arbitrary vertex amplitude (`amplitudeGFWith`), and value checks on `∂Δ⁵`
and on `K2`. The support of `ampP` (`tri_of_ampP_ne_zero`) is in `Ooguri.lean`. -/

open Lightlike.FourD Lightlike.FourD.Tests

variable {V : Type*} [LinearOrder V]

/-- The amplitude of a 4-simplex for an arbitrary vertex amplitude `a` in place of `ampP`, read off
the colouring at the positions of the sorted vertices exactly as `simpW` does. It runs the state
sum with a deliberately wrong vertex amplitude. -/
noncomputable def simpWith (a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ) (col : Finset V → ℕ)
    (s : Finset V) : ℝ :=
  if h : #s = 5 then
    a (fun p q => col ((s.erase (s.orderEmbOfFin h p)).erase (s.orderEmbOfFin h q)))
      (fun i => col (s.erase (s.orderEmbOfFin h i)))
  else 0

/-- The weight of a colouring for the vertex amplitude `a`, as in `weight`. -/
noncomputable def weightWith (a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ) (K : Complex4 V)
    (col : Finset V → ℕ) : ℝ :=
  (∏ f ∈ K.tris, ((col f : ℝ) + 1)) * ∏ s ∈ K.simps, simpWith a col s

/-- The gauge-fixed state sum for the vertex amplitude `a`, as in `amplitudeGF`. -/
noncomputable def amplitudeGFWith (a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ) (K : Complex4 V)
    (T : Finset (Finset V)) (cut : Finset V → ℕ) : ℝ :=
  ∑ c ∈ (colFaces K \ T).pi (fun f => range (cut f + 1)),
    weightWith a K (Lightlike.PR.extS (colFaces K \ T) c)

/-- For the Ooguri amplitude `ampP`, `simpWith` is `simpW`. -/
lemma simpWith_ampP (col : Finset V → ℕ) (s : Finset V) : simpWith ampP col s = simpW col s :=
  rfl

/-- For the Ooguri amplitude `ampP`, `weightWith` is `weight`. -/
lemma weightWith_ampP (K : Complex4 V) (col : Finset V → ℕ) :
    weightWith ampP K col = weight K col := rfl

/-- For the Ooguri amplitude `ampP`, `amplitudeGFWith` is `amplitudeGF`. -/
lemma amplitudeGFWith_ampP (K : Complex4 V) (T : Finset (Finset V)) (cut : Finset V → ℕ) :
    amplitudeGFWith ampP K T cut = amplitudeGF K T cut := rfl

/-- Evaluation from a table of faces: if `v` lists the vertices of `s` in increasing order and
`T p q` is `s` without `v p` and `v q` (so `T p p` is the tetrahedron opposite `v p`), the amplitude
of `s` is `a` at the colours of the table. -/
lemma simpWith_of_table (a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ) (col : Finset V → ℕ)
    {s : Finset V} (hs : #s = 5) {v : Fin 5 → V} (hmem : ∀ i, v i ∈ s) (hv : StrictMono v)
    {T : Fin 5 → Fin 5 → Finset V} (hT : ∀ p q, (s.erase (v p)).erase (v q) = T p q) :
    simpWith a col s = a (fun p q => col (T p q)) (fun i => col (T i i)) := by
  have e : v = s.orderEmbOfFin hs := orderEmbOfFin_unique hs hmem hv
  unfold simpWith
  rw [dite_eq_left hs, ← e]
  congr 1
  · funext p q; rw [hT]
  · funext i; rw [← hT i i, erase_idem]

/-- `simpWith_of_table` with the colours of the table given explicitly. -/
lemma simpWith_eq (a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ) {col : Finset V → ℕ}
    {s : Finset V} (hs : #s = 5) {v : Fin 5 → V} (hmem : ∀ i, v i ∈ s) (hv : StrictMono v)
    (T : Fin 5 → Fin 5 → Finset V) (hT : ∀ p q, (s.erase (v p)).erase (v q) = T p q)
    {J : Fin 5 → Fin 5 → ℕ} {K : Fin 5 → ℕ} (hJ : ∀ p q, col (T p q) = J p q)
    (hK : ∀ i, col (T i i) = K i) : simpWith a col s = a J K := by
  rw [simpWith_of_table a col hs hmem hv hT]
  congr 1
  · funext p q; exact hJ p q
  · funext i; exact hK i

/-- The amplitude of `s` depends only on the colours of its triangles and tetrahedra. -/
lemma simpWith_congr (a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ) {col col' : Finset V → ℕ}
    {s : Finset V} (h : ∀ f ⊆ s, (#f = 3 ∨ #f = 4) → col f = col' f) :
    simpWith a col s = simpWith a col' s := by
  unfold simpWith
  split_ifs with hs
  · congr 1
    · funext p q
      apply h _ ((erase_subset _ _).trans (erase_subset _ _))
      by_cases hpq : p = q
      · subst hpq
        right
        rw [erase_eq_of_notMem (notMem_erase _ _), card_erase_of_mem (s.orderEmbOfFin_mem hs p),
          hs]
      · left
        have hne : s.orderEmbOfFin hs q ≠ s.orderEmbOfFin hs p :=
          fun he => hpq ((s.orderEmbOfFin hs).injective he).symm
        rw [card_erase_of_mem (mem_erase.mpr ⟨hne, s.orderEmbOfFin_mem hs q⟩),
          card_erase_of_mem (s.orderEmbOfFin_mem hs p), hs]
    · funext i
      apply h _ (erase_subset _ _)
      right
      rw [card_erase_of_mem (s.orderEmbOfFin_mem hs i), hs]
  · rfl

/-- If `a` is `1` on the zero colouring, the zero colouring has weight `1`. -/
lemma weightWith_zero {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : a (fun _ _ => 0) (fun _ => 0) = 1) (K : Complex4 V) :
    weightWith a K (fun _ => 0) = 1 := by
  unfold weightWith simpWith
  simp only [Nat.cast_zero, zero_add, prod_const_one, one_mul]
  exact prod_eq_one fun s hs => by rw [dite_eq_left (K.card_eq s hs)]; exact ha

/-- If the colouring vanishes on every face that does not contain `σ`, only the 4-simplices
containing `σ` contribute to the product of the vertex amplitudes: the others see the zero
colouring. -/
lemma prod_simpWith_filter {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : a (fun _ _ => 0) (fun _ => 0) = 1) (K : Complex4 V) {col : Finset V → ℕ}
    (σ : Finset V) (hcol : ∀ f, ¬σ ⊆ f → col f = 0) :
    ∏ s ∈ K.simps, simpWith a col s = ∏ s ∈ K.simps.filter (σ ⊆ ·), simpWith a col s := by
  rw [← prod_filter_mul_prod_filter_not K.simps (σ ⊆ ·)]
  rw [prod_eq_one (s := K.simps.filter (¬σ ⊆ ·)) fun s hs => ?_, mul_one]
  obtain ⟨hs, hσ⟩ := mem_filter.1 hs
  rw [simpWith_congr a (col' := fun _ => 0) fun f hf _ => hcol f fun h => hσ (h.trans hf)]
  unfold simpWith
  rw [dite_eq_left (K.card_eq s hs)]
  exact ha

/-! ### A value with six nonzero spins -/

/-- The intertwiner `(½, 0, ½, 0; ½)` with zero projections on its spin-`0` legs: `±1/√2` on the two
opposite projections, `0` otherwise. -/
lemma fourJ_h0h0 (m m' : ℤ) :
    fourJ 1 0 1 0 1 m 0 m' 0 =
      if m = 1 ∧ m' = -1 then 1 / Real.sqrt 2 else if m = -1 ∧ m' = 1 then -1 / Real.sqrt 2
      else 0 := by
  unfold fourJ
  have hI : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  have hc1 : ∀ μ : ℤ, threeJ 1 0 1 m 0 μ = threeJ 0 1 1 0 μ m :=
    fun μ => (threeJ_cycle 1 1 0 μ m 0).trans (threeJ_cycle 0 1 1 0 μ m)
  have hc2 : ∀ μ : ℤ, threeJ 1 1 0 (-μ) m' 0 = threeJ 0 1 1 0 (-μ) m' :=
    fun μ => threeJ_cycle 0 1 1 0 (-μ) m'
  simp only [hI, hc1, hc2, Recoupling.Tests.threeJ_0hh_table,
    sum_insert (show (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) by decide),
    sum_insert (show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide), sum_singleton]
  norm_num
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  split_ifs <;> first | omega | (simp only [mul_zero, add_zero, zero_add]; done) |
    (field_simp; done) | (field_simp; nlinarith [h2])

/-- The intertwiner `(0, ½, 0, ½; ½)` with zero projections on its spin-`0` legs: `±1/√2` on the two
opposite projections, `0` otherwise. -/
lemma fourJ_0h0h (m m' : ℤ) :
    fourJ 0 1 0 1 1 0 m 0 m' =
      if m = 1 ∧ m' = -1 then 1 / Real.sqrt 2 else if m = -1 ∧ m' = 1 then -1 / Real.sqrt 2
      else 0 := by
  unfold fourJ
  have hI : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  have hc : ∀ μ : ℤ, threeJ 1 0 1 (-μ) 0 m' = threeJ 0 1 1 0 m' (-μ) :=
    fun μ => (threeJ_cycle 1 1 0 m' (-μ) 0).trans (threeJ_cycle 0 1 1 0 m' (-μ))
  simp only [hI, hc, Recoupling.Tests.threeJ_0hh_table,
    sum_insert (show (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) by decide),
    sum_insert (show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide), sum_singleton]
  norm_num
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  split_ifs <;> first | omega | (simp only [mul_zero, add_zero, zero_add]; done) |
    (field_simp; done) | (field_simp; nlinarith [h2])

/-- **Value check.** The 15j symbol with spin `½` on three triangles and three virtual spins (the
faces through one edge, below) is `1/√2`. -/
theorem fifteenJSimplex_tri : fifteenJSimplex 0 0 0 0 1 0 1 0 1 0 0 1 1 0 1 = 1 / Real.sqrt 2 := by
  unfold fifteenJSimplex
  simp only [Nat.cast_zero, neg_zero, Icc_self, sum_singleton, fourJ_zero, neg_zero]
  simp only [fourJ_h0h0, fourJ_0h0h, Recoupling.Tests.fourJ_0hh0, edgeSign]
  have hI : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  simp only [hI, sum_insert (show (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) by decide),
    sum_insert (show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide), sum_singleton]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  norm_num
  field_simp
  nlinarith [h2]

/-- Spin `1/2` (doubled `1`) on the faces among positions `2, 3, 4`, zero elsewhere. -/
def triJ : Fin 5 → Fin 5 → ℕ := fun p q => if 2 ≤ (p : ℕ) ∧ 2 ≤ (q : ℕ) then 1 else 0

/-- Spin `1/2` on the tetrahedra opposite positions `2, 3, 4`, zero elsewhere. -/
def triK : Fin 5 → ℕ := fun i => if 2 ≤ (i : ℕ) then 1 else 0

/-- **Value check.** The vertex amplitude of the colouring with spin `½` on the three triangles and
the three tetrahedra through the edge of positions `0, 1` is `1/√2`. The direct contraction of the
five intertwiners with the strand rule gives the same value for both orientations
(`scripts/spinfoam/vertex_check.py`; numerical evidence, not proof). -/
theorem ampP_tri : ampP triJ triK = 1 / Real.sqrt 2 := by
  have e : ampP triJ triK = (-1 : ℝ) ^ 0 * (-1 : ℝ) ^ 0 * (-1 : ℝ) ^ 1 * (-1 : ℝ) ^ 0 *
      (-1 : ℝ) ^ 0 * ((-1 : ℝ) ^ 1 * (-1 : ℝ) ^ 1 * (-1 : ℝ) ^ 1) * (-1 : ℝ) ^ 1 * (-1 : ℝ) ^ 1 *
      fifteenJSimplex 0 0 0 0 1 0 1 0 1 0 0 1 1 0 1 := rfl
  rw [e, fifteenJSimplex_tri]
  norm_num

/-! ### Support of the vertex amplitude on explicit 4-simplices -/

/-- A triad with first spin `0` has equal second and third spins. -/
lemma tri_zero_left {y z : ℕ} (h : Tri 0 y z) : y = z := by
  obtain ⟨-, h1, -, h3⟩ := h; omega

/-- A triad with second spin `0` has equal first and third spins. -/
lemma tri_zero_mid {x z : ℕ} (h : Tri x 0 z) : x = z := by
  obtain ⟨-, h1, h2, -⟩ := h; omega

/-- A triad with third spin `0` has equal first and second spins. -/
lemma tri_zero_right {x y : ℕ} (h : Tri x y 0) : x = y := by
  obtain ⟨-, -, h2, h3⟩ := h; omega

/-- If the vertex amplitude is nonzero and the triangles opposite the position pairs `02, 03, 04,
12, 14` have spin `0`, then the triangles opposite `23, 24, 34` and the tetrahedra opposite
`2, 3, 4` all carry the same spin. -/
lemma ampP_eq_of_ne_zero {J : Fin 5 → Fin 5 → ℕ} {K : Fin 5 → ℕ} (h : ampP J K ≠ 0)
    (h02 : J 0 2 = 0) (h03 : J 0 3 = 0) (h04 : J 0 4 = 0) (h12 : J 1 2 = 0) (h14 : J 1 4 = 0) :
    J 2 3 = K 2 ∧ J 2 4 = K 2 ∧ J 3 4 = K 2 ∧ K 3 = K 2 ∧ K 4 = K 2 := by
  obtain ⟨-, ⟨h2a, h2b⟩, ⟨h3a, h3b⟩, -, ⟨h5a, -⟩⟩ := tri_of_ampP_ne_zero h
  rw [h12] at h2a; rw [h02] at h2b; rw [h14] at h3a; rw [h04] at h3b; rw [h03] at h5a
  have e1 := tri_zero_mid h2a
  have e2 := tri_zero_right h2b
  have e3 := tri_zero_left h3a
  have e4 := tri_zero_mid h3b
  have e5 := tri_zero_left h5a
  omega

/-- `ampP_eq_of_ne_zero` for a 4-simplex given by a table of faces. -/
lemma simpW_rel {col : Finset V → ℕ} {s : Finset V} (hs : #s = 5) {v : Fin 5 → V}
    (hmem : ∀ i, v i ∈ s) (hv : StrictMono v) {T : Fin 5 → Fin 5 → Finset V}
    (hT : ∀ p q, (s.erase (v p)).erase (v q) = T p q) (h : simpW col s ≠ 0)
    (h0 : col (T 0 2) = 0 ∧ col (T 0 3) = 0 ∧ col (T 0 4) = 0 ∧ col (T 1 2) = 0 ∧
      col (T 1 4) = 0) :
    col (T 2 3) = col (T 2 2) ∧ col (T 2 4) = col (T 2 2) ∧ col (T 3 4) = col (T 2 2) ∧
      col (T 3 3) = col (T 2 2) ∧ col (T 4 4) = col (T 2 2) := by
  rw [← simpWith_ampP, simpWith_of_table ampP col hs hmem hv hT] at h
  exact ampP_eq_of_ne_zero h h0.1 h0.2.1 h0.2.2.1 h0.2.2.2.1 h0.2.2.2.2

/-- Extending the restriction to `S` of a colouring that vanishes outside `S` gives it back. -/
lemma extS_eq_self {S : Finset (Finset V)} {col : Finset V → ℕ} (h : ∀ f ∉ S, col f = 0) :
    Lightlike.PR.extS S (fun f _ => col f) = col := by
  funext f
  unfold Lightlike.PR.extS
  split_ifs with hf
  · rfl
  · exact (h f hf).symm

/-- `Lightlike.PR.extS` evaluated on a face of `S`. -/
lemma extS_apply {S : Finset (Finset V)} (c : ∀ f ∈ S, ℕ) {f : Finset V} (hf : f ∈ S) :
    Lightlike.PR.extS S c f = c f hf := by
  unfold Lightlike.PR.extS; rw [dite_eq_left hf]

/-- The face table of the 4-simplex `{0, 1, 3, 4, 5}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab01345 : Fin 5 → Fin 5 → Finset (Fin 6) :=
  ![![{1, 3, 4, 5}, {3, 4, 5}, {1, 4, 5}, {1, 3, 5}, {1, 3, 4}],
    ![{3, 4, 5}, {0, 3, 4, 5}, {0, 4, 5}, {0, 3, 5}, {0, 3, 4}],
    ![{1, 4, 5}, {0, 4, 5}, {0, 1, 4, 5}, {0, 1, 5}, {0, 1, 4}],
    ![{1, 3, 5}, {0, 3, 5}, {0, 1, 5}, {0, 1, 3, 5}, {0, 1, 3}],
    ![{1, 3, 4}, {0, 3, 4}, {0, 1, 4}, {0, 1, 3}, {0, 1, 3, 4}]]

/-- The face table of the 4-simplex `{0, 1, 2, 4, 5}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab01245 : Fin 5 → Fin 5 → Finset (Fin 6) :=
  ![![{1, 2, 4, 5}, {2, 4, 5}, {1, 4, 5}, {1, 2, 5}, {1, 2, 4}],
    ![{2, 4, 5}, {0, 2, 4, 5}, {0, 4, 5}, {0, 2, 5}, {0, 2, 4}],
    ![{1, 4, 5}, {0, 4, 5}, {0, 1, 4, 5}, {0, 1, 5}, {0, 1, 4}],
    ![{1, 2, 5}, {0, 2, 5}, {0, 1, 5}, {0, 1, 2, 5}, {0, 1, 2}],
    ![{1, 2, 4}, {0, 2, 4}, {0, 1, 4}, {0, 1, 2}, {0, 1, 2, 4}]]

/-- The face table of the 4-simplex `{0, 1, 2, 3, 5}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab01235 : Fin 5 → Fin 5 → Finset (Fin 6) :=
  ![![{1, 2, 3, 5}, {2, 3, 5}, {1, 3, 5}, {1, 2, 5}, {1, 2, 3}],
    ![{2, 3, 5}, {0, 2, 3, 5}, {0, 3, 5}, {0, 2, 5}, {0, 2, 3}],
    ![{1, 3, 5}, {0, 3, 5}, {0, 1, 3, 5}, {0, 1, 5}, {0, 1, 3}],
    ![{1, 2, 5}, {0, 2, 5}, {0, 1, 5}, {0, 1, 2, 5}, {0, 1, 2}],
    ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}, {0, 1, 2, 3}]]

/-- The face table of the 4-simplex `{0, 1, 2, 3, 4}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab01234 : Fin 5 → Fin 5 → Finset (Fin 6) :=
  ![![{1, 2, 3, 4}, {2, 3, 4}, {1, 3, 4}, {1, 2, 4}, {1, 2, 3}],
    ![{2, 3, 4}, {0, 2, 3, 4}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}],
    ![{1, 3, 4}, {0, 3, 4}, {0, 1, 3, 4}, {0, 1, 4}, {0, 1, 3}],
    ![{1, 2, 4}, {0, 2, 4}, {0, 1, 4}, {0, 1, 2, 4}, {0, 1, 2}],
    ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}, {0, 1, 2, 3}]]

/-- The face table of the 4-simplex `{0, 2, 3, 5, 6}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab02356 : Fin 5 → Fin 5 → Finset (Fin 8) :=
  ![![{2, 3, 5, 6}, {3, 5, 6}, {2, 5, 6}, {2, 3, 6}, {2, 3, 5}],
    ![{3, 5, 6}, {0, 3, 5, 6}, {0, 5, 6}, {0, 3, 6}, {0, 3, 5}],
    ![{2, 5, 6}, {0, 5, 6}, {0, 2, 5, 6}, {0, 2, 6}, {0, 2, 5}],
    ![{2, 3, 6}, {0, 3, 6}, {0, 2, 6}, {0, 2, 3, 6}, {0, 2, 3}],
    ![{2, 3, 5}, {0, 3, 5}, {0, 2, 5}, {0, 2, 3}, {0, 2, 3, 5}]]

/-- The face table of the 4-simplex `{0, 2, 3, 4, 6}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab02346 : Fin 5 → Fin 5 → Finset (Fin 8) :=
  ![![{2, 3, 4, 6}, {3, 4, 6}, {2, 4, 6}, {2, 3, 6}, {2, 3, 4}],
    ![{3, 4, 6}, {0, 3, 4, 6}, {0, 4, 6}, {0, 3, 6}, {0, 3, 4}],
    ![{2, 4, 6}, {0, 4, 6}, {0, 2, 4, 6}, {0, 2, 6}, {0, 2, 4}],
    ![{2, 3, 6}, {0, 3, 6}, {0, 2, 6}, {0, 2, 3, 6}, {0, 2, 3}],
    ![{2, 3, 4}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}, {0, 2, 3, 4}]]

/-- The face table of the 4-simplex `{0, 2, 3, 4, 5}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab02345 : Fin 5 → Fin 5 → Finset (Fin 8) :=
  ![![{2, 3, 4, 5}, {3, 4, 5}, {2, 4, 5}, {2, 3, 5}, {2, 3, 4}],
    ![{3, 4, 5}, {0, 3, 4, 5}, {0, 4, 5}, {0, 3, 5}, {0, 3, 4}],
    ![{2, 4, 5}, {0, 4, 5}, {0, 2, 4, 5}, {0, 2, 5}, {0, 2, 4}],
    ![{2, 3, 5}, {0, 3, 5}, {0, 2, 5}, {0, 2, 3, 5}, {0, 2, 3}],
    ![{2, 3, 4}, {0, 3, 4}, {0, 2, 4}, {0, 2, 3}, {0, 2, 3, 4}]]

/-- The face table of the 4-simplex `{2, 3, 4, 5, 6}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab23456 : Fin 5 → Fin 5 → Finset (Fin 8) :=
  ![![{3, 4, 5, 6}, {4, 5, 6}, {3, 5, 6}, {3, 4, 6}, {3, 4, 5}],
    ![{4, 5, 6}, {2, 4, 5, 6}, {2, 5, 6}, {2, 4, 6}, {2, 4, 5}],
    ![{3, 5, 6}, {2, 5, 6}, {2, 3, 5, 6}, {2, 3, 6}, {2, 3, 5}],
    ![{3, 4, 6}, {2, 4, 6}, {2, 3, 6}, {2, 3, 4, 6}, {2, 3, 4}],
    ![{3, 4, 5}, {2, 4, 5}, {2, 3, 5}, {2, 3, 4}, {2, 3, 4, 5}]]

/-- The face table of the 4-simplex `{0, 3, 4, 5, 6}`: entry `(p, q)` is the simplex without its
`p`-th and `q`-th vertices. -/
def tab03456 : Fin 5 → Fin 5 → Finset (Fin 8) :=
  ![![{3, 4, 5, 6}, {4, 5, 6}, {3, 5, 6}, {3, 4, 6}, {3, 4, 5}],
    ![{4, 5, 6}, {0, 4, 5, 6}, {0, 5, 6}, {0, 4, 6}, {0, 4, 5}],
    ![{3, 5, 6}, {0, 5, 6}, {0, 3, 5, 6}, {0, 3, 6}, {0, 3, 5}],
    ![{3, 4, 6}, {0, 4, 6}, {0, 3, 6}, {0, 3, 4, 6}, {0, 3, 4}],
    ![{3, 4, 5}, {0, 4, 5}, {0, 3, 5}, {0, 3, 4}, {0, 3, 4, 5}]]


/-! ### Value on the boundary of the 5-simplex -/

/-- The colourable faces of the boundary `∂Δ⁵` that contain the edge `{0, 1}`. -/
def sphereFree : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5},
    {0, 1, 3, 4}, {0, 1, 3, 5}, {0, 1, 4, 5}}

/-- Colour `1` (spin `1/2`) on the faces of `sphereFree`, `0` elsewhere. -/
def sphereCol (f : Finset (Fin 6)) : ℕ := if f ∈ sphereFree then 1 else 0

/-- The colouring `sphereCol` of `∂Δ⁵` has weight `4`: the four triangles of spin `½` give
`2⁴ = 16`, the four 4-simplices through the edge `{0, 1}` give `1/√2` each, and the other two
see the zero colouring. -/
theorem weight_sphereCol : weight sphere6 sphereCol = 4 := by
  rw [← weightWith_ampP]
  unfold weightWith
  have htri : ∏ f ∈ sphere6.tris, ((sphereCol f : ℝ) + 1) = 16 := by
    have h : ∏ f ∈ sphere6.tris, (sphereCol f + 1) = 16 := by decide +kernel
    exact_mod_cast h
  have hsub : ∀ f ∈ sphereFree, ({0, 1} : Finset (Fin 6)) ⊆ f := by decide
  rw [htri, prod_simpWith_filter (col := sphereCol) ampP_zero sphere6 {0, 1}
    fun f hf => ite_eq_right fun hm => hf (hsub f hm)]
  have hfil : sphere6.simps.filter (({0, 1} : Finset (Fin 6)) ⊆ ·) =
      {{0, 1, 3, 4, 5}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 4}} := by decide +kernel
  rw [hfil, prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_singleton]
  have e2 : simpWith ampP sphereCol {0, 1, 3, 4, 5} = ampP triJ triK :=
    simpWith_eq ampP (by decide) (v := ![0, 1, 3, 4, 5]) (by decide)
      (Fin.strictMono_iff_lt_succ.2 (by decide)) tab01345 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have e3 : simpWith ampP sphereCol {0, 1, 2, 4, 5} = ampP triJ triK :=
    simpWith_eq ampP (by decide) (v := ![0, 1, 2, 4, 5]) (by decide)
      (Fin.strictMono_iff_lt_succ.2 (by decide)) tab01245 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have e4 : simpWith ampP sphereCol {0, 1, 2, 3, 5} = ampP triJ triK :=
    simpWith_eq ampP (by decide) (v := ![0, 1, 2, 3, 5]) (by decide)
      (Fin.strictMono_iff_lt_succ.2 (by decide)) tab01235 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have e5 : simpWith ampP sphereCol {0, 1, 2, 3, 4} = ampP triJ triK :=
    simpWith_eq ampP (by decide) (v := ![0, 1, 2, 3, 4]) (by decide)
      (Fin.strictMono_iff_lt_succ.2 (by decide)) tab01234 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have hq : 1 / Real.sqrt 2 * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [e2, e3, e4, e5, ampP_tri,
    show ∀ x : ℝ, 16 * (x * (x * (x * x))) = 16 * ((x * x) * (x * x)) from fun x => by ring, hq]
  norm_num

/-- On `∂Δ⁵`, a colouring supported on `sphereFree` whose vertex amplitudes are all nonzero is
constant on `sphereFree`. -/
lemma sphere_rel {col : Finset (Fin 6) → ℕ} (hS : ∀ s ∈ sphere6.simps, simpW col s ≠ 0)
    (hn : ∀ f ∉ sphereFree, col f = 0) : ∀ f ∈ sphereFree, col f = col {0, 1, 2} := by
  have r2 : col {0, 1, 5} = col {0, 1, 4, 5} ∧ col {0, 1, 4} = col {0, 1, 4, 5} ∧
      col {0, 1, 3} = col {0, 1, 4, 5} ∧ col {0, 1, 3, 5} = col {0, 1, 4, 5} ∧
      col {0, 1, 3, 4} = col {0, 1, 4, 5} :=
    simpW_rel (s := {0, 1, 3, 4, 5}) (T := tab01345) (by decide) (v := ![0, 1, 3, 4, 5])
      (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide +kernel)
      (hS _ (by decide +kernel))
      ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide)⟩
  have r3 : col {0, 1, 5} = col {0, 1, 4, 5} ∧ col {0, 1, 4} = col {0, 1, 4, 5} ∧
      col {0, 1, 2} = col {0, 1, 4, 5} ∧ col {0, 1, 2, 5} = col {0, 1, 4, 5} ∧
      col {0, 1, 2, 4} = col {0, 1, 4, 5} :=
    simpW_rel (s := {0, 1, 2, 4, 5}) (T := tab01245) (by decide) (v := ![0, 1, 2, 4, 5])
      (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide +kernel)
      (hS _ (by decide +kernel))
      ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide)⟩
  have r4 : col {0, 1, 5} = col {0, 1, 3, 5} ∧ col {0, 1, 3} = col {0, 1, 3, 5} ∧
      col {0, 1, 2} = col {0, 1, 3, 5} ∧ col {0, 1, 2, 5} = col {0, 1, 3, 5} ∧
      col {0, 1, 2, 3} = col {0, 1, 3, 5} :=
    simpW_rel (s := {0, 1, 2, 3, 5}) (T := tab01235) (by decide) (v := ![0, 1, 2, 3, 5])
      (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide +kernel)
      (hS _ (by decide +kernel))
      ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide), hn _ (by decide)⟩
  intro f hf
  simp only [sphereFree, mem_insert, mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- **Value check of the gauge-fixed state sum.** On the 4-sphere `∂Δ⁵` (`sphere6`), with every face
outside `sphereFree` fixed at spin `0` and the cutoff `½` on the triangles and tetrahedra through
the edge `{0, 1}`, the state sum is `1 + 4 = 5`: only the zero colouring and the constant
colouring `½` contribute. The direct numerical state sum, with every face summed over its
admissible spins, gives `5` too (`scripts/recoupling/ooguri_moves_check.py`). -/
theorem amplitudeGF_sphere6_edge :
    amplitudeGF sphere6 (colFaces sphere6 \ sphereFree) (fun _ => 1) = 5 := by
  unfold amplitudeGF
  rw [Finset.sdiff_sdiff_eq_self (show sphereFree ⊆ colFaces sphere6 by decide +kernel)]
  have h012 : ({0, 1, 2} : Finset (Fin 6)) ∈ sphereFree := by decide
  have hm0 : (fun _ _ => 0 : ∀ f ∈ sphereFree, ℕ) ∈ sphereFree.pi fun _ => range (1 + 1) :=
    mem_pi.2 fun _ _ => by simp
  have hm1 : (fun _ _ => 1 : ∀ f ∈ sphereFree, ℕ) ∈ sphereFree.pi fun _ => range (1 + 1) :=
    mem_pi.2 fun _ _ => by simp
  have w0 : weight sphere6 (Lightlike.PR.extS sphereFree fun _ _ => 0) = 1 := by
    rw [extS_eq_self (col := fun _ => 0) fun _ _ => rfl, ← weightWith_ampP]
    exact weightWith_zero ampP_zero sphere6
  have w1 : weight sphere6 (Lightlike.PR.extS sphereFree fun _ _ => 1) = 4 := by
    have e : Lightlike.PR.extS sphereFree (fun _ _ => 1) = sphereCol := by
      funext f; unfold Lightlike.PR.extS sphereCol; split_ifs <;> rfl
    rw [e]; exact weight_sphereCol
  rw [sum_eq_add_of_mem _ _ hm0 hm1 fun h => by simpa using congr_fun (congr_fun h _) h012]
  · rw [w0, w1]; norm_num
  · rintro c hc ⟨h0, h1⟩
    by_contra hw
    have hall := sphere_rel (prod_ne_zero_iff.1 (right_ne_zero_of_mul hw))
      fun f hf => Lightlike.PR.extS_of_not_mem hf
    have hle : c {0, 1, 2} h012 < 1 + 1 := mem_range.1 (mem_pi.1 hc _ h012)
    have hc' : ∀ f (hf : f ∈ sphereFree), c f hf = c {0, 1, 2} h012 := fun f hf => by
      rw [← extS_apply c hf, ← extS_apply c h012]; exact hall f hf
    rcases (show c {0, 1, 2} h012 = 0 ∨ c {0, 1, 2} h012 = 1 by omega) with e | e
    · exact h0 (funext fun f => funext fun hf => (hc' f hf).trans e)
    · exact h1 (funext fun f => funext fun hf => (hc' f hf).trans e)

/-! ### A wrong amplitude breaks the 3-3 invariance -/

/-- Spin `1/2` on the face opposite positions `3` and `4` of a 4-simplex, `0` on the others. -/
def e34 : Fin 5 → Fin 5 → ℕ := fun p q => if (p = 3 ∧ q = 4) ∨ (p = 4 ∧ q = 3) then 1 else 0

/-- The vertex amplitude vanishes on `(e34, 0)`: the triad `(0, ½, 0)` of the intertwiner at the
tetrahedron opposite position `4` is not admissible. -/
theorem ampP_e34 : ampP e34 (fun _ => 0) = 0 := by
  by_contra h
  obtain ⟨-, -, -, h3⟩ := (tri_of_ampP_ne_zero h).2.2.1.1
  exact absurd h3 (by decide)

/-- **A deliberately wrong vertex amplitude**: `ampP` plus `1` on the single colouring
`(e34, 0)`, where `ampP` vanishes. -/
noncomputable def ampBad (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) : ℝ :=
  ampP J K + if J = e34 ∧ K = (fun _ => 0) then 1 else 0

/-- `ampBad` is `1` on the zero colouring, like `ampP`. -/
theorem ampBad_zero : ampBad (fun _ _ => 0) (fun _ => 0) = 1 := by
  unfold ampBad
  rw [ampP_zero, ite_eq_right fun h => absurd (congr_fun (congr_fun h.1 3) 4) (by decide),
    add_zero]

/-- `ampBad` is `1` on `(e34, 0)`, where `ampP` vanishes. -/
theorem ampBad_e34 : ampBad e34 (fun _ => 0) = 1 := by
  unfold ampBad
  rw [ampP_e34, ite_eq_left ⟨rfl, rfl⟩, zero_add]

/-- `ampBad` vanishes outside the support of `ampP` and the colouring `(e34, 0)`. -/
theorem ampBad_supp (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) (h : ampBad J K ≠ 0) :
    ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0) := by
  by_cases he : J = e34 ∧ K = fun _ => 0
  · exact Or.inr he
  · left; unfold ampBad at h; rwa [ite_eq_right he, add_zero] at h

/-- For an amplitude supported like `ampBad`: if it is nonzero and the triangles opposite
`04, 24, 14, 13` have spin `0`, then the triangle opposite `34` has spin at most `½` and the
tetrahedra opposite `3, 4` have spin `0`. -/
lemma rel_left_of_ne_zero {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    {J : Fin 5 → Fin 5 → ℕ} {K : Fin 5 → ℕ} (h : a J K ≠ 0)
    (h04 : J 0 4 = 0) (h24 : J 2 4 = 0) (h14 : J 1 4 = 0) (h13 : J 1 3 = 0) :
    J 3 4 ≤ 1 ∧ K 3 = 0 ∧ K 4 = 0 := by
  rcases ha J K h with h | ⟨rfl, rfl⟩
  · obtain ⟨-, -, ⟨h3a, h3b⟩, -, ⟨-, h5b⟩⟩ := tri_of_ampP_ne_zero h
    rw [h14] at h3a; rw [h04, h24] at h3b; rw [h13] at h5b
    have e1 := tri_zero_left h3a
    have e2 := tri_zero_right h3b
    have e3 := tri_zero_right h5b
    omega
  · decide

/-- For an amplitude supported like `ampBad`: if it is nonzero and the triangles opposite
`02, 04, 03, 13, 34` have spin `0`, then the triangle opposite `01` and the tetrahedra opposite
`0, 1` have spin `0`. -/
lemma rel_right_of_ne_zero {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    {J : Fin 5 → Fin 5 → ℕ} {K : Fin 5 → ℕ} (h : a J K ≠ 0)
    (h02 : J 0 2 = 0) (h04 : J 0 4 = 0) (h03 : J 0 3 = 0) (h13 : J 1 3 = 0) (h34 : J 3 4 = 0) :
    J 0 1 = 0 ∧ K 0 = 0 ∧ K 1 = 0 := by
  rcases ha J K h with h | ⟨rfl, -⟩
  · obtain ⟨⟨h1a, h1b⟩, -, -, ⟨h4a, -⟩, -⟩ := tri_of_ampP_ne_zero h
    rw [h02, h04] at h1a; rw [h03] at h1b; rw [h13] at h4a
    have e1 := tri_zero_left h1a
    have e2 := tri_zero_right h1b
    have e3 := tri_zero_left h4a
    omega
  · exact absurd h34 (by decide)

/-- `rel_left_of_ne_zero` for a 4-simplex given by a table of faces. -/
lemma simpWith_rel_left {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    {col : Finset V → ℕ} {s : Finset V} (hs : #s = 5) {v : Fin 5 → V}
    (hmem : ∀ i, v i ∈ s) (hv : StrictMono v) {T : Fin 5 → Fin 5 → Finset V}
    (hT : ∀ p q, (s.erase (v p)).erase (v q) = T p q) (h : simpWith a col s ≠ 0)
    (h0 : col (T 0 4) = 0 ∧ col (T 2 4) = 0 ∧ col (T 1 4) = 0 ∧ col (T 1 3) = 0) :
    col (T 3 4) ≤ 1 ∧ col (T 3 3) = 0 ∧ col (T 4 4) = 0 := by
  rw [simpWith_of_table a col hs hmem hv hT] at h
  exact rel_left_of_ne_zero ha h h0.1 h0.2.1 h0.2.2.1 h0.2.2.2

/-- `rel_right_of_ne_zero` for a 4-simplex given by a table of faces. -/
lemma simpWith_rel_right {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    {col : Finset V → ℕ} {s : Finset V} (hs : #s = 5) {v : Fin 5 → V}
    (hmem : ∀ i, v i ∈ s) (hv : StrictMono v) {T : Fin 5 → Fin 5 → Finset V}
    (hT : ∀ p q, (s.erase (v p)).erase (v q) = T p q) (h : simpWith a col s ≠ 0)
    (h0 : col (T 0 2) = 0 ∧ col (T 0 4) = 0 ∧ col (T 0 3) = 0 ∧ col (T 1 3) = 0 ∧
      col (T 3 4) = 0) :
    col (T 0 1) = 0 ∧ col (T 0 0) = 0 ∧ col (T 1 1) = 0 := by
  rw [simpWith_of_table a col hs hmem hv hT] at h
  exact rel_right_of_ne_zero ha h h0.1 h0.2.1 h0.2.2.1 h0.2.2.2.1 h0.2.2.2.2

/-- The faces of `K2` left free in the wrong-amplitude check: the triangle `{0,2,3}` that the
3-3 move removes and its three tetrahedra. -/
def freeK2 : Finset (Finset (Fin 8)) := {{0, 2, 3}, {0, 2, 3, 4}, {0, 2, 3, 5}, {0, 2, 3, 6}}

/-- The faces that the 3-3 move creates: the triangle `{4,5,6}` and its three tetrahedra. -/
def freeK3 : Finset (Finset (Fin 8)) := {{4, 5, 6}, {0, 4, 5, 6}, {2, 4, 5, 6}, {3, 4, 5, 6}}

/-- The gauge set of the wrong-amplitude check: every colourable face of `K2` outside
`freeK2`. -/
def T33 : Finset (Finset (Fin 8)) := colFaces K2 \ freeK2

/-- Colour `1` on the triangle `{0,2,3}`, `0` elsewhere. -/
def colStar (f : Finset (Fin 8)) : ℕ := if f = {0, 2, 3} then 1 else 0

/-- On `K2`, for an amplitude supported like `ampBad`: a colouring supported on `freeK2` with all
vertex amplitudes nonzero has spin at most `½` on `{0, 2, 3}` and `0` on its three tetrahedra. -/
lemma K2_rel {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    {col : Finset (Fin 8) → ℕ} (hS : ∀ s ∈ K2.simps, simpWith a col s ≠ 0)
    (hn : ∀ f ∉ freeK2, col f = 0) :
    col {0, 2, 3} ≤ 1 ∧ col {0, 2, 3, 4} = 0 ∧ col {0, 2, 3, 5} = 0 ∧ col {0, 2, 3, 6} = 0 := by
  have r1 : col {0, 2, 3} ≤ 1 ∧ col {0, 2, 3, 6} = 0 ∧ col {0, 2, 3, 5} = 0 :=
    simpWith_rel_left ha (s := {0, 2, 3, 5, 6}) (T := tab02356) (by decide) (v := ![0, 2, 3, 5, 6])
      (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide +kernel)
      (hS _ (by decide +kernel)) ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide),
        hn _ (by decide)⟩
  have r2 : col {0, 2, 3} ≤ 1 ∧ col {0, 2, 3, 6} = 0 ∧ col {0, 2, 3, 4} = 0 :=
    simpWith_rel_left ha (s := {0, 2, 3, 4, 6}) (T := tab02346) (by decide) (v := ![0, 2, 3, 4, 6])
      (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide +kernel)
      (hS _ (by decide +kernel)) ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide),
        hn _ (by decide)⟩
  exact ⟨r1.1, r2.2.2, r1.2.2, r1.2.1⟩

/-- After the 3-3 move, for an amplitude supported like `ampBad`: a colouring supported on `freeK3`
with all vertex amplitudes nonzero vanishes. -/
lemma K3_rel {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    {col : Finset (Fin 8) → ℕ} (hS : ∀ s ∈ (K2.move isMove33).simps, simpWith a col s ≠ 0)
    (hn : ∀ f ∉ freeK3, col f = 0) :
    col {4, 5, 6} = 0 ∧ col {0, 4, 5, 6} = 0 ∧ col {2, 4, 5, 6} = 0 ∧ col {3, 4, 5, 6} = 0 := by
  have r1 : col {4, 5, 6} = 0 ∧ col {3, 4, 5, 6} = 0 ∧ col {2, 4, 5, 6} = 0 :=
    simpWith_rel_right ha (s := {2, 3, 4, 5, 6}) (T := tab23456) (by decide) (v := ![2, 3, 4, 5, 6])
      (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide +kernel)
      (hS _ (by decide +kernel)) ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide),
        hn _ (by decide), hn _ (by decide)⟩
  have r2 : col {4, 5, 6} = 0 ∧ col {3, 4, 5, 6} = 0 ∧ col {0, 4, 5, 6} = 0 :=
    simpWith_rel_right ha (s := {0, 3, 4, 5, 6}) (T := tab03456) (by decide) (v := ![0, 3, 4, 5, 6])
      (by decide) (Fin.strictMono_iff_lt_succ.2 (by decide)) (by decide +kernel)
      (hS _ (by decide +kernel)) ⟨hn _ (by decide), hn _ (by decide), hn _ (by decide),
        hn _ (by decide), hn _ (by decide)⟩
  exact ⟨r1.1, r2.2.2, r1.2.2, r1.2.1⟩

/-- After the 3-3 move, the state sum with the gauge set `T33` is `1` for every amplitude supported
like `ampBad` with value `1` on the zero colouring: only the zero colouring contributes. -/
theorem amplitudeGFWith_move33_T33 {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    (h1 : a (fun _ _ => 0) (fun _ => 0) = 1) :
    amplitudeGFWith a (K2.move isMove33) T33 cut33 = 1 := by
  unfold amplitudeGFWith
  rw [show colFaces (K2.move isMove33) \ T33 = freeK3 by decide +kernel]
  have hm : (fun _ _ => 0 : ∀ f ∈ freeK3, ℕ) ∈ freeK3.pi fun f => range (cut33 f + 1) :=
    mem_pi.2 fun _ _ => by simp
  rw [sum_eq_single_of_mem _ hm]
  · rw [extS_eq_self (col := fun _ => 0) fun _ _ => rfl]
    exact weightWith_zero h1 _
  · intro c hc hne
    by_contra hw
    have r := K3_rel ha (prod_ne_zero_iff.1 (right_ne_zero_of_mul hw))
      fun f hf => Lightlike.PR.extS_of_not_mem hf
    apply hne
    funext f hf
    show c f hf = 0
    rw [← extS_apply c hf]
    simp only [freeK3, mem_insert, mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> omega

/-- On `K2`, the colouring `colStar` has weight `2 · a(e34, 0)³`: the triangle `{0, 2, 3}` gives
`2`, and each of the three 4-simplices through it sees the colouring `(e34, 0)`. -/
lemma weightWith_colStar {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (h1 : a (fun _ _ => 0) (fun _ => 0) = 1) :
    weightWith a K2 colStar = 2 * a e34 (fun _ => 0) ^ 3 := by
  unfold weightWith
  have htri : ∏ f ∈ K2.tris, ((colStar f : ℝ) + 1) = 2 := by
    have h : ∏ f ∈ K2.tris, (colStar f + 1) = 2 := by decide +kernel +revert
    exact_mod_cast h
  rw [htri, prod_simpWith_filter (col := colStar) h1 K2 {0, 2, 3}
    fun f hf => ite_eq_right fun he => hf (by subst he; exact Subset.refl _)]
  have hfil : K2.simps.filter (({0, 2, 3} : Finset (Fin 8)) ⊆ ·) =
      {{0, 2, 3, 5, 6}, {0, 2, 3, 4, 6}, {0, 2, 3, 4, 5}} := by decide +kernel
  rw [hfil, prod_insert (by decide), prod_insert (by decide), prod_singleton]
  have e1 : simpWith a colStar {0, 2, 3, 5, 6} = a e34 (fun _ => 0) :=
    simpWith_eq a (by decide) (v := ![0, 2, 3, 5, 6]) (by decide)
      (Fin.strictMono_iff_lt_succ.2 (by decide)) tab02356 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have e2 : simpWith a colStar {0, 2, 3, 4, 6} = a e34 (fun _ => 0) :=
    simpWith_eq a (by decide) (v := ![0, 2, 3, 4, 6]) (by decide)
      (Fin.strictMono_iff_lt_succ.2 (by decide)) tab02346 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have e3 : simpWith a colStar {0, 2, 3, 4, 5} = a e34 (fun _ => 0) :=
    simpWith_eq a (by decide) (v := ![0, 2, 3, 4, 5]) (by decide)
      (Fin.strictMono_iff_lt_succ.2 (by decide)) tab02345 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  rw [e1, e2, e3]
  ring

/-- Before the 3-3 move, the state sum with the gauge set `T33` is `1 + 2 · a(e34, 0)³` for every
amplitude supported like `ampBad` with value `1` on the zero colouring: the zero colouring and
`colStar` contribute. -/
theorem amplitudeGFWith_K2_T33 {a : (Fin 5 → Fin 5 → ℕ) → (Fin 5 → ℕ) → ℝ}
    (ha : ∀ J K, a J K ≠ 0 → ampP J K ≠ 0 ∨ (J = e34 ∧ K = fun _ => 0))
    (h1 : a (fun _ _ => 0) (fun _ => 0) = 1) :
    amplitudeGFWith a K2 T33 cut33 = 1 + 2 * a e34 (fun _ => 0) ^ 3 := by
  unfold amplitudeGFWith
  rw [show colFaces K2 \ T33 = freeK2 from Finset.sdiff_sdiff_eq_self (by decide +kernel)]
  have h023 : ({0, 2, 3} : Finset (Fin 8)) ∈ freeK2 := by decide
  have hm0 : (fun _ _ => 0 : ∀ f ∈ freeK2, ℕ) ∈ freeK2.pi fun f => range (cut33 f + 1) :=
    mem_pi.2 fun _ _ => by simp
  have hle : ∀ f ∈ freeK2, colStar f < cut33 f + 1 := by decide +kernel
  have hm1 : (fun f _ => colStar f : ∀ f ∈ freeK2, ℕ) ∈ freeK2.pi fun f => range (cut33 f + 1) :=
    mem_pi.2 fun f hf => mem_range.2 (hle f hf)
  rw [sum_eq_add_of_mem _ _ hm0 hm1
    fun h => by simpa [colStar] using congr_fun (congr_fun h _) h023]
  · rw [extS_eq_self (col := fun _ => 0) fun _ _ => rfl, weightWith_zero h1,
      extS_eq_self (col := colStar) fun f hf => ite_eq_right fun he => hf (by subst he; exact h023),
      weightWith_colStar h1]
  · rintro c hc ⟨h0, h1'⟩
    by_contra hw
    obtain ⟨r0, r4, r5, r6⟩ := K2_rel ha (prod_ne_zero_iff.1 (right_ne_zero_of_mul hw))
      fun f hf => Lightlike.PR.extS_of_not_mem hf
    have hs : colStar {0, 2, 3} = 1 ∧ colStar {0, 2, 3, 4} = 0 ∧ colStar {0, 2, 3, 5} = 0 ∧
        colStar {0, 2, 3, 6} = 0 := by decide
    rcases (show Lightlike.PR.extS freeK2 c {0, 2, 3} = 0 ∨ Lightlike.PR.extS freeK2 c {0, 2, 3} = 1 by omega)
      with e | e
    · apply h0
      funext f hf
      show c f hf = 0
      rw [← extS_apply c hf]
      simp only [freeK2, mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> omega
    · apply h1'
      funext f hf
      show c f hf = colStar f
      rw [← extS_apply c hf]
      simp only [freeK2, mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl | rfl | rfl <;> omega

/-- **Value check of the 3-3 move with a gauge set.** For the Ooguri amplitude both sides of the
3-3 move on `K2` with the gauge set `T33` are `1`, because `ampP` vanishes on `(e34, 0)`. -/
theorem amplitudeGF_T33 :
    amplitudeGF (K2.move isMove33) T33 cut33 = 1 ∧ amplitudeGF K2 T33 cut33 = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← amplitudeGFWith_ampP]
    exact amplitudeGFWith_move33_T33 (fun _ _ h => Or.inl h) ampP_zero
  · rw [← amplitudeGFWith_ampP, amplitudeGFWith_K2_T33 (fun _ _ h => Or.inl h) ampP_zero,
      ampP_e34]
    norm_num

/-- **Non-vacuity with a nonempty gauge set.** `amplitudeGF_move33` applies to the 3-3 move on `K2`
with the gauge set `T33`, which fixes every colourable face except the triangle `{0, 2, 3}` that
the move removes and its three tetrahedra; the kernel checks every hypothesis. -/
theorem amplitudeGF_move33_T33 :
    amplitudeGF (K2.move isMove33) T33 cut33 = amplitudeGF K2 T33 cut33 :=
  amplitudeGF_move33 K2 isMove33 (by decide) T33 (by decide +kernel) cut33
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Wrong model.** For the deliberately wrong vertex amplitude `ampBad` the two sides of the same
3-3 move differ (`1` after the move, `3` before), so the invariance `amplitudeGF_move33` is a
property of the Ooguri amplitude and not of the combinatorics of the state sum. -/
theorem ampBad_breaks_move33 :
    amplitudeGFWith ampBad (K2.move isMove33) T33 cut33 = 1 ∧
      amplitudeGFWith ampBad K2 T33 cut33 = 3 := by
  refine ⟨amplitudeGFWith_move33_T33 ampBad_supp ampBad_zero, ?_⟩
  rw [amplitudeGFWith_K2_T33 ampBad_supp ampBad_zero, ampBad_e34]
  norm_num

/-! ### The gauge rule

Value checks of `IsGauge` and of the forcing lemmas of `Ooguri.lean`. The collapses and the
forcing orders are certificates found by a search outside Lean; the kernel checks each of them
(`collapsible_of_collapsesBy`, `forces_of_forcesBy`). -/

/-- The ten triangles of `∂Δ⁵` through the vertex `5`: the cone from `5` on the edges of the
opposite 4-simplex. -/
def starT : Finset (Finset (Fin 6)) := sphere6.tris.filter (5 ∈ ·)

/-- **Non-vacuity of the gauge rule.** `starT` obeys the gauge rule on `∂Δ⁵`: the vertices, the
edges and `starT` collapse onto the vertex `5`. -/
theorem isGauge_starT : IsGauge sphere6 starT :=
  ⟨filter_subset _ _, collapsible_of_collapsesBy (v := 5)
    (l := [({0, 1}, {0, 1, 5}), ({0, 2}, {0, 2, 5}), ({0, 3}, {0, 3, 5}), ({0, 4}, {0, 4, 5}),
      ({1, 2}, {1, 2, 5}), ({1, 3}, {1, 3, 5}), ({1, 4}, {1, 4, 5}), ({2, 3}, {2, 3, 5}),
      ({2, 4}, {2, 4, 5}), ({3, 4}, {3, 4, 5}), ({0}, {0, 5}), ({1}, {1, 5}), ({2}, {2, 5}),
      ({3}, {3, 5}), ({4}, {4, 5})])
    (by decide +kernel)⟩

/-- **Value check.** In the gauge `starT` the state sum on `∂Δ⁵` is `1` for every cutoff: the ten
fixed triangles force every other triangle and every virtual spin to `0`. -/
theorem amplitudeGF_starT (cut : Finset (Fin 6) → ℕ) : amplitudeGF sphere6 starT cut = 1 :=
  amplitudeGF_eq_one_of_forces (forces_of_forcesBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}),
      ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}),
      ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}),
      ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)) cut

/-- **Non-vacuity of the removable cutoff.** In the gauge `starT` the state sum of `∂Δ⁵` at the
constant cutoff `L` tends to `1` as `L → ∞`: it is `1` for every `L`. -/
theorem amplitudeGF_tendsto_starT :
    Filter.Tendsto (fun L : ℕ => amplitudeGF sphere6 starT (fun _ => L)) Filter.atTop (nhds 1) :=
  amplitudeGF_tendsto_one_of_forces (forces_of_forcesBy
    (l := [({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 3, 5}, {0, 1, 3}), ({0, 1, 4, 5}, {0, 1, 4}),
      ({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}),
      ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}),
      ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel))

/-- A second gauge set on `∂Δ⁵`, not a star: ten triangles that collapse with the edges onto the
vertex `5`, with no vertex common to all of them. -/
def twistT : Finset (Finset (Fin 6)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5}, {0, 2, 3}, {1, 2, 4},
    {1, 3, 4}, {1, 3, 5}, {2, 3, 5}, {3, 4, 5}}

/-- **Non-vacuity of the gauge rule, a set that is not a star.** -/
theorem isGauge_twistT : IsGauge sphere6 twistT :=
  ⟨by decide +kernel, collapsible_of_collapsesBy (v := 5)
    (l := [({0, 4}, {0, 1, 4}), ({0, 5}, {0, 1, 5}), ({1, 5}, {1, 3, 5}), ({2, 4}, {1, 2, 4}),
      ({1, 2}, {0, 1, 2}), ({0, 1}, {0, 1, 3}), ({0, 2}, {0, 2, 3}), ({1, 3}, {1, 3, 4}),
      ({2, 3}, {2, 3, 5}), ({3, 4}, {3, 4, 5}), ({0}, {0, 3}), ({1}, {1, 4}), ({2}, {2, 5}),
      ({3}, {3, 5}), ({4}, {4, 5})])
    (by decide +kernel)⟩

/-- **Gauge independence on `∂Δ⁵`.** The state sum in the gauge `twistT` is `1` for every cutoff,
the same value as in the gauge `starT`. -/
theorem amplitudeGF_twistT (cut : Finset (Fin 6) → ℕ) : amplitudeGF sphere6 twistT cut = 1 :=
  amplitudeGF_eq_one_of_forces (forces_of_forcesBy
    (l := [({0, 1, 2, 3}, {1, 2, 3}), ({0, 1, 2, 4}, {0, 2, 4}), ({0, 1, 3, 4}, {0, 3, 4}),
      ({0, 1, 3, 5}, {0, 3, 5}), ({0, 2, 3, 4}, {2, 3, 4}), ({0, 2, 3, 5}, {0, 2, 5}),
      ({0, 3, 4, 5}, {0, 4, 5}), ({1, 2, 3, 5}, {1, 2, 5}), ({1, 3, 4, 5}, {1, 4, 5}),
      ({2, 3, 4, 5}, {2, 4, 5})])
    (by decide +kernel)) cut

/-- `starT` without the triangle `{0, 1, 5}`: nine triangles, one fewer than the gauge rule
needs. -/
def gauge9 : Finset (Finset (Fin 6)) := starT.erase {0, 1, 5}

/-- **Wrong input for the gauge rule.** `gauge9` does not obey the gauge rule: a gauge set of
`∂Δ⁵` has `E − V + 1 = 15 − 6 + 1 = 10` triangles (`IsGauge.card_eq`). -/
theorem not_isGauge_gauge9 : ¬ IsGauge sphere6 gauge9 := fun h => by
  have := h.card_eq
  rw [show #gauge9 = 9 by decide +kernel, show #sphere6.edges = 15 by decide +kernel,
    show #sphere6.verts = 6 by decide +kernel] at this
  omega

/-- In the gauge `gauge9` the state sum on `∂Δ⁵` equals the state sum in which only the faces
through the edge `{0, 1}` are free: the nine fixed triangles force every other face to `0`. -/
theorem amplitudeGF_gauge9 (cut : Finset (Fin 6) → ℕ) :
    amplitudeGF sphere6 gauge9 cut = amplitudeGF sphere6 (colFaces sphere6 \ sphereFree) cut := by
  refine (amplitudeGF_eq_of_vanish sphere6 (by decide +kernel) (fun col hW hT => ?_) cut).symm
  have hU := (forces_of_forcesBy (K := sphere6) (U := sphere6.tris \ sphereFree) (T := gauge9)
    (l := [({0, 2, 3, 5}, {0, 2, 3}), ({0, 2, 4, 5}, {0, 2, 4}), ({0, 3, 4, 5}, {0, 3, 4}),
      ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {1, 2, 4}), ({1, 3, 4, 5}, {1, 3, 4}),
      ({2, 3, 4, 5}, {2, 3, 4})])
    (by decide +kernel)).sound hW hT
  have htet : ∀ t ∈ sphere6.tets \ sphereFree, ∀ g ∈ t.powersetCard 3,
      g ∈ sphere6.tris \ sphereFree := by
    decide +kernel
  intro f hf
  rcases mem_union.mp (mem_sdiff.mp hf).1 with h3 | h4
  · exact hU f (mem_sdiff.mpr ⟨h3, (mem_sdiff.mp hf).2⟩)
  · have hf' : f ∈ sphere6.tets \ sphereFree := mem_sdiff.mpr ⟨h4, (mem_sdiff.mp hf).2⟩
    exact weight_tet_zero_of_tris hW h4 fun g hg => hU g (htet f hf' g hg)

/-- **Wrong gauge, different value.** With one triangle too few fixed, the state sum on `∂Δ⁵` with
cutoff `½` is `5`, not `1`: the spins on the faces through the edge `{0, 1}` are no longer
fixed. -/
theorem amplitudeGF_gauge9_one : amplitudeGF sphere6 gauge9 (fun _ => 1) = 5 := by
  rw [amplitudeGF_gauge9, amplitudeGF_sphere6_edge]

/-- The fifteen triangles of `K2` through the vertex `1`. -/
def star1 : Finset (Finset (Fin 8)) := K2.tris.filter (1 ∈ ·)

/-- **Non-vacuity on `K2`.** `star1` obeys the gauge rule on the closed 4-sphere `K2`, with
`E − V + 1 = 21 − 7 + 1 = 15`: the vertices, the edges and `star1` collapse onto the vertex `6`. -/
theorem isGauge_star1 : IsGauge K2 star1 :=
  ⟨filter_subset _ _, collapsible_of_collapsesBy (v := 6)
    (l := [({0, 2}, {0, 1, 2}), ({0, 3}, {0, 1, 3}), ({0, 4}, {0, 1, 4}), ({0, 5}, {0, 1, 5}),
      ({0, 1}, {0, 1, 6}), ({2, 3}, {1, 2, 3}), ({2, 4}, {1, 2, 4}), ({2, 5}, {1, 2, 5}),
      ({1, 2}, {1, 2, 6}), ({3, 4}, {1, 3, 4}), ({3, 5}, {1, 3, 5}), ({1, 3}, {1, 3, 6}),
      ({4, 5}, {1, 4, 5}), ({1, 4}, {1, 4, 6}), ({1, 5}, {1, 5, 6}), ({0}, {0, 6}), ({1}, {1, 6}),
      ({2}, {2, 6}), ({3}, {3, 6}), ({4}, {4, 6}), ({5}, {5, 6})])
    (by decide +kernel)⟩

/-- **Value check.** In the gauge `star1` the state sum on `K2` is `1` for every cutoff. -/
theorem amplitudeGF_K2_star1 (cut : Finset (Fin 8) → ℕ) : amplitudeGF K2 star1 cut = 1 :=
  amplitudeGF_eq_one_of_forces (forces_of_forcesBy
    (l := [({0, 1, 2, 4}, {0, 2, 4}), ({0, 1, 2, 5}, {0, 2, 5}), ({0, 1, 2, 6}, {0, 2, 6}),
      ({0, 1, 3, 4}, {0, 3, 4}), ({0, 1, 3, 5}, {0, 3, 5}), ({0, 1, 3, 6}, {0, 3, 6}),
      ({0, 1, 4, 5}, {0, 4, 5}), ({0, 1, 4, 6}, {0, 4, 6}), ({0, 1, 5, 6}, {0, 5, 6}),
      ({0, 2, 4, 5}, {2, 4, 5}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}),
      ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}),
      ({1, 2, 3, 4}, {2, 3, 4}), ({1, 2, 3, 5}, {2, 3, 5}), ({1, 2, 3, 6}, {2, 3, 6}),
      ({0, 2, 3, 4}, {0, 2, 3})])
    (by decide +kernel)) cut

/-- **Value check after the move.** In the same gauge `star1` the state sum on `K2` after the 3-3
move `{0, 2, 3} → {4, 5, 6}` is `1` for every cutoff. -/
theorem amplitudeGF_K3_star1 (cut : Finset (Fin 8) → ℕ) :
    amplitudeGF (K2.move isMove33) star1 cut = 1 :=
  amplitudeGF_eq_one_of_forces (forces_of_forcesBy
    (l := [({0, 1, 2, 4}, {0, 2, 4}), ({0, 1, 2, 5}, {0, 2, 5}), ({0, 1, 2, 6}, {0, 2, 6}),
      ({0, 1, 3, 4}, {0, 3, 4}), ({0, 1, 3, 5}, {0, 3, 5}), ({0, 1, 3, 6}, {0, 3, 6}),
      ({0, 1, 4, 5}, {0, 4, 5}), ({0, 1, 4, 6}, {0, 4, 6}), ({0, 1, 5, 6}, {0, 5, 6}),
      ({0, 2, 4, 5}, {2, 4, 5}), ({0, 2, 4, 6}, {2, 4, 6}), ({0, 2, 5, 6}, {2, 5, 6}),
      ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {3, 4, 6}), ({0, 3, 5, 6}, {3, 5, 6}),
      ({0, 4, 5, 6}, {4, 5, 6}), ({1, 2, 3, 4}, {2, 3, 4}), ({1, 2, 3, 5}, {2, 3, 5}),
      ({1, 2, 3, 6}, {2, 3, 6})])
    (by decide +kernel)) cut

/-- **Non-vacuity of the gauge-fixed 3-3 invariance.** `amplitudeGF_move33_gauge` applies to the
3-3 move on `K2` with the gauge set `star1`, which obeys the gauge rule and does not contain the
removed triangle `{0, 2, 3}`; the kernel checks every hypothesis. -/
theorem amplitudeGF_move33_star1 :
    IsGauge (K2.move isMove33) star1 ∧
      amplitudeGF (K2.move isMove33) star1 cut33 = amplitudeGF K2 star1 cut33 :=
  amplitudeGF_move33_gauge K2 isMove33 (by decide) isGauge_star1 (by decide +kernel) cut33
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## Trust checks of the Pachner moves (`Lightlike/FourD/Pachner.lean`) -/

/-- **The inverse moves undo the moves, from `move_move`.** The moves with `σ` and `τ` exchanged
take `K1` back to `K0`, `K2` to `K1` and `K3` to `K2`. -/
theorem pachner_move_move_predicts :
    K1.move isMove15.symm = K0 ∧ K2.move isMove24.symm = K1 ∧ K3.move isMove33.symm = K2 :=
  ⟨Complex4.move_move isMove15, Complex4.move_move isMove24, Complex4.move_move isMove33⟩

/-- **The same three equalities, computed** by the kernel from the lists of 4-simplices,
without `move_move`. -/
theorem pachner_move_move_direct :
    K1.move isMove15.symm = K0 ∧ K2.move isMove24.symm = K1 ∧ K3.move isMove33.symm = K2 :=
  ⟨Complex4.ext (by decide +kernel), Complex4.ext (by decide +kernel),
    Complex4.ext (by decide +kernel)⟩

/-- **The Euler characteristic along the moves, from `euler4_move`.** The boundary of the
5-simplex `K0` has Euler characteristic `2` (computed); the theorem then gives `2` for `K1`, `K2`
and `K3`. -/
theorem pachner_euler4_predicts : K1.euler4 = 2 ∧ K2.euler4 = 2 ∧ K3.euler4 = 2 := by
  have h0 : K0.euler4 = 2 := by decide +kernel +revert
  have h1 : K1.euler4 = 2 := (Complex4.euler4_move isMove15).trans h0
  have h2 : K2.euler4 = 2 := (Complex4.euler4_move isMove24).trans h1
  exact ⟨h1, h2, (Complex4.euler4_move isMove33).trans h2⟩

/-- **The same Euler characteristics, computed** from the face numbers, without
`euler4_move`. -/
theorem pachner_euler4_direct : K0.euler4 = 2 ∧ K1.euler4 = 2 ∧ K2.euler4 = 2 ∧ K3.euler4 = 2 :=
  ⟨by decide +kernel, moves_closed_euler.1, moves_closed_euler.2.1, moves_closed_euler.2.2.1⟩

/-- **Wrong input for `move_move`: the 1-5 move repeated without exchanging `σ` and `τ`.** On
`K1` the data `{0, 1, 2, 3, 4}`, `{6}` is not a move (the vertex `6` is already there), and the
move formula applied to it anyway returns `K1` unchanged, which is not `K0`. -/
theorem pachner_repeat_fails : ¬ K1.IsMove {0, 1, 2, 3, 4} {6} ∧
    rawMove K1 {0, 1, 2, 3, 4} {6} = K1.simps ∧ K1.simps ≠ K0.simps :=
  ⟨fun h => absurd h.fresh (by decide +kernel), by decide +kernel, by decide +kernel⟩

/-- **Wrong model for `euler4_move`: the unsigned face count.** Without the signs `(-1)^k`, the
count `f₀ + f₁ + f₂ + f₃ + f₄` is `62` on `K0` and `92` on `K1`, so it changes under the 1-5
move. -/
theorem pachner_unsigned_euler_fails :
    ∑ k ∈ range 5, #(K0.faces k) = 62 ∧ ∑ k ∈ range 5, #(K1.faces k) = 92 := by
  decide +kernel

/-! ## Trust checks of the injectivity criterion for the EPRL map (`Lightlike/Spin4/Fusion.lean`) -/

section Fusion

open Lightlike.Spin4 Lightlike.Spin4.Test

/-- `γ = 1/2`, `j = 8`: `(j₊, j₋) = (6, 2)`. -/
theorem label_half_sixteen : IsEPRLLabel (1 / 2) (12 + 4) 12 4 :=
  (isEPRLLabel_iff (by norm_num) (by norm_num)).mpr ⟨rfl, by norm_num⟩

/-- **Doubled spins `(4, 4, 4, 16)` admit no SU(2) intertwiner**, by the triangle condition alone
(their sum `28` is even): a spin coupling `4` and `4` is at most `8`, a spin coupling `4` and `16`
at least `12`. -/
theorem channel_4_4_4_16 : channel (3 + 1) (3 + 1) (3 + 1) (12 + 4) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
  rw [mem_channel] at hz
  unfold Tri at hz
  omega

/-- **The parity branch of `eprlIntertwiner_injective_iff`.** For `γ = 1/3` and four links
`j = 3/2` there are SU(2) intertwiners (`z = 0` couples all four links), `Σ_a 2j⁺_a = 8` is even,
and the criterion gives injectivity, as `Lightlike.Spin4.Test.injective_third` does from
`eprlIntertwiner_injective`. -/
theorem eprl_injective_iff_parity_predicts :
    (channel (2 + 1) (2 + 1) (2 + 1) (2 + 1)).Nonempty ∧
      ∀ T : Matrix (Idx (2 + 1) (2 + 1)) (Idx (2 + 1) (2 + 1)) ℂ,
        IsIntertwiner (2 + 1) (2 + 1) (2 + 1) (2 + 1) T →
          eprlIntertwiner 2 2 2 2 1 1 1 1 T = 0 → T = 0 :=
  ⟨⟨0, by rw [mem_channel]; unfold Tri; omega⟩,
    (eprlIntertwiner_injective_iff (γ := 1 / 3) (n₁ := 2) (n₂ := 2) (n₃ := 2) (n₄ := 2) (m₁ := 1)
      (m₂ := 1) (m₃ := 1) (m₄ := 1) (by norm_num) (by norm_num) label_third_three
      label_third_three label_third_three label_third_three).mpr (Or.inl ⟨4, rfl⟩)⟩

/-- **The empty-space branch of `eprlIntertwiner_injective_iff`.** For `γ = 1/2` and doubled spins
`J = (4, 4, 4, 16)` the labels are `2j⁺ = (3, 3, 3, 12)`, so the parity condition of the theorem
fails (`Σ_a 2j⁺_a = 21` is odd); the criterion still gives injectivity, because the triangle
condition leaves no SU(2) intertwiners (`channel_4_4_4_16`). -/
theorem eprl_injective_iff_empty_predicts :
    ∀ T : Matrix (Idx (3 + 1) (3 + 1)) (Idx (3 + 1) (12 + 4)) ℂ,
      IsIntertwiner (3 + 1) (3 + 1) (3 + 1) (12 + 4) T →
        eprlIntertwiner 3 3 3 12 1 1 1 4 T = 0 → T = 0 :=
  (eprlIntertwiner_injective_iff (γ := 1 / 2) (n₁ := 3) (n₂ := 3) (n₃ := 3) (n₄ := 12) (m₁ := 1)
    (m₂ := 1) (m₃ := 1) (m₄ := 4) (by norm_num) (by norm_num) label_half_four label_half_four
    label_half_four label_half_sixteen).mpr (Or.inr channel_4_4_4_16)

/-- **The same injectivity, directly**: an SU(2) intertwiner for `(4, 4, 4, 16)` is the sum of its
components along the basis `ι_z` over the empty channel (`eq_sum_ivec`), so it is `0`; neither the
EPRL map nor `eprlIntertwiner_injective_iff` is used. -/
theorem eprl_injective_iff_empty_direct :
    ∀ T : Matrix (Idx (3 + 1) (3 + 1)) (Idx (3 + 1) (12 + 4)) ℂ,
      IsIntertwiner (3 + 1) (3 + 1) (3 + 1) (12 + 4) T →
        eprlIntertwiner 3 3 3 12 1 1 1 4 T = 0 → T = 0 := fun T hT _ => by
  rw [eq_sum_ivec hT, channel_4_4_4_16, Finset.sum_empty]

/-- **Wrong model: the parity condition alone.** Without the alternative "no SU(2) intertwiners"
the criterion would read "injective exactly when `Σ_a 2j⁺_a` is even"; for `γ = 1/2` and doubled
spins `J = (4, 4, 4, 16)` the map is injective (the triangle condition leaves no SU(2)
intertwiners, although `Σ_a J_a = 28` is even) while `Σ_a 2j⁺_a = 21` is odd. -/
theorem eprl_injective_parity_only_fails :
    ¬ ((∀ T : Matrix (Idx (3 + 1) (3 + 1)) (Idx (3 + 1) (12 + 4)) ℂ,
      IsIntertwiner (3 + 1) (3 + 1) (3 + 1) (12 + 4) T →
        eprlIntertwiner 3 3 3 12 1 1 1 4 T = 0 → T = 0) ↔ Even (3 + 3 + 3 + 12)) := fun h =>
  absurd (h.mp eprl_injective_iff_empty_direct) (by rw [Nat.not_even_iff_odd]; decide)

end Fusion

/-! ## Trust checks of Clebsch–Gordan on the diagonal SU(2) (`Lightlike/Spin4/ClebschGordan.lean`)
-/

section ClebschGordan

open Lightlike.SU2 Lightlike.Spin4 Lightlike.Spin4.Test Matrix

/-- **Characters from `spin4_diag_clebschGordan`**: on the diagonal pairs `(g, g)`, the trace of
`(n/2, m/2)` is the trace of the block-diagonal matrix with the spins `(n+m)/2 - k`. -/
theorem cg_trace_predicts (n m : ℕ) (g : SU2) :
    trace (spin4Mat n m (g, g)) = trace (cgMat n m g) := by
  obtain ⟨T, hT⟩ := spin4_diag_clebschGordan n m
  exact (trace_eq_of_intertwine T (hT g)).symm

/-- The trace of spin `n/2` at `diag(e^{iθ}, e^{-iθ})` is `Σ_k e^{i(n-2k)θ}`. -/
lemma trace_spinMat_torusExp (n : ℕ) (θ : ℝ) :
    trace (spinMat n (torusExp θ)) =
      ∑ k : Fin (n + 1), Complex.exp ((((n : ℝ) - 2 * (k : ℕ)) * θ : ℝ) * Complex.I) := by
  unfold torusExp
  rw [spinMat_torus_exp, trace_diagonal]

/-- **The blocks of `(½, ½)`, computed**: `cgMat 1 1` has the blocks spin `1` and spin `0`, so at
`diag(e^{iθ}, e^{-iθ})` its trace is `(e^{2iθ} + 1 + e^{-2iθ}) + 1 = 2 cos 2θ + 2`, the trace of
`(½, ½)` at `(g, g)` (`trace_spin4Mat_half_half_torus`). -/
theorem cg_trace_half_half_direct (θ : ℝ) :
    trace (cgMat 1 1 (torusExp θ)) = ((2 * Real.cos (2 * θ) + 2 : ℝ) : ℂ) ∧
      trace (spin4Mat 1 1 (torusExp θ, torusExp θ)) = ((2 * Real.cos (2 * θ) + 2 : ℝ) : ℂ) := by
  refine ⟨?_, by
    rw [trace_spin4Mat_half_half_torus, sub_self, Real.cos_zero, ← two_mul θ]; congr 1; ring⟩
  rw [cgMat, trace_blockDiagonal']
  rw [Fin.sum_univ_eq_sum_range (fun k => trace (spinMat (1 + 1 - 2 * k) (torusExp θ)))]
  simp only [show min 1 1 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    show 1 + 1 - 2 * 0 = 2 from rfl, show 1 + 1 - 2 * 1 = 0 from rfl, trace_spinMat_torusExp,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  push_cast
  simp only [Complex.cos]
  ring_nf
  rw [Complex.exp_zero]
  ring

/-- **The same trace from the theorem**: `cg_trace_predicts` and the trace of `(½, ½)` at
`(g, g)` give `2 cos 2θ + 2` for the blocks of `cgMat 1 1`. -/
theorem cg_trace_half_half_predicts (θ : ℝ) :
    trace (cgMat 1 1 (torusExp θ)) = ((2 * Real.cos (2 * θ) + 2 : ℝ) : ℂ) := by
  rw [← cg_trace_predicts, trace_spin4Mat_half_half_torus, sub_self, Real.cos_zero, ← two_mul θ]
  congr 1
  ring

/-- **Wrong input: off the diagonal.** At `(g₊, g₋) = (-1, 1)` the trace of `(½, ½)` is `-4`,
while the blocks of `cgMat 1 1` have trace `4` at both `-1` and `1`; so no equivalence carries
`(½, ½)` at `(g, h)` to the blocks at `g` for all pairs, and the theorem needs `g₊ = g₋`. -/
theorem cg_offdiag_fails :
    trace (spin4Mat 1 1 (negOne, 1)) = -4 ∧ trace (cgMat 1 1 negOne) = 4 ∧
      ¬ ∃ T : (Idx 1 1 → ℂ) ≃ₗ[ℂ] (CGIdx 1 1 → ℂ), ∀ (g h : SU2) (v : Idx 1 1 → ℂ),
        T (spin4Mat 1 1 (g, h) *ᵥ v) = cgMat 1 1 g *ᵥ T v := by
  have h1 : trace (spin4Mat 1 1 (negOne, 1)) = -4 := by
    rw [spin4Mat_negOne_one, trace_smul, trace_one]
    simp [Fintype.card_prod]
  have h2 : trace (cgMat 1 1 negOne) = 4 := by
    rw [cgMat, trace_blockDiagonal']
    rw [Fin.sum_univ_eq_sum_range (fun k => trace (spinMat (1 + 1 - 2 * k) negOne))]
    simp only [show min 1 1 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, show 1 + 1 - 2 * 0 = 2 from rfl, show 1 + 1 - 2 * 1 = 0 from rfl, spinMat_negOne,
      trace_smul, trace_one, Fintype.card_fin]
    norm_num
  refine ⟨h1, h2, fun ⟨T, hT⟩ => ?_⟩
  have := trace_eq_of_intertwine T (hT negOne 1)
  rw [h1, h2] at this
  norm_num at this

end ClebschGordan

/-! ## Trust checks of the double cover Spin(4) → SO(4) (`Lightlike/Spin4/SO4.lean`) -/

section SO4
open Lightlike.SU2 Lightlike.Spin4 Quaternion

/-- **Prediction** (`toSO4_eq_one_iff`): `(-1, -1)` lies in the kernel of `Spin(4) → SO(4)`. -/
theorem so4_kernel_predicts : toSO4 (negOne, negOne) = 1 :=
  (toSO4_eq_one_iff _).2 (Or.inr rfl)

/-- **Direct computation:** `x ↦ (-1) x (-1)* = x` for every quaternion `x`. -/
theorem so4_kernel_direct (x : ℍ) : (toSO4 (negOne, negOne) : ℍ ≃ₗᵢ[ℝ] ℍ) x = x := by
  rw [toSO4_apply, quatEquiv_symm_negOne]
  simp

/-- `(-1)² = 1` in SU(2). -/
lemma negOne_mul_negOne : negOne * negOne = 1 := by
  apply Subtype.ext
  simp [negOne_coe]

/-- **Prediction:** `(1, -1)` and `(-1, 1)` differ by the kernel element `(-1, -1)`, so they have
the same image, and that image is not the identity. -/
theorem so4_half_kernel_predicts :
    toSO4 (1, negOne) = toSO4 (negOne, 1) ∧ toSO4 (1, negOne) ≠ 1 := by
  have hk : (1, negOne) * (negOne, negOne) = ((negOne, 1) : Spin4) := by
    simp [negOne_mul_negOne]
  refine ⟨?_, fun h => ?_⟩
  · rw [← hk, map_mul, so4_kernel_predicts, mul_one]
  · have hn : (negOne : SU2) ≠ 1 := fun h1 => negOne_ne_one (by rw [h1]; rfl)
    rcases (toSO4_eq_one_iff _).1 h with h | h
    · exact hn (congrArg Prod.snd h)
    · exact hn (congrArg Prod.fst h).symm

/-- **Direct computation:** `(1, -1)` and `(-1, 1)` both act as `x ↦ -x`. -/
theorem so4_half_kernel_direct (x : ℍ) :
    (toSO4 (1, negOne) : ℍ ≃ₗᵢ[ℝ] ℍ) x = -x ∧ (toSO4 (negOne, 1) : ℍ ≃ₗᵢ[ℝ] ℍ) x = -x := by
  rw [toSO4_apply, toSO4_apply, quatEquiv_symm_negOne]
  simp

/-- The 4 × 4 matrix of `(1, -1)` is `-1`. -/
theorem so4Mat_one_negOne : (toSO4Mat (1, negOne) : Matrix (Fin 4) (Fin 4) ℝ) = -1 := by
  have h : ((toSO4 (1, negOne) : ℍ ≃ₗᵢ[ℝ] ℍ).toLinearEquiv : ℍ →ₗ[ℝ] ℍ) = -LinearMap.id :=
    LinearMap.ext fun x => (so4_half_kernel_direct x).1
  show (SO4MatEquiv (toSO4 (1, negOne)) : Matrix (Fin 4) (Fin 4) ℝ) = -1
  rw [SO4MatEquiv_apply, h, map_neg, LinearMap.toMatrix_id]

/-- `|i|² = 1`. -/
lemma normSq_i : normSq (⟨0, 1, 0, 0⟩ : ℍ) = 1 := by
  rw [normSq_def']; norm_num

/-- The unit quaternion `i`. -/
noncomputable def quatI : unitary ℍ := ⟨⟨0, 1, 0, 0⟩, mem_unitary_of_normSq normSq_i⟩

/-- `(i, 1)` acts as left multiplication by `i`. -/
theorem so4_left_i (x : ℍ) :
    (toSO4 (quatEquiv quatI, 1) : ℍ ≃ₗᵢ[ℝ] ℍ) x = ⟨0, 1, 0, 0⟩ * x := by
  rw [toSO4_apply, MulEquiv.symm_apply_apply, map_one]
  simp [quatI]

/-- **Explicit values:** `(i, 1)` sends `1 ↦ i` and `j ↦ k`. -/
theorem so4_left_i_values :
    (toSO4 (quatEquiv quatI, 1) : ℍ ≃ₗᵢ[ℝ] ℍ) 1 = ⟨0, 1, 0, 0⟩ ∧
      (toSO4 (quatEquiv quatI, 1) : ℍ ≃ₗᵢ[ℝ] ℍ) ⟨0, 0, 1, 0⟩ = ⟨0, 0, 0, 1⟩ := by
  rw [so4_left_i, so4_left_i]
  constructor <;> ext <;> simp

/-- **Wrong input:** "`Spin(4) → SO(4)` is injective" fails; `(-1, -1)` is a second kernel
element. -/
theorem so4_trivial_kernel_fails : ¬ ∀ g : Spin4, toSO4 g = 1 ↔ g = 1 :=
  fun h => negOne_ne_one ((h _).1 so4_kernel_predicts)

end SO4

/-! ## Trust checks of the completeness of `Spin(4)` irreps (`Lightlike/Spin4/Completeness.lean`) -/

section Completeness
open Lightlike.SU2 Lightlike.Spin4 Lightlike.Spin4.Test Matrix

/-- The vector representation of Spin(4) on `ℂ⁴`: the SO(4) matrix, complexified. -/
noncomputable def vecRep : Spin4 →* Matrix (Fin 4) (Fin 4) ℂ :=
  (Complex.ofRealHom.mapMatrix :
      Matrix (Fin 4) (Fin 4) ℝ →+* Matrix (Fin 4) (Fin 4) ℂ).toMonoidHom.comp
    ((Submonoid.subtype _).comp toSO4Mat)

/-- `vecRep g` is the SO(4) matrix of `g` with real entries viewed as complex numbers. -/
lemma vecRep_apply (g : Spin4) :
    vecRep g = (toSO4Mat g : Matrix (Fin 4) (Fin 4) ℝ).map (fun r : ℝ => (r : ℂ)) := rfl

/-- The vector representation is continuous. -/
lemma continuous_vecRep : Continuous vecRep := by
  have : Continuous fun g : Spin4 =>
      (toSO4Mat g : Matrix (Fin 4) (Fin 4) ℝ).map (fun r : ℝ => (r : ℂ)) :=
    (continuous_subtype_val.comp continuous_toSO4Mat).matrix_map Complex.continuous_ofReal
  exact this

/-- The vector representation is irreducible (via the intertwiner with `(1/2, 1/2)`). -/
lemma vecRep_irreducible (W : Submodule ℂ (Fin 4 → ℂ))
    (hW : ∀ g : Spin4, ∀ v ∈ W, vecRep g *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  obtain ⟨T, hT⟩ := half_half_equiv_vector
  have hinv : ∀ g : Spin4, ∀ v ∈ W.comap (T : (Idx 1 1 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)),
      spin4Mat 1 1 g *ᵥ v ∈ W.comap (T : (Idx 1 1 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)) := by
    intro g v hv
    rw [Submodule.mem_comap] at hv ⊢
    rw [LinearEquiv.coe_coe, hT]
    exact hW g _ hv
  have hmap := Submodule.map_comap_eq_of_surjective
    (f := (T : (Idx 1 1 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))) T.surjective W
  rcases isInvariant_eq_bot_or_eq_top hinv with h | h
  · left; rw [← hmap, h, Submodule.map_bot]
  · right; rw [← hmap, h, Submodule.map_top]; exact LinearEquiv.range T

/-- **Prediction** (`spin4Rep_complete`): the vector representation is some `(n/2, m/2)`. -/
theorem completeness_vector_predicts :
    ∃ n m : ℕ, ∃ T : (Fin 4 → ℂ) ≃ₗ[ℂ] (Idx n m → ℂ),
      ∀ (g : Spin4) (v : Fin 4 → ℂ), T (vecRep g *ᵥ v) = spin4Mat n m g *ᵥ T v :=
  spin4Rep_complete vecRep continuous_vecRep vecRep_irreducible

/-- `(1, -1)` and `(-1, 1)` act as `-1` on `ℂ⁴`, so both traces are `-4`. -/
lemma trace_vecRep_minus :
    trace (vecRep (1, negOne)) = -4 ∧ trace (vecRep (negOne, 1)) = -4 := by
  have h1 : vecRep (1, negOne) = -1 := by
    show Complex.ofRealHom.mapMatrix (toSO4Mat (1, negOne) : Matrix (Fin 4) (Fin 4) ℝ) = -1
    rw [so4Mat_one_negOne, map_neg, map_one]
  have h2 : vecRep (negOne, 1) = vecRep (1, negOne) := by
    show Complex.ofRealHom.mapMatrix (SO4MatEquiv (toSO4 (negOne, 1)) : Matrix (Fin 4) (Fin 4) ℝ) =
      Complex.ofRealHom.mapMatrix (SO4MatEquiv (toSO4 (1, negOne)) : Matrix (Fin 4) (Fin 4) ℝ)
    rw [so4_half_kernel_predicts.1]
  rw [h2, h1, trace_neg, trace_one]
  simp

/-- **The labels are forced:** any intertwiner from the vector representation to `(n/2, m/2)`
has `n = m = 1`. The dimension gives `(n + 1)(m + 1) = 4`; the traces of `(1, -1)` and `(-1, 1)`,
`(-1)ᵐ · 4` and `(-1)ⁿ · 4`, must both be `-4`, so `n` and `m` are odd. -/
theorem completeness_vector_labels {n m : ℕ} (T : (Fin 4 → ℂ) ≃ₗ[ℂ] (Idx n m → ℂ))
    (hT : ∀ (g : Spin4) (v : Fin 4 → ℂ), T (vecRep g *ᵥ v) = spin4Mat n m g *ᵥ T v) :
    n = 1 ∧ m = 1 := by
  have hdim : 4 = (n + 1) * (m + 1) := by
    have := T.finrank_eq
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_prod] at this
    exact this
  have hcard : ((Fintype.card (Idx n m) : ℕ) : ℂ) = 4 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← hdim]; norm_num
  have htm := trace_eq_of_intertwine T (hT (1, negOne))
  have htn := trace_eq_of_intertwine T (hT (negOne, 1))
  rw [spin4Mat_one_negOne, trace_smul, trace_one, hcard, trace_vecRep_minus.1] at htm
  rw [spin4Mat_negOne_one, trace_smul, trace_one, hcard, trace_vecRep_minus.2] at htn
  have hodd : ∀ k : ℕ, (-1 : ℂ) ^ k • (4 : ℂ) = -4 → k % 2 = 1 := by
    intro k hk
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow, one_smul] at hk; norm_num at hk
    · exact Nat.odd_iff.mp ho
  have hm := hodd m htm
  have hn := hodd n htn
  have hn3 : n ≤ 3 := by nlinarith
  have hm3 : m ≤ 3 := by nlinarith
  interval_cases n <;> interval_cases m <;> omega

/-- **Direct computation:** the vector representation is `(1/2, 1/2)`, with an explicit
intertwiner (`half_half_equiv_vector`, inverted). -/
theorem completeness_vector_direct :
    ∃ T : (Fin 4 → ℂ) ≃ₗ[ℂ] (Idx 1 1 → ℂ),
      ∀ (g : Spin4) (v : Fin 4 → ℂ), T (vecRep g *ᵥ v) = spin4Mat 1 1 g *ᵥ T v := by
  obtain ⟨T, hT⟩ := half_half_equiv_vector
  refine ⟨T.symm, fun g v => ?_⟩
  rw [LinearEquiv.symm_apply_eq, hT, LinearEquiv.apply_symm_apply]
  rfl

/-- **Wrong input:** `(3/2, 0)` and `(0, 3/2)` also have dimension 4, but neither is the vector
representation: the trace of `(1, -1)` or `(-1, 1)` would be `+4`. -/
theorem completeness_vector_wrong_labels :
    (¬ ∃ T : (Fin 4 → ℂ) ≃ₗ[ℂ] (Idx 3 0 → ℂ),
      ∀ (g : Spin4) (v : Fin 4 → ℂ), T (vecRep g *ᵥ v) = spin4Mat 3 0 g *ᵥ T v) ∧
    ¬ ∃ T : (Fin 4 → ℂ) ≃ₗ[ℂ] (Idx 0 3 → ℂ),
      ∀ (g : Spin4) (v : Fin 4 → ℂ), T (vecRep g *ᵥ v) = spin4Mat 0 3 g *ᵥ T v :=
  ⟨fun ⟨T, hT⟩ => absurd (completeness_vector_labels T hT).1 (by norm_num),
    fun ⟨T, hT⟩ => absurd (completeness_vector_labels T hT).1 (by norm_num)⟩

end Completeness


/-! ### Robustness is not kept by the 3-3 move

A 4-sphere `Kcex` with 20 simplices on 8 vertices, a set `Tcex` of 23 triangles, and the 3-3 move
`{3,6,7} → {0,2,4}`: `Tcex` is robust for `Kcex` (forcing with any one of its 50 tetrahedra removed,
from explicit forcing steps), and not robust for the complex after the move, where removing the
tetrahedron `{0,2,3,6}` leaves a blocking set `Xcex` of 18 triangles that avoids `Tcex`. Found by
random search; `scripts/spinfoam/robust_counterexample_verify.py` checks the same data independently. -/

/-- The 20 four-simplices of the counterexample. -/
def KcexSimps : Finset (Finset (Fin 8)) :=
  {{0, 1, 2, 3, 5}, {0, 1, 2, 3, 6}, {0, 1, 2, 5, 7}, {0, 1, 2, 6, 7}, {0, 1, 3, 4, 5}, {0, 1, 3, 4, 6}, {0, 1, 4, 5, 6}, {0, 1, 5, 6, 7}, {0, 2, 3, 5, 7}, {0, 2, 3, 6, 7}, {0, 3, 4, 5, 7}, {0, 3, 4, 6, 7}, {0, 4, 5, 6, 7}, {1, 2, 3, 4, 5}, {1, 2, 3, 4, 6}, {1, 2, 4, 5, 6}, {1, 2, 5, 6, 7}, {2, 3, 4, 5, 7}, {2, 3, 4, 6, 7}, {2, 4, 5, 6, 7}}

/-- The counterexample sphere. -/
def Kcex : Complex4 (Fin 8) := ⟨KcexSimps, by decide +kernel⟩

/-- The 23 triangles of the counterexample. -/
def Tcex : Finset (Finset (Fin 8)) :=
  {{0, 1, 3}, {0, 1, 4}, {0, 1, 7}, {0, 2, 5}, {0, 2, 6}, {0, 3, 4}, {0, 3, 5}, {0, 3, 7}, {0, 4, 5}, {0, 4, 6}, {0, 5, 6}, {0, 6, 7}, {1, 2, 4}, {1, 2, 7}, {1, 3, 5}, {1, 3, 6}, {1, 4, 5}, {1, 6, 7}, {2, 3, 6}, {2, 3, 7}, {2, 4, 7}, {3, 4, 6}, {5, 6, 7}}

/-- The blocking set that stops the forcing in the complex after the move, without `{0,2,3,6}`. -/
def Xcex : Finset (Finset (Fin 8)) :=
  {{0, 1, 2}, {0, 2, 3}, {0, 2, 4}, {0, 2, 7}, {0, 4, 7}, {1, 2, 3}, {1, 2, 5}, {1, 2, 6}, {2, 3, 4}, {2, 3, 5}, {2, 4, 5}, {2, 4, 6}, {2, 5, 6}, {2, 5, 7}, {2, 6, 7}, {3, 4, 7}, {4, 5, 7}, {4, 6, 7}}

/-- The 3-3 move of the counterexample. -/
theorem isMoveCex : Kcex.IsMove {3, 6, 7} {0, 2, 4} :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- `Tcex` is robust for `Kcex`. -/
theorem robust_Kcex : Robust Kcex Tcex := robust_of_robustBy (L := [
    ({0, 1, 2, 3}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 2, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 6}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 2, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 2, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 3, 4}, [({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 5}, {1, 3, 4}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 3, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 4, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 3, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 4, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 4, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 5, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 1, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 1, 3, 6}, {0, 1, 6}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 2, 3, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 2, 3, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 6, 7}, {0, 2, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 6, 7}, {1, 2, 6}), ({0, 1, 2, 6}, {0, 1, 2}), ({0, 2, 3, 7}, {0, 2, 3}), ({0, 2, 5, 7}, {2, 5, 7}), ({1, 2, 3, 6}, {1, 2, 3}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 2, 5, 7}, {1, 2, 5}), ({2, 3, 4, 6}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 4, 6, 7}, {4, 6, 7}), ({2, 5, 6, 7}, {2, 5, 6}), ({3, 4, 5, 7}, {4, 5, 7}), ({0, 3, 4, 7}, {0, 4, 7}), ({1, 2, 4, 5}, {2, 4, 5})]),
    ({0, 2, 3, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 6, 7}, {0, 2, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 6, 7}, {1, 2, 6}), ({0, 1, 2, 6}, {0, 1, 2}), ({0, 2, 3, 5}, {2, 3, 5}), ({0, 2, 5, 7}, {2, 5, 7}), ({1, 2, 3, 6}, {1, 2, 3}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 2, 5, 7}, {1, 2, 5}), ({2, 3, 4, 6}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({2, 5, 6, 7}, {2, 5, 6}), ({3, 4, 5, 7}, {4, 5, 7}), ({0, 3, 4, 7}, {0, 4, 7}), ({1, 2, 4, 5}, {2, 4, 5})]),
    ({0, 2, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 6, 7}, {1, 2, 6}), ({0, 1, 2, 6}, {0, 1, 2}), ({0, 2, 3, 5}, {2, 3, 5}), ({1, 2, 3, 6}, {1, 2, 3}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 6}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 3, 5, 7}, {2, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({2, 5, 6, 7}, {2, 5, 6}), ({3, 4, 5, 7}, {4, 5, 7}), ({0, 1, 2, 5}, {1, 2, 5}), ({0, 3, 4, 7}, {0, 4, 7}), ({1, 2, 4, 5}, {2, 4, 5})]),
    ({0, 2, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 3, 4, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 5}, {3, 4, 5}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 3, 4, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({0, 1, 3, 6}, {0, 3, 6}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 2, 6, 7}, {2, 6, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({0, 3, 6, 7}, {3, 6, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 3, 4, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 4, 5, 7}, {0, 4, 7})]),
    ({0, 3, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({0, 2, 3, 5}, {2, 3, 5}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 3, 5, 7}, {3, 5, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 3, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 2, 6, 7}, {2, 6, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 3, 6, 7}, {3, 6, 7}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 4, 5, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 1, 5, 7}, {1, 5, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({1, 4, 5, 6}, {4, 5, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 4, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 4, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({0, 5, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 1, 5, 7}, {0, 5, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 3, 4}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 3, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 6}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 3, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 4, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 6}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 6}, {2, 4, 5}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 4, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 6}, {2, 4, 6}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 5, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 6}, {0, 1, 2}), ({1, 2, 3, 6}, {1, 2, 3}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 2, 5, 6}, {1, 2, 5}), ({2, 3, 4, 6}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 6}, {2, 4, 5}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 2, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({0, 1, 2, 6}, {1, 2, 6}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 3, 4, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 3, 4, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 1, 4, 6}, {1, 4, 6}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 1, 5, 7}, {1, 5, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 4, 5, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 1, 5, 6}, {1, 5, 6}), ({0, 1, 5, 7}, {1, 5, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({1, 5, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 1, 5, 7}, {1, 5, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 3, 4, 5}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 6}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 3, 4, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 3, 4, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({3, 4, 5, 7}, {3, 4, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 3, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({0, 2, 3, 5}, {2, 3, 5}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 3, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 2, 6, 7}, {2, 6, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 4, 5, 6}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 4, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({3, 4, 5, 7}, {4, 5, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 4, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({3, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({2, 5, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({1, 2, 5, 6}, {2, 5, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({3, 4, 5, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({3, 4, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})]),
    ({4, 5, 6, 7}, [({0, 1, 3, 4}, {1, 3, 4}), ({0, 1, 3, 5}, {0, 1, 5}), ({0, 1, 6, 7}, {0, 1, 6}), ({0, 3, 4, 5}, {3, 4, 5}), ({0, 3, 4, 6}, {0, 3, 6}), ({0, 3, 6, 7}, {3, 6, 7}), ({0, 4, 5, 6}, {4, 5, 6}), ({0, 5, 6, 7}, {0, 5, 7}), ({1, 3, 4, 6}, {1, 4, 6}), ({1, 4, 5, 6}, {1, 5, 6}), ({1, 5, 6, 7}, {1, 5, 7}), ({2, 3, 6, 7}, {2, 6, 7}), ({0, 2, 3, 6}, {0, 2, 3}), ({0, 2, 3, 7}, {0, 2, 7}), ({0, 2, 5, 7}, {2, 5, 7}), ({0, 3, 5, 7}, {3, 5, 7}), ({1, 2, 5, 7}, {1, 2, 5}), ({1, 2, 6, 7}, {1, 2, 6}), ({2, 3, 5, 7}, {2, 3, 5}), ({2, 5, 6, 7}, {2, 5, 6}), ({0, 1, 2, 5}, {0, 1, 2}), ({1, 2, 3, 5}, {1, 2, 3}), ({1, 2, 4, 5}, {2, 4, 5}), ({1, 2, 4, 6}, {2, 4, 6}), ({2, 3, 4, 5}, {2, 3, 4}), ({2, 3, 4, 7}, {3, 4, 7}), ({2, 4, 5, 7}, {4, 5, 7}), ({2, 4, 6, 7}, {4, 6, 7}), ({0, 3, 4, 7}, {0, 4, 7})])]
)
  (by decide +kernel)

/-- `Tcex` is not robust for the complex after the move: the tetrahedron `{0,2,3,6}` removed, the
triangles outside the blocking set `Xcex` contain `Tcex` and are closed, so forcing from `Tcex` never
reaches `Xcex`. -/
theorem not_robust_Kcex_move : ¬ Robust (Kcex.move isMoveCex) Tcex := by
  intro hR
  have ht : ({0, 2, 3, 6} : Finset (Fin 8)) ∈ (Kcex.move isMoveCex).tets := by decide +kernel
  have hs := (hR _ ht).sound (W := (Kcex.move isMoveCex).tris \ Xcex)
    (by unfold ClosedUnder; decide +kernel) (by decide +kernel)
  have hx : ({0, 1, 2} : Finset (Fin 8)) ∈ (Kcex.move isMoveCex).tris := by decide +kernel
  have := hs hx
  exact (mem_sdiff.mp this).2 (by decide)

/-- **Robustness is not kept under the 3-3 move.** A robust set that does not contain the moved
triangle need not be robust after the move (the converse of `Forcing33.forces_move33_of_robust`
holds only for forcing, not for robustness). -/
theorem robust_not_kept_by_move33 : ∃ (K : Complex4 (Fin 8)) (σ τ : Finset (Fin 8))
    (h : K.IsMove σ τ) (T : Finset (Finset (Fin 8))), Robust K T ∧ σ ∉ T ∧ ¬ Robust (K.move h) T :=
  ⟨Kcex, _, _, isMoveCex, Tcex, robust_Kcex, by decide, not_robust_Kcex_move⟩

end Lightlike.SpinFoam
