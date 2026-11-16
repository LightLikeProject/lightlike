import Lightlike.Recoupling.Symmetry
import Lightlike.FourD.Orientation

/-!
# The vertex amplitude of the Ooguri model and the 15j symbol

The vertex amplitude of the 4-dimensional SU(2) BF (Ooguri) model is the evaluation of the spin
network on the boundary of a 4-simplex `s`: one 4-valent intertwiner for each of the five
tetrahedra, joined along the ten triangles. This file fixes its conventions and proves that they
agree with Recoupling's 15j symbol `fifteenJSimplex` and with the orientations of `FourD`.

## Conventions

Doubled spins throughout.

* A colouring `col : Finset V → ℕ` gives a spin to every triangle and a virtual spin to every
  tetrahedron.
* **Tetrahedra.** A tetrahedron `t` with vertices `w₀ < w₁ < w₂ < w₃` carries the canonical
  intertwiner `canonTet`: `fourJ` with the legs `t∖w₀, t∖w₂, t∖w₁, t∖w₃` in this order, so that
  its virtual spin `col t` couples the triangles opposite `w₀` and `w₂`.
* **Strands.** At the triangle `f = s∖{a, b}` the two tetrahedra `s∖{a}` and `s∖{b}` are joined by
  the invariant bilinear form `(-1)^((j - m)/2) δ_{m', -m}`, whose first slot belongs to the
  tetrahedron `s∖{firstVert o s a b}`. The rule `firstVert` is derived from the group-integral form
  of BF theory for a 4-simplex with orientation `o = ±1` relative to its vertex order, using
  `FourD`'s incidence signs `inc`: the strand runs into the tetrahedron that induces the positive
  orientation on `f`, and the first slot belongs to it when its own vertex order induces the
  positive orientation on `f`.
* `vertexContr o s col`: the resulting contraction (`legSign` gives the sign of each leg's
  projection, `edgeSign` the sign of the bilinear form).

## Main results

* `vertexContr_eq`: for both orientations `o = 1` and `o = -1`,
  `vertexContr o s col = vertexAmp s col`, where `vertexAmp` is the 15j symbol
  `fifteenJSimplex` with the triangles and tetrahedra labelled in the order
  `(s₀, s₂, s₄, s₁, s₃)` of the sorted vertices, times explicit signs (`ampP`). In particular
  **the amplitude does not depend on the orientation** (`vertexContr_neg`).
* The proof is a change of variables at three (orientation `1`) or nine (orientation `-1`) of the
  ten triangles, and the symmetries `fourJ_swap₁₂`, `fourJ_swap₃₄`, `fourJ_swapPairs` at the
  tetrahedra; at orientation `-1` the six extra signs cancel by the parity of the intertwiners at
  positions `1` and `3`.

## Implementation notes

The statements are reduced to the positions `0, …, 4` of the sorted vertices:
`contrP σ J K` is the contraction for triangle spins `J p q` (`p < q`), virtual spins `K i`, and
leg signs `σ i q`; `σPlus` and `σMinus` are the leg signs of the two orientations
(`legSign_eq_σPlus`, `legSign_eq_σMinus`).

## References

* `ooguri-1992`: the 15j symbol as the vertex amplitude.
* `martin-dussaud-2019`, §5.6 and §9.2: the 15j symbol as a Yutsis diagram, and the vertex
  amplitude as the evaluation of the vertex graph.
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.SpinFoam

/-! ## Position level -/

/-- The contraction of five intertwiners at the corners of a 4-simplex, at the level of the
positions `0, …, 4` of its vertices: triangle `{p, q}ᶜ` has spin `J p q` (`p < q`) and projection
variable `x_pq` (carried with sign `σ p q` by the tetrahedron at `p` and `σ q p` by the one at `q`),
tetrahedron `i` (opposite position `i`) has virtual spin `K i` and its legs in the canonical order
`(i.succAbove 0, i.succAbove 2, i.succAbove 1, i.succAbove 3)`. The sums run in the order of the
pentagram labelling `(0, 2, 4, 1, 3)`. -/
noncomputable def contrP (σ : Fin 5 → Fin 5 → ℤ) (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) : ℝ :=
  ∑ x02 ∈ Icc (-(J 0 2 : ℤ)) (J 0 2), ∑ x04 ∈ Icc (-(J 0 4 : ℤ)) (J 0 4),
  ∑ x01 ∈ Icc (-(J 0 1 : ℤ)) (J 0 1), ∑ x03 ∈ Icc (-(J 0 3 : ℤ)) (J 0 3),
  ∑ x24 ∈ Icc (-(J 2 4 : ℤ)) (J 2 4), ∑ x12 ∈ Icc (-(J 1 2 : ℤ)) (J 1 2),
  ∑ x23 ∈ Icc (-(J 2 3 : ℤ)) (J 2 3), ∑ x14 ∈ Icc (-(J 1 4 : ℤ)) (J 1 4),
  ∑ x34 ∈ Icc (-(J 3 4 : ℤ)) (J 3 4), ∑ x13 ∈ Icc (-(J 1 3 : ℤ)) (J 1 3),
    edgeSign (J 0 1) x01 * edgeSign (J 0 2) x02 * edgeSign (J 0 3) x03 * edgeSign (J 0 4) x04 *
      edgeSign (J 1 2) x12 * edgeSign (J 1 3) x13 * edgeSign (J 1 4) x14 *
      edgeSign (J 2 3) x23 * edgeSign (J 2 4) x24 * edgeSign (J 3 4) x34 *
    (fourJ (J 0 1) (J 0 3) (J 0 2) (J 0 4) (K 0)
        (σ 0 1 * x01) (σ 0 3 * x03) (σ 0 2 * x02) (σ 0 4 * x04) *
      fourJ (J 0 1) (J 1 3) (J 1 2) (J 1 4) (K 1)
        (σ 1 0 * x01) (σ 1 3 * x13) (σ 1 2 * x12) (σ 1 4 * x14) *
      fourJ (J 0 2) (J 2 3) (J 1 2) (J 2 4) (K 2)
        (σ 2 0 * x02) (σ 2 3 * x23) (σ 2 1 * x12) (σ 2 4 * x24) *
      fourJ (J 0 3) (J 2 3) (J 1 3) (J 3 4) (K 3)
        (σ 3 0 * x03) (σ 3 2 * x23) (σ 3 1 * x13) (σ 3 4 * x34) *
      fourJ (J 0 4) (J 2 4) (J 1 4) (J 3 4) (K 4)
        (σ 4 0 * x04) (σ 4 2 * x24) (σ 4 1 * x14) (σ 4 3 * x34))

/-- The leg signs for orientation `o = 1`: `σPlus i q = 1` when the tetrahedron at `i` holds the
first slot of the bilinear form on the triangle `{i, q}ᶜ`. -/
def σPlus : Fin 5 → Fin 5 → ℤ :=
  ![![0, 1, -1, 1, -1], ![-1, 0, -1, 1, -1], ![1, 1, 0, 1, -1], ![-1, -1, -1, 0, -1],
    ![1, 1, 1, 1, 0]]

/-- The leg signs for orientation `o = -1`. -/
def σMinus : Fin 5 → Fin 5 → ℤ :=
  ![![0, -1, -1, -1, -1], ![1, 0, 1, 1, 1], ![1, -1, 0, -1, -1], ![1, -1, 1, 0, 1],
    ![1, -1, 1, -1, 0]]

@[simp] lemma σPlus_01 : σPlus 0 1 = 1 := rfl
@[simp] lemma σPlus_02 : σPlus 0 2 = -1 := rfl
@[simp] lemma σPlus_03 : σPlus 0 3 = 1 := rfl
@[simp] lemma σPlus_04 : σPlus 0 4 = -1 := rfl
@[simp] lemma σPlus_10 : σPlus 1 0 = -1 := rfl
@[simp] lemma σPlus_12 : σPlus 1 2 = -1 := rfl
@[simp] lemma σPlus_13 : σPlus 1 3 = 1 := rfl
@[simp] lemma σPlus_14 : σPlus 1 4 = -1 := rfl
@[simp] lemma σPlus_20 : σPlus 2 0 = 1 := rfl
@[simp] lemma σPlus_21 : σPlus 2 1 = 1 := rfl
@[simp] lemma σPlus_23 : σPlus 2 3 = 1 := rfl
@[simp] lemma σPlus_24 : σPlus 2 4 = -1 := rfl
@[simp] lemma σPlus_30 : σPlus 3 0 = -1 := rfl
@[simp] lemma σPlus_31 : σPlus 3 1 = -1 := rfl
@[simp] lemma σPlus_32 : σPlus 3 2 = -1 := rfl
@[simp] lemma σPlus_34 : σPlus 3 4 = -1 := rfl
@[simp] lemma σPlus_40 : σPlus 4 0 = 1 := rfl
@[simp] lemma σPlus_41 : σPlus 4 1 = 1 := rfl
@[simp] lemma σPlus_42 : σPlus 4 2 = 1 := rfl
@[simp] lemma σPlus_43 : σPlus 4 3 = 1 := rfl

@[simp] lemma σMinus_01 : σMinus 0 1 = -1 := rfl
@[simp] lemma σMinus_02 : σMinus 0 2 = -1 := rfl
@[simp] lemma σMinus_03 : σMinus 0 3 = -1 := rfl
@[simp] lemma σMinus_04 : σMinus 0 4 = -1 := rfl
@[simp] lemma σMinus_10 : σMinus 1 0 = 1 := rfl
@[simp] lemma σMinus_12 : σMinus 1 2 = 1 := rfl
@[simp] lemma σMinus_13 : σMinus 1 3 = 1 := rfl
@[simp] lemma σMinus_14 : σMinus 1 4 = 1 := rfl
@[simp] lemma σMinus_20 : σMinus 2 0 = 1 := rfl
@[simp] lemma σMinus_21 : σMinus 2 1 = -1 := rfl
@[simp] lemma σMinus_23 : σMinus 2 3 = -1 := rfl
@[simp] lemma σMinus_24 : σMinus 2 4 = -1 := rfl
@[simp] lemma σMinus_30 : σMinus 3 0 = 1 := rfl
@[simp] lemma σMinus_31 : σMinus 3 1 = -1 := rfl
@[simp] lemma σMinus_32 : σMinus 3 2 = 1 := rfl
@[simp] lemma σMinus_34 : σMinus 3 4 = 1 := rfl
@[simp] lemma σMinus_40 : σMinus 4 0 = 1 := rfl
@[simp] lemma σMinus_41 : σMinus 4 1 = -1 := rfl
@[simp] lemma σMinus_42 : σMinus 4 2 = 1 := rfl
@[simp] lemma σMinus_43 : σMinus 4 3 = -1 := rfl

/-- **The closed form of the vertex amplitude** (position level): the 15j symbol
`fifteenJSimplex` with the triangles and tetrahedra labelled in the pentagram order
`(0, 2, 4, 1, 3)`, times the signs of the leg permutations and of three reversed strands. -/
noncomputable def ampP (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) : ℝ :=
  (-1) ^ J 0 2 * (-1) ^ J 0 4 * (-1) ^ J 2 4 * (-1) ^ K 0 * (-1) ^ ((J 1 3 + J 0 1 + K 1) / 2) *
    ((-1) ^ ((K 2 + J 2 4 + J 1 2) / 2) * (-1) ^ ((J 2 3 + J 0 2 + K 2) / 2) * (-1) ^ K 2) *
    (-1) ^ ((K 3 + J 3 4 + J 1 3) / 2) * (-1) ^ K 4 *
    fifteenJSimplex (J 0 2) (J 0 4) (J 0 1) (J 0 3) (J 2 4) (J 1 2) (J 2 3) (J 1 4) (J 3 4) (J 1 3)
      (K 0) (K 2) (K 4) (K 1) (K 3)

/-- `edgeSign j (-m) = (-1)^j edgeSign j m` for `j - m` even. -/
lemma edgeSign_neg {j : ℕ} {m : ℤ} (h : ((j : ℤ) - m) % 2 = 0) :
    edgeSign j (-m) = (-1) ^ j * edgeSign j m := by
  unfold edgeSign
  have h1 : ((j : ℤ) - -m) / 2 = ((j : ℤ) - m) / 2 + m := by omega
  have h2 : (-1 : ℝ) ^ m = (-1) ^ j := by
    rw [← zpow_natCast]
    exact neg_one_zpow_congr (by omega)
  rw [h1, zpow_add₀ (by norm_num), h2]
  ring

/-- `edgeSign j (-m) F = (-1)^j edgeSign j m F` whenever `F` vanishes for `j - m` odd. -/
lemma edgeSign_neg_mul {j : ℕ} {m : ℤ} {F : ℝ} (h : ((j : ℤ) - m) % 2 ≠ 0 → F = 0) :
    edgeSign j (-m) * F = (-1) ^ j * edgeSign j m * F := by
  by_cases hp : ((j : ℤ) - m) % 2 = 0
  · rw [edgeSign_neg hp]
  · rw [h hp]; ring

/-- The parity of a nonzero intertwiner's first leg. -/
lemma fourJ_par₁ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₁ : ℤ) - m₁) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  by_contra h'
  exact h (admProj_of_fourJ_ne_zero h').1.2.2

/-- The parity of a nonzero intertwiner's second leg. -/
lemma fourJ_par₂ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₂ : ℤ) - m₂) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  by_contra h'
  exact h (admProj_of_fourJ_ne_zero h').2.1.2.2

/-- The parity of a nonzero intertwiner's third leg. -/
lemma fourJ_par₃ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₃ : ℤ) - m₃) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  by_contra h'
  exact h (admProj_of_fourJ_ne_zero h').2.2.1.2.2

/-- The parity of a nonzero intertwiner's fourth leg. -/
lemma fourJ_par₄ {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (h : ((j₄ : ℤ) - m₄) % 2 ≠ 0) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = 0 := by
  by_contra h'
  exact h (admProj_of_fourJ_ne_zero h').2.2.2.2.2

/-- **The contraction for orientation `1` is the closed form.** -/
theorem contrP_σPlus (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) : contrP σPlus J K = ampP J K := by
  unfold contrP ampP fifteenJSimplex
  simp only [Finset.mul_sum]
  -- reverse the strands at the triangles `{0,2}ᶜ`, `{0,4}ᶜ`, `{2,4}ᶜ`
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a1 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a2 _ => ?_
  refine sum_congr rfl fun a3 _ => ?_
  refine sum_congr rfl fun a4 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a5 _ => ?_
  refine sum_congr rfl fun a6 _ => ?_
  refine sum_congr rfl fun a7 _ => ?_
  refine sum_congr rfl fun a8 _ => ?_
  refine sum_congr rfl fun a9 _ => ?_
  refine sum_congr rfl fun a10 _ => ?_
  simp only [σPlus_01, σPlus_02, σPlus_03, σPlus_04, σPlus_10, σPlus_12, σPlus_13, σPlus_14,
    σPlus_20, σPlus_21, σPlus_23, σPlus_24, σPlus_30, σPlus_31, σPlus_32, σPlus_34, σPlus_40,
    σPlus_41, σPlus_42, σPlus_43, one_mul, neg_one_mul, neg_neg]
  -- the leg permutations at the five tetrahedra
  rw [fourJ_swapPairs (J 0 2) (J 0 4) (J 0 1) (J 0 3) (K 0) a1 a2 a3 a4,
    fourJ_swap₁₂ (J 1 3) (J 0 1) (J 1 2) (J 1 4) (K 1) a10 (-a3) (-a6) (-a8),
    show fourJ (J 0 2) (J 2 3) (J 1 2) (J 2 4) (K 2) (-a1) a7 a6 a5 =
      (-1) ^ ((K 2 + J 2 4 + J 1 2) / 2) * ((-1) ^ ((J 2 3 + J 0 2 + K 2) / 2) *
        ((-1) ^ K 2 * fourJ (J 2 4) (J 1 2) (J 2 3) (J 0 2) (K 2) a5 a6 a7 (-a1))) by
      rw [fourJ_swap₃₄ (J 0 2) (J 2 3) (J 2 4) (J 1 2) (K 2) (-a1) a7 a5 a6,
        fourJ_swap₁₂ (J 2 3) (J 0 2) (J 2 4) (J 1 2) (K 2) a7 (-a1) a5 a6,
        fourJ_swapPairs (J 2 4) (J 1 2) (J 2 3) (J 0 2) (K 2) a5 a6 a7 (-a1)],
    fourJ_swap₃₄ (J 0 3) (J 2 3) (J 3 4) (J 1 3) (K 3) (-a4) (-a7) (-a9) (-a10),
    fourJ_swapPairs (J 1 4) (J 3 4) (J 0 4) (J 2 4) (K 4) a8 a9 (-a2) (-a5)]
  -- the reversed strands
  have p1 : ((J 0 2 : ℤ) - a1) % 2 ≠ 0 →
      fourJ (J 0 2) (J 0 4) (J 0 1) (J 0 3) (K 0) a1 a2 a3 a4 = 0 := fourJ_par₁
  have p2 : ((J 0 4 : ℤ) - a2) % 2 ≠ 0 →
      fourJ (J 0 2) (J 0 4) (J 0 1) (J 0 3) (K 0) a1 a2 a3 a4 = 0 := fourJ_par₂
  have p5 : ((J 2 4 : ℤ) - a5) % 2 ≠ 0 →
      fourJ (J 2 4) (J 1 2) (J 2 3) (J 0 2) (K 2) a5 a6 a7 (-a1) = 0 := fourJ_par₁
  by_cases h1 : ((J 0 2 : ℤ) - a1) % 2 = 0
  · by_cases h2 : ((J 0 4 : ℤ) - a2) % 2 = 0
    · by_cases h5 : ((J 2 4 : ℤ) - a5) % 2 = 0
      · rw [edgeSign_neg h1, edgeSign_neg h2, edgeSign_neg h5]
        ring
      · rw [p5 h5]; ring
    · rw [p2 h2]; ring
  · rw [p1 h1]; ring

/-- **The contraction for orientation `-1` equals the one for orientation `1`.** The two differ in
the direction of the strands at the six triangles `{p, q}ᶜ` with `p, q` of different parity; the
change of variables `x ↦ -x` there gives `(-1)^(J₀₁ + J₀₃ + J₁₂ + J₁₄ + J₂₃ + J₃₄)`, which is `1`
whenever the intertwiners at positions `1` and `3` are nonzero. -/
theorem contrP_σMinus (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) :
    contrP σMinus J K = contrP σPlus J K := by
  unfold contrP
  refine sum_congr rfl fun a1 _ => ?_
  refine sum_congr rfl fun a2 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a3 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a4 _ => ?_
  refine sum_congr rfl fun a5 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a6 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a7 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a8 _ => ?_
  rw [sum_Icc_neg]
  refine sum_congr rfl fun a9 _ => ?_
  refine sum_congr rfl fun a10 _ => ?_
  simp only [σPlus_01, σPlus_02, σPlus_03, σPlus_04, σPlus_10, σPlus_12, σPlus_13, σPlus_14,
    σPlus_20, σPlus_21, σPlus_23, σPlus_24, σPlus_30, σPlus_31, σPlus_32, σPlus_34, σPlus_40,
    σPlus_41, σPlus_42, σPlus_43, σMinus_01, σMinus_02, σMinus_03, σMinus_04, σMinus_10,
    σMinus_12, σMinus_13, σMinus_14, σMinus_20, σMinus_21, σMinus_23, σMinus_24, σMinus_30,
    σMinus_31, σMinus_32, σMinus_34, σMinus_40, σMinus_41, σMinus_42, σMinus_43, one_mul,
    neg_one_mul, neg_neg]
  set T1 := fourJ (J 0 1) (J 1 3) (J 1 2) (J 1 4) (K 1) (-a3) a10 (-a6) (-a8) with hT1
  set T3 := fourJ (J 0 3) (J 2 3) (J 1 3) (J 3 4) (K 3) (-a4) (-a7) (-a10) (-a9) with hT3
  by_cases h1 : T1 = 0
  · rw [h1]; ring
  by_cases h3 : T3 = 0
  · rw [h3]; ring
  obtain ⟨q1, q13, q12, q14⟩ := admProj_of_fourJ_ne_zero h1
  obtain ⟨q3, q23, -, q34⟩ := admProj_of_fourJ_ne_zero h3
  have e1 := even_of_fourJ_ne_zero h1
  have e3 := even_of_fourJ_ne_zero h3
  unfold AdmProj at q1 q12 q14 q3 q23 q34
  rw [edgeSign_neg (by omega : ((J 0 1 : ℤ) - a3) % 2 = 0),
    edgeSign_neg (by omega : ((J 0 3 : ℤ) - a4) % 2 = 0),
    edgeSign_neg (by omega : ((J 1 2 : ℤ) - a6) % 2 = 0),
    edgeSign_neg (by omega : ((J 2 3 : ℤ) - a7) % 2 = 0),
    edgeSign_neg (by omega : ((J 1 4 : ℤ) - a8) % 2 = 0),
    edgeSign_neg (by omega : ((J 3 4 : ℤ) - a9) % 2 = 0)]
  have hs : (-1 : ℝ) ^ J 0 1 * (-1) ^ J 0 3 * (-1) ^ J 1 2 * (-1) ^ J 2 3 * (-1) ^ J 1 4 *
      (-1) ^ J 3 4 = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
  linear_combination (edgeSign (J 0 1) a3 * edgeSign (J 0 2) a1 * edgeSign (J 0 3) a4 *
    edgeSign (J 0 4) a2 * edgeSign (J 1 2) a6 * edgeSign (J 1 3) a10 * edgeSign (J 1 4) a8 *
    edgeSign (J 2 3) a7 * edgeSign (J 2 4) a5 * edgeSign (J 3 4) a9 *
    (fourJ (J 0 1) (J 0 3) (J 0 2) (J 0 4) (K 0) a3 a4 (-a1) (-a2) * T1 *
      fourJ (J 0 2) (J 2 3) (J 1 2) (J 2 4) (K 2) a1 a7 a6 (-a5) * T3 *
      fourJ (J 0 4) (J 2 4) (J 1 4) (J 3 4) (K 4) a2 a5 a8 a9)) * hs


/-! ## The vertex amplitude of a 4-simplex -/

section Simplex

variable {V : Type*} [LinearOrder V]

/-- **The canonical intertwiner of a tetrahedron** `t` with vertices `w₀ < w₁ < w₂ < w₃`:
`fourJ` on the legs `t∖w₀, t∖w₂, t∖w₁, t∖w₃` (the virtual spin `col t` couples the first two),
with projection `m i` on the leg `t∖wᵢ`. -/
noncomputable def canonTet (col : Finset V → ℕ) (t : Finset V) (ht : #t = 4) (m : Fin 4 → ℤ) : ℝ :=
  fourJ (col (t.erase (t.orderEmbOfFin ht 0))) (col (t.erase (t.orderEmbOfFin ht 2)))
    (col (t.erase (t.orderEmbOfFin ht 1))) (col (t.erase (t.orderEmbOfFin ht 3))) (col t)
    (m 0) (m 2) (m 1) (m 3)

/-- **The strand rule**, from the orientation `o = ±1` of the 4-simplex `s` and `FourD`'s
incidence signs: at the triangle `s∖{a, b}`, the strand enters the tetrahedron `s∖{x}`
(`x ∈ {a, b}`) with `o [s : s∖x] [s∖x : s∖{a,b}] = 1`; the first slot of the bilinear form belongs
to that tetrahedron if `[s∖x : s∖{a,b}] = 1`, and to the other one otherwise. The result is the
vertex whose tetrahedron holds the first slot. -/
def firstVert (o : ℤ) (s : Finset V) (a b : V) : V :=
  if o * Lightlike.FourD.inc s a * Lightlike.FourD.inc (s.erase a) b = 1 then
    (if Lightlike.FourD.inc (s.erase a) b = 1 then a else b)
  else (if Lightlike.FourD.inc (s.erase b) a = 1 then b else a)

/-- The sign with which the tetrahedron `s∖{a}` carries the projection of the strand at the
triangle `s∖{a, b}`: `1` if it holds the first slot, `-1` otherwise. -/
def legSign (o : ℤ) (s : Finset V) (a b : V) : ℤ := if firstVert o s a b = a then 1 else -1

lemma card_erase_orderEmbOfFin {s : Finset V} {n : ℕ} (hs : #s = n + 1) (i : Fin (n + 1)) :
    #(s.erase (s.orderEmbOfFin hs i)) = n := by
  rw [card_erase_of_mem (s.orderEmbOfFin_mem hs i), hs]
  rfl

/-- The symmetric matrix of the ten projection variables. -/
def cornerMat (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) : Fin 5 → Fin 5 → ℤ :=
  ![![0, x01, x02, x03, x04], ![x01, 0, x12, x13, x14], ![x02, x12, 0, x23, x24],
    ![x03, x13, x23, 0, x34], ![x04, x14, x24, x34, 0]]

/-- **The vertex contraction** of an oriented 4-simplex `s` (orientation `o` relative to its
vertex order `s₀ < ⋯ < s₄`): the canonical intertwiners of its five tetrahedra `s∖{sᵢ}`, joined
along the ten triangles by the invariant bilinear form with the strand rule `firstVert`. The
projection variable of the triangle `s∖{s_p, s_q}` is carried with sign `legSign` by each of its
two tetrahedra. -/
noncomputable def vertexContr (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) : ℝ :=
  let v := s.orderEmbOfFin hs
  let J : Fin 5 → Fin 5 → ℕ := fun p q => col ((s.erase (v p)).erase (v q))
  ∑ x02 ∈ Icc (-(J 0 2 : ℤ)) (J 0 2), ∑ x04 ∈ Icc (-(J 0 4 : ℤ)) (J 0 4),
  ∑ x01 ∈ Icc (-(J 0 1 : ℤ)) (J 0 1), ∑ x03 ∈ Icc (-(J 0 3 : ℤ)) (J 0 3),
  ∑ x24 ∈ Icc (-(J 2 4 : ℤ)) (J 2 4), ∑ x12 ∈ Icc (-(J 1 2 : ℤ)) (J 1 2),
  ∑ x23 ∈ Icc (-(J 2 3 : ℤ)) (J 2 3), ∑ x14 ∈ Icc (-(J 1 4 : ℤ)) (J 1 4),
  ∑ x34 ∈ Icc (-(J 3 4 : ℤ)) (J 3 4), ∑ x13 ∈ Icc (-(J 1 3 : ℤ)) (J 1 3),
    edgeSign (J 0 1) x01 * edgeSign (J 0 2) x02 * edgeSign (J 0 3) x03 * edgeSign (J 0 4) x04 *
      edgeSign (J 1 2) x12 * edgeSign (J 1 3) x13 * edgeSign (J 1 4) x14 *
      edgeSign (J 2 3) x23 * edgeSign (J 2 4) x24 * edgeSign (J 3 4) x34 *
    ∏ i : Fin 5, canonTet col (s.erase (v i)) (card_erase_orderEmbOfFin hs i) (fun j =>
      legSign o s (v i) (v (i.succAbove j)) *
        cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 i (i.succAbove j))

/-- **The vertex amplitude** of the 4-simplex `s` (the closed form `ampP`): the 15j symbol
`fifteenJSimplex` with the triangles and tetrahedra in the order `(s₀, s₂, s₄, s₁, s₃)` of the
sorted vertices, times explicit signs. -/
noncomputable def vertexAmp (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) : ℝ :=
  ampP (fun p q => col ((s.erase (s.orderEmbOfFin hs p)).erase (s.orderEmbOfFin hs q)))
    (fun i => col (s.erase (s.orderEmbOfFin hs i)))

/-! ### Positions -/

/-- The sorted vertices of a face `s∖{sᵢ}` are those of `s` with `sᵢ` skipped. -/
lemma orderEmbOfFin_erase {s : Finset V} {n : ℕ} (hs : #s = n + 1) (i : Fin (n + 1))
    (h : #(s.erase (s.orderEmbOfFin hs i)) = n) (j : Fin n) :
    (s.erase (s.orderEmbOfFin hs i)).orderEmbOfFin h j = s.orderEmbOfFin hs (i.succAbove j) := by
  have := Finset.orderEmbOfFin_unique h (f := fun j => s.orderEmbOfFin hs (i.succAbove j))
    (fun x => mem_erase.mpr ⟨fun he => Fin.succAbove_ne i x ((s.orderEmbOfFin hs).injective he),
      s.orderEmbOfFin_mem hs _⟩)
    ((s.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove i))
  exact (congrFun this j).symm

/-- The `i`-th sorted vertex has position `i`. -/
lemma pos_orderEmbOfFin {s : Finset V} {n : ℕ} (hs : #s = n) (i : Fin n) :
    Lightlike.FourD.pos s (s.orderEmbOfFin hs i) = i := by
  unfold Lightlike.FourD.pos
  have : s.filter (· < s.orderEmbOfFin hs i) =
      (univ.filter (fun j : Fin n => (j : ℕ) < i)).map (s.orderEmbOfFin hs).toEmbedding := by
    ext x
    simp only [mem_filter, mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hxs, hlt⟩
      have hx : x ∈ Set.range (s.orderEmbOfFin hs) := by
        rw [Finset.range_orderEmbOfFin]; exact hxs
      obtain ⟨j, rfl⟩ := hx
      exact ⟨j, (s.orderEmbOfFin hs).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨s.orderEmbOfFin_mem hs j, (s.orderEmbOfFin hs).lt_iff_lt.mpr hj⟩
  rw [this, card_map, Fin.card_filter_val_lt]
  exact min_eq_right i.2.le

lemma inc_orderEmbOfFin {s : Finset V} {n : ℕ} (hs : #s = n) (i : Fin n) :
    Lightlike.FourD.inc s (s.orderEmbOfFin hs i) = (-1) ^ (i : ℕ) := by
  rw [Lightlike.FourD.inc, pos_orderEmbOfFin]

lemma inc_erase_orderEmbOfFin {s : Finset V} {n : ℕ} (hs : #s = n) (p q : Fin n) (hpq : p ≠ q) :
    Lightlike.FourD.inc (s.erase (s.orderEmbOfFin hs p)) (s.orderEmbOfFin hs q) =
      (-1) ^ (if q < p then (q : ℕ) else (q : ℕ) - 1) := by
  rw [Lightlike.FourD.inc]
  congr 1
  rcases lt_or_gt_of_ne hpq with h | h
  · rw [ite_eq_right (not_lt.mpr h.le), ← pos_orderEmbOfFin hs q]
    have := Lightlike.FourD.pos_erase_of_gt (s.orderEmbOfFin_mem hs p)
      ((s.orderEmbOfFin hs).lt_iff_lt.mpr h)
    omega
  · rw [ite_eq_left h, Lightlike.FourD.pos_erase_of_lt ((s.orderEmbOfFin hs).lt_iff_lt.mpr h),
      pos_orderEmbOfFin]

@[simp] lemma succAbove_00 : ((0 : Fin 5).succAbove (0 : Fin 4)) = 1 := rfl
@[simp] lemma succAbove_01 : ((0 : Fin 5).succAbove (1 : Fin 4)) = 2 := rfl
@[simp] lemma succAbove_02 : ((0 : Fin 5).succAbove (2 : Fin 4)) = 3 := rfl
@[simp] lemma succAbove_03 : ((0 : Fin 5).succAbove (3 : Fin 4)) = 4 := rfl
@[simp] lemma succAbove_10 : ((1 : Fin 5).succAbove (0 : Fin 4)) = 0 := rfl
@[simp] lemma succAbove_11 : ((1 : Fin 5).succAbove (1 : Fin 4)) = 2 := rfl
@[simp] lemma succAbove_12 : ((1 : Fin 5).succAbove (2 : Fin 4)) = 3 := rfl
@[simp] lemma succAbove_13 : ((1 : Fin 5).succAbove (3 : Fin 4)) = 4 := rfl
@[simp] lemma succAbove_20 : ((2 : Fin 5).succAbove (0 : Fin 4)) = 0 := rfl
@[simp] lemma succAbove_21 : ((2 : Fin 5).succAbove (1 : Fin 4)) = 1 := rfl
@[simp] lemma succAbove_22 : ((2 : Fin 5).succAbove (2 : Fin 4)) = 3 := rfl
@[simp] lemma succAbove_23 : ((2 : Fin 5).succAbove (3 : Fin 4)) = 4 := rfl
@[simp] lemma succAbove_30 : ((3 : Fin 5).succAbove (0 : Fin 4)) = 0 := rfl
@[simp] lemma succAbove_31 : ((3 : Fin 5).succAbove (1 : Fin 4)) = 1 := rfl
@[simp] lemma succAbove_32 : ((3 : Fin 5).succAbove (2 : Fin 4)) = 2 := rfl
@[simp] lemma succAbove_33 : ((3 : Fin 5).succAbove (3 : Fin 4)) = 4 := rfl
@[simp] lemma succAbove_40 : ((4 : Fin 5).succAbove (0 : Fin 4)) = 0 := rfl
@[simp] lemma succAbove_41 : ((4 : Fin 5).succAbove (1 : Fin 4)) = 1 := rfl
@[simp] lemma succAbove_42 : ((4 : Fin 5).succAbove (2 : Fin 4)) = 2 := rfl
@[simp] lemma succAbove_43 : ((4 : Fin 5).succAbove (3 : Fin 4)) = 3 := rfl

@[simp] lemma cornerMat_01 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 0 1 = x01 := rfl
@[simp] lemma cornerMat_02 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 0 2 = x02 := rfl
@[simp] lemma cornerMat_03 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 0 3 = x03 := rfl
@[simp] lemma cornerMat_04 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 0 4 = x04 := rfl
@[simp] lemma cornerMat_10 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 1 0 = x01 := rfl
@[simp] lemma cornerMat_12 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 1 2 = x12 := rfl
@[simp] lemma cornerMat_13 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 1 3 = x13 := rfl
@[simp] lemma cornerMat_14 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 1 4 = x14 := rfl
@[simp] lemma cornerMat_20 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 2 0 = x02 := rfl
@[simp] lemma cornerMat_21 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 2 1 = x12 := rfl
@[simp] lemma cornerMat_23 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 2 3 = x23 := rfl
@[simp] lemma cornerMat_24 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 2 4 = x24 := rfl
@[simp] lemma cornerMat_30 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 3 0 = x03 := rfl
@[simp] lemma cornerMat_31 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 3 1 = x13 := rfl
@[simp] lemma cornerMat_32 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 3 2 = x23 := rfl
@[simp] lemma cornerMat_34 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 3 4 = x34 := rfl
@[simp] lemma cornerMat_40 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 4 0 = x04 := rfl
@[simp] lemma cornerMat_41 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 4 1 = x14 := rfl
@[simp] lemma cornerMat_42 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 4 2 = x24 := rfl
@[simp] lemma cornerMat_43 (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ) :
    cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 4 3 = x34 := rfl

/-- The leg signs of `FourD`'s strand rule at the sorted vertices: `σPlus` for orientation `1`,
`σMinus` for orientation `-1`. -/
lemma legSign_orderEmbOfFin {s : Finset V} (hs : #s = 5) {o : ℤ} (ho : o = 1 ∨ o = -1)
    (i q : Fin 5) (hiq : i ≠ q) :
    legSign o s (s.orderEmbOfFin hs i) (s.orderEmbOfFin hs q) =
      (if o = 1 then σPlus else σMinus) i q := by
  have hne : s.orderEmbOfFin hs q ≠ s.orderEmbOfFin hs i :=
    fun h => hiq ((s.orderEmbOfFin hs).injective h).symm
  unfold legSign firstVert
  rw [inc_orderEmbOfFin hs i, inc_erase_orderEmbOfFin hs i q hiq,
    inc_erase_orderEmbOfFin hs q i hiq.symm]
  rcases ho with rfl | rfl <;> fin_cases i <;> fin_cases q <;>
    first | exact absurd rfl hiq | simp

lemma canonTet_0 (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (σ : Fin 5 → Fin 5 → ℤ) (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ)
    (h1 : legSign o s (s.orderEmbOfFin hs 0) (s.orderEmbOfFin hs 1) = σ 0 1) (h2 : legSign o s (s.orderEmbOfFin hs 0) (s.orderEmbOfFin hs 2) = σ 0 2) (h3 : legSign o s (s.orderEmbOfFin hs 0) (s.orderEmbOfFin hs 3) = σ 0 3) (h4 : legSign o s (s.orderEmbOfFin hs 0) (s.orderEmbOfFin hs 4) = σ 0 4) :
    canonTet col (s.erase (s.orderEmbOfFin hs 0)) (card_erase_orderEmbOfFin hs 0) (fun j =>
      legSign o s (s.orderEmbOfFin hs 0) (s.orderEmbOfFin hs ((0 : Fin 5).succAbove j)) *
        cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 0 ((0 : Fin 5).succAbove j)) =
    fourJ (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 1))) (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 3))) (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 2))) (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 4))) (col (s.erase (s.orderEmbOfFin hs 0)))
      (σ 0 1 * x01) (σ 0 3 * x03) (σ 0 2 * x02) (σ 0 4 * x04) := by
  simp only [canonTet, orderEmbOfFin_erase, succAbove_00, succAbove_01, succAbove_02, succAbove_03, cornerMat_01, cornerMat_03, cornerMat_02, cornerMat_04, h1, h2, h3, h4]

lemma canonTet_1 (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (σ : Fin 5 → Fin 5 → ℤ) (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ)
    (h0 : legSign o s (s.orderEmbOfFin hs 1) (s.orderEmbOfFin hs 0) = σ 1 0) (h2 : legSign o s (s.orderEmbOfFin hs 1) (s.orderEmbOfFin hs 2) = σ 1 2) (h3 : legSign o s (s.orderEmbOfFin hs 1) (s.orderEmbOfFin hs 3) = σ 1 3) (h4 : legSign o s (s.orderEmbOfFin hs 1) (s.orderEmbOfFin hs 4) = σ 1 4) :
    canonTet col (s.erase (s.orderEmbOfFin hs 1)) (card_erase_orderEmbOfFin hs 1) (fun j =>
      legSign o s (s.orderEmbOfFin hs 1) (s.orderEmbOfFin hs ((1 : Fin 5).succAbove j)) *
        cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 1 ((1 : Fin 5).succAbove j)) =
    fourJ (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 1))) (col ((s.erase (s.orderEmbOfFin hs 1)).erase (s.orderEmbOfFin hs 3))) (col ((s.erase (s.orderEmbOfFin hs 1)).erase (s.orderEmbOfFin hs 2))) (col ((s.erase (s.orderEmbOfFin hs 1)).erase (s.orderEmbOfFin hs 4))) (col (s.erase (s.orderEmbOfFin hs 1)))
      (σ 1 0 * x01) (σ 1 3 * x13) (σ 1 2 * x12) (σ 1 4 * x14) := by
  simp only [canonTet, orderEmbOfFin_erase, succAbove_10, succAbove_11, succAbove_12, succAbove_13, cornerMat_10, cornerMat_13, cornerMat_12, cornerMat_14, h0, h2, h3, h4]
  rw [erase_right_comm (s := s) (a := s.orderEmbOfFin hs 1) (b := s.orderEmbOfFin hs 0)]

lemma canonTet_2 (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (σ : Fin 5 → Fin 5 → ℤ) (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ)
    (h0 : legSign o s (s.orderEmbOfFin hs 2) (s.orderEmbOfFin hs 0) = σ 2 0) (h1 : legSign o s (s.orderEmbOfFin hs 2) (s.orderEmbOfFin hs 1) = σ 2 1) (h3 : legSign o s (s.orderEmbOfFin hs 2) (s.orderEmbOfFin hs 3) = σ 2 3) (h4 : legSign o s (s.orderEmbOfFin hs 2) (s.orderEmbOfFin hs 4) = σ 2 4) :
    canonTet col (s.erase (s.orderEmbOfFin hs 2)) (card_erase_orderEmbOfFin hs 2) (fun j =>
      legSign o s (s.orderEmbOfFin hs 2) (s.orderEmbOfFin hs ((2 : Fin 5).succAbove j)) *
        cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 2 ((2 : Fin 5).succAbove j)) =
    fourJ (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 2))) (col ((s.erase (s.orderEmbOfFin hs 2)).erase (s.orderEmbOfFin hs 3))) (col ((s.erase (s.orderEmbOfFin hs 1)).erase (s.orderEmbOfFin hs 2))) (col ((s.erase (s.orderEmbOfFin hs 2)).erase (s.orderEmbOfFin hs 4))) (col (s.erase (s.orderEmbOfFin hs 2)))
      (σ 2 0 * x02) (σ 2 3 * x23) (σ 2 1 * x12) (σ 2 4 * x24) := by
  simp only [canonTet, orderEmbOfFin_erase, succAbove_20, succAbove_21, succAbove_22, succAbove_23, cornerMat_20, cornerMat_23, cornerMat_21, cornerMat_24, h0, h1, h3, h4]
  rw [erase_right_comm (s := s) (a := s.orderEmbOfFin hs 2) (b := s.orderEmbOfFin hs 0), erase_right_comm (s := s) (a := s.orderEmbOfFin hs 2) (b := s.orderEmbOfFin hs 1)]

lemma canonTet_3 (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (σ : Fin 5 → Fin 5 → ℤ) (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ)
    (h0 : legSign o s (s.orderEmbOfFin hs 3) (s.orderEmbOfFin hs 0) = σ 3 0) (h1 : legSign o s (s.orderEmbOfFin hs 3) (s.orderEmbOfFin hs 1) = σ 3 1) (h2 : legSign o s (s.orderEmbOfFin hs 3) (s.orderEmbOfFin hs 2) = σ 3 2) (h4 : legSign o s (s.orderEmbOfFin hs 3) (s.orderEmbOfFin hs 4) = σ 3 4) :
    canonTet col (s.erase (s.orderEmbOfFin hs 3)) (card_erase_orderEmbOfFin hs 3) (fun j =>
      legSign o s (s.orderEmbOfFin hs 3) (s.orderEmbOfFin hs ((3 : Fin 5).succAbove j)) *
        cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 3 ((3 : Fin 5).succAbove j)) =
    fourJ (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 3))) (col ((s.erase (s.orderEmbOfFin hs 2)).erase (s.orderEmbOfFin hs 3))) (col ((s.erase (s.orderEmbOfFin hs 1)).erase (s.orderEmbOfFin hs 3))) (col ((s.erase (s.orderEmbOfFin hs 3)).erase (s.orderEmbOfFin hs 4))) (col (s.erase (s.orderEmbOfFin hs 3)))
      (σ 3 0 * x03) (σ 3 2 * x23) (σ 3 1 * x13) (σ 3 4 * x34) := by
  simp only [canonTet, orderEmbOfFin_erase, succAbove_30, succAbove_31, succAbove_32, succAbove_33, cornerMat_30, cornerMat_32, cornerMat_31, cornerMat_34, h0, h1, h2, h4]
  rw [erase_right_comm (s := s) (a := s.orderEmbOfFin hs 3) (b := s.orderEmbOfFin hs 0), erase_right_comm (s := s) (a := s.orderEmbOfFin hs 3) (b := s.orderEmbOfFin hs 2), erase_right_comm (s := s) (a := s.orderEmbOfFin hs 3) (b := s.orderEmbOfFin hs 1)]

lemma canonTet_4 (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (σ : Fin 5 → Fin 5 → ℤ) (x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 : ℤ)
    (h0 : legSign o s (s.orderEmbOfFin hs 4) (s.orderEmbOfFin hs 0) = σ 4 0) (h1 : legSign o s (s.orderEmbOfFin hs 4) (s.orderEmbOfFin hs 1) = σ 4 1) (h2 : legSign o s (s.orderEmbOfFin hs 4) (s.orderEmbOfFin hs 2) = σ 4 2) (h3 : legSign o s (s.orderEmbOfFin hs 4) (s.orderEmbOfFin hs 3) = σ 4 3) :
    canonTet col (s.erase (s.orderEmbOfFin hs 4)) (card_erase_orderEmbOfFin hs 4) (fun j =>
      legSign o s (s.orderEmbOfFin hs 4) (s.orderEmbOfFin hs ((4 : Fin 5).succAbove j)) *
        cornerMat x01 x02 x03 x04 x12 x13 x14 x23 x24 x34 4 ((4 : Fin 5).succAbove j)) =
    fourJ (col ((s.erase (s.orderEmbOfFin hs 0)).erase (s.orderEmbOfFin hs 4))) (col ((s.erase (s.orderEmbOfFin hs 2)).erase (s.orderEmbOfFin hs 4))) (col ((s.erase (s.orderEmbOfFin hs 1)).erase (s.orderEmbOfFin hs 4))) (col ((s.erase (s.orderEmbOfFin hs 3)).erase (s.orderEmbOfFin hs 4))) (col (s.erase (s.orderEmbOfFin hs 4)))
      (σ 4 0 * x04) (σ 4 2 * x24) (σ 4 1 * x14) (σ 4 3 * x34) := by
  simp only [canonTet, orderEmbOfFin_erase, succAbove_40, succAbove_41, succAbove_42, succAbove_43, cornerMat_40, cornerMat_42, cornerMat_41, cornerMat_43, h0, h1, h2, h3]
  rw [erase_right_comm (s := s) (a := s.orderEmbOfFin hs 4) (b := s.orderEmbOfFin hs 0), erase_right_comm (s := s) (a := s.orderEmbOfFin hs 4) (b := s.orderEmbOfFin hs 2), erase_right_comm (s := s) (a := s.orderEmbOfFin hs 4) (b := s.orderEmbOfFin hs 1), erase_right_comm (s := s) (a := s.orderEmbOfFin hs 4) (b := s.orderEmbOfFin hs 3)]

/-- The vertex contraction is the position-level contraction `contrP` with the leg signs of the
strand rule. -/
lemma vertexContr_eq_contrP (o : ℤ) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ)
    (σ : Fin 5 → Fin 5 → ℤ)
    (hσ : ∀ i q, i ≠ q → legSign o s (s.orderEmbOfFin hs i) (s.orderEmbOfFin hs q) = σ i q) :
    vertexContr o s hs col =
      contrP σ (fun p q => col ((s.erase (s.orderEmbOfFin hs p)).erase (s.orderEmbOfFin hs q)))
        (fun i => col (s.erase (s.orderEmbOfFin hs i))) := by
  have h01 := hσ 0 1 (by decide)
  have h02 := hσ 0 2 (by decide)
  have h03 := hσ 0 3 (by decide)
  have h04 := hσ 0 4 (by decide)
  have h10 := hσ 1 0 (by decide)
  have h12 := hσ 1 2 (by decide)
  have h13 := hσ 1 3 (by decide)
  have h14 := hσ 1 4 (by decide)
  have h20 := hσ 2 0 (by decide)
  have h21 := hσ 2 1 (by decide)
  have h23 := hσ 2 3 (by decide)
  have h24 := hσ 2 4 (by decide)
  have h30 := hσ 3 0 (by decide)
  have h31 := hσ 3 1 (by decide)
  have h32 := hσ 3 2 (by decide)
  have h34 := hσ 3 4 (by decide)
  have h40 := hσ 4 0 (by decide)
  have h41 := hσ 4 1 (by decide)
  have h42 := hσ 4 2 (by decide)
  have h43 := hσ 4 3 (by decide)
  unfold vertexContr contrP
  dsimp only
  iterate 10 refine sum_congr rfl fun _ _ => ?_
  rw [Fin.prod_univ_five, canonTet_0 o s hs col σ _ _ _ _ _ _ _ _ _ _ h01 h02 h03 h04,
    canonTet_1 o s hs col σ _ _ _ _ _ _ _ _ _ _ h10 h12 h13 h14,
    canonTet_2 o s hs col σ _ _ _ _ _ _ _ _ _ _ h20 h21 h23 h24,
    canonTet_3 o s hs col σ _ _ _ _ _ _ _ _ _ _ h30 h31 h32 h34,
    canonTet_4 o s hs col σ _ _ _ _ _ _ _ _ _ _ h40 h41 h42 h43]

/-- **The vertex conventions agree with the 15j symbol and with `FourD`'s orientations.**
For both orientations `o = ±1` of the 4-simplex `s`, the contraction of the canonical
intertwiners with the strand rule `firstVert` is the closed form `vertexAmp`: the 15j symbol
`fifteenJSimplex` with the pentagram labelling `(s₀, s₂, s₄, s₁, s₃)` and explicit signs. -/
theorem vertexContr_eq {o : ℤ} (ho : o = 1 ∨ o = -1) (s : Finset V) (hs : #s = 5)
    (col : Finset V → ℕ) : vertexContr o s hs col = vertexAmp s hs col := by
  rw [vertexContr_eq_contrP o s hs col _ (legSign_orderEmbOfFin hs ho)]
  rcases ho with rfl | rfl
  · simp only [ite_true]
    exact contrP_σPlus _ _
  · simp only [show (-1 : ℤ) ≠ 1 by decide, ite_false]
    rw [contrP_σMinus]
    exact contrP_σPlus _ _

/-- **The vertex amplitude does not depend on the orientation.** -/
theorem vertexContr_neg (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) :
    vertexContr (-1) s hs col = vertexContr 1 s hs col := by
  rw [vertexContr_eq (Or.inr rfl), vertexContr_eq (Or.inl rfl)]

end Simplex

end Lightlike.SpinFoam
