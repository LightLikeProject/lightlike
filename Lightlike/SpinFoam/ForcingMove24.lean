import Lightlike.SpinFoam.ForcingMove33

/-!
# Forcing under the 2-4 move: the finite local lemma

The 2-4 move removes the tetrahedron `σ = {s_0, s_1, s_2, s_3}` shared by the two 4-simplices
`σ ∪ {p}` and `σ ∪ {q}`, and adds the edge `{p, q}` with the four 4-simplices `{p, q} ∪ (σ ∖ {s_i})`.
It keeps all triangles and adds the four triangles `N_i = {p, q, s_i}`. The tetrahedra of the
complex before the move are the common ones (all but `σ`) and `σ`; after the move they are the
common ones and the six `{p, q, s_j, s_k}`.

On the sixteen triangles `σ_i = σ ∖ {s_i}`, `P_{jk} = {p, s_j, s_k}` and `Q_{jk} = {q, s_j, s_k}` the
eight common tetrahedra `{p} ∪ (σ ∖ {s_i})` and `{q} ∪ (σ ∖ {s_i})` are the constraints; the
variables are Booleans (`true`: the triangle is in the set), and the pairs `{j, k}` are numbered
`0, …, 5` as `01, 02, 03, 12, 13, 23`. The finite lemma says that when the set is closed under the
eight common tetrahedra and exactly three of the `σ_i` are in it (the case where `σ` forces the
fourth), then for every `a` the triangles `N_i` can be added, starting with `N_a`, without any
forcing by the six new tetrahedra: the two complexes cannot both make progress.
-/

open Finset
open Lightlike.SpinFoam Lightlike.SpinFoam.Forcing33

namespace Lightlike.SpinFoam.Forcing24

open Lightlike.SpinFoam.Forcing33

/-- The two truth values, for the exhaustive checks. -/
def bools : List Bool := [false, true]

/-- Exactly three of four Booleans are `true`. -/
def eq3 (a b c d : Bool) : Bool := decide (a.toNat + b.toNat + c.toNat + d.toNat = 3)

set_option synthInstance.maxSize 256 in
set_option maxRecDepth 100000 in
/-- **The finite local lemma of the 2-4 move.** -/
theorem local24 :
    ∀ s0 : Bool, ∀ s1 : Bool, ∀ s2 : Bool, ∀ s3 : Bool, ∀ p0 : Bool, ∀ p1 : Bool, ∀ p2 : Bool, ∀ p3 : Bool, ok4 s3 p0 p1 p3 = true → ∀ p4 : Bool, ok4 s2 p0 p2 p4 = true → ∀ p5 : Bool, ok4 s0 p3 p4 p5 = true → ok4 s1 p1 p2 p5 = true → ∀ q0 : Bool, ∀ q1 : Bool, ∀ q2 : Bool, ∀ q3 : Bool, ok4 s3 q0 q1 q3 = true → ∀ q4 : Bool, ok4 s2 q0 q2 q4 = true → ∀ q5 : Bool, ok4 s0 q3 q4 q5 = true → ok4 s1 q1 q2 q5 = true → eq3 s0 s1 s2 s3 = true → (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n0 && ok4 n0 n1 p0 q0 && ok4 n0 n2 p1 q1 && ok4 n0 n3 p2 q2 && ok4 n1 n2 p3 q3 && ok4 n1 n3 p4 q4 && ok4 n2 n3 p5 q5)) = true ∧ (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n1 && ok4 n0 n1 p0 q0 && ok4 n0 n2 p1 q1 && ok4 n0 n3 p2 q2 && ok4 n1 n2 p3 q3 && ok4 n1 n3 p4 q4 && ok4 n2 n3 p5 q5)) = true ∧ (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n2 && ok4 n0 n1 p0 q0 && ok4 n0 n2 p1 q1 && ok4 n0 n3 p2 q2 && ok4 n1 n2 p3 q3 && ok4 n1 n3 p4 q4 && ok4 n2 n3 p5 q5)) = true ∧ (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n3 && ok4 n0 n1 p0 q0 && ok4 n0 n2 p1 q1 && ok4 n0 n3 p2 q2 && ok4 n1 n2 p3 q3 && ok4 n1 n3 p4 q4 && ok4 n2 n3 p5 q5)) = true := by decide +kernel

/-- **Wrong-input control for `local24`.** Without the hypothesis that exactly three of the `σ_i`
are in the set, the conclusion fails. Take no `σ_i`, and `P_01, P_03, P_12, P_23, Q_01, Q_03, Q_12`
only (numbered `p0 p2 p3 p5 q0 q2 q3`): the set is closed under the eight common tetrahedra, no
`σ_i` is in it, and no choice of the `N_i` containing `N_0` is closed under the six new
tetrahedra. -/
theorem local24_control :
    ok4 false true false true = true ∧
    ok4 false true false false = true ∧
    ok4 false false true true = true ∧
    ok4 false false true false = true ∧
    ok4 false true true false = true ∧
    ok4 false true true false = true ∧
    ok4 false true false true = true ∧
    ok4 false true false true = true ∧
    eq3 false false false false = false ∧
    (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n0 && ok4 n0 n1 true true && ok4 n0 n2 false false && ok4 n0 n3 true true && ok4 n1 n2 true true && ok4 n1 n3 false false && ok4 n2 n3 true false)) = false := by decide


/-! ## The six vertices of the 2-4 move as `Fin 6`

Positions `0, 1, 2, 3` are `s_0, …, s_3` (the tetrahedron `σ`), position `4` is `p` and `5` is `q`. -/

/-- The tetrahedron `σ` removed by the move: positions `0, 1, 2, 3`. -/
def sig4 : Finset (Fin 6) := {0, 1, 2, 3}

/-- The edge `τ = {p, q}`: positions `4, 5`. -/
def tau2 : Finset (Fin 6) := {4, 5}

/-- The pair `{s_j, s_k}` number `r`, in the order `01, 02, 03, 12, 13, 23`. -/
def ps : Fin 6 → Finset (Fin 6) := ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}]

/-- The triangle `σ ∖ {s_i}`. -/
def sgX (i : Fin 4) : Finset (Fin 6) := univ.filter fun v => v.val < 4 ∧ v.val ≠ i.val

/-- The triangle `{p, s_j, s_k}` of the pair `r`. -/
def mpX (r : Fin 6) : Finset (Fin 6) := insert 4 (ps r)

/-- The triangle `{q, s_j, s_k}` of the pair `r`. -/
def mqX (r : Fin 6) : Finset (Fin 6) := insert 5 (ps r)

/-- The new triangle `{p, q, s_i}`. -/
def nnX (i : Fin 4) : Finset (Fin 6) := univ.filter fun v => v.val = 4 ∨ v.val = 5 ∨ v.val = i.val

/-- The common tetrahedron `{p} ∪ (σ ∖ {s_i})`. -/
def tpX (i : Fin 4) : Finset (Fin 6) := univ.filter fun v => v.val = 4 ∨ (v.val < 4 ∧ v.val ≠ i.val)

/-- The common tetrahedron `{q} ∪ (σ ∖ {s_i})`. -/
def tqX (i : Fin 4) : Finset (Fin 6) := univ.filter fun v => v.val = 5 ∨ (v.val < 4 ∧ v.val ≠ i.val)

/-- The new tetrahedron `{p, q, s_j, s_k}` of the pair `r`. -/
def ntX (r : Fin 6) : Finset (Fin 6) := insert 4 (insert 5 (ps r))

lemma tris_sig4 : sig4.powersetCard 3 = {sgX 0, sgX 1, sgX 2, sgX 3} := by decide +kernel

lemma tris_tpX_0 : (tpX 0).powersetCard 3 = {sgX 0, mpX 3, mpX 4, mpX 5} := by decide +kernel

lemma tris_tqX_0 : (tqX 0).powersetCard 3 = {sgX 0, mqX 3, mqX 4, mqX 5} := by decide +kernel

lemma tris_tpX_1 : (tpX 1).powersetCard 3 = {sgX 1, mpX 1, mpX 2, mpX 5} := by decide +kernel

lemma tris_tqX_1 : (tqX 1).powersetCard 3 = {sgX 1, mqX 1, mqX 2, mqX 5} := by decide +kernel

lemma tris_tpX_2 : (tpX 2).powersetCard 3 = {sgX 2, mpX 0, mpX 2, mpX 4} := by decide +kernel

lemma tris_tqX_2 : (tqX 2).powersetCard 3 = {sgX 2, mqX 0, mqX 2, mqX 4} := by decide +kernel

lemma tris_tpX_3 : (tpX 3).powersetCard 3 = {sgX 3, mpX 0, mpX 1, mpX 3} := by decide +kernel

lemma tris_tqX_3 : (tqX 3).powersetCard 3 = {sgX 3, mqX 0, mqX 1, mqX 3} := by decide +kernel

lemma tris_ntX_0 : (ntX 0).powersetCard 3 = {nnX 0, nnX 1, mpX 0, mqX 0} := by decide +kernel

lemma tris_ntX_1 : (ntX 1).powersetCard 3 = {nnX 0, nnX 2, mpX 1, mqX 1} := by decide +kernel

lemma tris_ntX_2 : (ntX 2).powersetCard 3 = {nnX 0, nnX 3, mpX 2, mqX 2} := by decide +kernel

lemma tris_ntX_3 : (ntX 3).powersetCard 3 = {nnX 1, nnX 2, mpX 3, mqX 3} := by decide +kernel

lemma tris_ntX_4 : (ntX 4).powersetCard 3 = {nnX 1, nnX 3, mpX 4, mqX 4} := by decide +kernel

lemma tris_ntX_5 : (ntX 5).powersetCard 3 = {nnX 2, nnX 3, mpX 5, mqX 5} := by decide +kernel

lemma sgX_inj : ∀ i j : Fin 4, sgX i = sgX j → i = j := by decide

lemma nnX_inj : ∀ i j : Fin 4, nnX i = nnX j → i = j := by decide

lemma dist_ntX_0 : nnX 0 ≠ nnX 1 ∧ nnX 0 ≠ mpX 0 ∧ nnX 0 ≠ mqX 0 ∧ nnX 1 ≠ mpX 0 ∧
    nnX 1 ≠ mqX 0 ∧ mpX 0 ≠ mqX 0 := by decide

lemma dist_ntX_1 : nnX 0 ≠ nnX 2 ∧ nnX 0 ≠ mpX 1 ∧ nnX 0 ≠ mqX 1 ∧ nnX 2 ≠ mpX 1 ∧
    nnX 2 ≠ mqX 1 ∧ mpX 1 ≠ mqX 1 := by decide

lemma dist_ntX_2 : nnX 0 ≠ nnX 3 ∧ nnX 0 ≠ mpX 2 ∧ nnX 0 ≠ mqX 2 ∧ nnX 3 ≠ mpX 2 ∧
    nnX 3 ≠ mqX 2 ∧ mpX 2 ≠ mqX 2 := by decide

lemma dist_ntX_3 : nnX 1 ≠ nnX 2 ∧ nnX 1 ≠ mpX 3 ∧ nnX 1 ≠ mqX 3 ∧ nnX 2 ≠ mpX 3 ∧
    nnX 2 ≠ mqX 3 ∧ mpX 3 ≠ mqX 3 := by decide

lemma dist_ntX_4 : nnX 1 ≠ nnX 3 ∧ nnX 1 ≠ mpX 4 ∧ nnX 1 ≠ mqX 4 ∧ nnX 3 ≠ mpX 4 ∧
    nnX 3 ≠ mqX 4 ∧ mpX 4 ≠ mqX 4 := by decide

lemma dist_ntX_5 : nnX 2 ≠ nnX 3 ∧ nnX 2 ≠ mpX 5 ∧ nnX 2 ≠ mqX 5 ∧ nnX 3 ≠ mpX 5 ∧
    nnX 3 ≠ mqX 5 ∧ mpX 5 ≠ mqX 5 := by decide

/-- The first element of the pair `r`. -/
def p1 : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- The second element of the pair `r`. -/
def p2 : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

lemma tris_ntX : ∀ r : Fin 6, (ntX r).powersetCard 3 =
    {nnX (p1 r), nnX (p2 r), mpX r, mqX r} := by decide +kernel

lemma exists_pair : ∀ a i : Fin 4, a ≠ i → ∃ r : Fin 6, (p1 r = a ∧ p2 r = i) ∨ (p1 r = i ∧ p2 r = a) := by
  decide

lemma sgX_ne_nnX : ∀ i j : Fin 4, sgX i ≠ nnX j := by decide

lemma mpX_ne_nnX : ∀ r : Fin 6, ∀ j : Fin 4, mpX r ≠ nnX j := by decide

lemma mqX_ne_nnX : ∀ r : Fin 6, ∀ j : Fin 4, mqX r ≠ nnX j := by decide


/-- Extraction of the witnesses `n_i` from the conclusion of `local24`. -/
lemma extract_n (pb qb : Fin 6 → Bool) (a : Fin 4)
    (H : (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n0 && ok4 n0 n1 (pb 0) (qb 0) && ok4 n0 n2 (pb 1) (qb 1) && ok4 n0 n3 (pb 2) (qb 2) && ok4 n1 n2 (pb 3) (qb 3) && ok4 n1 n3 (pb 4) (qb 4) && ok4 n2 n3 (pb 5) (qb 5))) = true ∧
    (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n1 && ok4 n0 n1 (pb 0) (qb 0) && ok4 n0 n2 (pb 1) (qb 1) && ok4 n0 n3 (pb 2) (qb 2) && ok4 n1 n2 (pb 3) (qb 3) && ok4 n1 n3 (pb 4) (qb 4) && ok4 n2 n3 (pb 5) (qb 5))) = true ∧
    (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n2 && ok4 n0 n1 (pb 0) (qb 0) && ok4 n0 n2 (pb 1) (qb 1) && ok4 n0 n3 (pb 2) (qb 2) && ok4 n1 n2 (pb 3) (qb 3) && ok4 n1 n3 (pb 4) (qb 4) && ok4 n2 n3 (pb 5) (qb 5))) = true ∧
    (bools.any fun n0 => bools.any fun n1 => bools.any fun n2 => bools.any fun n3 => (n3 && ok4 n0 n1 (pb 0) (qb 0) && ok4 n0 n2 (pb 1) (qb 1) && ok4 n0 n3 (pb 2) (qb 2) && ok4 n1 n2 (pb 3) (qb 3) && ok4 n1 n3 (pb 4) (qb 4) && ok4 n2 n3 (pb 5) (qb 5))) = true) :
    ∃ nb : Fin 4 → Bool, nb a = true ∧
      ok4 (nb 0) (nb 1) (pb 0) (qb 0) = true ∧
      ok4 (nb 0) (nb 2) (pb 1) (qb 1) = true ∧
      ok4 (nb 0) (nb 3) (pb 2) (qb 2) = true ∧
      ok4 (nb 1) (nb 2) (pb 3) (qb 3) = true ∧
      ok4 (nb 1) (nb 3) (pb 4) (qb 4) = true ∧
      ok4 (nb 2) (nb 3) (pb 5) (qb 5) = true := by
  fin_cases a
  · obtain ⟨n0, -, h0⟩ := List.any_eq_true.mp H.1
    obtain ⟨n1, -, h1⟩ := List.any_eq_true.mp h0
    obtain ⟨n2, -, h2⟩ := List.any_eq_true.mp h1
    obtain ⟨n3, -, h3⟩ := List.any_eq_true.mp h2
    simp only [Bool.and_eq_true] at h3
    obtain ⟨⟨⟨⟨⟨⟨hna, o0⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩ := h3
    exact ⟨![n0, n1, n2, n3], by simpa using hna, by simpa using ⟨o0, o1, o2, o3, o4, o5⟩⟩
  · obtain ⟨n0, -, h0⟩ := List.any_eq_true.mp H.2.1
    obtain ⟨n1, -, h1⟩ := List.any_eq_true.mp h0
    obtain ⟨n2, -, h2⟩ := List.any_eq_true.mp h1
    obtain ⟨n3, -, h3⟩ := List.any_eq_true.mp h2
    simp only [Bool.and_eq_true] at h3
    obtain ⟨⟨⟨⟨⟨⟨hna, o0⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩ := h3
    exact ⟨![n0, n1, n2, n3], by simpa using hna, by simpa using ⟨o0, o1, o2, o3, o4, o5⟩⟩
  · obtain ⟨n0, -, h0⟩ := List.any_eq_true.mp H.2.2.1
    obtain ⟨n1, -, h1⟩ := List.any_eq_true.mp h0
    obtain ⟨n2, -, h2⟩ := List.any_eq_true.mp h1
    obtain ⟨n3, -, h3⟩ := List.any_eq_true.mp h2
    simp only [Bool.and_eq_true] at h3
    obtain ⟨⟨⟨⟨⟨⟨hna, o0⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩ := h3
    exact ⟨![n0, n1, n2, n3], by simpa using hna, by simpa using ⟨o0, o1, o2, o3, o4, o5⟩⟩
  · obtain ⟨n0, -, h0⟩ := List.any_eq_true.mp H.2.2.2
    obtain ⟨n1, -, h1⟩ := List.any_eq_true.mp h0
    obtain ⟨n2, -, h2⟩ := List.any_eq_true.mp h1
    obtain ⟨n3, -, h3⟩ := List.any_eq_true.mp h2
    simp only [Bool.and_eq_true] at h3
    obtain ⟨⟨⟨⟨⟨⟨hna, o0⟩, o1⟩, o2⟩, o3⟩, o4⟩, o5⟩ := h3
    exact ⟨![n0, n1, n2, n3], by simpa using hna, by simpa using ⟨o0, o1, o2, o3, o4, o5⟩⟩


section Abstract

variable {V : Type*} [DecidableEq V] (e : Fin 6 ↪ V)

lemma tris_four {X Y1 Y2 Y3 Y4 : Finset (Fin 6)} (h : X.powersetCard 3 = {Y1, Y2, Y3, Y4})
    (g : Finset V) : g ∈ (tx e X).powersetCard 3 ↔
      g = tx e Y1 ∨ g = tx e Y2 ∨ g = tx e Y3 ∨ g = tx e Y4 := by
  rw [mem_tris_tx]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rw [h] at hY
    simp only [mem_insert, mem_singleton] at hY
    rcases hY with rfl | rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨_, by rw [h]; simp, rfl⟩

/-- A closed tetrahedron whose four triangles are `X1, …, X4` has not exactly three of them in the set
(Boolean form). -/
lemma ok4_of_closedTet {A : Finset (Finset V)} {t : Finset V} {X1 X2 X3 X4 : Finset V}
    (hcl : ∀ f ∈ t.powersetCard 3, (∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ A) → f ∈ A)
    (htr : ∀ g, g ∈ t.powersetCard 3 ↔ g = X1 ∨ g = X2 ∨ g = X3 ∨ g = X4) :
    ok4 (decide (X1 ∈ A)) (decide (X2 ∈ A)) (decide (X3 ∈ A)) (decide (X4 ∈ A)) = true := by
  obtain ⟨c1, c2, c3, c4⟩ := closed_four hcl htr
  exact ok4_of_closed _ _ _ _
    (fun hb hc hd => decide_eq_true (c1 (of_decide_eq_true hb) (of_decide_eq_true hc)
      (of_decide_eq_true hd)))
    (fun ha hc hd => decide_eq_true (c2 (of_decide_eq_true ha) (of_decide_eq_true hc)
      (of_decide_eq_true hd)))
    (fun ha hb hd => decide_eq_true (c3 (of_decide_eq_true ha) (of_decide_eq_true hb)
      (of_decide_eq_true hd)))
    (fun ha hb hc => decide_eq_true (c4 (of_decide_eq_true ha) (of_decide_eq_true hb)
      (of_decide_eq_true hc)))

/-- Conversely, a tetrahedron with `ok4` and three triangles in the set has the fourth in it. -/
lemma mem_of_ok4 {A : Finset (Finset V)} {X1 X2 X3 X4 : Finset V}
    (h : ok4 (decide (X1 ∈ A)) (decide (X2 ∈ A)) (decide (X3 ∈ A)) (decide (X4 ∈ A)) = true) :
    (X2 ∈ A → X3 ∈ A → X4 ∈ A → X1 ∈ A) ∧ (X1 ∈ A → X3 ∈ A → X4 ∈ A → X2 ∈ A) ∧
      (X1 ∈ A → X2 ∈ A → X4 ∈ A → X3 ∈ A) ∧ (X1 ∈ A → X2 ∈ A → X3 ∈ A → X4 ∈ A) := by
  by_cases h1 : X1 ∈ A <;> by_cases h2 : X2 ∈ A <;> by_cases h3 : X3 ∈ A <;>
    by_cases h4 : X4 ∈ A <;> simp_all [ok4]


/-- Closedness of a tetrahedron from the four implications, when its four triangles are distinct. -/
lemma closed_of_four {W : Finset (Finset V)} {t : Finset V} {X1 X2 X3 X4 : Finset V}
    (htr : ∀ g, g ∈ t.powersetCard 3 ↔ g = X1 ∨ g = X2 ∨ g = X3 ∨ g = X4)
    (d12 : X1 ≠ X2) (d13 : X1 ≠ X3) (d14 : X1 ≠ X4) (d23 : X2 ≠ X3) (d24 : X2 ≠ X4) (d34 : X3 ≠ X4)
    (c1 : X2 ∈ W → X3 ∈ W → X4 ∈ W → X1 ∈ W) (c2 : X1 ∈ W → X3 ∈ W → X4 ∈ W → X2 ∈ W)
    (c3 : X1 ∈ W → X2 ∈ W → X4 ∈ W → X3 ∈ W) (c4 : X1 ∈ W → X2 ∈ W → X3 ∈ W → X4 ∈ W) :
    ∀ f ∈ t.powersetCard 3, (∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ W) → f ∈ W := by
  intro f hf hothers
  have o1 := fun h => hothers X1 ((htr _).mpr (Or.inl rfl)) h
  have o2 := fun h => hothers X2 ((htr _).mpr (Or.inr (Or.inl rfl))) h
  have o3 := fun h => hothers X3 ((htr _).mpr (Or.inr (Or.inr (Or.inl rfl)))) h
  have o4 := fun h => hothers X4 ((htr _).mpr (Or.inr (Or.inr (Or.inr rfl)))) h
  rcases (htr f).mp hf with rfl | rfl | rfl | rfl
  · exact c1 (o2 d12.symm) (o3 d13.symm) (o4 d14.symm)
  · exact c2 (o1 d12) (o3 d23.symm) (o4 d24.symm)
  · exact c3 (o1 d13) (o2 d23) (o4 d34.symm)
  · exact c4 (o1 d14) (o2 d24) (o3 d34)

open Classical in
/-- **The dichotomy of the 2-4 move.** `P0` are the tetrahedra common to the complexes before and
after the move, `C` the triangles of the complex before it (all of which are also triangles after
it). If `T ⊆ C` does not force `C` by `P0` alone, then it does not force both complexes: not the
complex before (with the tetrahedron `σ`), or not the complex after (with the six new tetrahedra and
the triangle `{p, q, s_a}` added to `T`). -/
theorem forcing_dichotomy24 (P0 C T : Finset (Finset V)) (a : Fin 4)
    (hCt : ∀ t ∈ P0, ∀ g ∈ t.powersetCard 3, g ∈ C)
    (hcom : ∀ i : Fin 4, tx e (tpX i) ∈ P0 ∧ tx e (tqX i) ∈ P0)
    (hNC : ∀ i, tx e (nnX i) ∉ C) (hT : T ⊆ C) (hnot : ¬ ForcesIn P0 C T) :
    ¬ ForcesIn (insert (tx e sig4) P0) C T ∨
      ¬ ForcesIn (P0 ∪ univ.image fun r => tx e (ntX r))
        (C ∪ univ.image fun i => tx e (nnX i)) (insert (tx e (nnX a)) T) := by
  set A : Finset (Finset V) := C.filter (fun f => ForcesIn P0 {f} T) with hA
  have hAC : A ⊆ C := filter_subset _ _
  have hTA : T ⊆ A := fun f hf => mem_filter.mpr ⟨hT hf, .done (by simpa using hf)⟩
  have hAforced : ForcesIn P0 A T := ForcesIn.of_singles fun g hg => (mem_filter.mp hg).2
  have hAcl : ClosedUnder P0 A := fun t ht f hf hothers =>
    mem_filter.mpr ⟨hCt t ht f hf, ForcesIn.of_forced_others ht hf
      fun g hg hne => (mem_filter.mp (hothers g hg hne)).2⟩
  have hCA : ¬ C ⊆ A := fun h => hnot (hAforced.mono_target (fun x hx => mem_union_left _ (h hx)))
  by_cases hfire : ∃ i, tx e (sgX i) ∉ A ∧ ∀ j, j ≠ i → tx e (sgX j) ∈ A
  swap
  · left
    intro hK
    have hcl : ClosedUnder {tx e sig4} A := by
      intro t ht f hf hothers
      rw [mem_singleton] at ht
      subst ht
      rcases (tris_four e tris_sig4 f).mp hf with rfl | rfl | rfl | rfl
      all_goals
        first
        | (by_contra hfA
           exact hfire ⟨_, hfA, fun j hj => hothers _ ((tris_four e tris_sig4 _).mpr (by
             fin_cases j <;> simp)) (fun h => hj (sgX_inj _ _ ((tx_inj e).mp h)))⟩)
    have hcl' : ClosedUnder (insert (tx e sig4) P0) A := by
      rw [insert_eq]; exact closedUnder_union hcl hAcl
    exact hCA (hK.sound hcl' hTA)
  · right
    obtain ⟨i0, hi0, hrest⟩ := hfire
    intro hK'
    set sb : Fin 4 → Bool := fun i => decide (tx e (sgX i) ∈ A) with hsb
    set pb : Fin 6 → Bool := fun r => decide (tx e (mpX r) ∈ A) with hpb
    set qb : Fin 6 → Bool := fun r => decide (tx e (mqX r) ∈ A) with hqb
    have htp0 : ok4 (sb 0) (pb 3) (pb 4) (pb 5) = true :=
      ok4_of_closedTet (hAcl _ (hcom 0).1) (tris_four e tris_tpX_0)
    have htq0 : ok4 (sb 0) (qb 3) (qb 4) (qb 5) = true :=
      ok4_of_closedTet (hAcl _ (hcom 0).2) (tris_four e tris_tqX_0)
    have htp1 : ok4 (sb 1) (pb 1) (pb 2) (pb 5) = true :=
      ok4_of_closedTet (hAcl _ (hcom 1).1) (tris_four e tris_tpX_1)
    have htq1 : ok4 (sb 1) (qb 1) (qb 2) (qb 5) = true :=
      ok4_of_closedTet (hAcl _ (hcom 1).2) (tris_four e tris_tqX_1)
    have htp2 : ok4 (sb 2) (pb 0) (pb 2) (pb 4) = true :=
      ok4_of_closedTet (hAcl _ (hcom 2).1) (tris_four e tris_tpX_2)
    have htq2 : ok4 (sb 2) (qb 0) (qb 2) (qb 4) = true :=
      ok4_of_closedTet (hAcl _ (hcom 2).2) (tris_four e tris_tqX_2)
    have htp3 : ok4 (sb 3) (pb 0) (pb 1) (pb 3) = true :=
      ok4_of_closedTet (hAcl _ (hcom 3).1) (tris_four e tris_tpX_3)
    have htq3 : ok4 (sb 3) (qb 0) (qb 1) (qb 3) = true :=
      ok4_of_closedTet (hAcl _ (hcom 3).2) (tris_four e tris_tqX_3)
    have hs : ∀ j, sb j = decide (j ≠ i0) := by
      intro j
      show decide (tx e (sgX j) ∈ A) = decide (j ≠ i0)
      by_cases hj : j = i0
      · rw [hj]; simp [hi0]
      · simp [hj, hrest j hj]
    have heq3 : eq3 (sb 0) (sb 1) (sb 2) (sb 3) = true := by
      rw [hs 0, hs 1, hs 2, hs 3]
      fin_cases i0 <;> decide
    have key := local24 (sb 0) (sb 1) (sb 2) (sb 3) (pb 0) (pb 1) (pb 2) (pb 3) htp3 (pb 4) htp2 (pb 5) htp0 htp1 (qb 0) (qb 1) (qb 2) (qb 3) htq3 (qb 4) htq2 (qb 5) htq0 htq1 heq3
    obtain ⟨nb, hna, hn0, hn1, hn2, hn3, hn4, hn5⟩ := extract_n pb qb a key
    set W' : Finset (Finset V) :=
      A ∪ (univ.filter fun i : Fin 4 => nb i = true).image (fun i => tx e (nnX i)) with hW'
    have hmemnn : ∀ i, tx e (nnX i) ∈ W' ↔ nb i = true := by
      intro i
      constructor
      · intro h
        rcases mem_union.mp h with h | h
        · exact absurd (hAC h) (hNC i)
        · obtain ⟨j, hj, hji⟩ := mem_image.mp h
          have := nnX_inj _ _ ((tx_inj e).mp hji)
          rw [← this]; exact (mem_filter.mp hj).2
      · intro h
        exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, h⟩))
    have hmemA : ∀ X : Finset (Fin 6), (∀ j, X ≠ nnX j) → (tx e X ∈ W' ↔ tx e X ∈ A) := by
      intro X hX
      constructor
      · intro h
        rcases mem_union.mp h with h | h
        · exact h
        · obtain ⟨j, -, hj⟩ := mem_image.mp h
          exact absurd ((tx_inj e).mp hj).symm (hX j)
      · exact fun h => mem_union_left _ h
    have hdn : ∀ i, decide (tx e (nnX i) ∈ W') = nb i := fun i => by
      cases h : nb i <;> simp [hmemnn, h]
    have hdp : ∀ r, decide (tx e (mpX r) ∈ W') = pb r := fun r =>
      decide_eq_decide.mpr (hmemA _ (mpX_ne_nnX r))
    have hdq : ∀ r, decide (tx e (mqX r) ∈ W') = qb r := fun r =>
      decide_eq_decide.mpr (hmemA _ (mqX_ne_nnX r))
    have hTW : insert (tx e (nnX a)) T ⊆ W' := by
      intro f hf
      rcases mem_insert.mp hf with rfl | hf
      · exact (hmemnn a).mpr hna
      · exact mem_union_left _ (hTA hf)
    have hcl0 : ClosedUnder P0 W' := by
      intro t ht f hf hothers
      refine mem_union_left _ (hAcl t ht f hf fun g hg hne => ?_)
      have hgW := hothers g hg hne
      rcases mem_union.mp hgW with h | h
      · exact h
      · obtain ⟨j, -, hj⟩ := mem_image.mp h
        exact absurd (hj ▸ hCt t ht g hg) (hNC j)
    have hcl1 : ClosedUnder (univ.image fun r => tx e (ntX r)) W' := by
      intro t ht f hf hothers
      obtain ⟨r, -, rfl⟩ := mem_image.mp ht
      fin_cases r
      · have h' : ok4 (decide (tx e (nnX 0) ∈ W')) (decide (tx e (nnX 1) ∈ W'))
            (decide (tx e (mpX 0) ∈ W')) (decide (tx e (mqX 0) ∈ W')) = true := by
          rw [hdn 0, hdn 1, hdp 0, hdq 0]; exact hn0
        obtain ⟨c1, c2, c3, c4⟩ := mem_of_ok4 h'
        have d := dist_ntX_0
        exact closed_of_four (tris_four e tris_ntX_0) ((tx_inj e).not.mpr d.1)
          ((tx_inj e).not.mpr d.2.1) ((tx_inj e).not.mpr d.2.2.1) ((tx_inj e).not.mpr d.2.2.2.1)
          ((tx_inj e).not.mpr d.2.2.2.2.1) ((tx_inj e).not.mpr d.2.2.2.2.2) c1 c2 c3 c4 f hf hothers
      · have h' : ok4 (decide (tx e (nnX 0) ∈ W')) (decide (tx e (nnX 2) ∈ W'))
            (decide (tx e (mpX 1) ∈ W')) (decide (tx e (mqX 1) ∈ W')) = true := by
          rw [hdn 0, hdn 2, hdp 1, hdq 1]; exact hn1
        obtain ⟨c1, c2, c3, c4⟩ := mem_of_ok4 h'
        have d := dist_ntX_1
        exact closed_of_four (tris_four e tris_ntX_1) ((tx_inj e).not.mpr d.1)
          ((tx_inj e).not.mpr d.2.1) ((tx_inj e).not.mpr d.2.2.1) ((tx_inj e).not.mpr d.2.2.2.1)
          ((tx_inj e).not.mpr d.2.2.2.2.1) ((tx_inj e).not.mpr d.2.2.2.2.2) c1 c2 c3 c4 f hf hothers
      · have h' : ok4 (decide (tx e (nnX 0) ∈ W')) (decide (tx e (nnX 3) ∈ W'))
            (decide (tx e (mpX 2) ∈ W')) (decide (tx e (mqX 2) ∈ W')) = true := by
          rw [hdn 0, hdn 3, hdp 2, hdq 2]; exact hn2
        obtain ⟨c1, c2, c3, c4⟩ := mem_of_ok4 h'
        have d := dist_ntX_2
        exact closed_of_four (tris_four e tris_ntX_2) ((tx_inj e).not.mpr d.1)
          ((tx_inj e).not.mpr d.2.1) ((tx_inj e).not.mpr d.2.2.1) ((tx_inj e).not.mpr d.2.2.2.1)
          ((tx_inj e).not.mpr d.2.2.2.2.1) ((tx_inj e).not.mpr d.2.2.2.2.2) c1 c2 c3 c4 f hf hothers
      · have h' : ok4 (decide (tx e (nnX 1) ∈ W')) (decide (tx e (nnX 2) ∈ W'))
            (decide (tx e (mpX 3) ∈ W')) (decide (tx e (mqX 3) ∈ W')) = true := by
          rw [hdn 1, hdn 2, hdp 3, hdq 3]; exact hn3
        obtain ⟨c1, c2, c3, c4⟩ := mem_of_ok4 h'
        have d := dist_ntX_3
        exact closed_of_four (tris_four e tris_ntX_3) ((tx_inj e).not.mpr d.1)
          ((tx_inj e).not.mpr d.2.1) ((tx_inj e).not.mpr d.2.2.1) ((tx_inj e).not.mpr d.2.2.2.1)
          ((tx_inj e).not.mpr d.2.2.2.2.1) ((tx_inj e).not.mpr d.2.2.2.2.2) c1 c2 c3 c4 f hf hothers
      · have h' : ok4 (decide (tx e (nnX 1) ∈ W')) (decide (tx e (nnX 3) ∈ W'))
            (decide (tx e (mpX 4) ∈ W')) (decide (tx e (mqX 4) ∈ W')) = true := by
          rw [hdn 1, hdn 3, hdp 4, hdq 4]; exact hn4
        obtain ⟨c1, c2, c3, c4⟩ := mem_of_ok4 h'
        have d := dist_ntX_4
        exact closed_of_four (tris_four e tris_ntX_4) ((tx_inj e).not.mpr d.1)
          ((tx_inj e).not.mpr d.2.1) ((tx_inj e).not.mpr d.2.2.1) ((tx_inj e).not.mpr d.2.2.2.1)
          ((tx_inj e).not.mpr d.2.2.2.2.1) ((tx_inj e).not.mpr d.2.2.2.2.2) c1 c2 c3 c4 f hf hothers
      · have h' : ok4 (decide (tx e (nnX 2) ∈ W')) (decide (tx e (nnX 3) ∈ W'))
            (decide (tx e (mpX 5) ∈ W')) (decide (tx e (mqX 5) ∈ W')) = true := by
          rw [hdn 2, hdn 3, hdp 5, hdq 5]; exact hn5
        obtain ⟨c1, c2, c3, c4⟩ := mem_of_ok4 h'
        have d := dist_ntX_5
        exact closed_of_four (tris_four e tris_ntX_5) ((tx_inj e).not.mpr d.1)
          ((tx_inj e).not.mpr d.2.1) ((tx_inj e).not.mpr d.2.2.1) ((tx_inj e).not.mpr d.2.2.2.1)
          ((tx_inj e).not.mpr d.2.2.2.2.1) ((tx_inj e).not.mpr d.2.2.2.2.2) c1 c2 c3 c4 f hf hothers
    have hsound := hK'.sound (closedUnder_union hcl0 hcl1) hTW
    refine hCA fun f hf => ?_
    rcases mem_union.mp (hsound (mem_union_left _ hf)) with h | h
    · exact h
    · obtain ⟨j, -, hj⟩ := mem_image.mp h
      exact absurd (hj ▸ hf) (hNC j)

/-- **The easy direction.** If `T` forces `C` using the common tetrahedra alone, then it forces `C`
using the common tetrahedra and `σ`, and it forces `C` together with the four triangles `N_i` using the
common tetrahedra and the six new ones once `N_a` is added to `T`: from `N_a` and the triangles
`P_{ak}`, `Q_{ak}` of `C`, the tetrahedron `{p, q, s_a, s_k}` forces `N_k`. -/
theorem forces24_of_common (P0 C T : Finset (Finset V)) (a : Fin 4)
    (hmix : ∀ r, tx e (mpX r) ∈ C ∧ tx e (mqX r) ∈ C) (hS : ForcesIn P0 C T) :
    ForcesIn (insert (tx e sig4) P0) C T ∧
      ForcesIn (P0 ∪ univ.image fun r => tx e (ntX r))
        (C ∪ univ.image fun i => tx e (nnX i)) (insert (tx e (nnX a)) T) := by
  refine ⟨hS.mono (subset_insert _ _) subset_rfl, ?_⟩
  have h1 : ForcesIn (P0 ∪ univ.image fun r => tx e (ntX r)) C (insert (tx e (nnX a)) T) :=
    hS.mono subset_union_left (subset_insert _ _)
  refine h1.union (ForcesIn.of_singles fun g hg => ?_)
  obtain ⟨i, -, rfl⟩ := mem_image.mp hg
  by_cases hia : i = a
  · subst hia
    exact .done (by simp)
  · obtain ⟨r, hr⟩ := exists_pair a i (Ne.symm hia)
    have ht : tx e (ntX r) ∈ P0 ∪ univ.image fun r => tx e (ntX r) :=
      mem_union_right _ (mem_image_of_mem _ (mem_univ _))
    have htr := tris_four e (tris_ntX r)
    refine h1.of_union (ForcesIn.single ht ((htr _).mpr ?_) fun g hg hne => ?_)
    · rcases hr with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact Or.inr (Or.inl (by rw [h2']))
      · exact Or.inl (by rw [h1'])
    · rcases (htr g).mp hg with rfl | rfl | rfl | rfl
      · rcases hr with ⟨h1', -⟩ | ⟨h1', -⟩
        · exact mem_union_left _ (by rw [h1']; exact mem_insert_self _ _)
        · exact absurd (by rw [h1']) hne
      · rcases hr with ⟨-, h2'⟩ | ⟨-, h2'⟩
        · exact absurd (by rw [h2']) hne
        · exact mem_union_left _ (by rw [h2']; exact mem_insert_self _ _)
      · exact mem_union_right _ (hmix r).1
      · exact mem_union_right _ (hmix r).2

end Abstract

end Lightlike.SpinFoam.Forcing24
