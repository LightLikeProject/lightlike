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

end Lightlike.SpinFoam.Forcing24
