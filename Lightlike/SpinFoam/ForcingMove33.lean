import Lightlike.SpinFoam.ForcingMoves

/-!
# Forcing under the 3-3 move: the finite local lemma

The six vertices of a 3-3 move are `s_0, s_1, s_2` (the triangle `σ` that the move removes) and
`c_0, c_1, c_2` (the triangle `τ` it creates). Of the twenty triangles on them, `σ` and `τ` change;
the other eighteen are *mixed*: `m c p` is `{s_i, s_j, c}` with `{i, j} = {0,1,2} ∖ {p}` and `n x q` is
`{c_k, c_l, x}` with `{k, l} = {0,1,2} ∖ {q}`. The nine tetrahedra `{s_i, s_j, c_k, c_l}` lie in the
complex before and after the move. They are the *common* tetrahedra; the tetrahedron `{s_i, s_j, c_k,
c_l}` for `p, q` has the four triangles `m k p`, `m l p`, `n i q`, `n j q`.

Here the mixed triangles are Boolean variables (`true`: the triangle is in the set), and the lemma
is the finite statement behind the characterization of when forcing survives the 3-3 move: a set
that is closed under the nine common tetrahedra and contains a full row of `m` (all three `m c p`
for one `c`: the three triangles of the tetrahedron `σ ∪ {c}` other than `σ`) and a full row of `n`
has no row of `m` or of `n` with exactly two triangles, so adding `σ` (or `τ`) to it creates no
further forcing in the tetrahedra `σ ∪ {c}` (or `τ ∪ {x}`).
-/

namespace Lightlike.SpinFoam.Forcing33

/-- A tetrahedron with the four triangles `a b c d` (`true`: in the set) forces nothing when it is
not the case that exactly one of them is missing. -/
def ok4 (a b c d : Bool) : Bool := decide (a.toNat + b.toNat + c.toNat + d.toNat ≠ 3)

/-- A row of three triangles has exactly two in the set: then the tetrahedron containing `σ` (or
`τ`) forces the third as soon as `σ` (or `τ`) is in the set. -/
def ne2 (a b c : Bool) : Bool := decide (a.toNat + b.toNat + c.toNat ≠ 2)

/-- The two truth values, for the exhaustive checks. -/
def bools : List Bool := [false, true]

set_option maxRecDepth 100000 in
/-- **The finite local lemma of the 3-3 move.** If the eighteen mixed triangles form a set that is
closed under the nine common tetrahedra (`ok4` for each), contains a full row of `m` and a full row
of `n`, then no row of `m` and no row of `n` has exactly two triangles in the set (`ne2`). The
statement is the Boolean `bools.all …` over the eighteen variables, with the constraint of each
tetrahedron placed as early as possible; the kernel checks it by `decide`. -/
theorem local33 :
    bools.all fun m00 => (bools.all fun m10 => (bools.all fun m20 => (bools.all fun m01 => (bools.all fun m11 => (bools.all fun m21 => (bools.all fun m02 => (bools.all fun m12 => (bools.all fun m22 => (bools.all fun n00 => (bools.all fun n10 => (!(ok4 m12 m22 n00 n10) || (bools.all fun n20 => (!(ok4 m10 m20 n10 n20 && ok4 m11 m21 n00 n20) || (bools.all fun n01 => (bools.all fun n11 => (!(ok4 m02 m22 n01 n11) || (bools.all fun n21 => (!(ok4 m00 m20 n11 n21 && ok4 m01 m21 n01 n21) || (bools.all fun n02 => (bools.all fun n12 => (!(ok4 m02 m12 n02 n12) || (bools.all fun n22 => (!(ok4 m00 m10 n12 n22 && ok4 m01 m11 n02 n22) || (!((m00 && m01 && m02) || (m10 && m11 && m12) || (m20 && m21 && m22)) || !((n00 && n01 && n02) || (n10 && n11 && n12) || (n20 && n21 && n22)) || (ne2 m00 m01 m02 && ne2 m10 m11 m12 && ne2 m20 m21 m22 && ne2 n00 n01 n02 && ne2 n10 n11 n12 && ne2 n20 n21 n22))))))))))))))))))))))))) = true := by decide +kernel

/-- **Wrong-input control for `local33`.** Without a full row of `n`, the conclusion fails. Take
`m 2 p` present for all `p`, `m 1 1` and `m 1 2` present, and nothing else: the nine common
tetrahedra force nothing (`ok4`), there is a full row of `m` and none of `n`, and the row `m 1 *` has
exactly two triangles, so adding `σ` forces `m 1 0`. -/
theorem local33_control :
    ok4 false true false false = true ∧
    ok4 false true false false = true ∧
    ok4 false false false false = true ∧
    ok4 true true false false = true ∧
    ok4 false true false false = true ∧
    ok4 false true false false = true ∧
    ok4 true true false false = true ∧
    ok4 false true false false = true ∧
    ok4 false true false false = true ∧
    ((true && true && true) || (false && true && true) || (false && false && false)) = true ∧
    ((false && false && false) || (false && false && false) || (false && false && false)) = false ∧
    ne2 false true true = false := by decide

end Lightlike.SpinFoam.Forcing33
