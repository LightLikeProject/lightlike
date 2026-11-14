import Lightlike.SpinFoam.SNet
import Lightlike.SpinFoam.Ooguri

/-!
# The 3-3 move of the Ooguri model

The 3-3 Pachner move replaces the three 4-simplices `W ∖ {b}`, `b ∈ B`, around the triangle `A`
by the three 4-simplices `W ∖ {a}`, `a ∈ A`, around the triangle `B`, where `W = A ∪ B` has six
vertices. The Ooguri amplitude is invariant: summed over the spin of the inner triangle and the
virtual spins of the three inner tetrahedra, the products of the three vertex amplitudes agree.

The proof writes each side as a signed network (`SNet`) and reduces it by the steps of `SNet.lean`.
All networks of the move live on six vertices, labelled by positions `Fin 6`, and their faces are
bitmasks of positions, so that every combinatorial hypothesis is checked by `decide`.

## Main results

* `vertexAmp_eq_ev_vnet`: the vertex amplitude of a 4-simplex is the evaluation of its vertex
  network.
* `vertexAmp_erase_eq`: the same for the 4-simplex `W ∖ {φ b}` of a six-vertex set `W` (the image
  of `φ : Fin 6 ↪o V`), with bitmask faces.
* `Move33.lhs_eq_ev_NL`: the local side of the move (sum over the inner triangle and the three
  inner tetrahedra of the three vertex networks) reduces to the network `NL c`.
* `Move33.ev_NL_rev`: `NL c` and `NL c.rev` evaluate to the same function of the boundary spins,
  so the reduced networks of the two sides agree.
* `Move33.inner_eq`: the local identity in terms of the vertex amplitudes of `V`.
* `amplitudeGF_move33`: the gauge-fixed Ooguri state sum is invariant under the 3-3 move, for
  cutoffs large enough on the inner faces of both sides.
* `amplitudeGF_move33_gauge`: the same for a gauge set obeying the gauge rule `IsGauge` and not
  containing the removed triangle; the gauge set obeys the rule after the move too.

## References

- H. Ooguri, *Topological lattice models in four dimensions*, Mod. Phys. Lett. A 7, 2799 (1992),
  arXiv:hep-th/9205090: the model, with 15j vertex amplitudes, and the invariance of its partition
  function under the Alexander moves of the triangulation.
- L. Freidel, D. Louapre, *Diffeomorphisms and spin foam models*, Nucl. Phys. B 662, 279 (2003),
  arXiv:gr-qc/0212001: the residual symmetry behind the divergences of spin foam state sums and
  its gauge fixing, worked out for the Ponzano–Regge model.
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam

open SNet

variable {V : Type*} [LinearOrder V]

/-- **The vertex amplitude is the evaluation of the vertex network** whose triangles and
tetrahedra are those of the 4-simplex. -/
theorem vertexAmp_eq_ev_vnet (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) :
    vertexAmp s hs col = (vnet (fun e => (s.erase (s.orderEmbOfFin hs (vtriP e))).erase
      (s.orderEmbOfFin hs (vtriQ e))) (fun i => s.erase (s.orderEmbOfFin hs i))).ev col := by
  rw [ev_vnet _ _ col (fun p q => col ((s.erase (s.orderEmbOfFin hs p)).erase
    (s.orderEmbOfFin hs q))) (fun i => col (s.erase (s.orderEmbOfFin hs i))) (fun _ => rfl)
    (fun _ => rfl), contrP_σPlus]
  rfl

/-! ## Bitmask faces -/

/-- The vertex positions (in `Fin 6`) of a bitmask. -/
def bits (n : Fin 64) : Finset (Fin 6) := univ.filter fun k => n.val.testBit k

/-- The triangles of the 4-simplex `Fin 6 ∖ {b}` as bitmasks, in the edge order of `vnet`: the
edge `e` is the triangle without the positions `vtriP e` and `vtriQ e` of the 4-simplex. -/
def fcB : Fin 6 → Fin 10 → Fin 64 :=
  ![![52, 28, 56, 44, 22, 50, 38, 26, 14, 42], ![52, 28, 56, 44, 21, 49, 37, 25, 13, 41],
    ![50, 26, 56, 42, 19, 49, 35, 25, 11, 41], ![50, 22, 52, 38, 19, 49, 35, 21, 7, 37],
    ![42, 14, 44, 38, 11, 41, 35, 13, 7, 37], ![26, 14, 28, 22, 11, 25, 19, 13, 7, 21]]

/-- The tetrahedra of the 4-simplex `Fin 6 ∖ {b}` as bitmasks: node `i` of `vnet` is the
tetrahedron without the position `i` of the 4-simplex. -/
def ttB : Fin 6 → Fin 5 → Fin 64 :=
  ![![60, 58, 54, 46, 30], ![60, 57, 53, 45, 29], ![58, 57, 51, 43, 27], ![54, 53, 51, 39, 23],
    ![46, 45, 43, 39, 15], ![30, 29, 27, 23, 15]]

lemma bits_fcB (b : Fin 6) (e : Fin 10) :
    bits (fcB b e) = ((univ.erase b).erase (b.succAbove (vtriP e))).erase (b.succAbove (vtriQ e)) := by
  revert b e; decide

lemma bits_ttB (b : Fin 6) (i : Fin 5) : bits (ttB b i) = (univ.erase b).erase (b.succAbove i) := by
  revert b i; decide

variable (φ : Fin 6 ↪o V)

/-- The colouring of the bitmask faces induced by a colouring `col` of the faces of `V`, through
the positions `φ`. -/
def bcol (col : Finset V → ℕ) (n : Fin 64) : ℕ := col ((bits n).map φ.toEmbedding)

lemma orderEmbOfFin_erase_map (b : Fin 6) (h : #((univ.map φ.toEmbedding).erase (φ b)) = 5)
    (j : Fin 5) : ((univ.map φ.toEmbedding).erase (φ b)).orderEmbOfFin h j = φ (b.succAbove j) := by
  have := Finset.orderEmbOfFin_unique h (f := fun j => φ (b.succAbove j)) (fun x => by
    simp [Fin.succAbove_ne]) (φ.strictMono.comp (Fin.strictMono_succAbove b))
  exact (congrFun this j).symm

/-- **The vertex amplitude of `W ∖ {φ b}` with bitmask faces**, for the six-vertex set `W` given
by `φ`. -/
theorem vertexAmp_erase_eq (b : Fin 6) (hs : #((univ.map φ.toEmbedding).erase (φ b)) = 5)
    (col : Finset V → ℕ) :
    vertexAmp ((univ.map φ.toEmbedding).erase (φ b)) hs col =
      (vnet (fcB b) (ttB b)).ev (bcol φ col) := by
  set s := (univ.map φ.toEmbedding).erase (φ b)
  unfold vertexAmp
  rw [ev_vnet (fcB b) (ttB b) (bcol φ col) (fun p q => col ((s.erase (s.orderEmbOfFin hs p)).erase
    (s.orderEmbOfFin hs q))) (fun i => col (s.erase (s.orderEmbOfFin hs i))), contrP_σPlus]
  · intro e
    simp only [bcol, bits_fcB, s, orderEmbOfFin_erase_map, map_erase]
    rfl
  · intro i
    simp only [bcol, bits_ttB, s, orderEmbOfFin_erase_map, map_erase]
    rfl

/-! ## The chain of steps

Case `c : Fin 20` is the 3-3 move with `B = trip c` (the triple of positions of the removed
vertices, in lexicographic order) and `A` its complement, which is `trip c.rev`. The left side is
the union `U c` of the vertex networks of the 4-simplices `Fin 6 ∖ {b}`, `b ∈ B`, as blocks
`0, 1, 2`. The inner tetrahedron `k` is `A ∪ {b_k}` (bitmask `tmT c k`); it is the tetrahedron of
node `nd c k' k''` of block `k'` for `{k, k', k''} = {0, 1, 2}`.

* Step 1 glues the two nodes of tetrahedron `0` through block `1`, step 2 those of tetrahedron `1`
  through block `0`, each followed by eliminating the four new constraints.
* Step 3 flips a node (and adds a parity) so that the two nodes of tetrahedron `2` read the edge of
  `A` alike, closes the strand of `A`, and eliminates the constraints. The result is `NL c`.
* A gauge transformation `NG c` of `NL c` (node flips `gNT c`, variable flips `gET c`, parities
  `gPT c`) is a relabelling of `NL c.rev`.
-/

namespace Move33

/-- Edges of a union of three vertex networks. -/
abbrev E3 := Fin 3 × Fin 10

/-- Nodes of a union of three vertex networks. -/
abbrev N3 := Fin 3 × Fin 5

/-- The triples of positions in `Fin 6`, in lexicographic order; `trip c.rev` is the complement
of `trip c`. -/
def trip : Fin 20 → Fin 3 → Fin 6 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 1, 4], ![0, 1, 5], ![0, 2, 3], ![0, 2, 4], ![0, 2, 5], ![0, 3, 4],
    ![0, 3, 5], ![0, 4, 5], ![1, 2, 3], ![1, 2, 4], ![1, 2, 5], ![1, 3, 4], ![1, 3, 5], ![1, 4, 5],
    ![2, 3, 4], ![2, 3, 5], ![2, 4, 5], ![3, 4, 5]]

/-- `posT b x`: the node of the vertex network of `Fin 6 ∖ {b}` opposite the position `x ≠ b`
(`0` for `x = b`). -/
def posT : Fin 6 → Fin 6 → Fin 5 :=
  ![![0, 0, 1, 2, 3, 4], ![0, 0, 1, 2, 3, 4], ![0, 1, 0, 2, 3, 4], ![0, 1, 2, 0, 3, 4],
    ![0, 1, 2, 3, 0, 4], ![0, 1, 2, 3, 4, 0]]

/-- The inner triangle `A` of case `c`, as a bitmask. -/
def fAT : Fin 20 → Fin 64 :=
  ![56, 52, 44, 28, 50, 42, 26, 38, 22, 14, 49, 41, 25, 37, 21, 13, 35, 19, 11, 7]

/-- The inner tetrahedra `A ∪ {b_k}` of case `c`, as bitmasks. -/
def tmT : Fin 20 → Fin 3 → Fin 64 :=
  ![![57, 58, 60], ![53, 54, 60], ![45, 46, 60], ![29, 30, 60], ![51, 54, 58], ![43, 46, 58],
    ![27, 30, 58], ![39, 46, 54], ![23, 30, 54], ![15, 30, 46], ![51, 53, 57], ![43, 45, 57],
    ![27, 29, 57], ![39, 45, 53], ![23, 29, 53], ![15, 29, 45], ![39, 43, 51], ![23, 27, 51],
    ![15, 27, 43], ![15, 23, 39]]

/-- The four triangles of the inner tetrahedron `k` of case `c`, in the leg order of its nodes
(leg `l` misses the `l`-th vertex of the tetrahedron). -/
def lfT : Fin 20 → Fin 3 → Fin 4 → Fin 64 :=
  ![![![56, 49, 41, 25], ![56, 50, 42, 26], ![56, 52, 44, 28]],
    ![![52, 49, 37, 21], ![52, 50, 38, 22], ![56, 52, 44, 28]],
    ![![44, 41, 37, 13], ![44, 42, 38, 14], ![56, 52, 44, 28]],
    ![![28, 25, 21, 13], ![28, 26, 22, 14], ![56, 52, 44, 28]],
    ![![50, 49, 35, 19], ![52, 50, 38, 22], ![56, 50, 42, 26]],
    ![![42, 41, 35, 11], ![44, 42, 38, 14], ![56, 50, 42, 26]],
    ![![26, 25, 19, 11], ![28, 26, 22, 14], ![56, 50, 42, 26]],
    ![![38, 37, 35, 7], ![44, 42, 38, 14], ![52, 50, 38, 22]],
    ![![22, 21, 19, 7], ![28, 26, 22, 14], ![52, 50, 38, 22]],
    ![![14, 13, 11, 7], ![28, 26, 22, 14], ![44, 42, 38, 14]],
    ![![50, 49, 35, 19], ![52, 49, 37, 21], ![56, 49, 41, 25]],
    ![![42, 41, 35, 11], ![44, 41, 37, 13], ![56, 49, 41, 25]],
    ![![26, 25, 19, 11], ![28, 25, 21, 13], ![56, 49, 41, 25]],
    ![![38, 37, 35, 7], ![44, 41, 37, 13], ![52, 49, 37, 21]],
    ![![22, 21, 19, 7], ![28, 25, 21, 13], ![52, 49, 37, 21]],
    ![![14, 13, 11, 7], ![28, 25, 21, 13], ![44, 41, 37, 13]],
    ![![38, 37, 35, 7], ![42, 41, 35, 11], ![50, 49, 35, 19]],
    ![![22, 21, 19, 7], ![26, 25, 19, 11], ![50, 49, 35, 19]],
    ![![14, 13, 11, 7], ![26, 25, 19, 11], ![42, 41, 35, 11]],
    ![![14, 13, 11, 7], ![22, 21, 19, 7], ![38, 37, 35, 7]]]

/-- The leg of the inner tetrahedron `k` of case `c` on the inner triangle `A`. -/
def lpT : Fin 20 → Fin 3 → Fin 4 :=
  ![![0, 0, 0], ![0, 0, 1], ![0, 0, 2], ![0, 0, 3], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3], ![0, 2, 2],
    ![0, 2, 3], ![0, 3, 3], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 2], ![1, 2, 3], ![1, 3, 3],
    ![2, 2, 2], ![2, 2, 3], ![2, 3, 3], ![3, 3, 3]]

/-- The three boundary triangles of the inner tetrahedron `k` of case `c` (those other than
`A`). -/
def triT (c : Fin 20) (k : Fin 3) (i : Fin 3) : Fin 64 := lfT c k ((lpT c k).succAbove i)

/-- Whether step 3 of case `c` needs a parity to make the count of `A` in the constant sign
even. -/
def parT : Fin 20 → Bool :=
  ![false, false, false, false, true, true, true, false, false, true, true, true, true, false,
    false, true, false, false, true, true]

/-- The node flips of the gauge transformation of case `c`. -/
def gNT : Fin 20 → List N3 :=
  ![[(1, 4), (0, 4), (2, 3), (2, 2)], [(2, 4), (1, 3), (0, 3), (1, 1), (0, 1)],
    [(1, 4), (0, 4), (2, 3), (2, 2)], [(2, 3), (2, 2), (1, 3), (0, 3)],
    [(1, 4), (0, 4), (2, 3), (2, 1)], [(1, 4), (0, 4), (2, 3), (2, 1)],
    [(2, 3), (2, 1), (1, 3), (0, 3)], [(1, 4), (0, 4), (2, 2), (2, 1)],
    [(2, 2), (2, 1), (1, 3), (0, 3)], [(2, 2), (2, 1), (1, 3), (0, 2)],
    [(1, 4), (0, 4), (2, 3), (2, 0)], [(1, 4), (0, 4), (2, 3), (2, 0)],
    [(2, 3), (2, 0), (1, 3), (0, 3)], [(1, 4), (0, 4), (2, 2), (2, 0)],
    [(2, 2), (2, 0), (1, 3), (0, 3)], [(2, 2), (2, 0), (1, 3), (0, 2)],
    [(1, 4), (0, 4), (2, 1), (2, 0)], [(2, 1), (2, 0), (1, 3), (0, 3)],
    [(2, 3), (1, 1), (1, 0), (0, 1), (0, 0)], [(2, 1), (2, 0), (1, 2), (0, 2)]]

/-- The variable flips of the gauge transformation of case `c`. -/
def gET : Fin 20 → List E3 :=
  ![[(2, 8), (2, 4), (0, 1), (2, 6), (0, 3), (1, 5), (0, 5)],
    [(1, 8), (0, 8), (1, 7), (0, 7), (1, 9), (0, 9), (1, 5), (0, 5)],
    [(2, 8), (2, 4), (0, 1), (0, 2)], [(1, 8), (0, 8), (2, 6), (0, 2)],
    [(2, 8), (1, 4), (2, 7), (0, 4), (1, 6), (2, 9), (0, 6)], [(2, 8), (2, 7), (0, 5)],
    [(1, 8), (0, 8), (2, 9), (0, 9), (0, 5)], [(2, 4), (2, 7), (0, 4), (2, 5), (1, 5)],
    [(1, 8), (0, 8), (1, 5)], [(1, 8), (2, 6), (2, 9), (0, 4), (1, 6), (1, 9), (0, 6)],
    [(2, 8), (1, 4), (0, 4), (2, 1), (1, 6), (0, 6), (2, 3)], [(2, 8), (2, 1), (0, 5)],
    [(1, 8), (0, 8), (2, 3), (0, 9), (0, 5)], [(2, 4), (2, 1), (0, 4), (2, 0), (1, 0)],
    [(1, 8), (0, 8), (1, 0)], [(1, 8), (2, 6), (0, 4), (2, 3), (1, 6), (0, 6), (1, 3)],
    [(2, 7), (2, 1), (0, 4), (0, 2)], [(1, 8), (0, 8), (2, 2), (0, 2)],
    [(1, 7), (1, 1), (0, 7), (0, 1), (0, 9), (0, 3), (0, 5), (0, 0)],
    [(1, 4), (0, 4), (2, 2), (0, 6), (1, 2), (0, 5), (0, 0)]]

/-- The parities of the gauge transformation of case `c`. -/
def gPT : Fin 20 → List N3 :=
  ![[(2, 4), (2, 3), (1, 3), (0, 3)], [(2, 4)], [(2, 4), (1, 1), (0, 1)], [(1, 1), (0, 1)],
    [(1, 3), (0, 3)], [(2, 4)], [], [(2, 4), (1, 2), (1, 1), (0, 1)], [(1, 2), (1, 1), (0, 1)],
    [(2, 3), (0, 1)], [(1, 3), (0, 3), (0, 0)], [(2, 4), (0, 0)], [(0, 0)],
    [(1, 4), (0, 4), (2, 2), (2, 0)], [(1, 2), (1, 0), (0, 1), (0, 0)], [(2, 3), (0, 1), (0, 0)],
    [(2, 4), (1, 1), (1, 0)], [(1, 1), (1, 0)], [(1, 1), (1, 0), (0, 1), (0, 0)],
    [(1, 2), (0, 1), (0, 0)]]

/-- The left side of case `c`: the vertex networks of `Fin 6 ∖ {b}`, `b ∈ trip c`, as blocks. -/
def U (c : Fin 20) : SNet (Fin 64) E3 N3 := union fun k => vnet (fcB (trip c k)) (ttB (trip c k))

/-- The node of block `k` opposite the vertex of block `k'`: its tetrahedron misses `b_k` and
`b_k'`. -/
def nd (c : Fin 20) (k k' : Fin 3) : N3 := (k, posT (trip c k) (trip c k'))

/-- Step 1: gluing the two nodes of the inner tetrahedron `0`. -/
def G1 (c : Fin 20) : SNet (Fin 64) E3 N3 := (U c).glue (nd c 1 2) (nd c 2 1)

/-- Step 1 with its constraints eliminated. -/
def N1 (c : Fin 20) : SNet (Fin 64) E3 N3 := elimN 4 (G1 c)

/-- Step 2: gluing the two nodes of the inner tetrahedron `1`. -/
def G2 (c : Fin 20) : SNet (Fin 64) E3 N3 := (N1 c).glue (nd c 0 2) (nd c 2 0)

/-- Step 2 with its constraints eliminated. -/
def N2 (c : Fin 20) : SNet (Fin 64) E3 N3 := elimN 4 (G2 c)

/-- The preparation of step 3: a node flip, and a parity where `parT c` says so. -/
def P3 (c : Fin 20) : SNet (Fin 64) E3 N3 :=
  addParities (flipNodes (N2 c) [nd c 1 0]) (if parT c then [nd c 0 1] else [])

/-- Step 3: closing the strand of the inner triangle `A`. -/
def L3 (c : Fin 20) : SNet (Fin 64) E3 N3 := (P3 c).loop (nd c 0 1) (nd c 1 0) (lpT c 2)

/-- **The reduced left side** of case `c`: step 3 with its constraints eliminated. -/
def NL (c : Fin 20) : SNet (Fin 64) E3 N3 := elimN 4 (L3 c)

/-- The gauge transformation of `NL c` that matches `NL c.rev`. -/
def NG (c : Fin 20) : SNet (Fin 64) E3 N3 :=
  addParities (flipVars (flipNodes (NL c) (gNT c)) (gET c)) (gPT c)

/-! ### Checked steps

The hypotheses of each step are bundled as a decidable proposition. The kernel decides quantifiers
over `E3` and `N3` much faster through the lists `allE`, `allN` than through `Fintype`, hence the
local instances. -/

/-- All edges of `E3`, as a list. -/
def allE : List E3 := (List.finRange 3).flatMap fun a => (List.finRange 10).map fun b => (a, b)

/-- All nodes of `N3`, as a list. -/
def allN : List N3 := (List.finRange 3).flatMap fun a => (List.finRange 5).map fun b => (a, b)

lemma mem_allE (e : E3) : e ∈ allE := by
  obtain ⟨a, b⟩ := e
  simp [allE]

lemma mem_allN (n : N3) : n ∈ allN := by
  obtain ⟨a, b⟩ := n
  simp [allN]

/-- Deciding a statement for all edges through `allE`. -/
local instance (priority := high) decForallE3 (P : E3 → Prop) [DecidablePred P] :
    Decidable (∀ e, P e) :=
  decidable_of_iff (allE.all fun e => decide (P e)) (by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h e => h e (mem_allE e), fun h e _ => h e⟩)

/-- Deciding a statement for all nodes through `allN`. -/
local instance (priority := high) decForallN3 (P : N3 → Prop) [DecidablePred P] :
    Decidable (∀ n, P n) :=
  decidable_of_iff (allN.all fun n => decide (P n)) (by
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h n => h n (mem_allN n), fun h n _ => h n⟩)

/-- The hypotheses of `ev_glue` for gluing the node `n₁` of an untouched block `b` (still the
vertex network of `Fin 6 ∖ {v}`) to the node `n₂` along the tetrahedron `t`. -/
abbrev GlueOK (S : SNet (Fin 64) E3 N3) (b : Fin 3) (v : Fin 6) (n₁ n₂ : N3) (t : Fin 64) :
    Prop :=
  n₁.1 = b ∧ n₂.1 ≠ b ∧ (∀ e, S.face (b, e) = fcB v e) ∧ (∀ e, S.kap (b, e) = true) ∧
  (∀ e, S.eLive (b, e) = true) ∧ (∀ n, S.tet (b, n) = ttB v n) ∧ (∀ n, S.nLive (b, n) = true) ∧
  (∀ n l, S.leg (b, n) l = (b, vleg n l)) ∧ (∀ n l, S.neg (b, n) l = vneg n l) ∧
  (∀ n, S.nLive n = true → ∀ l, ((S.leg n l).1 = b ↔ n.1 = b)) ∧
  (∀ c ∈ S.cons, c.1.1 ≠ b ∧ c.2.1.1 ≠ b) ∧
  (∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true) ∧ S.nLive n₂ = true ∧
  S.tet n₁ = t ∧ S.tet n₂ = t ∧ (∀ l, S.face (S.leg n₂ l) = S.face (S.leg n₁ l)) ∧
  (∀ e, S.eLive e = true → S.face e ≠ t) ∧
  (∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → S.tet n ≠ t) ∧ t ∉ S.cst

set_option synthInstance.maxSize 2048 in
/-- `GlueOK` is decidable. -/
instance (S : SNet (Fin 64) E3 N3) (b : Fin 3) (v : Fin 6) (n₁ n₂ : N3) (t : Fin 64) :
    Decidable (GlueOK S b v n₁ n₂ t) := by
  unfold GlueOK; infer_instance

/-- **Gluing through an untouched block**, with the hypotheses checked as `GlueOK`. -/
theorem ev_glue_of {S : SNet (Fin 64) E3 N3} {b : Fin 3} {v : Fin 6} {n₁ n₂ : N3} {t : Fin 64}
    (h : GlueOK S b v n₁ n₂ t) (col : Fin 64 → ℕ) (cut : ℕ)
    (hcut : ∑ l, col (S.face (S.leg n₁ l)) ≤ cut) :
    ∑ k ∈ range (cut + 1), S.ev (Function.update col t k) = (S.glue n₁ n₂).ev col := by
  obtain ⟨hb1, hb2, hface, hkap, hlive, htet, hnLive, hleg, hneg, hblk, hcons, hlegs, hn2, ht1,
    ht2, hf, hte, htn, htc⟩ := h
  obtain ⟨b', i⟩ := n₁
  dsimp only at hb1
  subst hb1
  rw [Fin.sum_univ_four] at hcut
  have htc' : t ∉ S.cst := htc
  have hb1' : (fun q : N3 => decide (q.1 = b')) (b', i) = true := by simp
  have hb2' : (fun q : N3 => decide (q.1 = b')) n₂ = false := by simpa using hb2
  have hc : ∀ c ∈ S.cons, (fun p : E3 => decide (p.1 = b')) c.1 = false ∧
      (fun p : E3 => decide (p.1 = b')) c.2.1 = false :=
    fun c hc => ⟨decide_eq_false (hcons c hc).1, decide_eq_false (hcons c hc).2⟩
  have hbl : ∀ n, S.nLive n = true → ∀ l,
      (fun p : E3 => decide (p.1 = b')) (S.leg n l) = (fun q : N3 => decide (q.1 = b')) n :=
    fun n hn l => decide_eq_decide.mpr (hblk n hn l)
  exact ev_glue (S := S) (col := col) (n₁ := (b', i)) (n₂ := n₂) (t := t)
    (fun p => decide (p.1 = b')) (fun q => decide (q.1 = b')) cut hb1' hb2' hbl hc hlegs
    (hnLive i) hn2 ht1 ht2 hf hte htn htc' (by omega)
    (isInv_rem_block S (fcB v) (ttB v) col b' i hface hkap hlive htet hnLive hleg hneg)

/-- The hypotheses of `ev_loop` for closing the strand of leg `lA` between `n₁` and `n₂`, with
tetrahedron `t` and strand face `fA`. -/
abbrev LoopOK (S : SNet (Fin 64) E3 N3) (n₁ n₂ : N3) (lA : Fin 4) (t fA : Fin 64) : Prop :=
  n₁ ≠ n₂ ∧ (∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true) ∧
  S.nLive n₁ = true ∧ S.nLive n₂ = true ∧ S.tet n₁ = t ∧ S.tet n₂ = t ∧
  (∀ l, S.face (S.leg n₂ l) = S.face (S.leg n₁ l)) ∧ S.leg n₂ lA = S.leg n₁ lA ∧
  S.face (S.leg n₁ lA) = fA ∧ S.neg n₂ lA = S.neg n₁ lA ∧ S.kap (S.leg n₁ lA) = false ∧
  (∀ l, l ≠ lA → S.leg n₁ l ≠ S.leg n₁ lA ∧ S.leg n₂ l ≠ S.leg n₁ lA) ∧
  (∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → ∀ l, S.leg n l ≠ S.leg n₁ lA) ∧
  (∀ c ∈ S.cons, c.1 ≠ S.leg n₁ lA ∧ c.2.1 ≠ S.leg n₁ lA) ∧ fA ≠ t ∧
  (∀ e, S.eLive e = true → e ≠ S.leg n₁ lA → S.face e ≠ t ∧ S.face e ≠ fA) ∧
  (∀ n, S.nLive n = true → n ≠ n₁ → n ≠ n₂ → S.tet n ≠ t ∧ S.tet n ≠ fA) ∧
  t ∉ S.cst ∧ S.cst.count fA % 2 = 0

set_option synthInstance.maxSize 2048 in
/-- `LoopOK` is decidable. -/
instance (S : SNet (Fin 64) E3 N3) (n₁ n₂ : N3) (lA : Fin 4) (t fA : Fin 64) :
    Decidable (LoopOK S n₁ n₂ lA t fA) := by
  unfold LoopOK; infer_instance

/-- **Closing a strand**, with the hypotheses checked as `LoopOK`. -/
theorem ev_loop_of {S : SNet (Fin 64) E3 N3} {n₁ n₂ : N3} {lA : Fin 4} {t fA : Fin 64}
    (h : LoopOK S n₁ n₂ lA t fA) (col : Fin 64 → ℕ) (cutA cut : ℕ)
    (hA : ∑ l ∈ univ.erase lA, col (S.face (S.leg n₁ l)) ≤ cutA)
    (hk : cutA + ∑ l ∈ univ.erase lA, col (S.face (S.leg n₁ l)) ≤ cut) :
    ∑ jA ∈ range (cutA + 1), ((jA : ℝ) + 1) * ∑ k ∈ range (cut + 1),
      S.ev (Function.update (Function.update col fA jA) t k) = (S.loop n₁ n₂ lA).ev col := by
  obtain ⟨h12, hlegs, hn1, hn2, ht1, ht2, hf, he2, hfA, hneg, hkap, hlA, hAo, hAc, hAt, hte, htn,
    htc, hcA⟩ := h
  have htc' : t ∉ S.cst := htc
  have hcA' : Even (S.cst.count fA) := Nat.even_iff.mpr hcA
  exact ev_loop (S := S) (col := col) (n₁ := n₁) (n₂ := n₂) (t := t) (fA := fA) lA cutA cut h12
    hlegs hn1 hn2 ht1 ht2 hf rfl he2 hfA hneg hkap hlA hAo hAc hAt hte htn htc' hcA' hA hk

/-- The first live edge of `S` on the face `f` (junk `(0, 0)` if there is none). -/
def findE (S : SNet (Fin 64) E3 N3) (f : Fin 64) : E3 :=
  (allE.find? fun e => S.eLive e && decide (S.face e = f)).getD (0, 0)

/-- The first live node of `S` on the tetrahedron `t` (junk `(0, 0)` if there is none). -/
def findN (S : SNet (Fin 64) E3 N3) (t : Fin 64) : N3 :=
  (allN.find? fun n => S.nLive n && decide (S.tet n = t)).getD (0, 0)

/-- The edge of `S'` on the face of the edge `e` of `S`. -/
def relE (S S' : SNet (Fin 64) E3 N3) (e : E3) : E3 := findE S' (S.face e)

/-- The node of `S'` on the tetrahedron of the node `n` of `S`. -/
def relN (S S' : SNet (Fin 64) E3 N3) (n : N3) : N3 := findN S' (S.tet n)

/-- The hypotheses of `ev_relabel` for the relabelling of `S` and `S'` by faces and
tetrahedra. -/
abbrev RelOK (S S' : SNet (Fin 64) E3 N3) : Prop :=
  (∀ e, S.eLive e = true → S'.eLive (relE S S' e) = true ∧ relE S' S (relE S S' e) = e) ∧
  (∀ e', S'.eLive e' = true → S.eLive (relE S' S e') = true ∧ relE S S' (relE S' S e') = e') ∧
  (∀ n, S.nLive n = true → S'.nLive (relN S S' n) = true ∧ relN S' S (relN S S' n) = n) ∧
  (∀ n', S'.nLive n' = true → S.nLive (relN S' S n') = true ∧ relN S S' (relN S' S n') = n') ∧
  (∀ e, S.eLive e = true → S'.face (relE S S' e) = S.face e ∧ S'.kap (relE S S' e) = S.kap e) ∧
  (∀ n, S.nLive n = true → S'.tet (relN S S' n) = S.tet n ∧
    ∀ l, S'.leg (relN S S' n) l = relE S S' (S.leg n l) ∧ S'.neg (relN S S' n) l = S.neg n l) ∧
  (∀ n, S.nLive n = true → ∀ l, S.eLive (S.leg n l) = true) ∧ S.cons = [] ∧ S'.cons = [] ∧
  (∀ f ∈ S.cst ++ S'.cst, S.cst.count f % 2 = S'.cst.count f % 2)

set_option synthInstance.maxSize 2048 in
/-- `RelOK` is decidable. -/
instance (S S' : SNet (Fin 64) E3 N3) : Decidable (RelOK S S') := by
  unfold RelOK; infer_instance

/-- **Relabelling by faces**, with the hypotheses checked as `RelOK`. -/
theorem ev_rel_of {S S' : SNet (Fin 64) E3 N3} (h : RelOK S S') (col : Fin 64 → ℕ) :
    S.ev col = S'.ev col := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ev_relabel S' (relE S S') (relE S' S) (relN S S') (relN S' S) h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10

/-! ### The checks, by `decide` -/

set_option maxRecDepth 100000 in
lemma chk_G1 : ∀ c : Fin 20,
    GlueOK (U c) 1 (trip c 1) (nd c 1 2) (nd c 2 1) (tmT c 0) ∧ elimOK 4 (G1 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_G2 : ∀ c : Fin 20,
    GlueOK (N1 c) 0 (trip c 0) (nd c 0 2) (nd c 2 0) (tmT c 1) ∧ elimOK 4 (G2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P3 : ∀ c : Fin 20, flipNodesOK (N2 c) [nd c 1 0] = true ∧
    addParitiesOK (flipNodes (N2 c) [nd c 1 0]) (if parT c then [nd c 0 1] else []) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L3 : ∀ c : Fin 20,
    LoopOK (P3 c) (nd c 0 1) (nd c 1 0) (lpT c 2) (tmT c 2) (fAT c) ∧ elimOK 4 (L3 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_legs : ∀ (c : Fin 20) (l : Fin 4), (U c).face ((U c).leg (nd c 1 2) l) = lfT c 0 l ∧
    (N1 c).face ((N1 c).leg (nd c 0 2) l) = lfT c 1 l ∧
    (P3 c).face ((P3 c).leg (nd c 0 1) l) = lfT c 2 l := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_gauge : ∀ c : Fin 20, flipNodesOK (NL c) (gNT c) = true ∧
    addParitiesOK (flipVars (flipNodes (NL c) (gNT c)) (gET c)) (gPT c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_rel : ∀ c : Fin 20, RelOK (NG c) (NL c.rev) := by
  decide +kernel

lemma lfT_lpT : ∀ c k, lfT c k (lpT c k) = fAT c := by decide

lemma triT_ne_fAT : ∀ c k i, triT c k i ≠ fAT c := by decide

lemma triT_ne_tmT : ∀ c k i j, triT c k i ≠ tmT c j := by decide

lemma fAT_ne_tmT : ∀ c j, fAT c ≠ tmT c j := by decide


/-- The four triangles of an inner tetrahedron: `A` and the three boundary triangles. -/
lemma sum_lfT (c : Fin 20) (k : Fin 3) (g : Fin 64 → ℕ) :
    ∑ l, g (lfT c k l) = g (fAT c) + ∑ i, g (triT c k i) := by
  rw [Fin.sum_univ_succAbove _ (lpT c k), lfT_lpT]
  rfl

/-- The three triangles of an inner tetrahedron other than `A`. -/
lemma sum_erase_lfT (c : Fin 20) (k : Fin 3) (g : Fin 64 → ℕ) :
    ∑ l ∈ univ.erase (lpT c k), g (lfT c k l) = ∑ i, g (triT c k i) := by
  have h := add_sum_erase univ (fun l => g (lfT c k l)) (mem_univ (lpT c k))
  rw [Fin.sum_univ_succAbove _ (lpT c k)] at h
  exact Nat.add_left_cancel h

/-- **The left side of case `c` reduces to `NL c`**: summed over the colour `jA` of the inner
triangle (weight `jA + 1`) and the colours of the three inner tetrahedra, the union of the three
vertex networks evaluates to the reduced network, once the cutoffs exceed the triangle
inequalities. -/
theorem lhs_eq_ev_NL (c : Fin 20) (col : Fin 64 → ℕ) (cutA cut₁ cut₂ cut₃ : ℕ)
    (h₁ : cutA + ∑ i, col (triT c 0 i) ≤ cut₁) (h₂ : cutA + ∑ i, col (triT c 1 i) ≤ cut₂)
    (hA : ∑ i, col (triT c 2 i) ≤ cutA) (h₃ : cutA + ∑ i, col (triT c 2 i) ≤ cut₃) :
    ∑ jA ∈ range (cutA + 1), ((jA : ℝ) + 1) * ∑ k₃ ∈ range (cut₃ + 1), ∑ k₂ ∈ range (cut₂ + 1),
      ∑ k₁ ∈ range (cut₁ + 1), (U c).ev (Function.update (Function.update (Function.update
        (Function.update col (fAT c) jA) (tmT c 2) k₃) (tmT c 1) k₂) (tmT c 0) k₁) =
      (NL c).ev col := by
  have e0 : ∀ l, (U c).face ((U c).leg (nd c 1 2) l) = lfT c 0 l := fun l => (chk_legs c l).1
  have e1 : ∀ l, (N1 c).face ((N1 c).leg (nd c 0 2) l) = lfT c 1 l := fun l => (chk_legs c l).2.1
  have e2 : ∀ l, (P3 c).face ((P3 c).leg (nd c 0 1) l) = lfT c 2 l := fun l => (chk_legs c l).2.2
  have hP3 : ∀ col', (P3 c).ev col' = (N2 c).ev col' := fun col' => by
    rw [P3, ev_addParities col' _ _ (chk_P3 c).2, ev_flipNodes col' _ _ (chk_P3 c).1]
  have hA' : ∑ l ∈ univ.erase (lpT c 2), col ((P3 c).face ((P3 c).leg (nd c 0 1) l)) ≤ cutA := by
    simp only [e2, sum_erase_lfT]
    exact hA
  have h₃' : cutA + ∑ l ∈ univ.erase (lpT c 2), col ((P3 c).face ((P3 c).leg (nd c 0 1) l)) ≤
      cut₃ := by
    simp only [e2, sum_erase_lfT]
    exact h₃
  rw [NL, ev_elimN col 4 _ (chk_L3 c).2, L3, ← ev_loop_of (chk_L3 c).1 col cutA cut₃ hA' h₃']
  refine sum_congr rfl fun jA hjA => congrArg _ (sum_congr rfl fun k₃ _ => ?_)
  rw [mem_range] at hjA
  have hb₂ : ∑ l, Function.update (Function.update col (fAT c) jA) (tmT c 2) k₃
      ((N1 c).face ((N1 c).leg (nd c 0 2) l)) ≤ cut₂ := by
    simp only [e1]
    rw [sum_lfT]
    simp only [Function.update_apply, fAT_ne_tmT, triT_ne_tmT, triT_ne_fAT, ↓reduceIte]
    omega
  rw [hP3, N2, ev_elimN _ 4 _ (chk_G2 c).2, G2, ← ev_glue_of (chk_G2 c).1 _ cut₂ hb₂]
  refine sum_congr rfl fun k₂ _ => ?_
  have hb₁ : ∑ l, Function.update (Function.update (Function.update col (fAT c) jA) (tmT c 2) k₃)
      (tmT c 1) k₂ ((U c).face ((U c).leg (nd c 1 2) l)) ≤ cut₁ := by
    simp only [e0]
    rw [sum_lfT]
    simp only [Function.update_apply, fAT_ne_tmT, triT_ne_tmT, triT_ne_fAT, ↓reduceIte]
    omega
  rw [N1, ev_elimN _ 4 _ (chk_G1 c).2, G1, ← ev_glue_of (chk_G1 c).1 _ cut₁ hb₁]

/-- **The reduced networks of the two sides agree**: `NL c` and `NL c.rev` are related by a
gauge transformation and a relabelling. -/
theorem ev_NL_rev (c : Fin 20) (col : Fin 64 → ℕ) : (NL c).ev col = (NL c.rev).ev col := by
  rw [← ev_rel_of (chk_rel c) col, NG, ev_addParities col _ _ (chk_gauge c).2, ev_flipVars,
    ev_flipNodes col _ _ (chk_gauge c).1]

/-! ### Bitmask facts -/

lemma bits_sum : ∀ n : Fin 64, ∑ k ∈ bits n, 2 ^ k.val = n.val := by decide +kernel

lemma bits_injective : Function.Injective bits := fun a b h =>
  Fin.ext (by rw [← bits_sum a, ← bits_sum b, h])

lemma bits_fAT_rev : ∀ c : Fin 20, bits (fAT c.rev) = univ.image (trip c) := by decide +kernel

lemma bits_fAT : ∀ c : Fin 20, bits (fAT c) = univ \ bits (fAT c.rev) := by decide +kernel

lemma card_bits_fAT : ∀ c : Fin 20, #(bits (fAT c)) = 3 := by decide +kernel

lemma bits_tmT : ∀ (c : Fin 20) (k : Fin 3), bits (tmT c k) = insert (trip c k) (bits (fAT c)) := by decide +kernel

lemma trip_injective (c : Fin 20) : Function.Injective (trip c) := by
  have : ∀ (c : Fin 20) (i j : Fin 3), trip c i = trip c j → i = j := by decide +kernel
  exact this c

set_option maxRecDepth 100000 in
lemma image_triT : ∀ (c : Fin 20) (k : Fin 3), univ.image (fun i => bits (triT c k i)) =
    ((bits (tmT c k)).powersetCard 3).erase (bits (fAT c)) := by decide +kernel

lemma triT_injective (c : Fin 20) (k : Fin 3) : Function.Injective (triT c k) := by
  have : ∀ (c : Fin 20) (k i j : Fin 3), triT c k i = triT c k j → i = j := by decide +kernel
  exact this c k

lemma tmT_ne : ∀ (c : Fin 20) (i j : Fin 3), i ≠ j → tmT c i ≠ tmT c j := by decide +kernel

set_option maxRecDepth 100000 in
lemma exists_trip : ∀ P : Finset (Fin 6), #P = 3 → ∃ c : Fin 20, bits (fAT c.rev) = P := by decide +kernel

/-! ### Transfer to colourings of `V` -/


/-- The face of `V` with the positions of the bitmask `n`. -/
def bF (n : Fin 64) : Finset V := (bits n).map φ.toEmbedding

lemma bF_injective : Function.Injective (bF φ) := (map_injective _).comp bits_injective

lemma bcol_update (g : Finset V → ℕ) (n : Fin 64) (x : ℕ) :
    bcol φ (Function.update g (bF φ n) x) = Function.update (bcol φ g) n x :=
  Function.update_comp_eq_of_injective g (bF_injective φ) n x

lemma bF_tmT (c : Fin 20) (k : Fin 3) : bF φ (tmT c k) = insert (φ (trip c k)) (bF φ (fAT c)) := by
  rw [bF, bits_tmT, map_insert]
  rfl

lemma bF_fAT_rev (c : Fin 20) : bF φ (fAT c.rev) = univ.image fun k => φ (trip c k) := by
  rw [bF, bits_fAT_rev, map_eq_image, image_image]
  rfl

lemma bF_fAT_union (c : Fin 20) : bF φ (fAT c) ∪ bF φ (fAT c.rev) = univ.map φ.toEmbedding := by
  rw [bF, bF, ← map_union, bits_fAT, sdiff_union_of_subset (subset_univ _)]

lemma card_erase_univ_map (b : Fin 6) : #((univ.map φ.toEmbedding).erase (φ b)) = 5 := by
  rw [card_erase_of_mem (by simp), card_map, card_univ, Fintype.card_fin]

/-- The three vertex amplitudes of the left side of case `c` are the evaluation of `U c`. -/
lemma prod_simpW_eq (c : Fin 20) (g : Finset V → ℕ) :
    ∏ k, simpW g ((univ.map φ.toEmbedding).erase (φ (trip c k))) = (U c).ev (bcol φ g) := by
  rw [U, ev_union _ _ (fun _ => ⟨rfl, rfl⟩)]
  refine prod_congr rfl fun k _ => ?_
  rw [simpW, dite_eq_left (card_erase_univ_map φ _), vertexAmp_erase_eq]

/-- The boundary triangles of the inner tetrahedron `k` as faces of `V`. -/
lemma sum_triT (c : Fin 20) (k : Fin 3) (h : Finset V → ℕ) :
    ∑ i, h (bF φ (triT c k i)) =
      ∑ f ∈ ((bF φ (tmT c k)).powersetCard 3).erase (bF φ (fAT c)), h f := by
  have e : ((bF φ (tmT c k)).powersetCard 3).erase (bF φ (fAT c)) =
      (univ.image fun i => bits (triT c k i)).map (mapEmbedding φ.toEmbedding).toEmbedding := by
    rw [image_triT, map_erase, ← powersetCard_map]
    rfl
  rw [e, sum_map, sum_image fun i _ j _ hij => triT_injective c k (bits_injective hij)]
  rfl

/-- **The left side of case `c` for colourings of `V`**: the sum over the colours of the inner
triangle and tetrahedra of the product of the three vertex amplitudes is `(NL c).ev`. -/
theorem inner_eq (c : Fin 20) (g : Finset V → ℕ) (cutA cut₀ cut₁ cut₂ : ℕ)
    (h₀ : cutA + ∑ i, g (bF φ (triT c 0 i)) ≤ cut₀) (h₁ : cutA + ∑ i, g (bF φ (triT c 1 i)) ≤ cut₁)
    (hA : ∑ i, g (bF φ (triT c 2 i)) ≤ cutA) (h₂ : cutA + ∑ i, g (bF φ (triT c 2 i)) ≤ cut₂) :
    ∑ x ∈ range (cutA + 1), ((x : ℝ) + 1) * ∑ y₂ ∈ range (cut₂ + 1), ∑ y₁ ∈ range (cut₁ + 1),
      ∑ y₀ ∈ range (cut₀ + 1), ∏ k, simpW (Function.update (Function.update (Function.update
        (Function.update g (bF φ (fAT c)) x) (bF φ (tmT c 2)) y₂) (bF φ (tmT c 1)) y₁)
        (bF φ (tmT c 0)) y₀) ((univ.map φ.toEmbedding).erase (φ (trip c k))) =
      (NL c).ev (bcol φ g) := by
  simp only [prod_simpW_eq, bcol_update]
  exact lhs_eq_ev_NL c (bcol φ g) cutA cut₀ cut₁ cut₂ h₀ h₁ hA h₂

end Move33

/-! ## Moves and the Ooguri weight -/

open Lightlike.FourD Complex4

section Moves


/-- The faces of dimension `k` are the faces with `k + 1` vertices. -/
lemma mem_faces_iff {K : Complex4 V} {k : ℕ} {f : Finset V} :
    f ∈ K.faces k ↔ f ∈ K.allFaces ∧ #f = k + 1 := by
  rw [Complex4.mem_faces, mem_allFaces]
  constructor
  · rintro ⟨s, hs, hfs, hc⟩
    exact ⟨⟨card_pos.mp (by omega), s, hs, hfs⟩, hc⟩
  · rintro ⟨⟨-, s, hs, hfs⟩, hc⟩
    exact ⟨s, hs, hfs, hc⟩

variable {K : Complex4 V} {σ τ : Finset V}

/-- The faces of dimension `k` of `K` away from `σ` are those after the move away from `τ`. -/
lemma faces_filter_move (h : IsMove K σ τ) (k : ℕ) :
    ((move K h).faces k).filter (¬ τ ⊆ ·) = (K.faces k).filter (¬ σ ⊆ ·) := by
  ext f
  have := congrArg (f ∈ ·) (filter_allFaces_move h)
  simp only [mem_filter, eq_iff_iff] at this
  simp only [mem_filter, mem_faces_iff]
  tauto

/-- The colourable faces of `K` away from `σ` are those after the move away from `τ`. -/
lemma colFaces_filter_move (h : IsMove K σ τ) :
    (colFaces (move K h)).filter (¬ τ ⊆ ·) = (colFaces K).filter (¬ σ ⊆ ·) := by
  rw [colFaces, colFaces, filter_union, filter_union, faces_filter_move h, faces_filter_move h]

/-- For a 3-3 move, the colourable faces containing the triangle `σ` are `σ` and the tetrahedra
`σ ∪ {b}`, `b ∈ τ`. -/
lemma mem_colFaces_of_subset (h : IsMove K σ τ) (hσ : #σ = 3) {f : Finset V} :
    (f ∈ colFaces K ∧ σ ⊆ f) ↔ (f = σ ∨ ∃ b ∈ τ, f = insert b σ) := by
  have hτ : #τ = 3 := by have := h.card; omega
  have key : f ∈ K.allFaces ∧ σ ⊆ f ↔ ∃ τ' ⊆ τ, τ' ≠ τ ∧ σ ∪ τ' = f := by
    have := congrArg (f ∈ ·) h.filter_allFaces_eq_image
    simp only [mem_filter, mem_image, mem_erase, mem_powerset, eq_iff_iff] at this
    rw [this]
    constructor
    · rintro ⟨τ', ⟨hne, hsub⟩, rfl⟩
      exact ⟨τ', hsub, hne, rfl⟩
    · rintro ⟨τ', hsub, hne, rfl⟩
      exact ⟨τ', ⟨hne, hsub⟩, rfl⟩
  have hc : ∀ τ' ⊆ τ, #(σ ∪ τ') = 3 + #τ' := fun τ' hτ' => by
    rw [card_union_of_disjoint (h.disj.mono_right hτ'), hσ]
  have hins : ∀ b, σ ∪ {b} = insert b σ := fun b => by
    ext x
    simp
  simp only [colFaces, mem_union, mem_faces_iff]
  constructor
  · rintro ⟨hf, hσf⟩
    have hfa : f ∈ K.allFaces := by rcases hf with ⟨hf, -⟩ | ⟨hf, -⟩ <;> exact hf
    obtain ⟨τ', hsub, -, rfl⟩ := key.mp ⟨hfa, hσf⟩
    rcases hf with ⟨-, h3⟩ | ⟨-, h4⟩
    · left
      rw [hc τ' hsub] at h3
      rw [card_eq_zero.mp (show #τ' = 0 by omega), union_empty]
    · right
      rw [hc τ' hsub] at h4
      obtain ⟨b, rfl⟩ := card_eq_one.mp (show #τ' = 1 by omega)
      exact ⟨b, hsub (mem_singleton_self b), hins b⟩
  · rintro (rfl | ⟨b, hb, rfl⟩)
    · have hne : (∅ : Finset V) ≠ τ := fun he => by rw [← he] at hτ; simp at hτ
      exact ⟨Or.inl ⟨(key.mpr ⟨∅, empty_subset _, hne, union_empty f⟩).1, hσ⟩, subset_refl _⟩
    · have hne : ({b} : Finset V) ≠ τ := fun he => by rw [← he] at hτ; simp at hτ
      have hb' : b ∉ σ := disjoint_right.mp h.disj hb
      refine ⟨Or.inr ⟨(key.mpr ⟨{b}, singleton_subset_iff.mpr hb, hne, hins b⟩).1, ?_⟩,
        subset_insert _ _⟩
      rw [card_insert_of_notMem hb', hσ]

/-- For a 3-3 move, `σ` is the only triangle containing `σ`. -/
lemma tris_filter_self (h : IsMove K σ τ) (hσ : #σ = 3) : K.tris.filter (σ ⊆ ·) = {σ} := by
  ext f
  rw [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hf, hσf⟩
    exact (eq_of_subset_of_card_le hσf (by rw [card_of_mem_faces hf, hσ])).symm
  · rintro rfl
    refine ⟨?_, subset_refl _⟩
    rcases mem_union.mp ((mem_colFaces_of_subset h hσ).mpr (Or.inl rfl)).1 with h3 | h4
    · exact h3
    · have := card_of_mem_faces h4
      omega

/-- The weight of the triangles and 4-simplices of `K` that do not contain `σ`. -/
noncomputable def outerW (K : Complex4 V) (σ : Finset V) (g : Finset V → ℕ) : ℝ :=
  (∏ f ∈ K.tris.filter (¬ σ ⊆ ·), ((g f : ℝ) + 1)) * ∏ s ∈ K.simps.filter (¬ σ ⊆ ·), simpW g s

/-- **The weight around the triangle of a 3-3 move**: the weight of `K` is the weight away from
`σ` times the dimension factor of `σ` and the three vertex amplitudes around it. -/
lemma weight_eq_outerW (h : IsMove K σ τ) (hσ : #σ = 3) (g : Finset V → ℕ) :
    weight K g = outerW K σ g * (((g σ : ℝ) + 1) * ∏ v ∈ τ, simpW g ((σ ∪ τ).erase v)) := by
  rw [weight, outerW, ← prod_filter_mul_prod_filter_not K.tris (σ ⊆ ·),
    ← prod_filter_mul_prod_filter_not K.simps (σ ⊆ ·), tris_filter_self h hσ, h.filter_simps,
    prod_singleton, prod_image fun x hx y hy hxy =>
      erase_injOn_union (mem_union_right σ hx) (mem_union_right σ hy) hxy]
  ring

/-- `outerW K σ` sees only the colours of the faces not containing `σ`. -/
lemma outerW_congr (K : Complex4 V) (σ : Finset V) {g g' : Finset V → ℕ}
    (hg : ∀ f, ¬ σ ⊆ f → g f = g' f) : outerW K σ g = outerW K σ g' := by
  unfold outerW
  congr 1
  · exact prod_congr rfl fun f hf => by rw [hg f (mem_filter.mp hf).2]
  · exact prod_congr rfl fun s hs =>
      simpW_congr fun f hfs _ => hg f fun hσf => (mem_filter.mp hs).2 (hσf.trans hfs)

/-- The weight away from `τ` after a move is the weight away from `σ` before it. -/
lemma outerW_move (h : IsMove K σ τ) (g : Finset V → ℕ) : outerW (move K h) τ g = outerW K σ g := by
  rw [outerW, outerW, faces_filter_move h, h.filter_move]

/-- Summing over colourings of four new faces, one after the other (`Lightlike.PR.sum_pi_insert`). -/
lemma sum_pi_insert4 {S : Finset (Finset V)} {a b c d : Finset V}
    (ha : a ∉ insert b (insert c (insert d S))) (hb : b ∉ insert c (insert d S))
    (hc : c ∉ insert d S) (hd : d ∉ S) (t : Finset V → Finset ℕ) (F : (Finset V → ℕ) → ℝ) :
    ∑ σ ∈ (insert a (insert b (insert c (insert d S)))).pi t, F (Lightlike.PR.extS _ σ) =
      ∑ σ ∈ S.pi t, ∑ x ∈ t d, ∑ y ∈ t c, ∑ z ∈ t b, ∑ w ∈ t a,
        F (Function.update (Function.update (Function.update (Function.update
          (Lightlike.PR.extS S σ) d x) c y) b z) a w) := by
  rw [Lightlike.PR.sum_pi_insert ha, Lightlike.PR.sum_pi_insert hb (F := fun g => ∑ w ∈ t a,
      F (Function.update g a w)),
    Lightlike.PR.sum_pi_insert hc (F := fun g => ∑ z ∈ t b, ∑ w ∈ t a,
      F (Function.update (Function.update g b z) a w)),
    Lightlike.PR.sum_pi_insert hd (F := fun g => ∑ y ∈ t c, ∑ z ∈ t b, ∑ w ∈ t a,
      F (Function.update (Function.update (Function.update g c y) b z) a w))]

end Moves

/-! ## The 3-3 move of the state sum -/

section Global


namespace Move33

/-- **One side of the 3-3 move**: for the triangle `σ` and its link `τ` given by case `c` and the
positions `φ`, the state sum is the sum over the outer colourings of the outer weight times
`(NL c).ev`. -/
theorem amplitudeGF_eq_sum (K : Complex4 V) {σ τ : Finset V} (h : IsMove K σ τ) (c : Fin 20)
    (hσ : σ = bF φ (fAT c)) (hτ : τ = bF φ (fAT c.rev)) (T : Finset (Finset V))
    (hT : ∀ f ∈ T, ¬ σ ⊆ f) (cut : Finset V → ℕ)
    (hA : ∀ b ∈ τ, ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut σ)
    (ht : ∀ b ∈ τ, cut σ + ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut (insert b σ)) :
    amplitudeGF K T cut =
      ∑ σ' ∈ ((colFaces K).filter (¬ σ ⊆ ·) \ T).pi (fun f => range (cut f + 1)),
        outerW K σ (Lightlike.PR.extS _ σ') * (NL c).ev (bcol φ (Lightlike.PR.extS _ σ')) := by
  have hσ3 : #σ = 3 := by rw [hσ, bF, card_map, card_bits_fAT]
  have hW : σ ∪ τ = univ.map φ.toEmbedding := by rw [hσ, hτ, bF_fAT_union]
  have hτ' : τ = univ.image fun k => φ (trip c k) := by rw [hτ, bF_fAT_rev]
  have hmem : ∀ k, φ (trip c k) ∈ τ := fun k => by
    rw [hτ']
    exact mem_image_of_mem _ (mem_univ k)
  have ht' : ∀ k, insert (φ (trip c k)) σ = bF φ (tmT c k) := fun k => by rw [bF_tmT, hσ]
  have hsub : ∀ k, σ ⊆ bF φ (tmT c k) := fun k => by
    rw [← ht']
    exact subset_insert _ _
  have hne : ∀ k, bF φ (tmT c k) ≠ σ := fun k he =>
    fAT_ne_tmT c k (bF_injective φ (he.trans hσ)).symm
  have htt : ∀ i j : Fin 3, i ≠ j → bF φ (tmT c i) ≠ bF φ (tmT c j) := fun i j hij he =>
    tmT_ne c i j hij (bF_injective φ he)
  have h3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  set O := (colFaces K).filter (¬ σ ⊆ ·) \ T with hO
  have hnO : ∀ f, σ ⊆ f → f ∉ O := fun f hf hm => (mem_filter.mp (mem_sdiff.mp hm).1).2 hf
  have hS : colFaces K \ T = insert (bF φ (tmT c 0)) (insert (bF φ (tmT c 1))
      (insert (bF φ (tmT c 2)) (insert σ O))) := by
    have hin : ∀ k, bF φ (tmT c k) ∈ colFaces K ∧ σ ⊆ bF φ (tmT c k) := fun k =>
      (mem_colFaces_of_subset h hσ3).mpr (Or.inr ⟨_, hmem k, (ht' k).symm⟩)
    have hσK := (mem_colFaces_of_subset h hσ3).mpr (Or.inl rfl)
    ext f
    simp only [mem_insert, mem_sdiff, hO, mem_filter]
    constructor
    · rintro ⟨hfK, hfT⟩
      by_cases hf : σ ⊆ f
      · rcases (mem_colFaces_of_subset h hσ3).mp ⟨hfK, hf⟩ with hfσ | ⟨b, hb, hfb⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl hfσ)))
        · rw [hτ', mem_image] at hb
          obtain ⟨k, -, rfl⟩ := hb
          rw [hfb, ht']
          rcases h3 k with rfl | rfl | rfl <;> simp
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨hfK, hf⟩, hfT⟩)))
    · rintro (rfl | rfl | rfl | rfl | ⟨⟨hfK, -⟩, hfT⟩)
      · exact ⟨(hin 0).1, fun hT' => hT _ hT' (hin 0).2⟩
      · exact ⟨(hin 1).1, fun hT' => hT _ hT' (hin 1).2⟩
      · exact ⟨(hin 2).1, fun hT' => hT _ hT' (hin 2).2⟩
      · exact ⟨hσK.1, fun hT' => hT _ hT' hσK.2⟩
      · exact ⟨hfK, hfT⟩
  have n₃ : σ ∉ O := hnO σ (subset_refl σ)
  have n₂ : bF φ (tmT c 2) ∉ insert σ O := by
    rw [mem_insert, not_or]
    exact ⟨hne 2, hnO _ (hsub 2)⟩
  have n₁ : bF φ (tmT c 1) ∉ insert (bF φ (tmT c 2)) (insert σ O) := by
    simp only [mem_insert, not_or]
    exact ⟨htt 1 2 (by decide), hne 1, hnO _ (hsub 1)⟩
  have n₀ : bF φ (tmT c 0) ∉ insert (bF φ (tmT c 1)) (insert (bF φ (tmT c 2)) (insert σ O)) := by
    simp only [mem_insert, not_or]
    exact ⟨htt 0 1 (by decide), htt 0 2 (by decide), hne 0, hnO _ (hsub 0)⟩
  rw [amplitudeGF, hS, sum_pi_insert4 n₀ n₁ n₂ n₃]
  refine sum_congr rfl fun σ' hσ' => ?_
  set g := Lightlike.PR.extS O σ'
  have hg : ∀ f, g f ≤ cut f := Lightlike.PR.extS_le hσ'
  have hb : ∀ k, ∑ i, g (bF φ (triT c k i)) ≤
      ∑ f ∈ ((insert (φ (trip c k)) σ).powersetCard 3).erase σ, cut f := fun k => by
    rw [sum_triT, ← ht', ← hσ]
    exact sum_le_sum fun f _ => hg f
  have hw : ∀ x y₂ y₁ y₀, weight K (Function.update (Function.update (Function.update
      (Function.update g σ x) (bF φ (tmT c 2)) y₂) (bF φ (tmT c 1)) y₁) (bF φ (tmT c 0)) y₀) =
      outerW K σ g * (((x : ℝ) + 1) * ∏ k, simpW (Function.update (Function.update
        (Function.update (Function.update g σ x) (bF φ (tmT c 2)) y₂) (bF φ (tmT c 1)) y₁)
        (bF φ (tmT c 0)) y₀) ((univ.map φ.toEmbedding).erase (φ (trip c k)))) := by
    intro x y₂ y₁ y₀
    rw [weight_eq_outerW h hσ3, hW, hτ', prod_image fun i _ j _ hij =>
      trip_injective c (φ.injective hij)]
    congr 1
    · apply outerW_congr
      intro f hf
      have hfne : ∀ k, f ≠ bF φ (tmT c k) := fun k he => hf (by rw [he]; exact hsub k)
      rw [Function.update_of_ne (hfne 0), Function.update_of_ne (hfne 1),
        Function.update_of_ne (hfne 2), Function.update_of_ne (fun he => hf (by rw [he]))]
    · rw [Function.update_of_ne (hne 0).symm, Function.update_of_ne (hne 1).symm,
        Function.update_of_ne (hne 2).symm, Function.update_self]
  simp only [hw, ← mul_sum]
  have hi := inner_eq φ c g (cut σ) (cut (bF φ (tmT c 0))) (cut (bF φ (tmT c 1)))
    (cut (bF φ (tmT c 2)))
    (by have := ht _ (hmem 0); have := hb 0; rw [← ht' 0]; omega)
    (by have := ht _ (hmem 1); have := hb 1; rw [← ht' 1]; omega)
    ((hb 2).trans (hA _ (hmem 2)))
    (by have := ht _ (hmem 2); have := hb 2; rw [← ht' 2]; omega)
  rw [← hσ] at hi
  rw [hi]

end Move33

/-- **The Ooguri state sum is invariant under the 3-3 move.** For a 3-3 move on `K` (the triangle
`σ` in the three 4-simplices `(σ ∪ τ) ∖ {b}`, `b ∈ τ`, replaced by the triangle `τ` in the three
4-simplices `(σ ∪ τ) ∖ {a}`, `a ∈ σ`), a gauge set avoiding the inner faces of both sides, and
cutoffs large enough on the inner faces (on each inner triangle at least the sum over the other
triangles of each inner tetrahedron, on each inner tetrahedron at least the sum over its four
triangles), the gauge-fixed state sums agree. -/
theorem amplitudeGF_move33 (K : Complex4 V) {σ τ : Finset V} (h : IsMove K σ τ) (hσ : #σ = 3)
    (T : Finset (Finset V)) (hT : ∀ f ∈ T, ¬ σ ⊆ f ∧ ¬ τ ⊆ f) (cut : Finset V → ℕ)
    (hAσ : ∀ b ∈ τ, ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut σ)
    (htσ : ∀ b ∈ τ, cut σ + ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut (insert b σ))
    (hAτ : ∀ a ∈ σ, ∑ f ∈ ((insert a τ).powersetCard 3).erase τ, cut f ≤ cut τ)
    (htτ : ∀ a ∈ σ, cut τ + ∑ f ∈ ((insert a τ).powersetCard 3).erase τ, cut f ≤ cut (insert a τ)) :
    amplitudeGF (move K h) T cut = amplitudeGF K T cut := by
  have h6 : #(σ ∪ τ) = 6 := h.card_union
  set φ := (σ ∪ τ).orderEmbOfFin h6
  have hW : univ.map φ.toEmbedding = σ ∪ τ := by
    ext v
    rw [mem_map]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact (σ ∪ τ).orderEmbOfFin_mem h6 i
    · intro hv
      have : v ∈ Set.range φ := by rw [range_orderEmbOfFin]; exact hv
      obtain ⟨i, rfl⟩ := this
      exact ⟨i, mem_univ _, rfl⟩
  have hτW : τ ⊆ univ.map φ.toEmbedding := hW ▸ subset_union_right
  set P := univ.filter fun i => φ i ∈ τ with hPdef
  have hP : P.map φ.toEmbedding = τ := by
    ext v
    simp only [mem_map, hPdef, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hv
      obtain ⟨i, -, rfl⟩ := mem_map.mp (hτW hv)
      exact ⟨i, hv, rfl⟩
  have hP3 : #P = 3 := by
    rw [← card_map φ.toEmbedding, hP]
    have := h.card
    omega
  obtain ⟨c, hc⟩ := Move33.exists_trip P hP3
  have hτ : τ = Move33.bF φ (Move33.fAT c.rev) := by rw [Move33.bF, hc, hP]
  have hσ' : σ = Move33.bF φ (Move33.fAT c) := by
    have : Move33.bF φ (Move33.fAT c) = univ.map φ.toEmbedding \ Move33.bF φ (Move33.fAT c.rev) := by
      rw [Move33.bF, Move33.bits_fAT, Finset.map_sdiff]
      rfl
    rw [this, ← hτ, hW, union_sdiff_cancel_right h.disj]
  rw [Move33.amplitudeGF_eq_sum φ (move K h) h.symm c.rev hτ (by rw [Fin.rev_rev]; exact hσ') T
      (fun f hf => (hT f hf).2) cut hAτ htτ,
    Move33.amplitudeGF_eq_sum φ K h c hσ' hτ T (fun f hf => (hT f hf).1) cut hAσ htσ,
    colFaces_filter_move h]
  refine sum_congr rfl fun σ' _ => ?_
  rw [outerW_move h, Move33.ev_NL_rev c]

/-- **Gauge-fixed 3-3 invariance.** For a 3-3 move `σ → τ`, a gauge set `T` of `K` (the gauge
rule `IsGauge`) that does not contain `σ`, and cutoffs that cut off nothing on the inner faces,
`T` is a gauge set of the new complex and the state sums before and after the move are equal. -/
theorem amplitudeGF_move33_gauge (K : Complex4 V) {σ τ : Finset V} (h : K.IsMove σ τ)
    (hσ : #σ = 3) {T : Finset (Finset V)} (hg : IsGauge K T) (hσT : σ ∉ T) (cut : Finset V → ℕ)
    (hAσ : ∀ b ∈ τ, ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut σ)
    (htσ : ∀ b ∈ τ, cut σ + ∑ f ∈ ((insert b σ).powersetCard 3).erase σ, cut f ≤ cut (insert b σ))
    (hAτ : ∀ a ∈ σ, ∑ f ∈ ((insert a τ).powersetCard 3).erase τ, cut f ≤ cut τ)
    (htτ : ∀ a ∈ σ, cut τ + ∑ f ∈ ((insert a τ).powersetCard 3).erase τ, cut f ≤ cut (insert a τ)) :
    IsGauge (K.move h) T ∧ amplitudeGF (K.move h) T cut = amplitudeGF K T cut := by
  refine ⟨hg.move33 h hσ hσT, amplitudeGF_move33 K h hσ T (fun f hf => ⟨fun hs => hσT ?_,
    fun hs => ?_⟩) cut hAσ htσ hAτ htτ⟩
  · rwa [eq_of_subset_of_card_le hs (by rw [Complex4.card_of_mem_faces (hg.1 hf), hσ])]
  · obtain ⟨s, hsK, hfs, -⟩ := Complex4.mem_faces.mp (hg.1 hf)
    exact h.fresh s hsK (hs.trans hfs)

end Global

end Lightlike.SpinFoam
