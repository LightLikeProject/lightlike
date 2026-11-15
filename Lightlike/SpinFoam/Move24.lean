import Lightlike.SpinFoam.MoveBlocks

/-!
# The 2-4 move of the Ooguri model: the local identity

The 2-4 Pachner move replaces the two 4-simplices `W ∖ {b}`, `b ∈ B`, around the tetrahedron
`A` (so `W = A ∪ B` has six vertices and `#B = 2`) by the four 4-simplices `W ∖ {a}`, `a ∈ A`,
around the edge `B`. The faces of the four-simplex side are the four triangles `B ∪ {a}` and the
six tetrahedra `B ∪ {a, a'}`; the face of the two-simplex side is the tetrahedron `A`.

Positions of `W` are `Fin 6`. Case `c : Fin 15` is the choice of the positions `bposT c` of `B`;
`aposT c` are those of `A`, in increasing order.

* The four-simplex side `U4 c` is the union of the vertex networks of `W ∖ {a_k}` (blocks `0..3`).
  Three gluings (tetrahedra `B ∪ {a_0, a_1}`, `B ∪ {a_0, a_2}`, `B ∪ {a_1, a_2}`) and three
  strand closings (triangles `B ∪ {a_1}`, `B ∪ {a_2}`, `B ∪ {a_3}`, in the tetrahedra
  `B ∪ {a_1, a_3}`, `B ∪ {a_2, a_3}`, `B ∪ {a_0, a_3}`) reduce it to `NL c`. What is left is one
  free closed strand, on the triangle `B ∪ {a_0}`: it multiplies the network by that triangle's
  dimension.
* The two-simplex side `UB c` is the union of the vertex networks of `W ∖ {b}`; one gluing
  (through the tetrahedron `A`) gives `QB c`.
* A gauge transformation of `NL c` without the free strand is a relabelling of `QB c`.

All hypotheses of the steps are checked by the kernel (`decide +kernel`).
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam

open SNet MoveBlocks

namespace Move24

/-- Edges of a union of four vertex networks. -/
abbrev E4 := EB 4

/-- Nodes of a union of four vertex networks. -/
abbrev N4 := NB 4

/-! ## Tables -/

/-- The positions of `A` (four) for the case `c`. -/
def aposT : Fin 15 → Fin 4 → Fin 6 :=
  ![![2, 3, 4, 5], ![1, 3, 4, 5], ![1, 2, 4, 5], ![1, 2, 3, 5], ![1, 2, 3, 4], ![0, 3, 4, 5], ![0, 2, 4, 5], ![0, 2, 3, 5], ![0, 2, 3, 4], ![0, 1, 4, 5], ![0, 1, 3, 5], ![0, 1, 3, 4], ![0, 1, 2, 5], ![0, 1, 2, 4], ![0, 1, 2, 3]]
/-- The positions of `B` (two) for the case `c`. -/
def bposT : Fin 15 → Fin 2 → Fin 6 :=
  ![![0, 1], ![0, 2], ![0, 3], ![0, 4], ![0, 5], ![1, 2], ![1, 3], ![1, 4], ![1, 5], ![2, 3], ![2, 4], ![2, 5], ![3, 4], ![3, 5], ![4, 5]]
/-- Loop 1: the node flips, the node parities, the nodes `n₁ n₂` and the leg. -/
def pre1F : Fin 15 → List N4 :=
  ![[(0, 3)], [(0, 3)], [(0, 3)], [(2, 1)], [(2, 1)], [(0, 3)], [(0, 3)], [(2, 0)], [(2, 0)], [(0, 3)], [(2, 0)], [(2, 0)], [(0, 1)], [(0, 1)], [(0, 1)]]
/-- Loop 1: the nodes whose parity is flipped before the loop. -/
def pre1P : Fin 15 → List N4 :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
/-- Loop 1: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop1N : Fin 15 → N4 × N4 × Fin 4 :=
  ![((0, 3), (2, 2), 3), ((0, 3), (2, 1), 3), ((0, 3), (2, 1), 3), ((0, 2), (2, 1), 3), ((0, 2), (2, 1), 2), ((0, 3), (2, 0), 3), ((0, 3), (2, 0), 3), ((0, 2), (2, 0), 3), ((0, 2), (2, 0), 2), ((0, 3), (2, 0), 3), ((0, 2), (2, 0), 3), ((0, 2), (2, 0), 2), ((0, 1), (2, 0), 3), ((0, 1), (2, 0), 2), ((0, 1), (2, 0), 1)]
/-- Loop 2: the node flips, the node parities, the nodes `n₁ n₂` and the leg. -/
def pre2F : Fin 15 → List N4 :=
  ![[(1, 2)], [(1, 1)], [(0, 1)], [(0, 1)], [(0, 1)], [(1, 0)], [(0, 1)], [(0, 1)], [(0, 1)], [(1, 0)], [(1, 0)], [(1, 0)], [(1, 0)], [(1, 0)], [(1, 0)]]
/-- Loop 2: the nodes whose parity is flipped before the loop. -/
def pre2P : Fin 15 → List N4 :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
/-- Loop 2: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop2N : Fin 15 → N4 × N4 × Fin 4 :=
  ![((0, 2), (1, 2), 3), ((0, 2), (1, 1), 3), ((0, 1), (1, 1), 3), ((0, 1), (1, 1), 3), ((0, 1), (1, 1), 2), ((0, 2), (1, 0), 3), ((0, 1), (1, 0), 3), ((0, 1), (1, 0), 3), ((0, 1), (1, 0), 2), ((0, 0), (1, 0), 3), ((0, 0), (1, 0), 3), ((0, 0), (1, 0), 2), ((0, 0), (1, 0), 3), ((0, 0), (1, 0), 2), ((0, 0), (1, 0), 1)]
/-- Loop 3: the node flips, the node parities, the nodes `n₁ n₂` and the leg. -/
def pre3F : Fin 15 → List N4 :=
  ![[(1, 3)], [(1, 3)], [(1, 3)], [(2, 2)], [(2, 2)], [(1, 3)], [(1, 3)], [(2, 2)], [(2, 2)], [(1, 3)], [(2, 1)], [(2, 1)], [(1, 1)], [(1, 1)], [(1, 1)]]
/-- Loop 3: the nodes whose parity is flipped before the loop. -/
def pre3P : Fin 15 → List N4 :=
  ![[], [], [], [], [], [], [], [], [], [], [], [], [], [], []]
/-- Loop 3: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop3N : Fin 15 → N4 × N4 × Fin 4 :=
  ![((1, 3), (2, 3), 2), ((1, 3), (2, 3), 1), ((1, 3), (2, 2), 1), ((1, 2), (2, 2), 1), ((1, 2), (2, 2), 1), ((1, 3), (2, 3), 0), ((1, 3), (2, 2), 0), ((1, 2), (2, 2), 0), ((1, 2), (2, 2), 0), ((1, 3), (2, 1), 0), ((1, 2), (2, 1), 0), ((1, 2), (2, 1), 0), ((1, 1), (2, 1), 0), ((1, 1), (2, 1), 0), ((1, 1), (2, 1), 0)]
/-- The free edge of the reduced left side. -/
def freeE : Fin 15 → E4 :=
  ![(1, 8), (1, 8), (1, 8), (1, 4), (1, 6), (1, 8), (1, 8), (1, 4), (1, 6), (1, 8), (1, 4), (1, 6), (1, 7), (1, 9), (1, 5)]
/-- The nodes of the reduced left side that are flipped. -/
def gNT : Fin 15 → List N4 :=
  ![[(2, 1), (1, 1), (0, 1), (3, 0)], [(2, 2), (1, 2), (0, 1), (3, 0)], [(2, 3), (1, 2), (0, 2), (3, 0)], [(2, 3), (1, 3), (0, 3), (3, 0)], [(2, 4), (1, 4), (0, 4), (3, 0)], [(2, 2), (1, 2), (3, 1), (0, 1)], [(2, 3), (1, 2), (3, 1), (0, 2)], [(2, 3), (1, 3), (3, 1), (0, 3)], [(2, 4), (1, 4), (3, 1), (0, 4)], [(2, 3), (3, 2), (1, 2), (0, 2)], [(2, 3), (3, 2), (1, 3), (0, 3)], [(2, 4), (3, 2), (1, 4), (0, 4)], [(3, 3), (2, 3), (1, 3), (0, 3)], [(3, 3), (2, 4), (1, 4), (0, 4)], [(3, 3), (2, 4), (1, 4), (0, 4)]]
/-- The edges of the reduced left side that are glued. -/
def gET : Fin 15 → List E4 :=
  ![[(2, 7), (1, 7), (1, 9), (0, 7), (0, 9), (0, 5), (3, 2), (2, 2), (0, 2)], [(2, 4), (1, 4), (1, 6), (0, 7), (0, 9), (0, 5), (1, 0)], [(2, 8), (1, 4), (1, 6), (0, 4), (0, 6), (3, 3), (2, 3)], [(2, 8), (1, 8), (0, 8), (0, 9)], [(1, 4), (0, 4), (3, 1)], [(2, 4), (1, 4), (1, 6), (1, 5), (0, 7), (0, 9), (0, 5)], [(2, 8), (1, 4), (1, 6), (3, 9), (2, 9), (0, 4), (0, 6)], [(2, 8), (1, 8), (0, 8), (0, 9)], [(1, 4), (3, 7), (0, 4)], [(2, 8), (3, 6), (2, 6), (1, 4), (1, 6), (0, 4), (0, 6), (0, 0), (0, 2)], [(2, 8), (1, 8), (0, 8), (0, 2)], [(3, 4), (1, 4), (0, 4), (0, 1), (0, 2)], [(2, 8), (1, 8), (1, 9), (1, 5), (0, 8), (0, 9), (0, 5)], [(3, 8), (1, 5), (0, 5), (0, 1)], [(3, 8), (2, 4), (2, 6), (1, 4), (1, 6), (0, 4), (0, 6), (0, 1), (0, 3)]]
/-- The nodes of the reduced left side whose parity is flipped. -/
def gPT : Fin 15 → List N4 :=
  ![[(2, 1), (0, 1), (3, 0), (2, 0), (0, 0)], [(2, 2), (1, 0), (0, 0)], [(2, 3), (1, 2), (0, 2), (3, 0), (2, 0), (1, 0)], [(2, 0), (0, 0)], [(2, 4), (1, 4), (0, 4), (3, 0), (1, 0)], [(2, 2), (1, 1)], [(2, 3), (1, 2), (3, 1), (2, 1), (1, 1), (0, 2), (0, 0)], [(2, 1)], [(2, 4), (1, 4), (3, 1), (1, 1), (0, 4), (0, 0)], [(2, 3), (3, 2), (2, 2), (1, 2), (0, 2)], [(2, 2), (1, 1), (0, 1)], [(2, 4), (3, 2), (1, 4), (0, 4)], [], [(3, 3), (2, 4), (2, 2), (1, 4), (1, 2), (0, 4), (0, 2)], [(2, 3), (1, 3), (0, 3)]]
/-- The edge `B` of case `c`, as a bitmask. -/
def bmT : Fin 15 → Fin 64 :=
  ![3, 5, 9, 17, 33, 6, 10, 18, 34, 12, 20, 36, 24, 40, 48]
/-- The tetrahedron `A` of case `c`, as a bitmask. -/
def sgT : Fin 15 → Fin 64 :=
  ![60, 58, 54, 46, 30, 57, 53, 45, 29, 51, 43, 27, 39, 23, 15]
/-- The inner triangles `B ∪ {a_k}`, as bitmasks. -/
def trT : Fin 15 → Fin 4 → Fin 64 :=
  ![![7, 11, 19, 35], ![7, 13, 21, 37], ![11, 13, 25, 41], ![19, 21, 25, 49], ![35, 37, 41, 49], ![7, 14, 22, 38], ![11, 14, 26, 42], ![19, 22, 26, 50], ![35, 38, 42, 50], ![13, 14, 28, 44], ![21, 22, 28, 52], ![37, 38, 44, 52], ![25, 26, 28, 56], ![41, 42, 44, 56], ![49, 50, 52, 56]]
/-- The inner tetrahedra `B ∪ {a_i, a_j}` in the order 01, 02, 03, 12, 13, 23. -/
def teT : Fin 15 → Fin 6 → Fin 64 :=
  ![![15, 23, 39, 27, 43, 51], ![15, 23, 39, 29, 45, 53], ![15, 27, 43, 29, 45, 57], ![23, 27, 51, 29, 53, 57], ![39, 43, 51, 45, 53, 57], ![15, 23, 39, 30, 46, 54], ![15, 27, 43, 30, 46, 58], ![23, 27, 51, 30, 54, 58], ![39, 43, 51, 46, 54, 58], ![15, 29, 45, 30, 46, 60], ![23, 29, 53, 30, 54, 60], ![39, 45, 53, 46, 54, 60], ![27, 29, 57, 30, 58, 60], ![43, 45, 57, 46, 58, 60], ![51, 53, 57, 54, 58, 60]]
/-- The outer triangles `{b_e, a_i, a_j}` of the inner tetrahedra, in the order of `teT`. -/
def ouT : Fin 15 → Fin 6 → Fin 2 → Fin 64 :=
  ![![![13, 14], ![21, 22], ![37, 38], ![25, 26], ![41, 42], ![49, 50]], ![![11, 14], ![19, 22], ![35, 38], ![25, 28], ![41, 44], ![49, 52]], ![![7, 14], ![19, 26], ![35, 42], ![21, 28], ![37, 44], ![49, 56]], ![![7, 22], ![11, 26], ![35, 50], ![13, 28], ![37, 52], ![41, 56]], ![![7, 38], ![11, 42], ![19, 50], ![13, 44], ![21, 52], ![25, 56]], ![![11, 13], ![19, 21], ![35, 37], ![26, 28], ![42, 44], ![50, 52]], ![![7, 13], ![19, 25], ![35, 41], ![22, 28], ![38, 44], ![50, 56]], ![![7, 21], ![11, 25], ![35, 49], ![14, 28], ![38, 52], ![42, 56]], ![![7, 37], ![11, 41], ![19, 49], ![14, 44], ![22, 52], ![26, 56]], ![![7, 11], ![21, 25], ![37, 41], ![22, 26], ![38, 42], ![52, 56]], ![![7, 19], ![13, 25], ![37, 49], ![14, 26], ![38, 50], ![44, 56]], ![![7, 35], ![13, 41], ![21, 49], ![14, 42], ![22, 50], ![28, 56]], ![![11, 19], ![13, 21], ![41, 49], ![14, 22], ![42, 50], ![44, 52]], ![![11, 35], ![13, 37], ![25, 49], ![14, 38], ![26, 50], ![28, 52]], ![![19, 35], ![21, 37], ![25, 41], ![22, 38], ![26, 42], ![28, 44]]]

/-! ## The chain of steps -/

/-- The four-simplex side of case `c`: the vertex networks of `W ∖ {a_k}` as blocks `k`. -/
def U4 (c : Fin 15) : SNet (Fin 64) E4 N4 :=
  union fun k => vnet (fcB (aposT c k)) (ttB (aposT c k))

/-- The node of block `k` opposite the vertex of block `k'`: its tetrahedron misses `a_k` and
`a_k'`. -/
def nd (c : Fin 15) (k k' : Fin 4) : N4 := (k, Move33.posT (aposT c k) (aposT c k'))

/-- Gluing the two nodes of the tetrahedron `B ∪ {a_0, a_1}`. -/
def G1 (c : Fin 15) : SNet (Fin 64) E4 N4 := (U4 c).glue (nd c 2 3) (nd c 3 2)

/-- Step 1 with its constraints eliminated. -/
def N1 (c : Fin 15) : SNet (Fin 64) E4 N4 := elimN 4 (G1 c)

/-- Gluing the two nodes of the tetrahedron `B ∪ {a_0, a_2}`. -/
def G2 (c : Fin 15) : SNet (Fin 64) E4 N4 := (N1 c).glue (nd c 1 3) (nd c 3 1)

/-- Step 2 with its constraints eliminated. -/
def N2 (c : Fin 15) : SNet (Fin 64) E4 N4 := elimN 4 (G2 c)

/-- Gluing the two nodes of the tetrahedron `B ∪ {a_1, a_2}`. -/
def G3 (c : Fin 15) : SNet (Fin 64) E4 N4 := (N2 c).glue (nd c 0 3) (nd c 3 0)

/-- Step 3 with its constraints eliminated. -/
def N3 (c : Fin 15) : SNet (Fin 64) E4 N4 := elimN 4 (G3 c)

/-- The preparation of a strand closing: node flips, then parities. -/
def prep (N : SNet (Fin 64) E4 N4) (f p : List N4) : SNet (Fin 64) E4 N4 :=
  addParities (flipNodes N f) p

/-- The preparation of the first strand closing. -/
def P1 (c : Fin 15) : SNet (Fin 64) E4 N4 := prep (N3 c) (pre1F c) (pre1P c)

/-- Closing the strand of the triangle `B ∪ {a_1}`. -/
def L1 (c : Fin 15) : SNet (Fin 64) E4 N4 :=
  (P1 c).loop (loop1N c).1 (loop1N c).2.1 (loop1N c).2.2

/-- The first strand closing with its constraints eliminated. -/
def M1 (c : Fin 15) : SNet (Fin 64) E4 N4 := elimN 4 (L1 c)

/-- The preparation of the second strand closing. -/
def P2 (c : Fin 15) : SNet (Fin 64) E4 N4 := prep (M1 c) (pre2F c) (pre2P c)

/-- Closing the strand of the triangle `B ∪ {a_2}`. -/
def L2 (c : Fin 15) : SNet (Fin 64) E4 N4 :=
  (P2 c).loop (loop2N c).1 (loop2N c).2.1 (loop2N c).2.2

/-- The second strand closing with its constraints eliminated. -/
def M2 (c : Fin 15) : SNet (Fin 64) E4 N4 := elimN 4 (L2 c)

/-- The preparation of the third strand closing. -/
def P3 (c : Fin 15) : SNet (Fin 64) E4 N4 := prep (M2 c) (pre3F c) (pre3P c)

/-- Closing the strand of the triangle `B ∪ {a_3}`. -/
def L3 (c : Fin 15) : SNet (Fin 64) E4 N4 :=
  (P3 c).loop (loop3N c).1 (loop3N c).2.1 (loop3N c).2.2

/-- **The reduced four-simplex side** of case `c`. -/
def NL (c : Fin 15) : SNet (Fin 64) E4 N4 := elimN 4 (L3 c)

/-- `NL c` without its free closed strand. -/
def NK (c : Fin 15) : SNet (Fin 64) E4 N4 := (NL c).killE (freeE c)

/-- The gauge transformation of `NK c` that matches `QB c`. -/
def NG (c : Fin 15) : SNet (Fin 64) E4 N4 :=
  addParities (flipVars (flipNodes (NK c) (gNT c)) (gET c)) (gPT c)

/-- The two-simplex side of case `c`: the vertex networks of `W ∖ {b}` as blocks `0, 1`. -/
def UB (c : Fin 15) : SNet (Fin 64) (EB 2) (NB 2) :=
  union fun k => vnet (fcB (bposT c k)) (ttB (bposT c k))

/-- The nodes of the two blocks of `UB c` on the tetrahedron `A`. -/
def ndB (c : Fin 15) (k k' : Fin 2) : NB 2 := (k, Move33.posT (bposT c k) (bposT c k'))

/-- Gluing the two nodes of the tetrahedron `A`. -/
def GB (c : Fin 15) : SNet (Fin 64) (EB 2) (NB 2) := (UB c).glue (ndB c 0 1) (ndB c 1 0)

/-- **The reduced two-simplex side** of case `c`. -/
def QB (c : Fin 15) : SNet (Fin 64) (EB 2) (NB 2) := elimN 4 (GB c)

/-- The triangles `A ∖ {a_i}` of the tetrahedron `A`, as bitmasks. -/
def faT : Fin 15 → Fin 4 → Fin 64 :=
  ![![56, 52, 44, 28], ![56, 50, 42, 26], ![52, 50, 38, 22], ![44, 42, 38, 14], ![28, 26, 22, 14], ![56, 49, 41, 25], ![52, 49, 37, 21], ![44, 41, 37, 13], ![28, 25, 21, 13], ![50, 49, 35, 19], ![42, 41, 35, 11], ![26, 25, 19, 11], ![38, 37, 35, 7], ![22, 21, 19, 7], ![14, 13, 11, 7]]

/-! ## Checked steps -/

set_option maxRecDepth 100000 in
lemma chk_G1 : ∀ c : Fin 15,
    GlueOK (U4 c) 2 (aposT c 2) (nd c 2 3) (nd c 3 2) (teT c 0) ∧ elimOK 4 (G1 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_G2 : ∀ c : Fin 15,
    GlueOK (N1 c) 1 (aposT c 1) (nd c 1 3) (nd c 3 1) (teT c 1) ∧ elimOK 4 (G2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_G3 : ∀ c : Fin 15,
    GlueOK (N2 c) 0 (aposT c 0) (nd c 0 3) (nd c 3 0) (teT c 3) ∧ elimOK 4 (G3 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P1 : ∀ c : Fin 15, flipNodesOK (N3 c) (pre1F c) = true ∧
    addParitiesOK (flipNodes (N3 c) (pre1F c)) (pre1P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L1 : ∀ c : Fin 15,
    LoopOK (P1 c) (loop1N c).1 (loop1N c).2.1 (loop1N c).2.2 (teT c 4) (trT c 1) ∧
      elimOK 4 (L1 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P2 : ∀ c : Fin 15, flipNodesOK (M1 c) (pre2F c) = true ∧
    addParitiesOK (flipNodes (M1 c) (pre2F c)) (pre2P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L2 : ∀ c : Fin 15,
    LoopOK (P2 c) (loop2N c).1 (loop2N c).2.1 (loop2N c).2.2 (teT c 5) (trT c 2) ∧
      elimOK 4 (L2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P3 : ∀ c : Fin 15, flipNodesOK (M2 c) (pre3F c) = true ∧
    addParitiesOK (flipNodes (M2 c) (pre3F c)) (pre3P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L3 : ∀ c : Fin 15,
    LoopOK (P3 c) (loop3N c).1 (loop3N c).2.1 (loop3N c).2.2 (teT c 2) (trT c 3) ∧
      elimOK 4 (L3 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_free : ∀ c : Fin 15, (NL c).eLive (freeE c) = true ∧ (NL c).kap (freeE c) = false ∧
    (∀ n, (NL c).nLive n = true → ∀ l, (NL c).leg n l ≠ freeE c) ∧
    (∀ x ∈ (NL c).cons, x.1 ≠ freeE c ∧ x.2.1 ≠ freeE c) ∧
    (NL c).face (freeE c) = trT c 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_gauge : ∀ c : Fin 15, flipNodesOK (NK c) (gNT c) = true ∧
    addParitiesOK (flipVars (flipNodes (NK c) (gNT c)) (gET c)) (gPT c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_B : ∀ c : Fin 15,
    GlueOK (UB c) 0 (bposT c 0) (ndB c 0 1) (ndB c 1 0) (sgT c) ∧ elimOK 4 (GB c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_rel : ∀ c : Fin 15, RelOK (NG c) (QB c) := by
  decide +kernel

/-! ## Faces at the glued and closed nodes -/

set_option maxRecDepth 100000 in
/-- The four triangles of the tetrahedron at each gluing node, as a list up to order. -/
lemma chk_legsG : ∀ c : Fin 15,
    (List.ofFn fun l => (U4 c).face ((U4 c).leg (nd c 2 3) l)).Perm
      [trT c 0, trT c 1, ouT c 0 0, ouT c 0 1] ∧
    (List.ofFn fun l => (N1 c).face ((N1 c).leg (nd c 1 3) l)).Perm
      [trT c 0, trT c 2, ouT c 1 0, ouT c 1 1] ∧
    (List.ofFn fun l => (N2 c).face ((N2 c).leg (nd c 0 3) l)).Perm
      [trT c 1, trT c 2, ouT c 3 0, ouT c 3 1] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The four triangles of the tetrahedron at each loop node: the strand face first. -/
lemma chk_legsL : ∀ c : Fin 15,
    (List.ofFn fun l => (P1 c).face ((P1 c).leg (loop1N c).1 l)).Perm
      [trT c 1, trT c 3, ouT c 4 0, ouT c 4 1] ∧
    (List.ofFn fun l => (P2 c).face ((P2 c).leg (loop2N c).1 l)).Perm
      [trT c 2, trT c 3, ouT c 5 0, ouT c 5 1] ∧
    (List.ofFn fun l => (P3 c).face ((P3 c).leg (loop3N c).1 l)).Perm
      [trT c 3, trT c 0, ouT c 2 0, ouT c 2 1] := by
  decide +kernel

/-! ## Distinctness of the faces of the move -/

lemma trT_eq_iff : ∀ c i j, trT c i = trT c j ↔ i = j := by decide +kernel
lemma trT_ne_teT : ∀ c i j, trT c i ≠ teT c j := by decide +kernel
lemma teT_ne_trT : ∀ c i j, teT c j ≠ trT c i := by decide +kernel
lemma trT_ne_ouT : ∀ c i j e, trT c i ≠ ouT c j e := by decide +kernel
lemma ouT_ne_trT : ∀ c i j e, ouT c j e ≠ trT c i := by decide +kernel
lemma teT_ne_ouT : ∀ c i j e, teT c i ≠ ouT c j e := by decide +kernel
lemma ouT_ne_teT : ∀ c i j e, ouT c j e ≠ teT c i := by decide +kernel

/-- Sum over the four legs, with the faces known up to order. -/
lemma sum_perm4 (f : Fin 4 → Fin 64) (a b c d : Fin 64)
    (h : (List.ofFn f).Perm [a, b, c, d]) (g : Fin 64 → ℕ) :
    ∑ l, g (f l) = g a + g b + g c + g d := by
  have h1 : ∑ l, g (f l) = ((List.ofFn f).map g).sum := by
    rw [List.map_ofFn, List.sum_ofFn]; rfl
  rw [h1, (h.map g).sum_eq]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- Sum over the three legs other than the strand leg. -/
lemma sum_erase_perm4 {S : SNet (Fin 64) E4 N4} {n₁ n₂ : N4} {lA : Fin 4} {t fA : Fin 64}
    (h : LoopOK S n₁ n₂ lA t fA) (x y z : Fin 64)
    (hp : (List.ofFn fun l => S.face (S.leg n₁ l)).Perm [fA, x, y, z]) (g : Fin 64 → ℕ) :
    ∑ l ∈ univ.erase lA, g (S.face (S.leg n₁ l)) = g x + g y + g z := by
  obtain ⟨-, -, -, -, -, -, -, -, h3, -⟩ := h
  have h1 := sum_perm4 _ _ _ _ _ hp g
  have h2 := add_sum_erase univ (fun l => g (S.face (S.leg n₁ l))) (mem_univ lA)
  simp only [h3] at h2
  omega

/-! ## The four-simplex side reduces to `NL c` -/

/-- Simplifying values of nested updates at the faces of the move. -/
local syntax "fs" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
local macro_rules
  | `(tactic| fs [$ts,*]) =>
    `(tactic| simp [Function.update_apply, trT_eq_iff, trT_ne_teT, teT_ne_trT, trT_ne_ouT,
      ouT_ne_trT, teT_ne_ouT, ouT_ne_teT, $ts,*])

set_option maxHeartbeats 1000000 in
/-- **The four-simplex side of case `c` reduces to `NL c`**: summed over the colours `x₃, x₂, x₁`
of the inner triangles `B ∪ {a_3}`, `B ∪ {a_2}`, `B ∪ {a_1}` (weights `x + 1`) and the colours of
the six inner tetrahedra, the union of the four vertex networks evaluates to the reduced
network, once the cutoffs exceed the triangle inequalities. The triangle `B ∪ {a_0}` and the
twelve outer triangles keep the colouring `col`. -/
theorem lhs_eq_ev_NL24 (c : Fin 15) (col : Fin 64 → ℕ)
    (cx3 ct2 cx2 ct5 cx1 ct4 ct3 ct1 ct0 : ℕ)
    (h1 : col (trT c 0) + (col (ouT c 2 0) + col (ouT c 2 1)) ≤ cx3)
    (h2 : cx3 + (col (trT c 0) + (col (ouT c 2 0) + col (ouT c 2 1))) ≤ ct2)
    (h3 : cx3 + (col (ouT c 5 0) + col (ouT c 5 1)) ≤ cx2)
    (h4 : cx2 + (cx3 + (col (ouT c 5 0) + col (ouT c 5 1))) ≤ ct5)
    (h5 : cx3 + (col (ouT c 4 0) + col (ouT c 4 1)) ≤ cx1)
    (h6 : cx1 + (cx3 + (col (ouT c 4 0) + col (ouT c 4 1))) ≤ ct4)
    (h7 : cx1 + cx2 + (col (ouT c 3 0) + col (ouT c 3 1)) ≤ ct3)
    (h8 : col (trT c 0) + cx2 + (col (ouT c 1 0) + col (ouT c 1 1)) ≤ ct1)
    (h9 : col (trT c 0) + cx1 + (col (ouT c 0 0) + col (ouT c 0 1)) ≤ ct0) :
    ∑ x3 ∈ range (cx3 + 1), ((x3 : ℝ) + 1) * ∑ k2 ∈ range (ct2 + 1),
      ∑ x2 ∈ range (cx2 + 1), ((x2 : ℝ) + 1) * ∑ k5 ∈ range (ct5 + 1),
      ∑ x1 ∈ range (cx1 + 1), ((x1 : ℝ) + 1) * ∑ k4 ∈ range (ct4 + 1),
      ∑ k3 ∈ range (ct3 + 1), ∑ k1 ∈ range (ct1 + 1), ∑ k0 ∈ range (ct0 + 1),
      (U4 c).ev (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update col
        (trT c 3) x3) (teT c 2) k2) (trT c 2) x2) (teT c 5) k5) (trT c 1) x1) (teT c 4) k4)
        (teT c 3) k3) (teT c 1) k1) (teT c 0) k0) = (NL c).ev col := by
  have lG := chk_legsG c
  have lL := chk_legsL c
  have hP1 : ∀ col', (P1 c).ev col' = (N3 c).ev col' := fun col' => by
    rw [P1, prep, ev_addParities col' _ _ (chk_P1 c).2, ev_flipNodes col' _ _ (chk_P1 c).1]
  have hP2 : ∀ col', (P2 c).ev col' = (M1 c).ev col' := fun col' => by
    rw [P2, prep, ev_addParities col' _ _ (chk_P2 c).2, ev_flipNodes col' _ _ (chk_P2 c).1]
  have hP3 : ∀ col', (P3 c).ev col' = (M2 c).ev col' := fun col' => by
    rw [P3, prep, ev_addParities col' _ _ (chk_P3 c).2, ev_flipNodes col' _ _ (chk_P3 c).1]
  -- the third closing: triangle `B ∪ {a_3}`
  have hA3 : ∑ l ∈ univ.erase (loop3N c).2.2, col ((P3 c).face ((P3 c).leg (loop3N c).1 l)) ≤ cx3 := by
    rw [sum_erase_perm4 (chk_L3 c).1 _ _ _ lL.2.2 col]; omega
  have hk3 : cx3 + ∑ l ∈ univ.erase (loop3N c).2.2, col ((P3 c).face ((P3 c).leg (loop3N c).1 l)) ≤
      ct2 := by
    rw [sum_erase_perm4 (chk_L3 c).1 _ _ _ lL.2.2 col]; omega
  rw [NL, ev_elimN col 4 _ (chk_L3 c).2, L3, ← ev_loop_of (chk_L3 c).1 col cx3 ct2 hA3 hk3]
  refine sum_congr rfl fun x3 hx3 => congrArg _ (sum_congr rfl fun k2 _ => ?_)
  rw [mem_range] at hx3
  generalize hcol1 : Function.update (Function.update col (trT c 3) x3) (teT c 2) k2 = col1
  have f1o : ∀ j e, col1 (ouT c j e) = col (ouT c j e) := fun j e => by rw [← hcol1]; fs []
  have f1a : col1 (trT c 3) = x3 := by rw [← hcol1]; fs []
  -- the second closing: triangle `B ∪ {a_2}`
  have hA2 : ∑ l ∈ univ.erase (loop2N c).2.2, col1 ((P2 c).face ((P2 c).leg (loop2N c).1 l)) ≤
      cx2 := by
    rw [sum_erase_perm4 (chk_L2 c).1 _ _ _ lL.2.1 col1, f1a, f1o, f1o]; omega
  have hk2 : cx2 + ∑ l ∈ univ.erase (loop2N c).2.2, col1 ((P2 c).face ((P2 c).leg (loop2N c).1 l)) ≤
      ct5 := by
    rw [sum_erase_perm4 (chk_L2 c).1 _ _ _ lL.2.1 col1, f1a, f1o, f1o]; omega
  rw [hP3, M2, ev_elimN col1 4 _ (chk_L2 c).2, L2, ← ev_loop_of (chk_L2 c).1 col1 cx2 ct5 hA2 hk2]
  refine sum_congr rfl fun x2 hx2 => congrArg _ (sum_congr rfl fun k5 _ => ?_)
  rw [mem_range] at hx2
  generalize hcol2 : Function.update (Function.update col1 (trT c 2) x2) (teT c 5) k5 = col2
  have f2o : ∀ j e, col2 (ouT c j e) = col (ouT c j e) := fun j e => by rw [← hcol2]; fs [f1o]
  have f2a : col2 (trT c 3) = x3 := by rw [← hcol2]; fs [f1a]
  have f2b : col2 (trT c 2) = x2 := by rw [← hcol2]; fs []
  have f2c : col2 (trT c 0) = col (trT c 0) := by
    rw [← hcol2]; fs []
    rw [← hcol1]; fs []
  -- the first closing: triangle `B ∪ {a_1}`
  have hA1 : ∑ l ∈ univ.erase (loop1N c).2.2, col2 ((P1 c).face ((P1 c).leg (loop1N c).1 l)) ≤
      cx1 := by
    rw [sum_erase_perm4 (chk_L1 c).1 _ _ _ lL.1 col2, f2a, f2o, f2o]; omega
  have hk1 : cx1 + ∑ l ∈ univ.erase (loop1N c).2.2, col2 ((P1 c).face ((P1 c).leg (loop1N c).1 l)) ≤
      ct4 := by
    rw [sum_erase_perm4 (chk_L1 c).1 _ _ _ lL.1 col2, f2a, f2o, f2o]; omega
  rw [hP2, M1, ev_elimN col2 4 _ (chk_L1 c).2, L1, ← ev_loop_of (chk_L1 c).1 col2 cx1 ct4 hA1 hk1]
  refine sum_congr rfl fun x1 hx1 => congrArg _ (sum_congr rfl fun k4 _ => ?_)
  rw [mem_range] at hx1
  generalize hcol3 : Function.update (Function.update col2 (trT c 1) x1) (teT c 4) k4 = col3
  have f3o : ∀ j e, col3 (ouT c j e) = col (ouT c j e) := fun j e => by rw [← hcol3]; fs [f2o]
  have f3a : col3 (trT c 1) = x1 := by rw [← hcol3]; fs []
  have f3b : col3 (trT c 2) = x2 := by rw [← hcol3]; fs [f2b]
  have f3c : col3 (trT c 0) = col (trT c 0) := by rw [← hcol3]; fs [f2c]
  -- the three gluings
  have hb3 : ∑ l, col3 ((N2 c).face ((N2 c).leg (nd c 0 3) l)) ≤ ct3 := by
    rw [sum_perm4 _ _ _ _ _ lG.2.2 col3, f3a, f3b, f3o, f3o]; omega
  rw [hP1, N3, ev_elimN col3 4 _ (chk_G3 c).2, G3, ← ev_glue_of (chk_G3 c).1 col3 ct3 hb3]
  refine sum_congr rfl fun k3 _ => ?_
  generalize hcol4 : Function.update col3 (teT c 3) k3 = col4
  have f4o : ∀ j e, col4 (ouT c j e) = col (ouT c j e) := fun j e => by rw [← hcol4]; fs [f3o]
  have f4a : col4 (trT c 1) = x1 := by rw [← hcol4]; fs [f3a]
  have f4b : col4 (trT c 2) = x2 := by rw [← hcol4]; fs [f3b]
  have f4c : col4 (trT c 0) = col (trT c 0) := by rw [← hcol4]; fs [f3c]
  have hb2 : ∑ l, col4 ((N1 c).face ((N1 c).leg (nd c 1 3) l)) ≤ ct1 := by
    rw [sum_perm4 _ _ _ _ _ lG.2.1 col4, f4c, f4b, f4o, f4o]; omega
  rw [N2, ev_elimN col4 4 _ (chk_G2 c).2, G2, ← ev_glue_of (chk_G2 c).1 col4 ct1 hb2]
  refine sum_congr rfl fun k1 _ => ?_
  generalize hcol5 : Function.update col4 (teT c 1) k1 = col5
  have f5o : ∀ j e, col5 (ouT c j e) = col (ouT c j e) := fun j e => by rw [← hcol5]; fs [f4o]
  have f5a : col5 (trT c 1) = x1 := by rw [← hcol5]; fs [f4a]
  have f5c : col5 (trT c 0) = col (trT c 0) := by rw [← hcol5]; fs [f4c]
  have hb1 : ∑ l, col5 ((U4 c).face ((U4 c).leg (nd c 2 3) l)) ≤ ct0 := by
    rw [sum_perm4 _ _ _ _ _ lG.1 col5, f5c, f5a, f5o, f5o]; omega
  rw [N1, ev_elimN col5 4 _ (chk_G1 c).2, G1, ← ev_glue_of (chk_G1 c).1 col5 ct0 hb1]

/-- **The reduced network of the four-simplex side is the one of the two-simplex side times the
dimension of the free triangle `B ∪ {a_0}`.** -/
theorem ev_NL_eq_QB (c : Fin 15) (col : Fin 64 → ℕ) :
    (NL c).ev col = ((col (trT c 0) : ℝ) + 1) * (QB c).ev col := by
  obtain ⟨hl, hk, hn, hc, hf⟩ := chk_free c
  rw [ev_killE (NL c) col (freeE c) hl hk hn hc, hf]
  congr 1
  show (NK c).ev col = (QB c).ev col
  rw [← ev_rel_of (chk_rel c) col, NG, ev_addParities col _ _ (chk_gauge c).2, ev_flipVars,
    ev_flipNodes col _ _ (chk_gauge c).1]

/-! ## The two-simplex side -/

set_option maxRecDepth 100000 in
/-- The four triangles of `A` at the gluing node of the two-simplex side. -/
lemma chk_legsB : ∀ c : Fin 15,
    (List.ofFn fun l => (UB c).face ((UB c).leg (ndB c 0 1) l)).Perm
      [faT c 0, faT c 1, faT c 2, faT c 3] := by
  decide +kernel

/-- **The two-simplex side of case `c` reduces to `QB c`**: summed over the colour of the
tetrahedron `A` the union of the two vertex networks evaluates to the reduced network, once the
cutoff exceeds the triangle inequality. -/
theorem sumB_eq_ev_QB (c : Fin 15) (col : Fin 64 → ℕ) (cut : ℕ)
    (h : col (faT c 0) + col (faT c 1) + col (faT c 2) + col (faT c 3) ≤ cut) :
    ∑ k ∈ range (cut + 1), (UB c).ev (Function.update col (sgT c) k) = (QB c).ev col := by
  have hb : ∑ l, col ((UB c).face ((UB c).leg (ndB c 0 1) l)) ≤ cut := by
    rw [sum_perm4 _ _ _ _ _ (chk_legsB c) col]; exact h
  rw [QB, ev_elimN col 4 _ (chk_B c).2, GB, ← ev_glue_of (chk_B c).1 col cut hb]
