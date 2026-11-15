import Lightlike.SpinFoam.MoveBlocks

/-!
# The 1-5 move of the Ooguri model: the local identity

The 1-5 Pachner move replaces the one 4-simplex `A = W ∖ {b}` (`W` has six vertices, `b` is the
new vertex) by the five 4-simplices `W ∖ {a}`, `a ∈ A`, around `b`. The new faces are the ten
triangles `{b} ∪ {a_i, a_j}` and the ten tetrahedra `{b} ∪ {a_i, a_j, a_k}`.

Positions of `W` are `Fin 6`. Case `c : Fin 6` is the position of `b`; `aposT c` are the
positions of `A`, in increasing order.

* The five-simplex side `U5 c` is the union of the vertex networks of `W ∖ {a_k}` (blocks
  `0..4`). Four gluings (the tetrahedra `{b} ∪ {a_0, a_1, a_2}`, `{b} ∪ {a_0, a_1, a_3}`,
  `{b} ∪ {a_0, a_2, a_3}`, `{b} ∪ {a_1, a_2, a_3}`, joining blocks `3, 2, 1, 0` to block `4`)
  and six strand closings (the triangles `{b} ∪ {a_i, a_j}` with `i ≥ 1`) reduce it to `NL c`.
  What is left are four free closed strands on the triangles `{b, a_0, a_j}`; each multiplies
  the network by that triangle's dimension.
* The one-simplex side `QB c` is the vertex network of `W ∖ {b}`.
* A gauge transformation of `NL c` without the free strands is a relabelling of `QB c`.

All hypotheses of the steps are checked by the kernel (`decide +kernel`).
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam

open SNet MoveBlocks

namespace Move15

/-- Edges of a union of five vertex networks. -/
abbrev E5 := EB 5

/-- Nodes of a union of five vertex networks. -/
abbrev N5 := NB 5

/-! ## Tables -/

/-- The positions of `A` (five) for the case `c`. -/
def aposT : Fin 6 → Fin 5 → Fin 6 :=
  ![![1, 2, 3, 4, 5], ![0, 2, 3, 4, 5], ![0, 1, 3, 4, 5], ![0, 1, 2, 4, 5], ![0, 1, 2, 3, 5], ![0, 1, 2, 3, 4]]
/-- Loop 1: the node flips, the node parities the nodes `n₁ n₂` and the leg. -/
def pre1F : Fin 6 → List N5 :=
  ![[(0, 3)], [(0, 3)], [(0, 3)], [(0, 3)], [(3, 0)], [(3, 0)]]
/-- Loop 1: the nodes whose parity is flipped before the loop. -/
def pre1P : Fin 6 → List N5 :=
  ![[], [], [], [], [], []]
/-- Loop 1: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop1N : Fin 6 → N5 × N5 × Fin 4 :=
  ![((0, 3), (3, 1), 3), ((0, 3), (3, 0), 3), ((0, 3), (3, 0), 3), ((0, 3), (3, 0), 3), ((0, 2), (3, 0), 3), ((0, 2), (3, 0), 2)]
/-- Loop 2: the node flips, the node parities the nodes `n₁ n₂` and the leg. -/
def pre2F : Fin 6 → List N5 :=
  ![[(2, 1)], [(2, 0)], [(2, 0)], [(0, 1)], [(0, 1)], [(0, 1)]]
/-- Loop 2: the nodes whose parity is flipped before the loop. -/
def pre2P : Fin 6 → List N5 :=
  ![[], [], [], [], [], []]
/-- Loop 2: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop2N : Fin 6 → N5 × N5 × Fin 4 :=
  ![((0, 2), (2, 1), 3), ((0, 2), (2, 0), 3), ((0, 2), (2, 0), 3), ((0, 1), (2, 0), 3), ((0, 1), (2, 0), 3), ((0, 1), (2, 0), 2)]
/-- Loop 3: the node flips, the node parities the nodes `n₁ n₂` and the leg. -/
def pre3F : Fin 6 → List N5 :=
  ![[(2, 3)], [(2, 3)], [(2, 3)], [(2, 3)], [(3, 2)], [(3, 2)]]
/-- Loop 3: the nodes whose parity is flipped before the loop. -/
def pre3P : Fin 6 → List N5 :=
  ![[], [], [], [], [], []]
/-- Loop 3: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop3N : Fin 6 → N5 × N5 × Fin 4 :=
  ![((2, 3), (3, 3), 1), ((2, 3), (3, 3), 0), ((2, 3), (3, 3), 0), ((2, 3), (3, 2), 0), ((2, 2), (3, 2), 0), ((2, 2), (3, 2), 0)]
/-- Loop 4: the node flips, the node parities the nodes `n₁ n₂` and the leg. -/
def pre4F : Fin 6 → List N5 :=
  ![[(0, 1)], [(0, 1)], [(1, 0)], [(1, 0)], [(1, 0)], [(1, 0)]]
/-- Loop 4: the nodes whose parity is flipped before the loop. -/
def pre4P : Fin 6 → List N5 :=
  ![[], [], [], [], [], []]
/-- Loop 4: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop4N : Fin 6 → N5 × N5 × Fin 4 :=
  ![((0, 1), (1, 1), 3), ((0, 1), (1, 0), 3), ((0, 0), (1, 0), 3), ((0, 0), (1, 0), 3), ((0, 0), (1, 0), 3), ((0, 0), (1, 0), 2)]
/-- Loop 5: the node flips, the node parities the nodes `n₁ n₂` and the leg. -/
def pre5F : Fin 6 → List N5 :=
  ![[(1, 3)], [(1, 3)], [(1, 3)], [(1, 3)], [(3, 1)], [(3, 1)]]
/-- Loop 5: the nodes whose parity is flipped before the loop. -/
def pre5P : Fin 6 → List N5 :=
  ![[], [], [], [], [], []]
/-- Loop 5: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop5N : Fin 6 → N5 × N5 × Fin 4 :=
  ![((1, 3), (3, 2), 1), ((1, 3), (3, 2), 0), ((1, 3), (3, 1), 0), ((1, 3), (3, 1), 0), ((1, 2), (3, 1), 0), ((1, 2), (3, 1), 0)]
/-- Loop 6: the node flips, the node parities the nodes `n₁ n₂` and the leg. -/
def pre6F : Fin 6 → List N5 :=
  ![[(2, 2)], [(2, 2)], [(2, 1)], [(1, 1)], [(1, 1)], [(1, 1)]]
/-- Loop 6: the nodes whose parity is flipped before the loop. -/
def pre6P : Fin 6 → List N5 :=
  ![[], [], [], [], [], []]
/-- Loop 6: the nodes `n₁ n₂` that are joined and the leg that is closed. -/
def loop6N : Fin 6 → N5 × N5 × Fin 4 :=
  ![((1, 2), (2, 2), 1), ((1, 2), (2, 2), 0), ((1, 2), (2, 1), 0), ((1, 1), (2, 1), 0), ((1, 1), (2, 1), 0), ((1, 1), (2, 1), 0)]
/-- The four free edges of the reduced network, on the triangles through `a_0` (in the order of `trT`). -/
def freeE : Fin 6 → Fin 4 → E5 :=
  ![![(2, 8), (1, 8), (1, 4), (1, 6)], ![(2, 8), (1, 8), (1, 4), (1, 6)], ![(2, 8), (1, 8), (1, 4), (1, 6)], ![(2, 8), (1, 8), (1, 7), (1, 9)], ![(2, 4), (1, 4), (1, 7), (1, 5)], ![(2, 6), (1, 6), (1, 9), (1, 5)]]
/-- The nodes of the reduced left side that are flipped. -/
def gNT : Fin 6 → List N5 :=
  ![[(3, 0), (2, 0), (1, 0), (0, 0)], [(3, 1), (2, 1), (1, 1), (0, 0)], [(3, 2), (2, 2), (1, 1), (0, 1)], [(3, 3), (2, 2), (1, 2), (0, 2)], [(3, 3), (2, 3), (1, 3), (0, 3)], [(3, 4), (2, 4), (1, 4), (0, 4)]]
/-- The edges of the reduced left side that are glued. -/
def gET : Fin 6 → List E5 :=
  ![[(3, 1), (2, 1), (2, 3), (1, 1), (1, 3), (1, 0), (0, 1), (0, 3), (0, 0), (0, 2)], [(3, 7), (2, 7), (2, 9), (1, 7), (1, 9), (1, 5), (0, 1), (0, 3), (0, 0), (0, 2)], [(3, 4), (2, 4), (2, 6), (1, 7), (1, 9), (1, 5), (0, 7), (0, 9), (0, 5)], [(3, 8), (2, 4), (2, 6), (1, 4), (1, 6), (0, 4), (0, 6), (0, 0)], [(3, 8), (2, 8), (1, 8), (1, 9), (0, 8), (0, 9)], [(2, 4), (1, 4), (0, 4), (0, 1)]]
/-- The nodes of the reduced left side whose parity is flipped. -/
def gPT : Fin 6 → List N5 :=
  ![[(3, 0), (1, 0)], [(3, 1), (1, 1), (0, 0)], [(3, 2)], [(3, 3), (2, 2), (1, 2), (0, 2)], [], [(3, 4), (2, 4), (1, 4), (0, 4)]]
/-- The vertex `B` of case `c`, as a bitmask. -/
def bmT : Fin 6 → Fin 64 :=
  ![1, 2, 4, 8, 16, 32]
/-- The inner triangles `B ∪ {a_i, a_j}` (pairs in lexicographic order), as bitmasks. -/
def trT : Fin 6 → Fin 10 → Fin 64 :=
  ![![7, 11, 19, 35, 13, 21, 37, 25, 41, 49], ![7, 11, 19, 35, 14, 22, 38, 26, 42, 50], ![7, 13, 21, 37, 14, 22, 38, 28, 44, 52], ![11, 13, 25, 41, 14, 26, 42, 28, 44, 56], ![19, 21, 25, 49, 22, 26, 50, 28, 52, 56], ![35, 37, 41, 49, 38, 42, 50, 44, 52, 56]]
/-- The inner tetrahedra `B ∪ {a_i, a_j, a_k}` (triples in lexicographic order), as bitmasks. -/
def teT : Fin 6 → Fin 10 → Fin 64 :=
  ![![15, 23, 39, 27, 43, 51, 29, 45, 53, 57], ![15, 23, 39, 27, 43, 51, 30, 46, 54, 58], ![15, 23, 39, 29, 45, 53, 30, 46, 54, 60], ![15, 27, 43, 29, 45, 57, 30, 46, 58, 60], ![23, 27, 51, 29, 53, 57, 30, 54, 58, 60], ![39, 43, 51, 45, 53, 57, 46, 54, 58, 60]]
/-- The outer triangles `{a_i, a_j, a_k}` (triples in lexicographic order), as bitmasks. -/
def otT : Fin 6 → Fin 10 → Fin 64 :=
  ![![14, 22, 38, 26, 42, 50, 28, 44, 52, 56], ![13, 21, 37, 25, 41, 49, 28, 44, 52, 56], ![11, 19, 35, 25, 41, 49, 26, 42, 50, 56], ![7, 19, 35, 21, 37, 49, 22, 38, 50, 52], ![7, 11, 35, 13, 37, 41, 14, 38, 42, 44], ![7, 11, 19, 13, 21, 25, 14, 22, 26, 28]]

/-! ## The chain of steps -/

/-- The five-simplex side of case `c`: the vertex networks of `W ∖ {a_k}` as blocks `k`. -/
def U5 (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  union fun k => vnet (fcB (aposT c k)) (ttB (aposT c k))

/-- The node of block `k` opposite the vertex of block `k'`: its tetrahedron misses `a_k` and
`a_k'`. -/
def nd (c : Fin 6) (k k' : Fin 5) : N5 := (k, Move33.posT (aposT c k) (aposT c k'))

/-- Gluing the two nodes of the tetrahedron `{b} ∪ {a_0, a_1, a_2}`. -/
def G1 (c : Fin 6) : SNet (Fin 64) E5 N5 := (U5 c).glue (nd c 3 4) (nd c 4 3)

/-- Step 1 with its constraints eliminated. -/
def N1 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (G1 c)

/-- Gluing the two nodes of the tetrahedron `{b} ∪ {a_0, a_1, a_3}`. -/
def G2 (c : Fin 6) : SNet (Fin 64) E5 N5 := (N1 c).glue (nd c 2 4) (nd c 4 2)

/-- Step 2 with its constraints eliminated. -/
def N2 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (G2 c)

/-- Gluing the two nodes of the tetrahedron `{b} ∪ {a_0, a_2, a_3}`. -/
def G3 (c : Fin 6) : SNet (Fin 64) E5 N5 := (N2 c).glue (nd c 1 4) (nd c 4 1)

/-- Step 3 with its constraints eliminated. -/
def N3 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (G3 c)

/-- Gluing the two nodes of the tetrahedron `{b} ∪ {a_1, a_2, a_3}`. -/
def G4 (c : Fin 6) : SNet (Fin 64) E5 N5 := (N3 c).glue (nd c 0 4) (nd c 4 0)

/-- Step 4 with its constraints eliminated. -/
def N4 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (G4 c)

/-- The preparation of a strand closing: node flips, then parities. -/
def prep (N : SNet (Fin 64) E5 N5) (f p : List N5) : SNet (Fin 64) E5 N5 :=
  addParities (flipNodes N f) p

/-- The preparation of the first strand closing. -/
def P1 (c : Fin 6) : SNet (Fin 64) E5 N5 := prep (N4 c) (pre1F c) (pre1P c)

/-- Closing the strand of the triangle `{b} ∪ {a_1, a_2}`. -/
def L1 (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  (P1 c).loop (loop1N c).1 (loop1N c).2.1 (loop1N c).2.2

/-- The first strand closing with its constraints eliminated. -/
def M1 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (L1 c)

/-- The preparation of the second strand closing. -/
def P2 (c : Fin 6) : SNet (Fin 64) E5 N5 := prep (M1 c) (pre2F c) (pre2P c)

/-- Closing the strand of the triangle `{b} ∪ {a_1, a_3}`. -/
def L2 (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  (P2 c).loop (loop2N c).1 (loop2N c).2.1 (loop2N c).2.2

/-- The second strand closing with its constraints eliminated. -/
def M2 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (L2 c)

/-- The preparation of the third strand closing. -/
def P3 (c : Fin 6) : SNet (Fin 64) E5 N5 := prep (M2 c) (pre3F c) (pre3P c)

/-- Closing the strand of the triangle `{b} ∪ {a_1, a_4}`. -/
def L3 (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  (P3 c).loop (loop3N c).1 (loop3N c).2.1 (loop3N c).2.2

/-- The third strand closing with its constraints eliminated. -/
def M3 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (L3 c)

/-- The preparation of the fourth strand closing. -/
def P4 (c : Fin 6) : SNet (Fin 64) E5 N5 := prep (M3 c) (pre4F c) (pre4P c)

/-- Closing the strand of the triangle `{b} ∪ {a_2, a_3}`. -/
def L4 (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  (P4 c).loop (loop4N c).1 (loop4N c).2.1 (loop4N c).2.2

/-- The fourth strand closing with its constraints eliminated. -/
def M4 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (L4 c)

/-- The preparation of the fifth strand closing. -/
def P5 (c : Fin 6) : SNet (Fin 64) E5 N5 := prep (M4 c) (pre5F c) (pre5P c)

/-- Closing the strand of the triangle `{b} ∪ {a_2, a_4}`. -/
def L5 (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  (P5 c).loop (loop5N c).1 (loop5N c).2.1 (loop5N c).2.2

/-- The fifth strand closing with its constraints eliminated. -/
def M5 (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (L5 c)

/-- The preparation of the sixth strand closing. -/
def P6 (c : Fin 6) : SNet (Fin 64) E5 N5 := prep (M5 c) (pre6F c) (pre6P c)

/-- Closing the strand of the triangle `{b} ∪ {a_3, a_4}`. -/
def L6 (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  (P6 c).loop (loop6N c).1 (loop6N c).2.1 (loop6N c).2.2

/-- **The reduced five-simplex side** of case `c`. -/
def NL (c : Fin 6) : SNet (Fin 64) E5 N5 := elimN 12 (L6 c)

/-- `NL c` without its first free closed strand. -/
def K1 (c : Fin 6) : SNet (Fin 64) E5 N5 := (NL c).killE (freeE c 0)

/-- `NL c` without its first two free closed strands. -/
def K2 (c : Fin 6) : SNet (Fin 64) E5 N5 := (K1 c).killE (freeE c 1)

/-- `NL c` without its first three free closed strands. -/
def K3 (c : Fin 6) : SNet (Fin 64) E5 N5 := (K2 c).killE (freeE c 2)

/-- `NL c` without its four free closed strands. -/
def NK (c : Fin 6) : SNet (Fin 64) E5 N5 := (K3 c).killE (freeE c 3)

/-- The gauge transformation of `NK c` that matches `QB c`. -/
def NG (c : Fin 6) : SNet (Fin 64) E5 N5 :=
  addParities (flipVars (flipNodes (NK c) (gNT c)) (gET c)) (gPT c)

/-- **The one-simplex side** of case `c`: the vertex network of `W ∖ {b}`. -/
def QB (c : Fin 6) : SNet (Fin 64) (EB 1) (NB 1) :=
  union fun _ => vnet (fcB c) (ttB c)

/-! ## Checked steps -/

set_option maxRecDepth 100000 in
lemma chk_G1 : ∀ c : Fin 6,
    GlueOK (U5 c) 3 (aposT c 3) (nd c 3 4) (nd c 4 3) (teT c 0) ∧ elimOK 12 (G1 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_G2 : ∀ c : Fin 6,
    GlueOK (N1 c) 2 (aposT c 2) (nd c 2 4) (nd c 4 2) (teT c 1) ∧ elimOK 12 (G2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_G3 : ∀ c : Fin 6,
    GlueOK (N2 c) 1 (aposT c 1) (nd c 1 4) (nd c 4 1) (teT c 3) ∧ elimOK 12 (G3 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_G4 : ∀ c : Fin 6,
    GlueOK (N3 c) 0 (aposT c 0) (nd c 0 4) (nd c 4 0) (teT c 6) ∧ elimOK 12 (G4 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P1 : ∀ c : Fin 6, flipNodesOK (N4 c) (pre1F c) = true ∧
    addParitiesOK (flipNodes (N4 c) (pre1F c)) (pre1P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L1 : ∀ c : Fin 6,
    LoopOK (P1 c) (loop1N c).1 (loop1N c).2.1 (loop1N c).2.2 (teT c 7) (trT c 4) ∧
      elimOK 12 (L1 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P2 : ∀ c : Fin 6, flipNodesOK (M1 c) (pre2F c) = true ∧
    addParitiesOK (flipNodes (M1 c) (pre2F c)) (pre2P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L2 : ∀ c : Fin 6,
    LoopOK (P2 c) (loop2N c).1 (loop2N c).2.1 (loop2N c).2.2 (teT c 8) (trT c 5) ∧
      elimOK 12 (L2 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P3 : ∀ c : Fin 6, flipNodesOK (M2 c) (pre3F c) = true ∧
    addParitiesOK (flipNodes (M2 c) (pre3F c)) (pre3P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L3 : ∀ c : Fin 6,
    LoopOK (P3 c) (loop3N c).1 (loop3N c).2.1 (loop3N c).2.2 (teT c 2) (trT c 6) ∧
      elimOK 12 (L3 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P4 : ∀ c : Fin 6, flipNodesOK (M3 c) (pre4F c) = true ∧
    addParitiesOK (flipNodes (M3 c) (pre4F c)) (pre4P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L4 : ∀ c : Fin 6,
    LoopOK (P4 c) (loop4N c).1 (loop4N c).2.1 (loop4N c).2.2 (teT c 9) (trT c 7) ∧
      elimOK 12 (L4 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P5 : ∀ c : Fin 6, flipNodesOK (M4 c) (pre5F c) = true ∧
    addParitiesOK (flipNodes (M4 c) (pre5F c)) (pre5P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L5 : ∀ c : Fin 6,
    LoopOK (P5 c) (loop5N c).1 (loop5N c).2.1 (loop5N c).2.2 (teT c 4) (trT c 8) ∧
      elimOK 12 (L5 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_P6 : ∀ c : Fin 6, flipNodesOK (M5 c) (pre6F c) = true ∧
    addParitiesOK (flipNodes (M5 c) (pre6F c)) (pre6P c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_L6 : ∀ c : Fin 6,
    LoopOK (P6 c) (loop6N c).1 (loop6N c).2.1 (loop6N c).2.2 (teT c 5) (trT c 9) ∧
      elimOK 12 (L6 c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_free0 : ∀ c : Fin 6, (NL c).eLive (freeE c 0) = true ∧
    (NL c).kap (freeE c 0) = false ∧
    (∀ n, (NL c).nLive n = true → ∀ l, (NL c).leg n l ≠ freeE c 0) ∧
    (∀ x ∈ (NL c).cons, x.1 ≠ freeE c 0 ∧ x.2.1 ≠ freeE c 0) ∧
    (NL c).face (freeE c 0) = trT c 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_free1 : ∀ c : Fin 6, (K1 c).eLive (freeE c 1) = true ∧
    (K1 c).kap (freeE c 1) = false ∧
    (∀ n, (K1 c).nLive n = true → ∀ l, (K1 c).leg n l ≠ freeE c 1) ∧
    (∀ x ∈ (K1 c).cons, x.1 ≠ freeE c 1 ∧ x.2.1 ≠ freeE c 1) ∧
    (K1 c).face (freeE c 1) = trT c 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_free2 : ∀ c : Fin 6, (K2 c).eLive (freeE c 2) = true ∧
    (K2 c).kap (freeE c 2) = false ∧
    (∀ n, (K2 c).nLive n = true → ∀ l, (K2 c).leg n l ≠ freeE c 2) ∧
    (∀ x ∈ (K2 c).cons, x.1 ≠ freeE c 2 ∧ x.2.1 ≠ freeE c 2) ∧
    (K2 c).face (freeE c 2) = trT c 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_free3 : ∀ c : Fin 6, (K3 c).eLive (freeE c 3) = true ∧
    (K3 c).kap (freeE c 3) = false ∧
    (∀ n, (K3 c).nLive n = true → ∀ l, (K3 c).leg n l ≠ freeE c 3) ∧
    (∀ x ∈ (K3 c).cons, x.1 ≠ freeE c 3 ∧ x.2.1 ≠ freeE c 3) ∧
    (K3 c).face (freeE c 3) = trT c 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_gauge : ∀ c : Fin 6, flipNodesOK (NK c) (gNT c) = true ∧
    addParitiesOK (flipVars (flipNodes (NK c) (gNT c)) (gET c)) (gPT c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chk_rel : ∀ c : Fin 6, RelOK (NG c) (QB c) := by
  decide +kernel
/-! ## Faces at the glued and closed nodes -/

set_option maxRecDepth 100000 in
/-- The four triangles of the tetrahedron at each gluing node, as a list up to order. -/
lemma chk_legsG : ∀ c : Fin 6,
    (List.ofFn fun l => (U5 c).face ((U5 c).leg (nd c 3 4) l)).Perm
      [otT c 0, trT c 0, trT c 1, trT c 4] ∧
    (List.ofFn fun l => (N1 c).face ((N1 c).leg (nd c 2 4) l)).Perm
      [otT c 1, trT c 0, trT c 2, trT c 5] ∧
    (List.ofFn fun l => (N2 c).face ((N2 c).leg (nd c 1 4) l)).Perm
      [otT c 3, trT c 1, trT c 2, trT c 7] ∧
    (List.ofFn fun l => (N3 c).face ((N3 c).leg (nd c 0 4) l)).Perm
      [otT c 6, trT c 4, trT c 5, trT c 7] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The four triangles of the tetrahedron at each loop node: the strand face first. -/
lemma chk_legsL : ∀ c : Fin 6,
    (List.ofFn fun l => (P1 c).face ((P1 c).leg (loop1N c).1 l)).Perm
      [trT c 4, otT c 7, trT c 6, trT c 8] ∧
    (List.ofFn fun l => (P2 c).face ((P2 c).leg (loop2N c).1 l)).Perm
      [trT c 5, otT c 8, trT c 6, trT c 9] ∧
    (List.ofFn fun l => (P3 c).face ((P3 c).leg (loop3N c).1 l)).Perm
      [trT c 6, otT c 2, trT c 0, trT c 3] ∧
    (List.ofFn fun l => (P4 c).face ((P4 c).leg (loop4N c).1 l)).Perm
      [trT c 7, otT c 9, trT c 8, trT c 9] ∧
    (List.ofFn fun l => (P5 c).face ((P5 c).leg (loop5N c).1 l)).Perm
      [trT c 8, otT c 4, trT c 1, trT c 3] ∧
    (List.ofFn fun l => (P6 c).face ((P6 c).leg (loop6N c).1 l)).Perm
      [trT c 9, otT c 5, trT c 2, trT c 3] := by
  decide +kernel

/-! ## Distinctness of the faces of the move -/

lemma trT_eq_iff : ∀ c i j, trT c i = trT c j ↔ i = j := by decide +kernel
lemma trT_ne_teT : ∀ c i j, trT c i ≠ teT c j := by decide +kernel
lemma teT_ne_trT : ∀ c i j, teT c j ≠ trT c i := by decide +kernel
lemma trT_ne_otT : ∀ c i j, trT c i ≠ otT c j := by decide +kernel
lemma otT_ne_trT : ∀ c i j, otT c j ≠ trT c i := by decide +kernel
lemma teT_ne_otT : ∀ c i j, teT c i ≠ otT c j := by decide +kernel
lemma otT_ne_teT : ∀ c i j, otT c j ≠ teT c i := by decide +kernel

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
lemma sum_erase_perm4 {S : SNet (Fin 64) E5 N5} {n₁ n₂ : N5} {lA : Fin 4} {t fA : Fin 64}
    (h : LoopOK S n₁ n₂ lA t fA) (x y z : Fin 64)
    (hp : (List.ofFn fun l => S.face (S.leg n₁ l)).Perm [fA, x, y, z]) (g : Fin 64 → ℕ) :
    ∑ l ∈ univ.erase lA, g (S.face (S.leg n₁ l)) = g x + g y + g z := by
  obtain ⟨-, -, -, -, -, -, -, -, h3, -⟩ := h
  have h1 := sum_perm4 _ _ _ _ _ hp g
  have h2 := add_sum_erase univ (fun l => g (S.face (S.leg n₁ l))) (mem_univ lA)
  simp only [h3] at h2
  omega

/-! ## The five-simplex side reduces to `NL c` -/

/-- Simplifying values of nested updates at the faces of the move. -/
local syntax "fs" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
local macro_rules
  | `(tactic| fs [$ts,*]) =>
    `(tactic| simp [Function.update_apply, trT_eq_iff, trT_ne_teT, teT_ne_trT, trT_ne_otT,
      otT_ne_trT, teT_ne_otT, otT_ne_teT, $ts,*])
set_option maxHeartbeats 4000000 in
/-- **The five-simplex side of case `c` reduces to `NL c`**: summed over the colours `x_i` of the
six inner triangles `{b} ∪ {a_i, a_j}` with `i ≥ 1` (weights `x + 1`) and the colours of the ten
inner tetrahedra, the union of the five vertex networks evaluates to the reduced network, once
the cutoffs exceed the triangle inequalities. The four triangles `{b} ∪ {a_0, a_j}` and the ten
outer triangles keep the colouring `col`. -/
theorem lhs_eq_ev_NL15 (c : Fin 6) (col : Fin 64 → ℕ)
    (cx6 ct6 cx5 ct5 cx4 ct4 cx3 ct3 cx2 ct2 cx1 ct1 cg4 cg3 cg2 cg1 : ℕ)
    (hA6 : col (otT c 5) + col (trT c 2) + col (trT c 3) ≤ cx6)
    (hk6 : cx6 + (col (otT c 5) + col (trT c 2) + col (trT c 3)) ≤ ct6)
    (hA5 : col (otT c 4) + col (trT c 1) + col (trT c 3) ≤ cx5)
    (hk5 : cx5 + (col (otT c 4) + col (trT c 1) + col (trT c 3)) ≤ ct5)
    (hA4 : col (otT c 9) + cx5 + cx6 ≤ cx4)
    (hk4 : cx4 + (col (otT c 9) + cx5 + cx6) ≤ ct4)
    (hA3 : col (otT c 2) + col (trT c 0) + col (trT c 3) ≤ cx3)
    (hk3 : cx3 + (col (otT c 2) + col (trT c 0) + col (trT c 3)) ≤ ct3)
    (hA2 : col (otT c 8) + cx3 + cx6 ≤ cx2)
    (hk2 : cx2 + (col (otT c 8) + cx3 + cx6) ≤ ct2)
    (hA1 : col (otT c 7) + cx3 + cx5 ≤ cx1)
    (hk1 : cx1 + (col (otT c 7) + cx3 + cx5) ≤ ct1)
    (hg4 : col (otT c 6) + cx1 + cx2 + cx4 ≤ cg4)
    (hg3 : col (otT c 3) + col (trT c 1) + col (trT c 2) + cx4 ≤ cg3)
    (hg2 : col (otT c 1) + col (trT c 0) + col (trT c 2) + cx2 ≤ cg2)
    (hg1 : col (otT c 0) + col (trT c 0) + col (trT c 1) + cx1 ≤ cg1) :
    ∑ x6 ∈ range (cx6 + 1), ((x6 : ℝ) + 1) * ∑ k6 ∈ range (ct6 + 1),
      ∑ x5 ∈ range (cx5 + 1), ((x5 : ℝ) + 1) * ∑ k5 ∈ range (ct5 + 1),
      ∑ x4 ∈ range (cx4 + 1), ((x4 : ℝ) + 1) * ∑ k4 ∈ range (ct4 + 1),
      ∑ x3 ∈ range (cx3 + 1), ((x3 : ℝ) + 1) * ∑ k3 ∈ range (ct3 + 1),
      ∑ x2 ∈ range (cx2 + 1), ((x2 : ℝ) + 1) * ∑ k2 ∈ range (ct2 + 1),
      ∑ x1 ∈ range (cx1 + 1), ((x1 : ℝ) + 1) * ∑ k1 ∈ range (ct1 + 1),
      ∑ g4 ∈ range (cg4 + 1),
      ∑ g3 ∈ range (cg3 + 1),
      ∑ g2 ∈ range (cg2 + 1),
      ∑ g1 ∈ range (cg1 + 1),
      (U5 c).ev (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update col (trT c 9) x6) (teT c 5) k6) (trT c 8) x5) (teT c 4) k5) (trT c 7) x4) (teT c 9) k4) (trT c 6) x3) (teT c 2) k3) (trT c 5) x2) (teT c 8) k2) (trT c 4) x1) (teT c 7) k1) (teT c 6) g4) (teT c 3) g3) (teT c 1) g2) (teT c 0) g1) = (NL c).ev col := by
  have lG := chk_legsG c
  have lL := chk_legsL c
  have hP1 : ∀ col', (P1 c).ev col' = (N4 c).ev col' := fun col' => by
    rw [P1, prep, ev_addParities col' _ _ (chk_P1 c).2, ev_flipNodes col' _ _ (chk_P1 c).1]
  have hP2 : ∀ col', (P2 c).ev col' = (M1 c).ev col' := fun col' => by
    rw [P2, prep, ev_addParities col' _ _ (chk_P2 c).2, ev_flipNodes col' _ _ (chk_P2 c).1]
  have hP3 : ∀ col', (P3 c).ev col' = (M2 c).ev col' := fun col' => by
    rw [P3, prep, ev_addParities col' _ _ (chk_P3 c).2, ev_flipNodes col' _ _ (chk_P3 c).1]
  have hP4 : ∀ col', (P4 c).ev col' = (M3 c).ev col' := fun col' => by
    rw [P4, prep, ev_addParities col' _ _ (chk_P4 c).2, ev_flipNodes col' _ _ (chk_P4 c).1]
  have hP5 : ∀ col', (P5 c).ev col' = (M4 c).ev col' := fun col' => by
    rw [P5, prep, ev_addParities col' _ _ (chk_P5 c).2, ev_flipNodes col' _ _ (chk_P5 c).1]
  have hP6 : ∀ col', (P6 c).ev col' = (M5 c).ev col' := fun col' => by
    rw [P6, prep, ev_addParities col' _ _ (chk_P6 c).2, ev_flipNodes col' _ _ (chk_P6 c).1]
  -- closing the strand of the triangle `tr9`
  have hA6' : ∑ l ∈ univ.erase (loop6N c).2.2, col ((P6 c).face ((P6 c).leg (loop6N c).1 l)) ≤
      cx6 := by
    rw [sum_erase_perm4 (chk_L6 c).1 _ _ _ lL.2.2.2.2.2 col]; omega
  have hk6' : cx6 + ∑ l ∈ univ.erase (loop6N c).2.2, col ((P6 c).face ((P6 c).leg (loop6N c).1 l)) ≤
      ct6 := by
    rw [sum_erase_perm4 (chk_L6 c).1 _ _ _ lL.2.2.2.2.2 col]; omega
  rw [NL, ev_elimN col 12 _ (chk_L6 c).2, L6, ← ev_loop_of (chk_L6 c).1 col cx6 ct6 hA6' hk6']
  refine sum_congr rfl fun x6 hx6 => congrArg _ (sum_congr rfl fun k6 _ => ?_)
  rw [mem_range] at hx6
  generalize hcol1 : Function.update (Function.update col (trT c 9) x6) (teT c 5) k6 = s1
  have fo1 : ∀ j, s1 (otT c j) = col (otT c j) := fun j => by rw [← hcol1]; fs []
  have ft0_1 : s1 (trT c 0) = col (trT c 0) := by rw [← hcol1]; fs []
  have ft1_1 : s1 (trT c 1) = col (trT c 1) := by rw [← hcol1]; fs []
  have ft2_1 : s1 (trT c 2) = col (trT c 2) := by rw [← hcol1]; fs []
  have ft3_1 : s1 (trT c 3) = col (trT c 3) := by rw [← hcol1]; fs []
  have fx6_1 : s1 (trT c 9) = x6 := by rw [← hcol1]; fs []
  -- closing the strand of the triangle `tr8`
  have hA5' : ∑ l ∈ univ.erase (loop5N c).2.2, s1 ((P5 c).face ((P5 c).leg (loop5N c).1 l)) ≤
      cx5 := by
    rw [sum_erase_perm4 (chk_L5 c).1 _ _ _ lL.2.2.2.2.1 s1]; simp only [fo1, ft1_1, ft3_1]; omega
  have hk5' : cx5 + ∑ l ∈ univ.erase (loop5N c).2.2, s1 ((P5 c).face ((P5 c).leg (loop5N c).1 l)) ≤
      ct5 := by
    rw [sum_erase_perm4 (chk_L5 c).1 _ _ _ lL.2.2.2.2.1 s1]; simp only [fo1, ft1_1, ft3_1]; omega
  rw [hP6, M5, ev_elimN s1 12 _ (chk_L5 c).2, L5, ← ev_loop_of (chk_L5 c).1 s1 cx5 ct5 hA5' hk5']
  refine sum_congr rfl fun x5 hx5 => congrArg _ (sum_congr rfl fun k5 _ => ?_)
  rw [mem_range] at hx5
  generalize hcol2 : Function.update (Function.update s1 (trT c 8) x5) (teT c 4) k5 = s2
  have fo2 : ∀ j, s2 (otT c j) = col (otT c j) := fun j => by rw [← hcol2]; fs [fo1]
  have ft0_2 : s2 (trT c 0) = col (trT c 0) := by rw [← hcol2]; fs [ft0_1]
  have ft1_2 : s2 (trT c 1) = col (trT c 1) := by rw [← hcol2]; fs [ft1_1]
  have ft2_2 : s2 (trT c 2) = col (trT c 2) := by rw [← hcol2]; fs [ft2_1]
  have ft3_2 : s2 (trT c 3) = col (trT c 3) := by rw [← hcol2]; fs [ft3_1]
  have fx5_2 : s2 (trT c 8) = x5 := by rw [← hcol2]; fs []
  have fx6_2 : s2 (trT c 9) = x6 := by rw [← hcol2]; fs [fx6_1]
  -- closing the strand of the triangle `tr7`
  have hA4' : ∑ l ∈ univ.erase (loop4N c).2.2, s2 ((P4 c).face ((P4 c).leg (loop4N c).1 l)) ≤
      cx4 := by
    rw [sum_erase_perm4 (chk_L4 c).1 _ _ _ lL.2.2.2.1 s2]; simp only [fo2, fx5_2, fx6_2]; omega
  have hk4' : cx4 + ∑ l ∈ univ.erase (loop4N c).2.2, s2 ((P4 c).face ((P4 c).leg (loop4N c).1 l)) ≤
      ct4 := by
    rw [sum_erase_perm4 (chk_L4 c).1 _ _ _ lL.2.2.2.1 s2]; simp only [fo2, fx5_2, fx6_2]; omega
  rw [hP5, M4, ev_elimN s2 12 _ (chk_L4 c).2, L4, ← ev_loop_of (chk_L4 c).1 s2 cx4 ct4 hA4' hk4']
  refine sum_congr rfl fun x4 hx4 => congrArg _ (sum_congr rfl fun k4 _ => ?_)
  rw [mem_range] at hx4
  generalize hcol3 : Function.update (Function.update s2 (trT c 7) x4) (teT c 9) k4 = s3
  have fo3 : ∀ j, s3 (otT c j) = col (otT c j) := fun j => by rw [← hcol3]; fs [fo2]
  have ft0_3 : s3 (trT c 0) = col (trT c 0) := by rw [← hcol3]; fs [ft0_2]
  have ft1_3 : s3 (trT c 1) = col (trT c 1) := by rw [← hcol3]; fs [ft1_2]
  have ft2_3 : s3 (trT c 2) = col (trT c 2) := by rw [← hcol3]; fs [ft2_2]
  have ft3_3 : s3 (trT c 3) = col (trT c 3) := by rw [← hcol3]; fs [ft3_2]
  have fx4_3 : s3 (trT c 7) = x4 := by rw [← hcol3]; fs []
  have fx5_3 : s3 (trT c 8) = x5 := by rw [← hcol3]; fs [fx5_2]
  have fx6_3 : s3 (trT c 9) = x6 := by rw [← hcol3]; fs [fx6_2]
  -- closing the strand of the triangle `tr6`
  have hA3' : ∑ l ∈ univ.erase (loop3N c).2.2, s3 ((P3 c).face ((P3 c).leg (loop3N c).1 l)) ≤
      cx3 := by
    rw [sum_erase_perm4 (chk_L3 c).1 _ _ _ lL.2.2.1 s3]; simp only [fo3, ft0_3, ft3_3]; omega
  have hk3' : cx3 + ∑ l ∈ univ.erase (loop3N c).2.2, s3 ((P3 c).face ((P3 c).leg (loop3N c).1 l)) ≤
      ct3 := by
    rw [sum_erase_perm4 (chk_L3 c).1 _ _ _ lL.2.2.1 s3]; simp only [fo3, ft0_3, ft3_3]; omega
  rw [hP4, M3, ev_elimN s3 12 _ (chk_L3 c).2, L3, ← ev_loop_of (chk_L3 c).1 s3 cx3 ct3 hA3' hk3']
  refine sum_congr rfl fun x3 hx3 => congrArg _ (sum_congr rfl fun k3 _ => ?_)
  rw [mem_range] at hx3
  generalize hcol4 : Function.update (Function.update s3 (trT c 6) x3) (teT c 2) k3 = s4
  have fo4 : ∀ j, s4 (otT c j) = col (otT c j) := fun j => by rw [← hcol4]; fs [fo3]
  have ft0_4 : s4 (trT c 0) = col (trT c 0) := by rw [← hcol4]; fs [ft0_3]
  have ft1_4 : s4 (trT c 1) = col (trT c 1) := by rw [← hcol4]; fs [ft1_3]
  have ft2_4 : s4 (trT c 2) = col (trT c 2) := by rw [← hcol4]; fs [ft2_3]
  have fx3_4 : s4 (trT c 6) = x3 := by rw [← hcol4]; fs []
  have fx4_4 : s4 (trT c 7) = x4 := by rw [← hcol4]; fs [fx4_3]
  have fx5_4 : s4 (trT c 8) = x5 := by rw [← hcol4]; fs [fx5_3]
  have fx6_4 : s4 (trT c 9) = x6 := by rw [← hcol4]; fs [fx6_3]
  -- closing the strand of the triangle `tr5`
  have hA2' : ∑ l ∈ univ.erase (loop2N c).2.2, s4 ((P2 c).face ((P2 c).leg (loop2N c).1 l)) ≤
      cx2 := by
    rw [sum_erase_perm4 (chk_L2 c).1 _ _ _ lL.2.1 s4]; simp only [fo4, fx3_4, fx6_4]; omega
  have hk2' : cx2 + ∑ l ∈ univ.erase (loop2N c).2.2, s4 ((P2 c).face ((P2 c).leg (loop2N c).1 l)) ≤
      ct2 := by
    rw [sum_erase_perm4 (chk_L2 c).1 _ _ _ lL.2.1 s4]; simp only [fo4, fx3_4, fx6_4]; omega
  rw [hP3, M2, ev_elimN s4 12 _ (chk_L2 c).2, L2, ← ev_loop_of (chk_L2 c).1 s4 cx2 ct2 hA2' hk2']
  refine sum_congr rfl fun x2 hx2 => congrArg _ (sum_congr rfl fun k2 _ => ?_)
  rw [mem_range] at hx2
  generalize hcol5 : Function.update (Function.update s4 (trT c 5) x2) (teT c 8) k2 = s5
  have fo5 : ∀ j, s5 (otT c j) = col (otT c j) := fun j => by rw [← hcol5]; fs [fo4]
  have ft0_5 : s5 (trT c 0) = col (trT c 0) := by rw [← hcol5]; fs [ft0_4]
  have ft1_5 : s5 (trT c 1) = col (trT c 1) := by rw [← hcol5]; fs [ft1_4]
  have ft2_5 : s5 (trT c 2) = col (trT c 2) := by rw [← hcol5]; fs [ft2_4]
  have fx2_5 : s5 (trT c 5) = x2 := by rw [← hcol5]; fs []
  have fx3_5 : s5 (trT c 6) = x3 := by rw [← hcol5]; fs [fx3_4]
  have fx4_5 : s5 (trT c 7) = x4 := by rw [← hcol5]; fs [fx4_4]
  have fx5_5 : s5 (trT c 8) = x5 := by rw [← hcol5]; fs [fx5_4]
  -- closing the strand of the triangle `tr4`
  have hA1' : ∑ l ∈ univ.erase (loop1N c).2.2, s5 ((P1 c).face ((P1 c).leg (loop1N c).1 l)) ≤
      cx1 := by
    rw [sum_erase_perm4 (chk_L1 c).1 _ _ _ lL.1 s5]; simp only [fo5, fx3_5, fx5_5]; omega
  have hk1' : cx1 + ∑ l ∈ univ.erase (loop1N c).2.2, s5 ((P1 c).face ((P1 c).leg (loop1N c).1 l)) ≤
      ct1 := by
    rw [sum_erase_perm4 (chk_L1 c).1 _ _ _ lL.1 s5]; simp only [fo5, fx3_5, fx5_5]; omega
  rw [hP2, M1, ev_elimN s5 12 _ (chk_L1 c).2, L1, ← ev_loop_of (chk_L1 c).1 s5 cx1 ct1 hA1' hk1']
  refine sum_congr rfl fun x1 hx1 => congrArg _ (sum_congr rfl fun k1 _ => ?_)
  rw [mem_range] at hx1
  generalize hcol6 : Function.update (Function.update s5 (trT c 4) x1) (teT c 7) k1 = s6
  have fo6 : ∀ j, s6 (otT c j) = col (otT c j) := fun j => by rw [← hcol6]; fs [fo5]
  have ft0_6 : s6 (trT c 0) = col (trT c 0) := by rw [← hcol6]; fs [ft0_5]
  have ft1_6 : s6 (trT c 1) = col (trT c 1) := by rw [← hcol6]; fs [ft1_5]
  have ft2_6 : s6 (trT c 2) = col (trT c 2) := by rw [← hcol6]; fs [ft2_5]
  have fx1_6 : s6 (trT c 4) = x1 := by rw [← hcol6]; fs []
  have fx2_6 : s6 (trT c 5) = x2 := by rw [← hcol6]; fs [fx2_5]
  have fx4_6 : s6 (trT c 7) = x4 := by rw [← hcol6]; fs [fx4_5]
  -- the gluing along the tetrahedron `te6`
  have hb4' : ∑ l, s6 ((N3 c).face ((N3 c).leg (nd c 0 4) l)) ≤ cg4 := by
    rw [sum_perm4 _ _ _ _ _ lG.2.2.2 s6]; simp only [fo6, fx1_6, fx2_6, fx4_6]; omega
  rw [hP1, N4, ev_elimN s6 12 _ (chk_G4 c).2, G4, ← ev_glue_of (chk_G4 c).1 s6 cg4 hb4']
  refine sum_congr rfl fun g4 _ => ?_
  generalize hcol7 : Function.update s6 (teT c 6) g4 = s7
  have fo7 : ∀ j, s7 (otT c j) = col (otT c j) := fun j => by rw [← hcol7]; fs [fo6]
  have ft0_7 : s7 (trT c 0) = col (trT c 0) := by rw [← hcol7]; fs [ft0_6]
  have ft1_7 : s7 (trT c 1) = col (trT c 1) := by rw [← hcol7]; fs [ft1_6]
  have ft2_7 : s7 (trT c 2) = col (trT c 2) := by rw [← hcol7]; fs [ft2_6]
  have fx1_7 : s7 (trT c 4) = x1 := by rw [← hcol7]; fs [fx1_6]
  have fx2_7 : s7 (trT c 5) = x2 := by rw [← hcol7]; fs [fx2_6]
  have fx4_7 : s7 (trT c 7) = x4 := by rw [← hcol7]; fs [fx4_6]
  -- the gluing along the tetrahedron `te3`
  have hb3' : ∑ l, s7 ((N2 c).face ((N2 c).leg (nd c 1 4) l)) ≤ cg3 := by
    rw [sum_perm4 _ _ _ _ _ lG.2.2.1 s7]; simp only [fo7, ft1_7, ft2_7, fx4_7]; omega
  rw [N3, ev_elimN s7 12 _ (chk_G3 c).2, G3, ← ev_glue_of (chk_G3 c).1 s7 cg3 hb3']
  refine sum_congr rfl fun g3 _ => ?_
  generalize hcol8 : Function.update s7 (teT c 3) g3 = s8
  have fo8 : ∀ j, s8 (otT c j) = col (otT c j) := fun j => by rw [← hcol8]; fs [fo7]
  have ft0_8 : s8 (trT c 0) = col (trT c 0) := by rw [← hcol8]; fs [ft0_7]
  have ft1_8 : s8 (trT c 1) = col (trT c 1) := by rw [← hcol8]; fs [ft1_7]
  have ft2_8 : s8 (trT c 2) = col (trT c 2) := by rw [← hcol8]; fs [ft2_7]
  have fx1_8 : s8 (trT c 4) = x1 := by rw [← hcol8]; fs [fx1_7]
  have fx2_8 : s8 (trT c 5) = x2 := by rw [← hcol8]; fs [fx2_7]
  -- the gluing along the tetrahedron `te1`
  have hb2' : ∑ l, s8 ((N1 c).face ((N1 c).leg (nd c 2 4) l)) ≤ cg2 := by
    rw [sum_perm4 _ _ _ _ _ lG.2.1 s8]; simp only [fo8, ft0_8, ft2_8, fx2_8]; omega
  rw [N2, ev_elimN s8 12 _ (chk_G2 c).2, G2, ← ev_glue_of (chk_G2 c).1 s8 cg2 hb2']
  refine sum_congr rfl fun g2 _ => ?_
  generalize hcol9 : Function.update s8 (teT c 1) g2 = s9
  have fo9 : ∀ j, s9 (otT c j) = col (otT c j) := fun j => by rw [← hcol9]; fs [fo8]
  have ft0_9 : s9 (trT c 0) = col (trT c 0) := by rw [← hcol9]; fs [ft0_8]
  have ft1_9 : s9 (trT c 1) = col (trT c 1) := by rw [← hcol9]; fs [ft1_8]
  have fx1_9 : s9 (trT c 4) = x1 := by rw [← hcol9]; fs [fx1_8]
  -- the gluing along the tetrahedron `te0`
  have hb1' : ∑ l, s9 ((U5 c).face ((U5 c).leg (nd c 3 4) l)) ≤ cg1 := by
    rw [sum_perm4 _ _ _ _ _ lG.1 s9]; simp only [fo9, ft0_9, ft1_9, fx1_9]; omega
  rw [N1, ev_elimN s9 12 _ (chk_G1 c).2, G1, ← ev_glue_of (chk_G1 c).1 s9 cg1 hb1']
  -- the last sum is `rfl`


/-- **The reduced network of the five-simplex side is the one of the one-simplex side times the
dimensions of the four free triangles `{b} ∪ {a_0, a_j}`.** -/
theorem ev_NL_eq_QB (c : Fin 6) (col : Fin 64 → ℕ) :
    (NL c).ev col = ((col (trT c 0) : ℝ) + 1) * (((col (trT c 1) : ℝ) + 1) *
      (((col (trT c 2) : ℝ) + 1) * (((col (trT c 3) : ℝ) + 1) * (QB c).ev col))) := by
  obtain ⟨hl0, hk0, hn0, hc0, hf0⟩ := chk_free0 c
  obtain ⟨hl1, hk1, hn1, hc1, hf1⟩ := chk_free1 c
  obtain ⟨hl2, hk2, hn2, hc2, hf2⟩ := chk_free2 c
  obtain ⟨hl3, hk3, hn3, hc3, hf3⟩ := chk_free3 c
  rw [ev_killE (NL c) col _ hl0 hk0 hn0 hc0, hf0]
  congr 1
  show (K1 c).ev col = _
  rw [ev_killE (K1 c) col _ hl1 hk1 hn1 hc1, hf1]
  congr 1
  show (K2 c).ev col = _
  rw [ev_killE (K2 c) col _ hl2 hk2 hn2 hc2, hf2]
  congr 1
  show (K3 c).ev col = _
  rw [ev_killE (K3 c) col _ hl3 hk3 hn3 hc3, hf3]
  congr 1
  show (NK c).ev col = (QB c).ev col
  rw [← ev_rel_of (chk_rel c) col, NG, ev_addParities col _ _ (chk_gauge c).2, ev_flipVars,
    ev_flipNodes col _ _ (chk_gauge c).1]

end Move15

end Lightlike.SpinFoam
