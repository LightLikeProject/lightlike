import Lightlike.Surfaces.Glue
import Lightlike.Surfaces.Pieces

/-!
# Finite move chains for the classification of surfaces

The classification turns a handle or a cross-cap found by cutting a surface (`IsSurface.cut`)
into a connected sum with a torus `T9`, a Klein bottle `KB` or a projective plane `P6`. Each step
of that conversion is a fixed chain of 2D moves on a few labelled triangles, checked here by the
kernel with the chain checker `checkChain` (`Lightlike/Surfaces/Check.lean`), whose soundness
theorem `checkChain_sound` then transports it into any surface with fresh enough labels.

* `tube a b c p q r`: the six triangles of a cylinder between the triangles `abc` and `pqr`.
* `chain_tslide`: the end `pqr` of a tube moves across a neighbouring triangle `qrs`.
* `chain_layer`: a tube gets two more rings of vertices.
* `chain_final_*`: a three-ring tube whose end is a triangle `019` next to its start `012`
  becomes `T9` (for the three rotations of `019`) or `KB` (for the three reflections) glued at
  `012`, with `019` restored.
* `chain_cc`: the Möbius band of a one-sided cut becomes a disc with `P6` glued to it.
* `chain_dyck`: **Dyck's relation**: inside a projective plane, a torus can be replaced by a
  Klein bottle (rel the boundary triangle `012`).

The chains were found and checked independently by `scripts/pl/surf_chains.py`.
-/

open Finset Relation

namespace Lightlike.Surfaces

open Lightlike.PR

set_option maxRecDepth 100000

variable {V : Type*} [DecidableEq V]

/-! ## Tubes -/

/-- The **tube** between the triangles `abc` and `pqr`: the six triangles `abp`, `bpq`, `bcq`,
`cqr`, `car`, `arp` of a cylinder whose boundary circles are `a b c` and `p q r`. -/
def tube (a b c p q r : V) : Finset (Finset V) :=
  {{a, b, p}, {b, p, q}, {b, c, q}, {c, q, r}, {c, a, r}, {a, r, p}}

/-- A tube is unchanged by rotating both of its ends. -/
lemma tube_rot (a b c p q r : V) : tube a b c p q r = tube b c a q r p := by
  ext t; simp only [tube, mem_insert, mem_singleton]; tauto

/-- Relabelling a tube. -/
lemma liftK_tube (f : ℕ ↪ V) (a b c p q r : ℕ) :
    liftK f (tube a b c p q r) = tube (f a) (f b) (f c) (f p) (f q) (f r) := by
  simp only [tube, liftK, image_insert, image_singleton, map_insert, map_singleton]

/-- The tube of a two-sided cut is a tube. -/
lemma cutTube_eq : cutTube = tube 0 1 2 3 4 5 := rfl

/-! ## The Klein bottle piece and the three-ring tube -/

/-- The relabelling `0, 1, 2 ↦ 1, 3, 4`, `n ↦ n + 3` that glues a second piece to the triangle
`134` of a first one. -/
def e134 : ℕ ↪ ℕ := tabE [1, 3, 4] 3 (by decide)

/-- The **Klein bottle piece** on the labels `0, …, 8`: two projective planes `P6`, the second
glued to the triangle `134` of the first. -/
def KB : Finset (Finset ℕ) := P6.erase {1, 3, 4} ∪ liftK e134 (P6.erase {0, 1, 2})

/-- The **three-ring tube** from `012` through `345` and `678` to the triangle with vertices
`o₀ o₁ o₂`, in this order. -/
def finX (o₀ o₁ o₂ : ℕ) : Finset (Finset ℕ) :=
  tube 0 1 2 3 4 5 ∪ tube 3 4 5 6 7 8 ∪ tube 6 7 8 o₀ o₁ o₂

/-! ## Moving and lengthening tubes -/

/-- **Sliding the end of a tube.** The end `345` of the tube from `012` moves across the
triangle `456`; the result is the tube from `012` to `465` and the triangle `345`. -/
theorem chain_tslide : checkChain {0, 1, 2, 3, 4, 5, 6}
    [(4, 5), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5),
      (2, 6)] (insert {4, 5, 6} (tube 0 1 2 3 4 5))
    [.flip 4 5 2 6, .flip 1 3 0 4, .flip 4 2 1 6, .flip 0 3 4 5] =
    some (insert {3, 4, 5} (tube 0 1 2 4 6 5)) := by decide +kernel

/-- **Two more rings.** The tube from `012` to `345` becomes the tubes from `012` to `678`, from
`678` to `9 10 11` and from `9 10 11` to `345` (18 moves). -/
theorem chain_layer : checkChain {0, 1, 2, 3, 4, 5}
    [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)] (tube 0 1 2 3 4 5)
    [.sub 1 2 4 7, .sub 0 1 3 6, .sub 2 4 5 8, .flip 1 4 7 3, .flip 0 3 5 6, .flip 2 5 8 0,
      .flip 1 3 6 7, .flip 4 2 7 8, .flip 0 5 6 8, .sub 7 8 4 10, .sub 6 7 3 9, .sub 8 4 5 11,
      .flip 7 4 10 3, .flip 6 3 5 9, .flip 8 5 11 6, .flip 7 3 9 10, .flip 4 8 10 11,
      .flip 6 5 9 11] =
    some (tube 0 1 2 6 7 8 ∪ tube 6 7 8 9 10 11 ∪ tube 9 10 11 3 4 5) := by decide +kernel

/-! ## Closing a tube next to its start

The three-ring tube `finX o` runs from `012` to the triangle `019`, which shares the edge `01`
with `012`. If it enters `019` in a rotation of the order `0 1 9`, the chain turns it into a torus
`T9` glued at `012`; in a reflected order, into a Klein bottle `KB`. In each case the triangle
`019` comes back and the interior labels of the piece are permuted by the given table. -/

/-- Closing the tube entering in the order `0 1 9`: a torus. -/
theorem chain_final_019 : checkChain {0, 1, 2, 9} [(0, 1)] (finX 0 1 9)
    [.flip 3 6 8 4, .flip 6 9 0 8, .flip 0 1 7 3, .flip 8 9 0 1, .flip 4 5 2 7, .flip 8 3 4 5,
      .flip 7 0 3 6, .flip 4 7 2 6] =
    some (insert {0, 1, 9}
      (liftK (tabE [0, 1, 2, 3, 4, 5, 6, 8, 7] 0 (by decide)) (T9.erase {0, 1, 2}))) := by
  decide +kernel

/-- Closing the tube entering in the order `1 9 0`: a torus. -/
theorem chain_final_190 : checkChain {0, 1, 2, 9} [(0, 1)] (finX 1 9 0)
    [.flip 3 6 8 4, .flip 6 8 4 0, .flip 0 1 6 3, .flip 0 3 5 6, .flip 4 5 2 7, .flip 9 7 1 8,
      .flip 9 8 0 1, .flip 4 1 2 3] =
    some (insert {0, 1, 9}
      (liftK (tabE [0, 1, 2, 6, 3, 5, 4, 8, 7] 0 (by decide)) (T9.erase {0, 1, 2}))) := by
  decide +kernel

/-- Closing the tube entering in the order `9 0 1`: a torus. -/
theorem chain_final_901 : checkChain {0, 1, 2, 9} [(0, 1)] (finX 9 0 1)
    [.flip 3 8 6 5, .flip 0 1 8 3, .flip 6 8 5 1, .flip 1 3 8 4, .flip 7 9 0 6, .flip 0 5 2 3,
      .flip 9 6 0 1, .flip 4 5 2 7] =
    some (insert {0, 1, 9}
      (liftK (tabE [0, 1, 2, 8, 4, 3, 7, 6, 5] 0 (by decide)) (T9.erase {0, 1, 2}))) := by
  decide +kernel

/-- Closing the tube entering in the order `0 9 1`: a Klein bottle. -/
theorem chain_final_091 : checkChain {0, 1, 2, 9} [(0, 1)] (finX 0 9 1)
    [.flip 3 6 8 4, .flip 0 1 6 3, .flip 0 3 5 6, .flip 4 5 7 2, .flip 7 6 0 4, .flip 8 9 1 7,
      .flip 9 7 0 1, .flip 7 8 1 5, .flip 0 6 5 4] =
    some (insert {0, 1, 9}
      (liftK (tabE [0, 1, 2, 5, 4, 7, 3, 6, 8] 0 (by decide)) (KB.erase {0, 1, 2}))) := by
  decide +kernel

/-- Closing the tube entering in the order `1 0 9`: a Klein bottle. -/
theorem chain_final_109 : checkChain {0, 1, 2, 9} [(0, 1)] (finX 1 0 9)
    [.flip 0 1 7 3, .flip 5 7 4 8, .flip 0 3 5 7, .flip 4 5 8 2, .flip 8 7 0 4, .flip 6 9 1 8,
      .flip 3 8 6 5, .flip 9 8 0 1, .flip 8 6 1 5, .flip 0 7 5 4] =
    some (insert {0, 1, 9}
      (liftK (tabE [0, 1, 2, 5, 4, 8, 3, 7, 6] 0 (by decide)) (KB.erase {0, 1, 2}))) := by
  decide +kernel

/-- Closing the tube entering in the order `9 1 0`: a Klein bottle. -/
theorem chain_final_910 : checkChain {0, 1, 2, 9} [(0, 1)] (finX 9 1 0)
    [.flip 3 6 8 4, .flip 0 8 1 6, .flip 0 1 6 3, .flip 0 3 5 6, .flip 4 5 2 7, .flip 6 9 0 7,
      .flip 7 6 0 4, .flip 9 7 0 1, .flip 7 8 1 5, .flip 0 6 5 4] =
    some (insert {0, 1, 9}
      (liftK (tabE [0, 1, 2, 5, 4, 7, 3, 6, 8] 0 (by decide)) (KB.erase {0, 1, 2}))) := by
  decide +kernel

/-! ## The cross-cap and Dyck's relation -/

/-- **The cross-cap chain.** The Möbius band `cutBand` of a one-sided cut becomes the disc
`cutCap` with a projective plane glued at its triangle `320` (14 moves). -/
theorem chain_cc : checkChain {0, 1, 2, 3, 4, 5}
    [(0, 3), (0, 4), (0, 5), (1, 4), (4, 5), (2, 5), (3, 2), (3, 1)] cutBand
    [.sub 2 4 5 6, .flip 0 5 3 2, .sub 0 2 3 7, .sub 7 0 3 8, .flip 1 4 0 5, .flip 2 5 3 6,
      .flip 4 5 0 6, .flip 3 0 8 4, .flip 6 5 0 3, .flip 2 3 6 7, .flip 4 0 6 8, .flip 6 4 8 2,
      .flip 5 0 1 3, .flip 8 4 2 3] =
    some (cutCap.erase {3, 2, 0} ∪
      liftK (tabE [3, 2, 0] 3 (by decide)) (P6.erase {0, 1, 2})) := by
  decide +kernel

/-- The relabelling of `T9` in Dyck's relation: `0, 1, 2 ↦ 1, 3, 4`, the interior to `6, …, 11`. -/
def eDyck : ℕ ↪ ℕ := tabE [1, 3, 4, 9, 7, 6, 10, 11, 8] 3 (by decide)

/-- **Dyck's relation.** A projective plane `P6` with a torus glued at its triangle `134` is
related by moves to `P6` with a Klein bottle glued there, keeping the triangle `012` (and the
labels `0, 1, 2`) fixed: the complexes below are these connected sums without `012` (42 flips). -/
theorem chain_dyck : checkChain {0, 1, 2} []
    ((P6.erase {0, 1, 2}).erase {1, 3, 4} ∪ liftK eDyck (T9.erase {0, 1, 2}))
    [.flip 4 10 7 8, .flip 9 10 8 1, .flip 7 6 11 9, .flip 4 8 7 6, .flip 1 3 11 5, .flip 8 9 1 3,
      .flip 1 11 10 5, .flip 11 7 9 10, .flip 3 5 11 2, .flip 8 1 10 3, .flip 3 11 8 2,
      .flip 10 1 3 5, .flip 3 2 8 0, .flip 10 5 11 3, .flip 3 8 10 0, .flip 11 5 3 2,
      .flip 3 0 10 4, .flip 11 2 8 3, .flip 3 10 11 4, .flip 8 2 3 0, .flip 4 0 10 5,
      .flip 11 3 8 4, .flip 4 10 11 5, .flip 8 3 4 0, .flip 5 0 10 1, .flip 11 4 8 5,
      .flip 5 10 11 1, .flip 8 4 5 0, .flip 5 1 11 3, .flip 8 0 10 5, .flip 5 11 8 3,
      .flip 10 0 5 1, .flip 9 10 11 7, .flip 1 11 3 10, .flip 1 3 10 9, .flip 1 9 6 10,
      .flip 7 6 4 8, .flip 10 5 1 8, .flip 8 10 1 7, .flip 5 8 1 3, .flip 8 11 3 6,
      .flip 1 10 6 7] =
    some ((P6.erase {0, 1, 2}).erase {1, 3, 4} ∪ liftK e134 (KB.erase {0, 1, 2})) := by
  decide +kernel

end Lightlike.Surfaces
