import Mathlib.Basic.Real.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Twisted cochains of a 2-complex with a connection

The Ponzano–Regge partition function in group variables (Barrett–Naish-Guzman) integrates a delta
function of the face holonomies over the edge holonomies. Whether this integral exists depends on
the differential of the holonomy map, which is a *twisted* coboundary. This file defines the
cochain complex `C⁰ → C¹ → C²` of a finite 2-complex whose edges carry elements of a group `G`
(the connection), with coefficients in a real representation `V` of `G`.

A 2-complex is given by its oriented edges (with source and target vertex) and, for each face, a
boundary word: a list of edges, each traversed forwards or backwards. The cochain `Φ : E → V`
stands for the variation `dg g⁻¹` of the edge holonomy `g`, read at the source of the edge.

## Main results

* `Cell2`, `Cell2.WellFormed`: boundary words are closed walks.
* `hol g w`: holonomy of a word; `Flat g`: every face has holonomy `1`.
* `d0`, `d1`: the twisted coboundaries; `d1` is the differential of the face-holonomy map
  (eq. (19) of `barrett-naish-guzman-2009`).
* `d1_comp_d0`: `d1 ∘ d0 = 0` for a flat connection on a well-formed complex.
* `H2`, `d1_surjective_iff`: the second cohomology group `C² / im d1` is trivial iff `d1` is onto.
-/

open Finset

namespace Lightlike.SpinFoam

variable {Vtx E F G V : Type*}

/-- A 2-complex: oriented edges and, for each face, a boundary word of edges traversed forwards
(`true`) or backwards (`false`). -/
structure Cell2 (Vtx E F : Type*) where
  /-- Source vertex of an edge. -/
  src : E → Vtx
  /-- Target vertex of an edge. -/
  tgt : E → Vtx
  /-- Boundary word of a face. -/
  bdry : F → List (E × Bool)

namespace Cell2

/-- The vertex where a traversed edge starts. -/
def startV (C : Cell2 Vtx E F) (l : E × Bool) : Vtx := if l.2 then C.src l.1 else C.tgt l.1

/-- The vertex where a traversed edge ends. -/
def endV (C : Cell2 Vtx E F) (l : E × Bool) : Vtx := if l.2 then C.tgt l.1 else C.src l.1

/-- `IsWalk a b w`: the word `w` is a walk from `a` to `b`. -/
def IsWalk (C : Cell2 Vtx E F) : Vtx → Vtx → List (E × Bool) → Prop
  | a, b, [] => a = b
  | a, b, l :: w => C.startV l = a ∧ C.IsWalk (C.endV l) b w

/-- Every boundary word is a closed walk. -/
def WellFormed (C : Cell2 Vtx E F) : Prop := ∀ f, ∃ v, C.IsWalk v v (C.bdry f)

end Cell2

section Twisted

variable [Group G] [AddCommGroup V] [Module ℝ V]

/-- The holonomy of a traversed edge. -/
def lh (g : E → G) (l : E × Bool) : G := if l.2 then g l.1 else (g l.1)⁻¹

/-- The holonomy of a word. -/
def hol (g : E → G) : List (E × Bool) → G
  | [] => 1
  | l :: w => lh g l * hol g w

/-- The connection `g` is **flat** on `C`: every face has holonomy `1`. -/
def Flat (C : Cell2 Vtx E F) (g : E → G) : Prop := ∀ f, hol g (C.bdry f) = 1

/-- The contribution of one traversed edge to the variation of a word's holonomy: `Φ` for a
forward edge, `-Ad(g⁻¹) Φ` for a backward one (the derivative of `g⁻¹` times `g`). -/
def lc (ρ : Representation ℝ G V) (g : E → G) (l : E × Bool) (x : V) : V :=
  if l.2 then x else -(ρ (g l.1)⁻¹ x)

/-- The variation `dh h⁻¹` of the holonomy `h` of a word, as a function of the variations `Φ` of
the edge holonomies: `dh h⁻¹ = Σᵢ (g₁ ⋯ gᵢ₋₁) ⊲ (dgᵢ gᵢ⁻¹)`. -/
def dword (ρ : Representation ℝ G V) (g : E → G) (Φ : E → V) : List (E × Bool) → V
  | [] => 0
  | l :: w => lc ρ g l (Φ l.1) + ρ (lh g l) (dword ρ g Φ w)

lemma dword_add (ρ : Representation ℝ G V) (g : E → G) (Φ Ψ : E → V) (w : List (E × Bool)) :
    dword ρ g (Φ + Ψ) w = dword ρ g Φ w + dword ρ g Ψ w := by
  induction w with
  | nil => simp [dword]
  | cons l w ih =>
    simp only [dword, ih, map_add, Pi.add_apply, lc]
    split_ifs <;> (try simp) <;> abel

lemma dword_smul (ρ : Representation ℝ G V) (g : E → G) (c : ℝ) (Φ : E → V)
    (w : List (E × Bool)) : dword ρ g (c • Φ) w = c • dword ρ g Φ w := by
  induction w with
  | nil => simp [dword]
  | cons l w ih =>
    simp only [dword, ih, map_smul, Pi.smul_apply, lc]
    split_ifs <;> simp [smul_add]

/-- The twisted coboundary `C⁰ → C¹`: the variation `ψ(src) - Ad(g) ψ(tgt)` of a gauge
transformation `ψ`. -/
def d0 (ρ : Representation ℝ G V) (C : Cell2 Vtx E F) (g : E → G) : (Vtx → V) →ₗ[ℝ] (E → V) where
  toFun ψ e := ψ (C.src e) - ρ (g e) (ψ (C.tgt e))
  map_add' ψ χ := by funext e; simp; abel
  map_smul' c ψ := by funext e; simp [smul_sub]

/-- The twisted coboundary `C¹ → C²`: the differential of the face-holonomy map. -/
def d1 (ρ : Representation ℝ G V) (C : Cell2 Vtx E F) (g : E → G) : (E → V) →ₗ[ℝ] (F → V) where
  toFun Φ f := dword ρ g Φ (C.bdry f)
  map_add' Φ Ψ := by funext f; exact dword_add ρ g Φ Ψ _
  map_smul' c Φ := by funext f; exact dword_smul ρ g c Φ _

lemma dword_d0 (ρ : Representation ℝ G V) (C : Cell2 Vtx E F) (g : E → G) (ψ : Vtx → V)
    (w : List (E × Bool)) (a b : Vtx) (h : C.IsWalk a b w) :
    dword ρ g (d0 ρ C g ψ) w = ψ a - ρ (hol g w) (ψ b) := by
  induction w generalizing a with
  | nil => simp only [Cell2.IsWalk] at h; subst h; simp [dword, hol]
  | cons l w ih =>
    obtain ⟨hl, hw⟩ := h
    obtain ⟨e, s⟩ := l
    simp only [Cell2.startV, Cell2.endV] at hl hw
    rw [dword, hol, ih _ hw]
    subst hl
    cases s <;> simp [lh, lc, d0, map_sub]

/-- **`d1 ∘ d0 = 0`** for a flat connection on a complex whose faces are closed walks. -/
theorem d1_comp_d0 (ρ : Representation ℝ G V) {C : Cell2 Vtx E F} (hC : C.WellFormed)
    {g : E → G} (hg : Flat C g) : d1 ρ C g ∘ₗ d0 ρ C g = 0 := by
  ext ψ f
  obtain ⟨v, hv⟩ := hC f
  simp only [LinearMap.comp_apply, d1, d0, LinearMap.coe_mk, AddHom.coe_mk] at *
  have := dword_d0 ρ C g ψ _ v v hv
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this, hg f]; simp

/-- The second twisted cohomology group `H² = C² / im d1`. -/
abbrev H2 (ρ : Representation ℝ G V) (C : Cell2 Vtx E F) (g : E → G) :=
  (F → V) ⧸ LinearMap.range (d1 ρ C g)

/-- **`d1` is onto exactly when `H²` is trivial.** -/
theorem d1_surjective_iff (ρ : Representation ℝ G V) (C : Cell2 Vtx E F) (g : E → G) :
    Function.Surjective (d1 ρ C g) ↔ Subsingleton (H2 ρ C g) := by
  rw [← LinearMap.range_eq_top, Submodule.Quotient.subsingleton_iff]

end Twisted

end Lightlike.SpinFoam
