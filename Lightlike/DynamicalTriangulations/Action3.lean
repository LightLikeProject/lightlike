import Lightlike.DynamicalTriangulations.DehnSommerville3
import Lightlike.PonzanoRegge.Manifold
import Lightlike.PonzanoRegge.InverseMoves

/-!
# The Einstein–Regge action of three-dimensional dynamical triangulations

For a triangulation `K` of a 3-manifold by equilateral tetrahedra the Regge action reduces to
`S(K) = −κ₁ N₁ + κ₃ N₃`, with `N₁` the number of edges and `N₃` the number of tetrahedra
(Ambjørn, Jurkiewicz and Loll, Non-perturbative 3d Lorentzian quantum gravity, 2001,
Appendix 1, eq. (24)). For a closed combinatorial 3-manifold `N₁ = N₀ + N₃`, so
`S = −κ₁ N₀ + (κ₃ − κ₁) N₃` depends only on `N₀` and `N₃` (eqs. (25) to (27) there).

## Main results

* `dtAction3 κ₁ κ₃ K = −κ₁ N₁ + κ₃ N₃`.
* `dtAction3_eq`: for a closed combinatorial 3-manifold, `S = −κ₁ N₀ + (κ₃ − κ₁) N₃`.
* `dtAction3_move23`, `dtAction3_move32`: the 2-3 move changes the action by `κ₃ − κ₁`, the 3-2 move
  by `κ₁ − κ₃`.
* `dtAction3_move14`, `dtAction3_move41`: the 1-4 move changes it by `3κ₃ − 4κ₁`, the 4-1 move by
  `4κ₁ − 3κ₃`.
-/

open Finset Lightlike.PR

namespace Lightlike.DynamicalTriangulations

-- The distinctness proofs pass every inequality to `simp`; each proof uses only some of them.
set_option linter.unusedSimpArgs false

variable {V : Type*} [DecidableEq V]

/-- The **Einstein–Regge action** of a triangulation by equilateral tetrahedra:
`S = −κ₁ N₁ + κ₃ N₃`, with `N₁` edges and `N₃` tetrahedra. -/
noncomputable def dtAction3 (κ₁ κ₃ : ℝ) (K : Complex3 V) : ℝ :=
  -κ₁ * #K.edges + κ₃ * #K.tets

/-- For a closed combinatorial 3-manifold, `S = −κ₁ N₀ + (κ₃ − κ₁) N₃`. -/
theorem dtAction3_eq (κ₁ κ₃ : ℝ) {K : Complex3 V} (hK : IsCombManifold K) :
    dtAction3 κ₁ κ₃ K = -κ₁ * #K.verts + (κ₃ - κ₁) * #K.tets := by
  have h : (#K.edges : ℝ) = #K.verts + #K.tets := by exact_mod_cast hK.card_edges
  rw [dtAction3, h]
  ring

omit [DecidableEq V] in
/-- Two sets differ if one contains an element the other lacks. -/
private lemma ne_of_mem {s t : Finset V} {x : V} (hs : x ∈ s) (ht : x ∉ t) : s ≠ t :=
  fun h => ht (h ▸ hs)

/-- **The 2-3 move adds one tetrahedron.** -/
theorem card_tets_move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    #(move23 K h).tets = #K.tets + 1 := by
  have h1 : ({A, B, C, D} : Finset V) ∈ K.tets := h.mem₁
  have h2 : ({A, B, C, E} : Finset V) ∈ K.tets := h.mem₂
  have hne : ({A, B, C, D} : Finset V) ≠ {A, B, C, E} := ne_of_mem (x := D) (by simp)
    (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
  have hc : #((K.tets.erase {A, B, C, D}).erase {A, B, C, E}) = #K.tets - 2 := by
    rw [card_erase_of_mem (mem_erase.2 ⟨hne.symm, h2⟩), card_erase_of_mem h1]; omega
  have hpos : 2 ≤ #K.tets := by
    have : ({{A, B, C, D}, {A, B, C, E}} : Finset (Finset V)) ⊆ K.tets := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have := card_le_card this
    rwa [card_pair hne] at this
  have hdisj : Disjoint ({{A, B, D, E}, {B, C, D, E}, {C, A, D, E}} : Finset (Finset V))
      ((K.tets.erase {A, B, C, D}).erase {A, B, C, E}) := by
    rw [disjoint_left]
    intro t ht ht'
    have ht'' := mem_of_mem_erase (mem_of_mem_erase ht')
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;>
      exact h.fresh _ ht'' (by intro y hy; simp only [mem_insert, mem_singleton] at hy ⊢; tauto)
  have h3 : #({{A, B, D, E}, {B, C, D, E}, {C, A, D, E}} : Finset (Finset V)) = 3 := by
    have n12 : ({A, B, D, E} : Finset V) ≠ {B, C, D, E} :=
      ne_of_mem (x := A) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n13 : ({A, B, D, E} : Finset V) ≠ {C, A, D, E} :=
      ne_of_mem (x := B) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n23 : ({B, C, D, E} : Finset V) ≠ {C, A, D, E} :=
      ne_of_mem (x := B) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    rw [card_insert_of_notMem (by simp [n12, n13]), card_pair n23]
  rw [move23, card_union_of_disjoint hdisj, h3, hc]
  omega

/-- **The 2-3 move adds one edge, `DE`.** -/
theorem card_edges_move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    #(move23 K h).edges = #K.edges + 1 := by
  rw [edges_move23, card_insert_of_notMem]
  intro hm
  obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.1 hm
  exact h.fresh t ht hst

/-- **The change of the action under the 2-3 move** is `κ₃ − κ₁`. -/
theorem dtAction3_move23 (κ₁ κ₃ : ℝ) {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    dtAction3 κ₁ κ₃ (move23 K h) - dtAction3 κ₁ κ₃ K = κ₃ - κ₁ := by
  rw [dtAction3, dtAction3, card_tets_move23 h, card_edges_move23 h]
  push_cast; ring

/-- **The change of the action under the 3-2 move** is `κ₁ − κ₃`. -/
theorem dtAction3_move32 (κ₁ κ₃ : ℝ) {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E) :
    dtAction3 κ₁ κ₃ (move32 K h) - dtAction3 κ₁ κ₃ K = κ₁ - κ₃ := by
  have := dtAction3_move23 κ₁ κ₃ (isMove23_move32 h)
  rw [move23_move32] at this
  linarith

/-- **The 1-4 move adds three tetrahedra.** -/
theorem card_tets_move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    #(move14 K h).tets = #K.tets + 3 := by
  have h1 : ({A, B, C, D} : Finset V) ∈ K.tets := h.mem
  have hdisj : Disjoint ({{A, B, C, E}, {A, B, D, E}, {A, C, D, E}, {B, C, D, E}} : Finset (Finset V))
      (K.tets.erase {A, B, C, D}) := by
    rw [disjoint_left]
    intro t ht ht'
    have := h.fresh t (mem_of_mem_erase ht')
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> simp at this
  have h4 : #({{A, B, C, E}, {A, B, D, E}, {A, C, D, E}, {B, C, D, E}} : Finset (Finset V)) = 4 := by
    have n12 : ({A, B, C, E} : Finset V) ≠ {A, B, D, E} :=
      ne_of_mem (x := C) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n13 : ({A, B, C, E} : Finset V) ≠ {A, C, D, E} :=
      ne_of_mem (x := B) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n14 : ({A, B, C, E} : Finset V) ≠ {B, C, D, E} :=
      ne_of_mem (x := A) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n23 : ({A, B, D, E} : Finset V) ≠ {A, C, D, E} :=
      ne_of_mem (x := B) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n24 : ({A, B, D, E} : Finset V) ≠ {B, C, D, E} :=
      ne_of_mem (x := A) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n34 : ({A, C, D, E} : Finset V) ≠ {B, C, D, E} :=
      ne_of_mem (x := A) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    rw [card_insert_of_notMem (by simp [n12, n13, n14]),
      card_insert_of_notMem (by simp [n23, n24]), card_pair n34]
  rw [move14, card_union_of_disjoint hdisj, h4, card_erase_of_mem h1]
  have : 0 < #K.tets := card_pos.2 ⟨_, h1⟩
  omega

/-- **The 1-4 move adds four edges**, those through the new vertex `E`. -/
theorem card_edges_move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    #(move14 K h).edges = #K.edges + 4 := by
  have hdisj : Disjoint K.edges ({{A, E}, {B, E}, {C, E}, {D, E}} : Finset (Finset V)) := by
    rw [disjoint_right]
    intro s hs hs'
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.1 hs'
    have hE := h.fresh t ht
    simp only [mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> exact hE (hst (by simp))
  have h4 : #({{A, E}, {B, E}, {C, E}, {D, E}} : Finset (Finset V)) = 4 := by
    have n12 : ({A, E} : Finset V) ≠ {B, E} :=
      ne_of_mem (x := A) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n13 : ({A, E} : Finset V) ≠ {C, E} :=
      ne_of_mem (x := A) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n14 : ({A, E} : Finset V) ≠ {D, E} :=
      ne_of_mem (x := A) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n23 : ({B, E} : Finset V) ≠ {C, E} :=
      ne_of_mem (x := B) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n24 : ({B, E} : Finset V) ≠ {D, E} :=
      ne_of_mem (x := B) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    have n34 : ({C, E} : Finset V) ≠ {D, E} :=
      ne_of_mem (x := C) (by simp) (by simp [h.hAB, h.hAC, h.hAD, h.hAE, h.hBC, h.hBD, h.hBE, h.hCD, h.hCE, h.hDE, h.hAB.symm, h.hAC.symm, h.hAD.symm, h.hAE.symm, h.hBC.symm, h.hBD.symm, h.hBE.symm, h.hCD.symm, h.hCE.symm, h.hDE.symm])
    rw [card_insert_of_notMem (by simp [n12, n13, n14]),
      card_insert_of_notMem (by simp [n23, n24]), card_pair n34]
  rw [edges_move14, card_union_of_disjoint hdisj, h4]

/-- **The change of the action under the 1-4 move** is `3κ₃ − 4κ₁`. -/
theorem dtAction3_move14 (κ₁ κ₃ : ℝ) {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    dtAction3 κ₁ κ₃ (move14 K h) - dtAction3 κ₁ κ₃ K = 3 * κ₃ - 4 * κ₁ := by
  rw [dtAction3, dtAction3, card_tets_move14 h, card_edges_move14 h]
  push_cast; ring

/-- **The change of the action under the 4-1 move** is `4κ₁ − 3κ₃`. -/
theorem dtAction3_move41 (κ₁ κ₃ : ℝ) {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E) :
    dtAction3 κ₁ κ₃ (move41 K h) - dtAction3 κ₁ κ₃ K = 4 * κ₁ - 3 * κ₃ := by
  have := dtAction3_move14 κ₁ κ₃ (isMove14_move41 h)
  rw [move14_move41] at this
  linarith

end Lightlike.DynamicalTriangulations
