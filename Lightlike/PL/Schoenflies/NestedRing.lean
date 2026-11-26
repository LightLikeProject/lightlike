import Mathlib
import Lightlike.PL.Schoenflies.StripChord
import Lightlike.PL.Schoenflies.SplitSide

/-!
# The ring between two nested polygons: the strip and the keyhole quad

Row G3-188 (PL5), nested ring.  `NestedRing` records two good cells that share the spokes `[w₀, v₀]`, `[w_N, v_N]`:
the strip (inner chain `αs`, from `w_N` to `w₀`, outer chain `βs`, from `v_N` to `v₀`) and the keyhole quad (inner chain
`αl` from `w₀` to `w_N`, outer chain `βl` from `v₀` to `v_N`), with the inner arcs meeting only at the ends, the outer
arcs likewise, and the inner arcs disjoint from the outer ones.  `NestedRing.split1_hyps` gives the chain hypotheses of the
first chord split of the outer polygon along the short chord `v₀ → αs reversed → v_N`.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

/-- The two cells of the ring between two nested polygons cut along two spokes. -/
structure NestedRing (w₀ wN v₀ vN : ℝ × ℝ) (αs αl βs βl : List (ℝ × ℝ)) : Prop where
  strip : GoodQuad wN w₀ vN v₀ αs βs
  keyhole : GoodQuad w₀ wN v₀ vN αl βl
  aa : chainSet αs ∩ chainSet αl = {w₀, wN}
  bb : chainSet βs ∩ chainSet βl = {v₀, vN}
  ab1 : chainSet αl ∩ chainSet βs = ∅
  ab2 : chainSet αs ∩ chainSet βl = ∅

theorem NestedRing.split1_hyps {w₀ wN v₀ vN : ℝ × ℝ} {αs αl βs βl m₁ m₂ : List (ℝ × ℝ)}
    (h : NestedRing w₀ wN v₀ vN αs αl βs βl) (hβl : βl = v₀ :: m₁ ++ [vN]) (hβs : βs = vN :: m₂ ++ [v₀]) :
    v₀ ≠ vN ∧ IsSimpleChain (v₀ :: m₁ ++ [vN]) ∧ IsSimpleChain (vN :: m₂ ++ [v₀]) ∧
    IsSimpleChain (v₀ :: αs.reverse ++ [vN]) ∧
    chainSet (v₀ :: m₁ ++ [vN]) ∩ chainSet (vN :: m₂ ++ [v₀]) = {v₀, vN} ∧
    chainSet (v₀ :: m₁ ++ [vN]) ∩ chainSet (v₀ :: αs.reverse ++ [vN]) = {v₀, vN} ∧
    chainSet (vN :: m₂ ++ [v₀]) ∩ chainSet (v₀ :: αs.reverse ++ [vN]) = {v₀, vN} := by
  obtain ⟨hE, hEset⟩ := h.strip.chord_simple
  have hv₀ : v₀ ∈ segment ℝ w₀ v₀ := right_mem_segment ℝ _ _
  have hvN : vN ∈ segment ℝ wN vN := right_mem_segment ℝ _ _
  have hne : v₀ ≠ vN := by
    intro e
    exact Set.disjoint_left.1 h.keyhole.ss hv₀ (e ▸ hvN)
  subst hβl hβs
  refine ⟨hne, h.keyhole.simpβ, h.strip.simpβ, hE, by rw [inter_comm]; exact h.bb, ?_, ?_⟩
  · rw [hEset]
    ext z; constructor
    · rintro ⟨hzb, (hz | hz) | hz⟩
      · have : z ∈ segment ℝ w₀ v₀ ∩ chainSet (v₀ :: m₁ ++ [vN]) := ⟨hz, hzb⟩
        rw [h.keyhole.sv] at this; exact Or.inl this
      · have : z ∈ chainSet αs ∩ chainSet (v₀ :: m₁ ++ [vN]) := ⟨hz, hzb⟩
        rw [h.ab2] at this; exact this.elim
      · have : z ∈ segment ℝ wN vN ∩ chainSet (v₀ :: m₁ ++ [vN]) := ⟨hz, hzb⟩
        rw [h.keyhole.sv'] at this; exact Or.inr this
    · rintro (rfl | rfl)
      · exact ⟨mem_chainSet_of_head h.keyhole.headβ, Or.inl (Or.inl hv₀)⟩
      · exact ⟨mem_chainSet_of_getLast h.keyhole.lastβ, Or.inr hvN⟩
  · rw [hEset]
    ext z; constructor
    · rintro ⟨hzb, (hz | hz) | hz⟩
      · have : z ∈ segment ℝ w₀ v₀ ∩ chainSet (vN :: m₂ ++ [v₀]) := ⟨hz, hzb⟩
        rw [h.strip.sv'] at this; exact Or.inl this
      · have : z ∈ chainSet αs ∩ chainSet (vN :: m₂ ++ [v₀]) := ⟨hz, hzb⟩
        rw [h.strip.disj] at this; exact this.elim
      · have : z ∈ segment ℝ wN vN ∩ chainSet (vN :: m₂ ++ [v₀]) := ⟨hz, hzb⟩
        rw [h.strip.sv] at this; exact Or.inr this
    · rintro (rfl | rfl)
      · exact ⟨mem_chainSet_of_getLast h.strip.lastβ, Or.inl (Or.inl hv₀)⟩
      · exact ⟨mem_chainSet_of_head h.strip.headβ, Or.inr hvN⟩

/-- The chain hypotheses of the second chord split: the polygon `αs ++ βl` (the outer part, containing the inner
polygon) is cut along the long inner arc `αl`. -/
theorem NestedRing.split2_hyps {w₀ wN v₀ vN : ℝ × ℝ} {αs αl βs βl p₁ q : List (ℝ × ℝ)}
    (h : NestedRing w₀ wN v₀ vN αs αl βs βl) (hαs : αs = wN :: p₁ ++ [w₀]) (hαl : αl.reverse = wN :: q ++ [w₀]) :
    wN ≠ w₀ ∧ IsSimpleChain (wN :: p₁ ++ [w₀]) ∧ IsSimpleChain (w₀ :: βl ++ [wN]) ∧
    IsSimpleChain (wN :: q ++ [w₀]) ∧
    chainSet (wN :: p₁ ++ [w₀]) ∩ chainSet (w₀ :: βl ++ [wN]) = {wN, w₀} ∧
    chainSet (wN :: p₁ ++ [w₀]) ∩ chainSet (wN :: q ++ [w₀]) = {wN, w₀} ∧
    chainSet (w₀ :: βl ++ [wN]) ∩ chainSet (wN :: q ++ [w₀]) = {wN, w₀} := by
  obtain ⟨hE, hEset⟩ := h.keyhole.outer_chord_simple
  have hw₀ : w₀ ∈ segment ℝ w₀ v₀ := left_mem_segment ℝ _ _
  have hwN : wN ∈ segment ℝ wN vN := left_mem_segment ℝ _ _
  have hne : wN ≠ w₀ := by
    intro e
    exact Set.disjoint_left.1 h.keyhole.ss hw₀ (e ▸ hwN)
  have hαlset : chainSet (wN :: q ++ [w₀]) = chainSet αl := by rw [← hαl, chainSet_reverse]
  rw [← hαs] 
  rw [hαlset]
  refine ⟨hne, h.strip.simpα, hE, ?_, ?_, ?_, ?_⟩
  · rw [← hαl]; exact isSimpleChain_reverse h.keyhole.simpα
  · rw [hEset]
    ext z; constructor
    · rintro ⟨hza, (hz | hz) | hz⟩
      · have : z ∈ segment ℝ w₀ v₀ ∩ chainSet αs := ⟨hz, hza⟩
        rw [h.strip.sw'] at this; exact Or.inr this
      · have : z ∈ chainSet αs ∩ chainSet βl := ⟨hza, hz⟩
        rw [h.ab2] at this; exact this.elim
      · have : z ∈ segment ℝ wN vN ∩ chainSet αs := ⟨hz, hza⟩
        rw [h.strip.sw] at this; exact Or.inl this
    · rintro (rfl | rfl)
      · exact ⟨mem_chainSet_of_head h.strip.headα, Or.inr hwN⟩
      · exact ⟨mem_chainSet_of_getLast h.strip.lastα, Or.inl (Or.inl hw₀)⟩
  · have := h.aa
    rw [this, Set.pair_comm]
  · rw [hEset]
    ext z; constructor
    · rintro ⟨(hz | hz) | hz, hza⟩
      · have : z ∈ segment ℝ w₀ v₀ ∩ chainSet αl := ⟨hz, hza⟩
        rw [h.keyhole.sw] at this; exact Or.inr this
      · have : z ∈ chainSet αl ∩ chainSet βl := ⟨hza, hz⟩
        rw [h.keyhole.disj] at this; exact this.elim
      · have : z ∈ segment ℝ wN vN ∩ chainSet αl := ⟨hz, hza⟩
        rw [h.keyhole.sw'] at this; exact Or.inl this
    · rintro (rfl | rfl)
      · exact ⟨Or.inr hwN, mem_chainSet_of_getLast h.keyhole.lastα⟩
      · exact ⟨Or.inl (Or.inl hw₀), mem_chainSet_of_head h.keyhole.headα⟩

end Lightlike.PL.Schoenflies
