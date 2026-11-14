import Lightlike.Surfaces.Glue

/-!
# Moves commute with connected sums

If two closed surfaces `M₁` and `M₂` are related by 2D moves, so are their connected sums with
a good piece `P` (`GoodPiece.add`), whatever triangles and labellings are used for the gluings.

A single move of `M₁` leaves some triangle `ρ` untouched (`IsSurface.exists_untouched`). Glued
at `ρ` with labels fresh for both complexes, the copy of `P` lies away from the move, so the
same move applies to the connected sum (`IsGlue.move_sub`, `IsGlue.move_flip`). Homogeneity
(`GoodPiece.homog`) moves any other gluing to this one, and induction over `EqvGen` gives the
general case.
-/

open Finset Relation

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Two set identities -/

/-- Erasing commutes with erasing `ρ` and adding a part `N` that does not contain the erased
triangle. -/
lemma union_erase_swap {X N : Finset (Finset V)} {ρ a : Finset V} (ha : a ∉ N) :
    (X.erase ρ ∪ N).erase a = (X.erase a).erase ρ ∪ N := by
  rw [erase_union_distrib, erase_eq_of_notMem ha, erase_right_comm]

/-- Inserting a triangle `a ≠ ρ` commutes with erasing `ρ` and adding a part `N`. -/
lemma insert_erase_union_of_ne {X N : Finset (Finset V)} {ρ a : Finset V} (h : a ≠ ρ) :
    (insert a X).erase ρ ∪ N = insert a (X.erase ρ ∪ N) := by
  rw [erase_insert_of_ne h, insert_union]

/-! ## The glued copy lies away from the rest of the surface -/

section glue

variable {P : Finset (Finset ℕ)} {τ₀ : Finset ℕ} {M : Finset (Finset V)} {ρ : Finset V}
  {g : ℕ ↪ V}

/-- A vertex of the glued copy of `P` that is a vertex of `M` lies in the gluing triangle. -/
lemma IsGlue.mem_site (hg : IsGlue M ρ P τ₀ g) {t : Finset ℕ} (ht : t ∈ P) {v : V}
    (hv : v ∈ t.map g) (hvM : v ∈ verts2 M) : v ∈ ρ := by
  obtain ⟨n, hn, rfl⟩ := mem_map.mp hv
  by_cases h : n ∈ τ₀
  · rw [← hg.map]
    exact mem_map_of_mem g h
  · exact absurd hvM (hg.fresh n (mem_verts2.mpr ⟨t, ht, hn⟩) h)

/-- An edge of `M` that is not an edge of the gluing triangle lies in no triangle of the glued
copy. -/
lemma IsGlue.not_subset (hg : IsGlue M ρ P τ₀ g) {u w : V} (hu : u ∈ verts2 M)
    (hw : w ∈ verts2 M) (h : ¬ ({u, w} : Finset V) ⊆ ρ) :
    ∀ τ ∈ liftK g (P.erase τ₀), ¬ ({u, w} : Finset V) ⊆ τ := by
  intro τ hτ hsub
  obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hτ
  refine h (insert_subset_iff.mpr ⟨?_, singleton_subset_iff.mpr ?_⟩)
  · exact hg.mem_site (mem_of_mem_erase ht) (hsub (mem_insert_self _ _)) hu
  · exact hg.mem_site (mem_of_mem_erase ht) (hsub (mem_insert_of_mem (mem_singleton_self _))) hw

/-- No triangle of the glued copy is a triangle of `M`. -/
lemma IsGlue.notMem (hg : IsGlue M ρ P τ₀ g) (hPt : IsTri2 P) (hMt : IsTri2 M) {τ : Finset V}
    (hτ : τ ∈ liftK g (P.erase τ₀)) : τ ∉ M := by
  intro hm
  obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hτ
  have hsub : t.map g ⊆ ρ := fun v hv =>
    hg.mem_site (mem_of_mem_erase ht) hv (mem_verts2.mpr ⟨_, hm, hv⟩)
  have heq : t.map g = ρ := eq_of_subset_of_card_le hsub (by
    rw [card_map, hPt t (mem_of_mem_erase ht), hMt ρ hg.mem])
  exact ne_of_mem_erase ht (map_injective g (heq.trans hg.map.symm))

/-- **A subdivision away from the gluing triangle lifts** to the connected sum. -/
lemma IsGlue.move_sub (hg : IsGlue M ρ P τ₀ g) (hPt : IsTri2 P) (hMt : IsTri2 M) {b c d x : V}
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hτ : ({b, c, d} : Finset V) ∈ M)
    (hx : x ∉ verts2 M) (hρ : ρ ≠ {b, c, d}) (hgx : ∀ n ∈ verts2 P, n ∉ τ₀ → g n ≠ x) :
    Move2 (csum M ρ P τ₀ g) (csum (subRes M b c d x) ρ P τ₀ g) := by
  have hxρ : x ∉ ρ := fun h => hx (mem_verts2.mpr ⟨ρ, hg.mem, h⟩)
  have hN : ({b, c, d} : Finset V) ∉ liftK g (P.erase τ₀) := fun h => hg.notMem hPt hMt h hτ
  have hne : ∀ u w : V, ({u, w, x} : Finset V) ≠ ρ := fun u w h => hxρ (by rw [← h]; simp)
  have e1 : csum (subRes M b c d x) ρ P τ₀ g =
      insert {b, c, x} (insert {c, d, x} (insert {b, d, x} ((csum M ρ P τ₀ g).erase {b, c, d}))) := by
    unfold csum subRes
    rw [insert_erase_union_of_ne (hne b c), insert_erase_union_of_ne (hne c d),
      insert_erase_union_of_ne (hne b d), union_erase_swap hN]
  rw [e1]
  refine Move2.sub13 hbc hbd hcd (mem_union_left _ (mem_erase.mpr ⟨Ne.symm hρ, hτ⟩)) ?_
  rw [csum, verts2_union, mem_union, not_or]
  refine ⟨fun h => hx ?_, fun h => ?_⟩
  · obtain ⟨τ, hτ', hxτ⟩ := mem_verts2.mp h
    exact mem_verts2.mpr ⟨τ, mem_of_mem_erase hτ', hxτ⟩
  · obtain ⟨τ, hτ', hxτ⟩ := mem_verts2.mp h
    obtain ⟨t, ht, rfl⟩ := mem_liftK.mp hτ'
    obtain ⟨n, hn, hgn⟩ := mem_map.mp hxτ
    by_cases hn0 : n ∈ τ₀
    · apply hxρ
      rw [← hgn, ← hg.map]
      exact mem_map_of_mem g hn0
    · exact hgx n (mem_verts2.mpr ⟨t, mem_of_mem_erase ht, hn⟩) hn0 hgn

/-- **A flip away from the gluing triangle lifts** to the connected sum. -/
lemma IsGlue.move_flip (hg : IsGlue M ρ P τ₀ g) (hPt : IsTri2 P) (hMt : IsTri2 M) {b c d e : V}
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (h₁ : ({b, c, d} : Finset V) ∈ M) (h₂ : ({b, c, e} : Finset V) ∈ M)
    (hstar : ∀ τ ∈ M, ({b, c} : Finset V) ⊆ τ → τ = {b, c, d} ∨ τ = {b, c, e})
    (hfresh : ∀ τ ∈ M, ¬ ({d, e} : Finset V) ⊆ τ) (hρ₁ : ρ ≠ {b, c, d}) (hρ₂ : ρ ≠ {b, c, e}) :
    Move2 (csum M ρ P τ₀ g) (csum (flipRes M b c d e) ρ P τ₀ g) := by
  have hbcρ : ¬ ({b, c} : Finset V) ⊆ ρ := fun h => (hstar ρ hg.mem h).elim hρ₁ hρ₂
  have hdeρ : ¬ ({d, e} : Finset V) ⊆ ρ := hfresh ρ hg.mem
  have hb : b ∈ verts2 M := mem_verts2.mpr ⟨_, h₁, by simp⟩
  have hc : c ∈ verts2 M := mem_verts2.mpr ⟨_, h₁, by simp⟩
  have hd : d ∈ verts2 M := mem_verts2.mpr ⟨_, h₁, by simp⟩
  have he : e ∈ verts2 M := mem_verts2.mpr ⟨_, h₂, by simp⟩
  have hN1 : ({b, c, d} : Finset V) ∉ liftK g (P.erase τ₀) := fun h => hg.notMem hPt hMt h h₁
  have hN2 : ({b, c, e} : Finset V) ∉ liftK g (P.erase τ₀) := fun h => hg.notMem hPt hMt h h₂
  have hbde : ({b, d, e} : Finset V) ≠ ρ := fun h => hdeρ (by rw [← h]; simp)
  have hcde : ({c, d, e} : Finset V) ≠ ρ := fun h => hdeρ (by rw [← h]; simp)
  have e1 : csum (flipRes M b c d e) ρ P τ₀ g =
      insert {b, d, e} (insert {c, d, e} (((csum M ρ P τ₀ g).erase {b, c, d}).erase {b, c, e})) := by
    unfold csum flipRes
    rw [insert_erase_union_of_ne hbde, insert_erase_union_of_ne hcde, union_erase_swap hN1,
      union_erase_swap hN2]
  rw [e1]
  refine Move2.flip22 hbc hbd hbe hcd hce hde (mem_union_left _ (mem_erase.mpr ⟨Ne.symm hρ₁, h₁⟩))
    (mem_union_left _ (mem_erase.mpr ⟨Ne.symm hρ₂, h₂⟩)) ?_ ?_
  · intro τ hτ hsub
    rcases mem_union.mp (show τ ∈ M.erase ρ ∪ liftK g (P.erase τ₀) from hτ) with hτ | hτ
    · exact hstar τ (mem_of_mem_erase hτ) hsub
    · exact absurd hsub (hg.not_subset hb hc hbcρ τ hτ)
  · intro τ hτ hsub
    rcases mem_union.mp (show τ ∈ M.erase ρ ∪ liftK g (P.erase τ₀) from hτ) with hτ | hτ
    · exact hfresh τ (mem_of_mem_erase hτ) hsub
    · exact hg.not_subset hd he hdeρ τ hτ hsub

end glue

/-! ## A move leaves a triangle untouched -/

/-- A triangle `{b, d, y}` is different from `{b, c, d}` and `{b, c, e}` when `c ∉ {b, d, y}`. -/
lemma tri_ne_of_notMem {b c d e y : V} (hcb : c ≠ b) (hcd : c ≠ d) (hcy : c ≠ y) :
    ({b, d, y} : Finset V) ≠ {b, c, d} ∧ ({b, d, y} : Finset V) ≠ {b, c, e} := by
  have hc : c ∉ ({b, d, y} : Finset V) := by simp [hcb, hcd, hcy]
  exact ⟨fun h => hc (by rw [h]; simp), fun h => hc (by rw [h]; simp)⟩

/-- **A move of a closed surface lifts to its connected sums.** For a move `M₁ → M₂` there is a
triangle `ρ` of both, such that any gluing of `P` to `ρ` with interior labels outside `M₂` turns
the move into a move of the connected sums. -/
theorem IsSurface.lift_move {M₁ M₂ : Finset (Finset V)} (hM : IsSurface M₁) (h : Move2 M₁ M₂)
    {P : Finset (Finset ℕ)} (hPt : IsTri2 P) (τ₀ : Finset ℕ) :
    ∃ ρ ∈ M₁, ρ ∈ M₂ ∧ ∀ g : ℕ ↪ V, IsGlue M₁ ρ P τ₀ g →
      (∀ n ∈ verts2 P, n ∉ τ₀ → g n ∉ verts2 M₂) →
      Move2 (csum M₁ ρ P τ₀ g) (csum M₂ ρ P τ₀ g) := by
  cases h with
  | @sub13 b c d x hbc hbd hcd hτ hx =>
    obtain ⟨y, hyd, hyb, hyc, hy, -⟩ := hM.other_tri hτ
    have hne : ({b, c, y} : Finset V) ≠ {b, c, d} := by
      intro h
      have : y ∈ ({b, c, d} : Finset V) := by rw [← h]; simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h
      · exact hyb h
      · exact hyc h
      · exact hyd h
    refine ⟨{b, c, y}, hy, mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
      (mem_erase.mpr ⟨hne, hy⟩))), fun g hg hg₂ => ?_⟩
    refine hg.move_sub hPt hM.card hbc hbd hcd hτ hx hne fun n hn hn0 hgx => ?_
    refine hg₂ n hn hn0 ?_
    rw [hgx]
    exact mem_verts2.mpr ⟨_, mem_insert_self _ _, by simp⟩
  | @flip22 b c d e hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh =>
    have h₁' := h₁
    rw [show ({b, c, d} : Finset V) = {b, d, c} by
      ext; simp only [mem_insert, mem_singleton]; tauto] at h₁'
    obtain ⟨y, hyc, hyb, hyd, hy, -⟩ := hM.other_tri h₁'
    obtain ⟨hne₁, hne₂⟩ := tri_ne_of_notMem (e := e) hbc.symm hcd (Ne.symm hyc)
    refine ⟨{b, d, y}, hy, mem_insert_of_mem (mem_insert_of_mem
      (mem_erase.mpr ⟨hne₂, mem_erase.mpr ⟨hne₁, hy⟩⟩)), fun g hg _ => ?_⟩
    exact hg.move_flip hPt hM.card hbc hbd hbe hcd hce hde h₁ h₂ hstar hfresh hne₁ hne₂

/-! ## Moves commute with connected sums -/

section add

variable {P : Finset (Finset ℕ)} {k : ℕ}

/-- **Connected sums of move-equivalent surfaces are move-equivalent.** If `M₁` is a closed
surface related to `M₂` by 2D moves, any connected sum of `M₁` with a good piece `P` is related
by moves to any connected sum of `M₂` with `P`. -/
theorem GoodPiece.add [Infinite V] (hP : GoodPiece P k) {M₁ M₂ : Finset (Finset V)}
    (h : EqvGen Move2 M₁ M₂) (hM : IsSurface M₁) {s t : Finset V} {f g : ℕ ↪ V}
    (hf : IsGlue M₁ s P {0, 1, 2} f) (hg : IsGlue M₂ t P {0, 1, 2} g) :
    EqvGen Move2 (csum M₁ s P {0, 1, 2} f) (csum M₂ t P {0, 1, 2} g) := by
  suffices H : ∀ M₁ M₂ : Finset (Finset V), EqvGen Move2 M₁ M₂ → IsSurface M₁ →
      ∀ (s t : Finset V) (f g : ℕ ↪ V), IsGlue M₁ s P {0, 1, 2} f → IsGlue M₂ t P {0, 1, 2} g →
      EqvGen Move2 (csum M₁ s P {0, 1, 2} f) (csum M₂ t P {0, 1, 2} g) from
    H M₁ M₂ h hM s t f g hf hg
  intro M₁ M₂ h
  induction h with
  | rel M₁ M₂ hmv =>
    intro hM s t f g hf hg
    have hM₂ := (Move2.isSurface_iff hmv).mp hM
    obtain ⟨ρ, hρ₁, hρ₂, hlift⟩ := hM.lift_move hmv hP.tri {0, 1, 2}
    obtain ⟨h', hh, hhF⟩ := exists_glue hP hM.card hρ₁ (verts2 M₂)
    have hfr : ∀ n ∈ verts2 P, n ∉ ({0, 1, 2} : Finset ℕ) → h' n ∉ verts2 M₂ := by
      intro n _ hn
      simp only [mem_insert, mem_singleton, not_or] at hn
      exact hhF n (by omega)
    have hh₂ : IsGlue M₂ ρ P {0, 1, 2} h' := ⟨hρ₂, hh.mem₀, hh.map, hfr⟩
    exact EqvGen.trans _ _ _ (EqvGen.trans _ _ _ (hP.homog hM hf hh)
      (EqvGen.rel _ _ (hlift h' hh hfr))) (hP.homog hM₂ hh₂ hg)
  | refl M =>
    intro hM s t f g hf hg
    exact hP.homog hM hf hg
  | symm M₁ M₂ h₂₁ ih =>
    intro hM s t f g hf hg
    have hM₂ := (isSurface_iff_of_eqvGen h₂₁).mpr hM
    exact EqvGen.symm _ _ (ih hM₂ t s g f hg hf)
  | trans M₁ M₂ M₃ h₁₂ _ ih₁ ih₂ =>
    intro hM s t f g hf hg
    have hM₂ := (isSurface_iff_of_eqvGen h₁₂).mp hM
    obtain ⟨ρ, hρ⟩ := hM₂.nonempty
    obtain ⟨h', hh, -⟩ := exists_glue hP hM₂.card hρ ∅
    exact EqvGen.trans _ _ _ (ih₁ hM s ρ f h' hf hh) (ih₂ hM₂ ρ t h' g hh hg)

end add

end Lightlike.Surfaces
