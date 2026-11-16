import Lightlike.PL.Bistellar
import Lightlike.PL.Boundary

/-!
# Attaching a triangle along a boundary edge

If the edge `{u, w}` of a complex lies in exactly one triangle `{u, w, x}`, then adding a
triangle `{u, v, w}` on a new vertex `v` gives a stellar equivalent complex: subdivide the edge at
`v`, which turns `{u, w, x}` into `{u, v, x}` and `{v, w, x}`, and then flip the edge `{v, x}` to
`{u, w}`.

## Main results

* `Lightlike.PL.SComplex.stellarEquivIn_closure_insert`
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V]

-- needs 150000–200000 heartbeats (measured); twice the smallest passing limit
set_option maxHeartbeats 400000 in
/-- **Attaching an ear.** -/
theorem stellarEquivIn_closure_insert [Infinite V] {T : Finset (Finset V)} {u w x v : V}
    (huw : u ≠ w) (hxu : x ≠ u) (hxw : x ≠ w)
    (hmem : ({u, w, x} : Finset V) ∈ T) (hv : ∀ t ∈ T, v ∉ t)
    (huniq : ∀ t ∈ T, u ∈ t → w ∈ t → t = {u, w, x}) :
    StellarEquivIn (closure T) (closure (insert ({u, v, w} : Finset V) T)) := by
  classical
  set K := closure T with hK
  set A : Finset V := {u, w} with hA
  have hvu : v ≠ u := fun h => hv _ hmem (by simp [h])
  have hvw : v ≠ w := fun h => hv _ hmem (by simp [h])
  have hvx : v ≠ x := fun h => hv _ hmem (by simp [h])
  have hAK : A ∈ K := mem_closure.2 ⟨{u, w, x}, hmem, by intro y hy; rw [hA] at hy; simp at hy ⊢; tauto⟩
  have hvK : v ∉ K.verts := by
    intro h
    obtain ⟨t, ht, hst⟩ := mem_closure.1 (mem_verts.1 h)
    exact hv t ht (hst (mem_singleton_self v))
  have h1 : StellarEquivIn K (K.starAt A v) :=
    StellarEquivIn.starAt hAK ⟨u, by simp [hA]⟩ hvK
  set t0 : Finset V := {u, w, x} with ht0
  have hKmem : ∀ s, s ∈ K ↔ ∃ t ∈ T, s ⊆ t := fun s => mem_closure
  -- faces containing the edge lie in the triangle
  have F1 : ∀ s ∈ K, A ⊆ s → s ⊆ t0 := by
    intro s hs hAs
    obtain ⟨t, ht, hst⟩ := (hKmem s).1 hs
    have hu : u ∈ t := hst (hAs (by simp [hA]))
    have hw : w ∈ t := hst (hAs (by simp [hA]))
    rw [huniq t ht hu hw] at hst
    exact hst
  have hvK' : ∀ s ∈ K, v ∉ s := by
    intro s hs hvs
    obtain ⟨t, ht, hst⟩ := (hKmem s).1 hs
    exact hv t ht (hst hvs)
  have ht0K : t0 ∈ K := (hKmem t0).2 ⟨t0, hmem, subset_rfl⟩
  have hsub_t0 : ∀ s, s ⊆ t0 → s ∈ K := fun s hs => down_mem ht0K hs
  set K2 := K.starAt A v with hK2
  have hbis : IsBistellar K2 {v, x} {u, w} := by
    refine ⟨⟨v, by simp⟩, ⟨u, by simp⟩, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro y hy hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
      rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl <;> simp_all
    · refine ext_mem fun s => ?_
      rw [mem_link, mem_boundary]
      simp only [hK2, mem_starAt]
      constructor
      · rintro ⟨hs, hdis, h3⟩
        have hvs : v ∉ s := fun h => (Finset.disjoint_left.1 hdis (by simp)) h
        have hxs : x ∉ s := fun h => (Finset.disjoint_left.1 hdis (by simp)) h
        have hsK : s ∈ K ∧ ¬ A ⊆ s := by
          rcases hs with h | ⟨t, -, -, -, h⟩
          · exact h
          · exact absurd (h ▸ mem_insert_self v t) hvs
        rcases h3 with h3 | ⟨t, ht, hAt, hAtK, hte⟩
        · exact absurd (mem_union_left s (by simp : v ∈ ({v, x} : Finset V))) (hvK' _ h3.1)
        · have hst : s ⊆ t := by
            intro y hy
            have : y ∈ insert v t := by rw [hte]; exact mem_union_right _ hy
            rcases mem_insert.1 this with rfl | h
            · exact absurd hy hvs
            · exact h
          have hAt0 : A ∪ t ⊆ t0 := F1 _ hAtK subset_union_left
          have hsA : s ⊆ A := by
            intro y hy
            have := hAt0 (mem_union_right _ (hst hy))
            simp only [ht0, mem_insert, mem_singleton] at this
            rcases this with rfl | rfl | rfl
            · simp [hA]
            · simp [hA]
            · exact absurd hy hxs
          exact Finset.ssubset_iff_subset_ne.2 ⟨hsA, fun h => hsK.2 (h ▸ subset_rfl)⟩
      · intro hs
        have hsA : s ⊆ A := hs.subset
        have hsK : s ∈ K := hsub_t0 s (hsA.trans (by intro y hy; rw [hA] at hy; simp [ht0] at hy ⊢; tauto))
        have hdis : Disjoint ({v, x} : Finset V) s := by
          rw [Finset.disjoint_left]
          intro y hy hys
          have := hsA hys
          rw [hA] at this
          simp only [mem_insert, mem_singleton] at hy this
          rcases hy with rfl | rfl <;> rcases this with rfl | rfl <;> simp_all
        refine ⟨Or.inl ⟨hsK, hs.not_subset⟩, hdis, Or.inr ⟨insert x s, ?_, ?_, ?_, ?_⟩⟩
        · refine hsub_t0 _ ?_
          intro y hy
          rcases mem_insert.1 hy with rfl | h
          · simp [ht0]
          · have := hsA h
            rw [hA] at this
            simp [ht0] at this ⊢; tauto
        · intro h
          apply hs.not_subset
          intro y hy
          have := h hy
          rcases mem_insert.1 this with hyx | h'
          · simp only [mem_insert, mem_singleton] at hy
            rcases hy with h1 | h1
            · rw [h1] at hyx; exact absurd hyx.symm hxu
            · rw [h1] at hyx; exact absurd hyx.symm hxw
          · exact h'
        · refine hsub_t0 _ ?_
          intro y hy
          rcases mem_union.1 hy with h | h
          · rw [hA] at h; simp [ht0] at h ⊢; tauto
          · rcases mem_insert.1 h with rfl | h'
            · simp [ht0]
            · have := hsA h'
              rw [hA] at this
              simp [ht0] at this ⊢; tauto
        · ext y; simp only [mem_insert, mem_union, mem_singleton]; tauto
    · simp only [hK2, mem_starAt]
      rintro (⟨-, h⟩ | ⟨t, -, -, -, h⟩)
      · exact h subset_rfl
      · have : v ∈ ({u, w} : Finset V) := h ▸ mem_insert_self v t
        simp at this
        rcases this with h | h <;> simp_all
  have hxnotuvw : x ∉ ({u, v, w} : Finset V) := by
    simp only [mem_insert, mem_singleton]; rintro (h | h | h)
    · exact hxu h
    · exact hvx h.symm
    · exact hxw h
  have hsub_A : ∀ s, s ⊆ A → s ⊆ t0 := fun s hs y hy => by
    have := hs hy
    rw [hA] at this
    simp only [ht0, mem_insert, mem_singleton] at this ⊢
    tauto
  have heq : K2.bistellar {v, x} {u, w} hbis = closure (insert ({u, v, w} : Finset V) T) := by
    refine ext_mem fun s => ?_
    rw [mem_bistellar, mem_closure]
    simp only [hK2, mem_starAt, Finset.mem_insert]
    constructor
    · rintro (⟨(⟨hsK, hsA⟩ | ⟨t, htK, hAt, hAtK, hte⟩), hnot⟩ | ⟨t, ht, rfl⟩)
      · obtain ⟨t', ht', hst'⟩ := (hKmem s).1 hsK
        exact ⟨t', Or.inr ht', hst'⟩
      · subst hte
        have hxt : x ∉ t := fun h => hnot (by
          intro y hy
          simp only [mem_insert, mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact mem_insert_self _ _
          · exact mem_insert_of_mem h)
        have hAt0 : A ∪ t ⊆ t0 := F1 _ hAtK subset_union_left
        have htA : t ⊆ A := by
          intro y hy
          have := hAt0 (mem_union_right _ hy)
          simp only [ht0, mem_insert, mem_singleton] at this
          rcases this with rfl | rfl | rfl
          · simp [hA]
          · simp [hA]
          · exact absurd hy hxt
        refine ⟨{u, v, w}, Or.inl rfl, ?_⟩
        intro y hy
        rcases mem_insert.1 hy with rfl | h
        · simp
        · have := htA h
          rw [hA] at this
          simp only [mem_insert, mem_singleton] at this ⊢
          tauto
      · by_cases hxt : x ∈ t
        · have hvt : v ∉ t := fun hvt => ht.2 (by
            intro y hy
            simp only [mem_insert, mem_singleton] at hy
            rcases hy with rfl | rfl
            · exact hvt
            · exact hxt)
          refine ⟨t0, Or.inr hmem, ?_⟩
          intro y hy
          rcases mem_union.1 hy with h | h
          · have := ht.1 h
            simp only [mem_insert, mem_singleton] at this
            rcases this with rfl | rfl
            · exact absurd h hvt
            · simp [ht0]
          · simp only [mem_insert, mem_singleton] at h
            simp only [ht0, mem_insert, mem_singleton]; tauto
        · refine ⟨{u, v, w}, Or.inl rfl, ?_⟩
          intro y hy
          rcases mem_union.1 hy with h | h
          · have := ht.1 h
            simp only [mem_insert, mem_singleton] at this
            rcases this with rfl | rfl
            · simp
            · exact absurd h hxt
          · simp only [mem_insert, mem_singleton] at h ⊢; tauto
    · have hxs_not : ∀ s : Finset V, s ⊆ {u, v, w} → ¬ ({v, x} : Finset V) ⊆ s := fun s hs h =>
        hxnotuvw (hs (h (by simp)))
      rintro ⟨t, ht | ht, hst⟩
      · -- the new triangle
        subst ht
        by_cases hAs : A ⊆ s
        · right
          by_cases hvs : v ∈ s
          · refine ⟨{v}, ?_, ?_⟩
            · exact Finset.ssubset_iff_subset_ne.2 ⟨by simp, by
                intro h
                have : x ∈ ({v} : Finset V) := by rw [h]; simp
                simp at this; exact hvx this.symm⟩
            · ext y
              simp only [mem_union, mem_singleton]
              constructor
              · rintro (rfl | h)
                · exact hvs
                · exact hAs (by simpa [hA] using h)
              · intro hy
                have := hst hy
                simp only [mem_insert, mem_singleton] at this
                simp only [mem_insert, mem_singleton]
                tauto
          · refine ⟨∅, ?_, ?_⟩
            · exact Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, by
                intro h
                have : v ∈ (∅ : Finset V) := by rw [h]; simp
                simp at this⟩
            · ext y
              simp only [mem_union, notMem_empty, false_or]
              constructor
              · intro h; exact hAs (by simpa [hA] using h)
              · intro hy
                have := hst hy
                simp only [mem_insert, mem_singleton] at this
                rcases this with rfl | rfl | rfl
                · simp
                · exact absurd hy hvs
                · simp
        · left
          refine ⟨?_, hxs_not s hst⟩
          by_cases hvs : v ∈ s
          · right
            refine ⟨s.erase v, ?_, ?_, ?_, insert_erase hvs⟩
            · refine hsub_t0 _ ?_
              intro y hy
              have h1 := mem_erase.1 hy
              have := hst h1.2
              simp only [ht0, mem_insert, mem_singleton] at this ⊢
              tauto
            · intro h; apply hAs
              intro y hy
              have := h hy
              by_cases hyv : y = v
              · exfalso
                rw [hyv] at hy
                simp only [hA, mem_insert, mem_singleton] at hy
                rcases hy with h' | h' <;> simp_all
              · exact mem_of_mem_erase this
            · refine hsub_t0 _ ?_
              intro y hy
              rcases mem_union.1 hy with h | h
              · rw [hA] at h
                simp only [ht0, mem_insert, mem_singleton] at h ⊢
                tauto
              · have h1 := mem_erase.1 h
                have := hst h1.2
                simp only [ht0, mem_insert, mem_singleton] at this ⊢
                tauto
          · left
            refine ⟨hsub_t0 s ?_, hAs⟩
            intro y hy
            have := hst hy
            simp only [mem_insert, mem_singleton] at this
            simp only [ht0, mem_insert, mem_singleton]
            rcases this with rfl | rfl | rfl
            · tauto
            · exact absurd hy hvs
            · tauto
      · -- a triangle of `T`
        have hsK : s ∈ K := (hKmem s).2 ⟨t, ht, hst⟩
        by_cases hAs : A ⊆ s
        · right
          have hs0 : s ⊆ t0 := F1 s hsK hAs
          by_cases hxs : x ∈ s
          · refine ⟨{x}, ?_, ?_⟩
            · refine Finset.ssubset_iff_subset_ne.2 ⟨by intro y hy; simp at hy ⊢; tauto, ?_⟩
              intro h
              have : v ∈ ({x} : Finset V) := by rw [h]; simp
              simp at this; exact hvx this
            · ext y
              simp only [mem_union, mem_singleton]
              constructor
              · rintro (rfl | h)
                · exact hxs
                · exact hAs (by simpa [hA] using h)
              · intro hy
                by_cases hyx : y = x
                · exact Or.inl hyx
                · right
                  have := hs0 hy
                  simp only [ht0, mem_insert, mem_singleton] at this
                  simpa using (by tauto : y = u ∨ y = w)
          · refine ⟨∅, ?_, ?_⟩
            · exact Finset.ssubset_iff_subset_ne.2 ⟨empty_subset _, by
                intro h
                have : v ∈ (∅ : Finset V) := by rw [h]; simp
                simp at this⟩
            · ext y
              simp only [mem_union, notMem_empty, false_or]
              constructor
              · intro h; exact hAs (by simpa [hA] using h)
              · intro hy
                have := hs0 hy
                simp only [ht0, mem_insert, mem_singleton] at this
                rcases this with rfl | rfl | rfl
                · simp
                · simp
                · exact absurd hy hxs
        · left
          refine ⟨Or.inl ⟨hsK, hAs⟩, fun h => ?_⟩
          exact hvK' s hsK (h (by simp))
  rw [← heq]
  exact h1.trans (StellarEquivIn.bistellar' hbis)

end SComplex
end Lightlike.PL
