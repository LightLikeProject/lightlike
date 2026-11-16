import Lightlike.SpinFoam.Move15Global

/-!
# Forcing gauge sets along 4D Pachner moves

`Forces K U T` says that the triangles `U` follow from `T` by the rule "a tetrahedron with three of
its triangles in the set forces the fourth" (`Lightlike.SpinFoam.Forces`). This file proves that the
1-5 move keeps a forcing gauge set forcing.

The statements are for complexes reached from `∂Δ⁵` by 3-3, 2-4 and 1-5 moves; nothing here says
that a forcing gauge set exists on every triangulation of the 4-sphere (numerical evidence in
`scripts/spinfoam/forcechain.py` shows that the inverse moves 4-2 and 5-1 can lose forcing of the
transported set).

## Main results

* `Forces.mono`, `Forces.of_union`, `Forces.mono_target`, `forces_of_direct`: forcing is monotone
  in the tetrahedra and composes.
* `Move15.forces_move15`: a set that forces `K` forces the complex after a 1-5 move once the four
  gauge triangles of the move are added.
-/

open Finset Lightlike.FourD Complex4

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- Forcing is monotone in the complex (more tetrahedra) and in the starting set. -/
theorem Forces.mono {K K' : Complex4 V} {U T T' : Finset (Finset V)} (h : Forces K U T)
    (hK : K.tets ⊆ K'.tets) (hT : T ⊆ T') : Forces K' U T' := by
  induction h generalizing T' with
  | done h => exact .done (h.trans hT)
  | step t f ht hf hg _ ih =>
    exact .step t f (hK ht) hf (fun g hg' hne => hT (hg g hg' hne)) (ih (insert_subset_insert f hT))

/-- Forcing composes: what `T` forces, together with `T`, forces whatever `T ∪ U` forces. -/
theorem Forces.of_union {K : Complex4 V} {U U' T : Finset (Finset V)} (h : Forces K U T)
    (h' : Forces K U' (T ∪ U)) : Forces K U' T := by
  induction h with
  | done hU => rwa [union_eq_left.mpr hU] at h'
  | step t f ht hf hg _ ih =>
    refine .step t f ht hf hg (ih ?_)
    exact h'.mono subset_rfl (by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact mem_union_left _ (mem_insert_of_mem hx)
      · exact mem_union_right _ hx)

/-- A smaller target set is forced when a larger one is, or when it is already in the set. -/
theorem Forces.mono_target {K : Complex4 V} {U U' T : Finset (Finset V)} (h : Forces K U T)
    (hU : U' ⊆ U ∪ T) : Forces K U' T := by
  induction h generalizing U' with
  | done hU0 =>
    refine .done fun x hx => ?_
    rcases mem_union.mp (hU hx) with hx' | hx'
    · exact hU0 hx'
    · exact hx'
  | step t f ht hf hg _ ih =>
    refine .step t f ht hf hg (ih fun x hx => ?_)
    rcases mem_union.mp (hU hx) with hx' | hx'
    · exact mem_union_left _ hx'
    · exact mem_union_right _ (mem_insert_of_mem hx')

/-- If every triangle of `N` is forced in one step from `Z` by a tetrahedron, then `Z` forces `N`. -/
theorem forces_of_direct {K : Complex4 V} (N : Finset (Finset V)) :
    ∀ Z : Finset (Finset V),
      (∀ f ∈ N, ∃ t ∈ K.tets, f ∈ t.powersetCard 3 ∧ ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ Z) →
      Forces K N Z := by
  induction N using Finset.induction_on with
  | empty => exact fun Z _ => .done (empty_subset _)
  | insert f N hfN ih =>
    intro Z hZ
    obtain ⟨t, ht, hft, hg⟩ := hZ f (mem_insert_self _ _)
    refine .step t f ht hft hg ?_
    refine (ih (insert f Z) fun g hg' => ?_).mono_target ?_
    · obtain ⟨t', ht', hgt, hh⟩ := hZ g (mem_insert_of_mem hg')
      exact ⟨t', ht', hgt, fun x hx hne => mem_insert_of_mem (hh x hx hne)⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_union_right _ (mem_insert_self _ _)
      · exact mem_union_left _ hx

/-- A set of at most three elements is at most 3 in size. -/
lemma card_le_three (p q r : V) : #(insert p (insert q {r})) ≤ 3 :=
  (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))

namespace Move15

variable {K : Complex4 V} {σ τ : Finset V} (h : Complex4.IsMove K σ τ)
include h

/-- The 1-5 move only adds tetrahedra. -/
lemma tets_subset_move15 (hσ : #σ = 5) : K.tets ⊆ (Complex4.move K h).tets := by
  intro f hf
  obtain ⟨s, hs, hfs, hc⟩ := Complex4.mem_faces.mp hf
  by_cases hsσ : σ ⊆ s
  · have hss : σ = s := eq_of_subset_of_card_le hsσ (by rw [K.card_eq s hs, hσ])
    subst hss
    obtain ⟨u, hu, hnf⟩ : ∃ u ∈ σ, u ∉ f := by
      by_contra hcon
      have : σ ⊆ f := fun u hu => not_not.mp fun hn => hcon ⟨u, hu, hn⟩
      have := card_le_card this
      omega
    exact Complex4.mem_faces.mpr ⟨(σ ∪ τ).erase u, Complex4.mem_move.mpr (Or.inr ⟨u, hu, rfl⟩),
      Complex4.subset_erase_of_notMem (hfs.trans subset_union_left) hnf, hc⟩
  · exact Complex4.mem_faces.mpr ⟨s, Complex4.mem_move.mpr (Or.inl ⟨hs, hsσ⟩), hfs, hc⟩

variable {v : V} (hτ : τ = {v})
include hτ

/-- The 4-simplex `σ` of a 1-5 move is a 4-simplex of `K`. -/
lemma mem_simps_of_move15 : σ ∈ K.simps := by
  have hv : v ∉ σ := hvσ h hτ
  have := h.mem v (by rw [hτ]; exact mem_singleton_self v)
  rwa [show (σ ∪ τ).erase v = σ by
    ext x; simp only [mem_erase, mem_union, hτ, mem_singleton]
    constructor
    · rintro ⟨hx, hx' | hx'⟩
      · exact hx'
      · exact absurd hx' hx
    · intro hx; exact ⟨fun e => hv (e ▸ hx), Or.inl hx⟩] at this

/-- A triangle of the complex after a 1-5 move is a triangle of `K` or has the form `{v, x, y}`
with `x ≠ y` in `σ`. -/
lemma tris_move15 {f : Finset V} (hf : f ∈ (Complex4.move K h).tris) :
    f ∈ K.tris ∨ ∃ x ∈ σ, ∃ y ∈ σ, x ≠ y ∧ f = insert v {x, y} := by
  have hv : v ∉ σ := hvσ h hτ
  obtain ⟨s, hs, hfs, hc⟩ := Complex4.mem_faces.mp hf
  rcases Complex4.mem_move.mp hs with ⟨hsK, -⟩ | ⟨u, hu, rfl⟩
  · exact Or.inl (Complex4.mem_faces.mpr ⟨s, hsK, hfs, hc⟩)
  · have hsub : ∀ x ∈ f, x ≠ v → x ∈ σ := fun x hx hxv => by
      have := hfs hx
      simp only [mem_erase, mem_union, hτ, mem_singleton] at this
      rcases this.2 with h' | h'
      · exact h'
      · exact absurd h' hxv
    by_cases hvf : v ∈ f
    · right
      have hc2 : #(f.erase v) = 2 := by rw [card_erase_of_mem hvf, hc]
      obtain ⟨x, y, hxy, hg⟩ := card_eq_two.mp hc2
      have hx : x ∈ f.erase v := by rw [hg]; simp
      have hy : y ∈ f.erase v := by rw [hg]; simp
      refine ⟨x, hsub x (mem_of_mem_erase hx) (mem_erase.mp hx).1, y,
        hsub y (mem_of_mem_erase hy) (mem_erase.mp hy).1, hxy, ?_⟩
      rw [← hg, insert_erase hvf]
    · left
      exact Complex4.mem_faces.mpr ⟨σ, mem_simps_of_move15 h hτ,
        fun x hx => hsub x hx (fun e => hvf (e ▸ hx)), hc⟩

/-- **A forcing gauge set stays forcing under the 1-5 move.** If `T` forces every triangle of `K`,
then `T` together with the four gauge triangles `{v, a_0, a_j}` of the move forces every triangle
of the complex after the move. This is for complexes reached by the moves treated here; it says
nothing about the inverse 5-1 move, where the transported set can fail to force
(`scripts/spinfoam/forcechain.py`). -/
theorem forces_move15 (hσ : #σ = 5) {a : Fin 5 → V}
    (hsurj : ∀ x, x ∈ σ ↔ ∃ j, a j = x) {T : Finset (Finset V)} (hF : Forces K K.tris T) :
    Forces (Complex4.move K h) (Complex4.move K h).tris (gaugeTri a v ∪ T) := by
  have hv : v ∉ σ := hvσ h hτ
  have hmemσ : ∀ j, a j ∈ σ := fun j => (hsurj _).mpr ⟨j, rfl⟩
  have hgt : ∀ z ∈ σ, z ≠ a 0 → insert v (insert (a 0) {z}) ∈ gaugeTri a v := by
    intro z hz hne
    obtain ⟨j, rfl⟩ := (hsurj z).mp hz
    exact mem_image.mpr ⟨j, mem_erase.mpr ⟨fun e => hne (e ▸ rfl), mem_univ _⟩, rfl⟩
  have h1 : Forces (Complex4.move K h) K.tris (gaugeTri a v ∪ T) :=
    hF.mono (tets_subset_move15 h hσ) subset_union_right
  set Z : Finset (Finset V) := (gaugeTri a v ∪ T) ∪ K.tris with hZ
  have hσK := mem_simps_of_move15 h hτ
  have hdirect : ∀ f ∈ (Complex4.move K h).tris \ Z, ∃ t ∈ (Complex4.move K h).tets,
      f ∈ t.powersetCard 3 ∧ ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ Z := by
    intro f hfm
    obtain ⟨hf, hfZ⟩ := mem_sdiff.mp hfm
    obtain hfK | ⟨x, hx, y, hy, hxy, rfl⟩ := tris_move15 h hτ hf
    · exact absurd (mem_union_right _ hfK) hfZ
    · have hc3 : #(insert v {x, y}) = 3 := by
        have := (Complex4.mem_faces.mp hf); obtain ⟨_, _, _, hc⟩ := this; omega
      have hxa : x ≠ a 0 := fun e => hfZ (mem_union_left _ (mem_union_left _ (by
        have := hgt y hy (fun e' => hxy (e.trans e'.symm)); rw [e]; simpa using this)))
      have hya : y ≠ a 0 := fun e => hfZ (mem_union_left _ (mem_union_left _ (by
        have := hgt x hx (fun e' => hxy (e'.trans e.symm)); rw [e, pair_comm]; simpa using this)))
      have hxv : x ≠ v := fun e => hv (e ▸ hx)
      have hyv : y ≠ v := fun e => hv (e ▸ hy)
      have hav : a 0 ≠ v := fun e => hv (e ▸ hmemσ 0)
      set t : Finset V := insert v (insert (a 0) {x, y}) with ht
      have htc : #t = 4 := by
        rw [ht, card_insert_of_notMem, card_insert_of_notMem, card_pair hxy]
        · simp [hxa.symm, hya.symm]
        · simp [hav.symm, hxv.symm, hyv.symm]
      obtain ⟨u, hu, hut⟩ : ∃ u ∈ σ, u ∉ t := by
        by_contra hcon
        have hsub : σ ⊆ insert (a 0) {x, y} := fun u hu => by
          by_contra hn
          exact hcon ⟨u, hu, by
            simp only [ht, mem_insert, mem_singleton] at hn ⊢
            rintro (rfl | h' | h' | h')
            · exact hv hu
            · exact hn (by simp [h'])
            · exact hn (by simp [h'])
            · exact hn (by simp [h'])⟩
        have := card_le_card hsub
        have := card_le_three (a 0) x y
        omega
      refine ⟨t, Complex4.mem_faces.mpr ⟨(σ ∪ τ).erase u,
        Complex4.mem_move.mpr (Or.inr ⟨u, hu, rfl⟩), ?_, htc⟩, ?_, ?_⟩
      · refine Complex4.subset_erase_of_notMem ?_ hut
        intro z hz
        simp only [ht, mem_insert, mem_singleton] at hz
        rw [hτ]
        rcases hz with rfl | rfl | rfl | rfl
        · exact mem_union_right _ (mem_singleton_self _)
        · exact mem_union_left _ (hmemσ 0)
        · exact mem_union_left _ hx
        · exact mem_union_left _ hy
      · exact mem_powersetCard.mpr ⟨by
          intro z hz; simp only [ht, mem_insert, mem_singleton] at hz ⊢; tauto, hc3⟩
      · intro g hg hgf
        obtain ⟨hgt', hgc⟩ := mem_powersetCard.mp hg
        have hcs : #(t \ g) = 1 := by rw [card_sdiff_of_subset hgt', htc, hgc]
        obtain ⟨w, hw⟩ := card_eq_one.mp hcs
        have hwt : w ∈ t := (mem_sdiff.mp (by rw [hw]; exact mem_singleton_self w)).1
        have hwg : w ∉ g := (mem_sdiff.mp (by rw [hw]; exact mem_singleton_self w)).2
        have hsubw : ∀ z ∈ g, z ∈ t ∧ z ≠ w := fun z hz =>
          ⟨hgt' hz, fun e => hwg (e ▸ hz)⟩
        simp only [ht, mem_insert, mem_singleton] at hwt
        rcases hwt with rfl | rfl | rfl | rfl
        · refine mem_union_right _ (Complex4.mem_faces.mpr ⟨σ, hσK, fun z hz => ?_, hgc⟩)
          obtain ⟨hz1, hz2⟩ := hsubw z hz
          simp only [ht, mem_insert, mem_singleton] at hz1
          rcases hz1 with e | e | e | e
          · exact absurd e hz2
          · exact e ▸ hmemσ 0
          · exact e ▸ hx
          · exact e ▸ hy
        · exact absurd (eq_of_subset_of_card_le (fun z hz => by
            obtain ⟨hz1, hz2⟩ := hsubw z hz
            simp only [ht, mem_insert, mem_singleton] at hz1 ⊢
            tauto) (by omega : #(insert v {x, y}) ≤ #g)) hgf
        · have : g = insert v (insert (a 0) {y}) := eq_of_subset_of_card_le (fun z hz => by
            obtain ⟨hz1, hz2⟩ := hsubw z hz
            simp only [ht, mem_insert, mem_singleton] at hz1 ⊢
            tauto) (by simpa [hgc] using card_le_three v (a 0) y)
          exact mem_union_left _ (mem_union_left _ (this ▸ hgt y hy hya))
        · have : g = insert v (insert (a 0) {x}) := eq_of_subset_of_card_le (fun z hz => by
            obtain ⟨hz1, hz2⟩ := hsubw z hz
            simp only [ht, mem_insert, mem_singleton] at hz1 ⊢
            tauto) (by simpa [hgc] using card_le_three v (a 0) x)
          exact mem_union_left _ (mem_union_left _ (this ▸ hgt x hx hxa))
  have h2 : Forces (Complex4.move K h) (Complex4.move K h).tris Z :=
    (forces_of_direct _ Z hdirect).mono_target (fun x hx => by
      by_cases hxZ : x ∈ Z
      · exact mem_union_right _ hxZ
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxZ⟩))
  exact h1.of_union h2

end Move15

end Lightlike.SpinFoam
