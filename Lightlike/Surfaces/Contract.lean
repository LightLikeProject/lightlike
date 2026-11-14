import Lightlike.Surfaces.Local

/-!
# Contracting an edge by bistellar moves

`contract L y v` renames the vertex `y` to `v` and drops the triangles that become degenerate (the
two triangles at the edge `yv`). If the only common neighbours of `y` and `v` are the two apexes
of `yv` (the edge lies in no other 3-cycle), and those apexes do not span a triangle with `v`, the
contraction is a composite of 2D bistellar moves (`IsSurface.contract_eqvGen`).

The proof flips the edges at `y` one by one: if `yvw₁` and `yw₁w₂` are consecutive triangles at
`y` and `vw₂` is not an edge, flipping `yw₁` to `vw₂` lowers the degree of `y` by one and does not
change the contraction. When `vw₂` is an edge, `y` has degree 3 and an inverse 1-3 move removes
it, which is the contraction.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- Renaming the vertex `y` to `v`. -/
def rn (y v u : V) : V := if u = y then v else u

/-- **Contracting `y` into `v`**: rename `y` to `v` in every triangle and keep the triangles that
still have three vertices. -/
def contract (L : Finset (Finset V)) (y v : V) : Finset (Finset V) :=
  (L.image (Finset.image (rn y v))).filter (#· = 3)

lemma image_rn_of_notMem {t : Finset V} {y v : V} (h : y ∉ t) : t.image (rn y v) = t := by
  conv_rhs => rw [← image_id (s := t)]
  apply image_congr
  intro u hu
  simp only [rn, id, ite_eq_right_iff]
  intro e
  exact absurd (e ▸ hu) h

lemma image_rn_tri {y v a b : V} (ha : a ≠ y) (hb : b ≠ y) :
    ({y, a, b} : Finset V).image (rn y v) = {v, a, b} := by
  simp [image_insert, rn, ha, hb]

/-- The contraction of a complex whose triangles avoid `y` (apart from listed ones). -/
lemma filter_image_rn_of_notMem {E : Finset (Finset V)} {y v : V} (hE : IsTri2 E)
    (hy : ∀ t ∈ E, y ∉ t) : (E.image (Finset.image (rn y v))).filter (#· = 3) = E := by
  have : E.image (Finset.image (rn y v)) = E := by
    conv_rhs => rw [← image_id (s := E)]
    exact image_congr fun t ht => image_rn_of_notMem (hy t ht)
  rw [this, filter_true_of_mem hE]

lemma card_tri_dup {v w : V} (h : v ≠ w) : #({v, v, w} : Finset V) ≠ 3 := by
  rw [insert_idem, card_pair h]; omega

lemma card_tri_dup' {v w : V} (h : v ≠ w) : #({v, w, v} : Finset V) ≠ 3 := by
  rw [show ({v, w, v} : Finset V) = {v, w} by ext; simp only [mem_insert, mem_singleton]; tauto,
    card_pair h]; omega

lemma card_tri {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    #({a, b, c} : Finset V) = 3 := by
  rw [card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]

/-- **Removing a vertex of degree 3 is its contraction**: if the triangles at `y` are `yvw₁`,
`yw₁w₂`, `yw₂v` and `vw₁w₂` is not a face, subdividing `vw₁w₂` in the contraction gives back
`L`. -/
lemma IsSurface.contract_deg3 {L : Finset (Finset V)} (hL : IsSurface L) {y v w₁ w₂ : V}
    (h1 : ({y, v, w₁} : Finset V) ∈ L) (h2 : ({y, w₁, w₂} : Finset V) ∈ L)
    (h3 : ({y, w₂, v} : Finset V) ∈ L) (hn : ({v, w₁, w₂} : Finset V) ∉ L) :
    Move2 (contract L y v) L := by
  obtain ⟨hyv, hyw₁, hvw₁⟩ := tri_ne (hL.card _ h1)
  obtain ⟨-, hyw₂, hw₁w₂⟩ := tri_ne (hL.card _ h2)
  obtain ⟨-, -, hw₂v⟩ := tri_ne (hL.card _ h3)
  have hall := hL.link_triangle h1 h2 h3
  have n12 : ({y, v, w₁} : Finset V) ≠ {y, w₁, w₂} :=
    ne_of_mem_notMem (y := v) (by simp) (by simp [hyv.symm, hvw₁, hw₂v.symm])
  have n13 : ({y, v, w₁} : Finset V) ≠ {y, w₂, v} :=
    ne_of_mem_notMem (y := w₁) (by simp) (by simp [hyw₁.symm, hw₁w₂, hvw₁.symm])
  have n23 : ({y, w₁, w₂} : Finset V) ≠ {y, w₂, v} :=
    ne_of_mem_notMem (y := w₁) (by simp) (by simp [hyw₁.symm, hw₁w₂, hvw₁.symm])
  have m2 : ({y, w₁, w₂} : Finset V) ∈ L.erase {y, v, w₁} := mem_erase.mpr ⟨n12.symm, h2⟩
  have m3 : ({y, w₂, v} : Finset V) ∈ (L.erase {y, v, w₁}).erase {y, w₁, w₂} :=
    mem_erase.mpr ⟨n23.symm, mem_erase.mpr ⟨n13.symm, h3⟩⟩
  set E := ((L.erase {y, v, w₁}).erase {y, w₁, w₂}).erase {y, w₂, v} with hE
  have hLE : L = insert {y, v, w₁} (insert {y, w₁, w₂} (insert {y, w₂, v} E)) := by
    rw [hE, insert_erase m3, insert_erase m2, insert_erase h1]
  have hEL : E ⊆ L := fun t ht => mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase ht))
  have hyE : ∀ t ∈ E, y ∉ t := by
    intro t ht hyt
    have h3' := mem_erase.mp ht
    have h2' := mem_erase.mp h3'.2
    have h1' := mem_erase.mp h2'.2
    rcases hall t h1'.2 hyt with h | h | h
    exacts [h1'.1 h, h2'.1 h, h3'.1 h]
  have hnE : ({v, w₁, w₂} : Finset V) ∉ E := fun h => hn (hEL h)
  have hcon : contract L y v = insert {v, w₁, w₂} E := by
    rw [contract, hLE, image_insert (Finset.image (rn y v)), image_insert (Finset.image (rn y v)),
      image_insert (Finset.image (rn y v)), image_rn_tri hyv.symm hyw₁.symm,
      image_rn_tri hyw₁.symm hyw₂.symm, image_rn_tri hyw₂.symm hyv.symm]
    simp only [filter_insert, card_tri_dup hvw₁, card_tri hvw₁ hw₂v.symm hw₁w₂,
      card_tri_dup' hw₂v.symm, ite_true, ite_false]
    rw [filter_image_rn_of_notMem (fun t ht => hL.card t (hEL ht)) hyE]
  have hy : y ∉ verts2 (insert {v, w₁, w₂} E) := by
    rw [mem_verts2]
    rintro ⟨t, ht, hyt⟩
    rw [mem_insert] at ht
    rcases ht with rfl | ht
    · simp only [mem_insert, mem_singleton] at hyt
      rcases hyt with h | h | h
      exacts [hyv h, hyw₁ h, hyw₂ h]
    · exact hyE t ht hyt
  have hmv := Move2.sub13 hvw₁ hw₂v.symm hw₁w₂ (mem_insert_self ({v, w₁, w₂} : Finset V) E) hy
  rw [erase_insert hnE] at hmv
  have e1 : ({v, w₁, y} : Finset V) = {y, v, w₁} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  have e2 : ({w₁, w₂, y} : Finset V) = {y, w₁, w₂} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  have e3 : ({v, w₂, y} : Finset V) = {y, w₂, v} := by
    ext; simp only [mem_insert, mem_singleton]; tauto
  rw [e1, e2, e3, ← hLE] at hmv
  rw [hcon]
  exact hmv

/-- **Contracting an edge is a composite of 2D bistellar moves.** If every common neighbour `w` of
`y` and `v` spans a triangle `yvw` with them (the edge `yv` lies in no other 3-cycle) and the two
apexes of `yv` do not span a triangle with `v`, then `L` and `contract L y v` are related by
bistellar moves (`n` is the degree of `y`, for the induction). -/
theorem IsSurface.contract_eqvGen (n : ℕ) : ∀ {L : Finset (Finset V)} {y v : V}, deg2 L y = n →
    IsSurface L → ({y, v} : Finset V) ∈ edges2 L →
    (∀ w, ({y, w} : Finset V) ∈ edges2 L → ({v, w} : Finset V) ∈ edges2 L →
      ({y, v, w} : Finset V) ∈ L) →
    (∀ w₁ w₂, ({y, v, w₁} : Finset V) ∈ L → ({y, v, w₂} : Finset V) ∈ L → w₁ ≠ w₂ →
      ({v, w₁, w₂} : Finset V) ∉ L) →
    Relation.EqvGen Move2 L (contract L y v) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L y v hn hL hyv hc hnt
  obtain ⟨τ, hτ, hsub, hcard⟩ := mem_edges2.mp hyv
  have hyv' : y ≠ v := by
    intro h
    subst h
    simp at hcard
  obtain ⟨w₁, hw₁y, hw₁v, rfl⟩ :=
    eq_tri_of_mem (hL.card τ hτ) (hsub (by simp)) (hsub (by simp)) hyv'
  have hτ' : ({y, w₁, v} : Finset V) ∈ L := by rw [tri_swap]; exact hτ
  obtain ⟨w₂, hw₂v, hw₂y, hw₂w₁, h2, hstar⟩ := hL.other_tri hτ'
  by_cases hvw₂ : ({v, w₂} : Finset V) ∈ edges2 L
  · -- `y` has degree 3: remove it
    have hyw₂ : ({y, w₂} : Finset V) ∈ edges2 L :=
      pair_mem_edges2 h2 (by simp) (by simp) hw₂y.symm
    have h3 : ({y, v, w₂} : Finset V) ∈ L := hc w₂ hyw₂ hvw₂
    exact .symm _ _ (.rel _ _ (hL.contract_deg3 hτ h2 (by rw [tri_swap]; exact h3)
      (hnt w₁ w₂ hτ h3 hw₂w₁.symm)))
  -- flip `yw₁` to `vw₂`
  have hfresh : ∀ t ∈ L, ¬ ({v, w₂} : Finset V) ⊆ t := fun t ht hs =>
    hvw₂ (mem_edges2.mpr ⟨t, ht, hs, card_pair hw₂v.symm⟩)
  have hmove := Move2.flip22 hw₁y.symm hyv' hw₂y.symm hw₁v hw₂w₁.symm hw₂v.symm hτ' h2 hstar
    hfresh
  set R := (L.erase {y, w₁, v}).erase {y, w₁, w₂} with hR
  set L₁ := insert {y, v, w₂} (insert {w₁, v, w₂} R) with hL₁
  have hS₁ : IsSurface L₁ := (Move2.isSurface_iff hmove).mp hL
  have n12 : ({y, w₁, v} : Finset V) ≠ {y, w₁, w₂} :=
    ne_of_mem_notMem (y := v) (by simp) (by simp [hyv'.symm, hw₁v.symm, hw₂v.symm])
  have m2 : ({y, w₁, w₂} : Finset V) ∈ L.erase {y, w₁, v} := mem_erase.mpr ⟨n12.symm, h2⟩
  have hLR : L = insert {y, w₁, v} (insert {y, w₁, w₂} R) := by
    rw [hR, insert_erase m2, insert_erase hτ']
  have hvw₂L : ∀ t ∈ L, v ∈ t → w₂ ∉ t := fun t ht hv hw =>
    hfresh t ht (pair_subset_of_mem hv hw)
  have hnot1 : ({y, v, w₂} : Finset V) ∉ L := fun h => hvw₂L _ h (by simp) (by simp)
  have hnot2 : ({w₁, v, w₂} : Finset V) ∉ L := fun h => hvw₂L _ h (by simp) (by simp)
  have hRL : R ⊆ L := fun t ht => mem_of_mem_erase (mem_of_mem_erase ht)
  -- the degree of `y` drops by one
  have hdeg : deg2 L₁ y + 1 = deg2 L y := by
    unfold deg2
    have hyR : ({y, v, w₂} : Finset V) ∉ R.filter (y ∈ ·) := fun h => hnot1 (hRL (mem_filter.mp h).1)
    have hy2 : y ∉ ({w₁, v, w₂} : Finset V) := by simp [hw₁y.symm, hyv', hw₂y.symm]
    have e₁ : L₁.filter (y ∈ ·) = insert {y, v, w₂} (R.filter (y ∈ ·)) := by
      rw [hL₁, filter_insert, filter_insert]
      simp [hy2]
    have hy1 : ({y, w₁, w₂} : Finset V) ∉ R := by simp [hR]
    have hy0 : ({y, w₁, v} : Finset V) ∉ insert {y, w₁, w₂} R := by
      simp only [mem_insert, not_or]
      exact ⟨n12, by simp [hR]⟩
    have e₂ : L.filter (y ∈ ·) = insert {y, w₁, v} (insert {y, w₁, w₂} (R.filter (y ∈ ·))) := by
      conv_lhs => rw [hLR]
      rw [filter_insert, filter_insert]
      simp
    rw [e₁, e₂, card_insert_of_notMem hyR, card_insert_of_notMem, card_insert_of_notMem]
    · exact fun h => hy1 (mem_filter.mp h).1
    · simp only [mem_insert, not_or]
      exact ⟨n12, fun h => by simp [hR] at h⟩
  -- the hypotheses for `L₁`
  have hyv₁ : ({y, v} : Finset V) ∈ edges2 L₁ :=
    pair_mem_edges2 (mem_insert_self _ _) (by simp) (by simp) hyv'
  have hE₁ : edges2 L₁ = insert {v, w₂} ((edges2 L).erase {y, w₁}) :=
    edges2_flip22 hw₁y.symm hyv' hw₂y.symm hw₁v hw₂w₁.symm hw₂v.symm hτ' h2 hstar
  have hmemR : ∀ {t : Finset V}, t ∈ L → t ≠ {y, w₁, v} → t ≠ {y, w₁, w₂} → t ∈ L₁ :=
    fun ht h1 h2 => mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨h2, mem_erase.mpr ⟨h1, ht⟩⟩))
  have hc₁ : ∀ w, ({y, w} : Finset V) ∈ edges2 L₁ → ({v, w} : Finset V) ∈ edges2 L₁ →
      ({y, v, w} : Finset V) ∈ L₁ := by
    intro w hyw hvw
    rw [hE₁, mem_insert, mem_erase] at hyw hvw
    rcases hyw with hyw | ⟨hyw1, hyw⟩
    · have : y ∈ ({v, w₂} : Finset V) := hyw ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h
      exacts [absurd h hyv', absurd h hw₂y.symm]
    rcases hvw with hvw | ⟨-, hvw⟩
    · have hw : w ∈ ({v, w₂} : Finset V) := hvw ▸ by simp
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw
      · exfalso
        rw [hw] at hvw
        have : w₂ ∈ ({v, v} : Finset V) := hvw ▸ by simp
        simp only [mem_insert, mem_singleton, or_self] at this
        exact hw₂v this
      · rw [hw]
        exact mem_insert_self _ _
    · have hw1 : w ≠ w₁ := by rintro rfl; exact hyw1 rfl
      have hm := hc w hyw hvw
      refine hmemR hm ?_ ?_
      · intro h
        apply hw1
        have : w₁ ∈ ({y, v, w} : Finset V) := h ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h' | h'
        exacts [absurd h' hw₁y, absurd h' hw₁v, h'.symm]
      · intro h
        have : v ∈ ({y, w₁, w₂} : Finset V) := h ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with h' | h' | h'
        exacts [absurd h' hyv'.symm, absurd h' hw₁v.symm, absurd h' hw₂v.symm]
  -- the apexes of `yv` in `L₁`
  obtain ⟨w', hw'w₁, hw'y, hw'v, hw', hyvstar⟩ := hL.other_tri hτ
  have hapex : ∀ p, ({y, v, p} : Finset V) ∈ L₁ → p = w₂ ∨ p = w' := by
    intro p hp
    obtain ⟨-, hpy, hpv⟩ := tri_ne (hS₁.card _ hp)
    have hm := hp
    rw [hL₁, mem_insert, mem_insert] at hm
    rcases hm with hm | hm | hm
    · exact Or.inl (eq_of_tri_eq hm hpy.symm hpv.symm)
    · have : y ∈ ({w₁, v, w₂} : Finset V) := hm ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h
      exacts [absurd h hw₁y.symm, absurd h hyv', absurd h hw₂y.symm]
    · have hpL := hRL hm
      rcases hyvstar _ hpL (pair_subset_of_mem (by simp) (by simp)) with h | h
      · exfalso
        rw [hR] at hm
        simp only [mem_erase] at hm
        exact hm.2.1 (h.trans (tri_swap _ _ _))
      · exact Or.inr (eq_of_tri_eq h hpy.symm hpv.symm)
  have hw'w₂ : w' ≠ w₂ := by
    rintro rfl
    exact hvw₂ (pair_mem_edges2 hw' (by simp) (by simp) hw'v.symm)
  have hnot3 : ({v, w₂, w'} : Finset V) ∉ L₁ := by
    intro h
    rw [hL₁, mem_insert, mem_insert] at h
    rcases h with h | h | h
    · have : w' ∈ ({y, v, w₂} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      exacts [hw'y h', hw'v h', hw'w₂ h']
    · have : w' ∈ ({w₁, v, w₂} : Finset V) := h ▸ by simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      exacts [hw'w₁ h', hw'v h', hw'w₂ h']
    · exact hvw₂L _ (hRL h) (by simp) (by simp)
  have hnt₁ : ∀ p q, ({y, v, p} : Finset V) ∈ L₁ → ({y, v, q} : Finset V) ∈ L₁ → p ≠ q →
      ({v, p, q} : Finset V) ∉ L₁ := by
    intro p q hp hq hpq
    rcases hapex p hp with rfl | rfl <;> rcases hapex q hq with rfl | rfl
    · exact absurd rfl hpq
    · exact hnot3
    · rw [tri_swap]; exact hnot3
    · exact absurd rfl hpq
  -- the contraction does not change
  have hcon : contract L₁ y v = contract L y v := by
    have hy2 : y ∉ ({w₁, v, w₂} : Finset V) := by simp [hw₁y.symm, hyv', hw₂y.symm]
    rw [contract, contract, hL₁, image_insert (Finset.image (rn y v)),
      image_insert (Finset.image (rn y v)), image_rn_tri hyv'.symm hw₂y, image_rn_of_notMem hy2]
    conv_rhs => rw [hLR, image_insert (Finset.image (rn y v)), image_insert (Finset.image (rn y v)),
      image_rn_tri hw₁y hyv'.symm, image_rn_tri hw₁y hw₂y]
    simp only [filter_insert, card_tri_dup hw₂v.symm, card_tri hw₁v hw₂w₁.symm hw₂v.symm,
      card_tri_dup' hw₁v.symm, card_tri hw₁v.symm hw₂v.symm hw₂w₁.symm, ite_true, ite_false]
    rw [Finset.insert_comm w₁ v {w₂}]
  have := ih (deg2 L₁ y) (by omega) rfl hS₁ hyv₁ hc₁ hnt₁
  rw [hcon] at this
  exact (Relation.EqvGen.rel _ _ hmove).trans _ _ _ this

end Lightlike.Surfaces
