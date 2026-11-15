import Lightlike.PL.Collar

/-!
# The complement of a vertex star in a sphere is a ball

For a stellar `n`-sphere `S` and a vertex `z`, the complex `S.del {z}` of faces avoiding `z` is a
stellar `n`-ball whose boundary is the link of `z` (Newman's theorem, Lickorish's Theorem 3.8, in
the form for the star of a vertex). This file holds the deletion lemmas for stellar moves, the
induction along a chain of moves, and the final statement.
-/

open Finset

namespace Lightlike.PL
namespace SComplex
variable {V : Type*} [DecidableEq V]

/-! ## Joining a simplex to a sphere or ball -/

/-- Joining a simplex on `D` to a sphere or ball model `L` of index `m` gives a ball model of index
`m + #D`. -/
theorem isSB_simplex_join [Infinite V] {m : ℕ} {L : SComplex V} (hL : IsSB true m L)
    (D : Finset V) (hD : Disjoint D L.verts) : IsSB true (m + #D) ((simplex D).join L) := by
  induction D using Finset.induction_on with
  | empty =>
    rw [simplex_empty_join]; simpa using hL
  | insert x D hxD ih =>
    have hD' : Disjoint D L.verts := Disjoint.mono_left (subset_insert x D) hD
    have hx : x ∉ ((simplex D).join L).verts := by
      intro hx
      rcases mem_union.1 (verts_join_subset _ _ hx) with h | h
      · rw [verts_simplex] at h
        exact hxD h
      · exact disjoint_left.1 hD (mem_insert_self x D) h
    have := isSB_cone (ih hD') hx
    rw [simplex_insert_eq_cone, cone_join, card_insert_of_notMem hxD]
    convert this using 2

/-! ## Deleting a face from a stellar subdivision -/

/-- Deleting the new vertex from a stellar subdivision at `A` gives the deletion of `A`. -/
lemma del_starAt_apex {K : SComplex V} {A : Finset V} {a : V} (ha : a ∉ K.verts) :
    (K.starAt A a).del {a} = K.del A := by
  refine ext_mem fun s => ?_
  rw [mem_del, mem_del, mem_starAt]
  constructor
  · rintro ⟨hs | ⟨t, ht, hAt, hAt', rfl⟩, hn⟩
    · exact hs
    · exact absurd (singleton_subset_iff.2 (mem_insert_self a t)) hn
  · rintro ⟨hs, hA⟩
    exact ⟨.inl ⟨hs, hA⟩, fun h => ha (mem_verts.2 (down_mem hs h))⟩

/-- Deleting a vertex outside `A` commutes with the stellar subdivision at `A`. -/
lemma del_starAt_of_notMem {K : SComplex V} {A : Finset V} {a v : V}
    (hvA : v ∉ A) (hav : a ≠ v) : (K.starAt A a).del {v} = (K.del {v}).starAt A a := by
  refine ext_mem fun s => ?_
  rw [mem_del, mem_starAt, mem_starAt]
  simp only [mem_del, singleton_subset_iff]
  constructor
  · rintro ⟨hs | ⟨t, ht, hAt, hAt', rfl⟩, hn⟩
    · exact .inl ⟨⟨hs.1, hn⟩, hs.2⟩
    · refine .inr ⟨t, ⟨ht, fun h => hn (mem_insert_of_mem h)⟩, hAt, ⟨hAt', ?_⟩, rfl⟩
      intro h
      rcases mem_union.1 h with h | h
      · exact hvA h
      · exact hn (mem_insert_of_mem h)
  · rintro (⟨⟨hs, hv⟩, hA⟩ | ⟨t, ⟨ht, hvt⟩, hAt, ⟨hAt', hv⟩, rfl⟩)
    · exact ⟨.inl ⟨hs, hA⟩, hv⟩
    · refine ⟨.inr ⟨t, ht, hAt, hAt', rfl⟩, fun h => ?_⟩
      rcases mem_insert.1 h with h | h
      · exact hav h.symm
      · exact hvt h

/-- `X` is a PL ball model of index `m`: an `(m-1)`-dimensional stellar ball. -/
def IsNBall (m : ℕ) (X : SComplex V) : Prop := IsSB true m X ∧ IsBallIn X

lemma IsNBall.of_stellarEquivIn {m : ℕ} {X Y : SComplex V} (h : IsNBall m X)
    (e : StellarEquivIn X Y) : IsNBall m Y :=
  ⟨h.1.of_stellarEquivIn e, h.2.of_stellarEquivIn e⟩

/-- The part of the star of `C` that avoids the vertex `w ∈ C`, as a join. -/
def ballPart (U : SComplex V) (C : Finset V) (w : V) : SComplex V :=
  (simplex (C.erase w)).join (U.link C)

lemma mem_ballPart {U : SComplex V} {C : Finset V} {w : V} (hw : w ∈ C) {t : Finset V} :
    t ∈ ballPart U C w ↔ w ∉ t ∧ C ∪ t ∈ U := by
  unfold ballPart
  rw [mem_join]
  constructor
  · rintro ⟨b, hb, l, hl, rfl⟩
    rw [mem_simplex] at hb
    rw [mem_link'] at hl
    refine ⟨fun h => ?_, ?_⟩
    · rcases mem_union.1 h with h | h
      · exact notMem_erase w C (hb h)
      · exact disjoint_left.1 hl.1 hw h
    · have : C ∪ (b ∪ l) = C ∪ l := by
        rw [← union_assoc, union_eq_left.2 ((hb.trans (erase_subset w C)))]
      rw [this]; exact hl.2
  · rintro ⟨hwt, hU⟩
    refine ⟨t ∩ C, ?_, t \ C, ?_, ?_⟩
    · rw [mem_simplex]
      intro x hx
      rw [mem_inter] at hx
      exact mem_erase.2 ⟨fun e => hwt (e ▸ hx.1), hx.2⟩
    · rw [mem_link']
      refine ⟨disjoint_sdiff, ?_⟩
      have : C ∪ (t \ C) = C ∪ t := union_sdiff_self_eq_union
      rw [this]; exact hU
    · ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto

lemma ballPart_subset {U : SComplex V} {C : Finset V} {w : V} (hw : w ∈ C) {t : Finset V}
    (h : t ∈ ballPart U C w) : t ∈ U := down_mem ((mem_ballPart hw).1 h).2 subset_union_right

/-- Subdividing at a face `C ∋ w` adds to the deletion of `w` exactly a cone on `ballPart`. -/
lemma del_starAt_of_mem {U : SComplex V} {C : Finset V} {c w : V} (hC : C ∈ U) (hw : w ∈ C)
    (hc : c ∉ U.verts) :
    (U.starAt C c).del {w} = (U.del {w}).union (cone c (ballPart U C w)) := by
  have hcw : c ≠ w := fun e => hc (e ▸ mem_verts.2 (down_mem hC (singleton_subset_iff.2 hw)))
  refine ext_mem fun s => ?_
  rw [mem_del, mem_starAt, mem_union_iff, mem_del, mem_cone]
  simp only [singleton_subset_iff]
  constructor
  · rintro ⟨hs | ⟨t, ht, hCt, hCt', rfl⟩, hn⟩
    · exact .inl ⟨hs.1, hn⟩
    · refine .inr ⟨t, (mem_ballPart hw).2 ⟨fun h => hn (mem_insert_of_mem h), hCt'⟩, .inr rfl⟩
  · rintro (⟨hs, hn⟩ | ⟨t, ht, rfl | rfl⟩)
    · exact ⟨.inl ⟨hs, fun h => hn (h hw)⟩, hn⟩
    · have := (mem_ballPart hw).1 ht
      exact ⟨.inl ⟨down_mem this.2 subset_union_right, fun h => this.1 (h hw)⟩, this.1⟩
    · have := (mem_ballPart hw).1 ht
      refine ⟨.inr ⟨t, down_mem this.2 subset_union_right, fun h => this.1 (h hw), this.2, rfl⟩, ?_⟩
      intro h
      rcases mem_insert.1 h with h | h
      · exact hcw h.symm
      · exact this.1 h

/-- Links commute with deleting a vertex that is not in the face. -/
lemma link_del_singleton {K : SComplex V} {σ : Finset V} {w : V} (hw : w ∉ σ) :
    (K.del {w}).link σ = (K.link σ).del {w} := by
  refine ext_mem fun s => ?_
  simp only [mem_link', mem_del, singleton_subset_iff, mem_union]
  constructor
  · rintro ⟨hd, hs, hn⟩
    exact ⟨⟨hd, hs⟩, fun h => hn (.inr h)⟩
  · rintro ⟨⟨hd, hs⟩, hn⟩
    exact ⟨hd, hs, fun h => h.elim hw hn⟩

/-! ## The induction hypothesis and the manifold property of a deletion -/

/-- **Deleting a vertex from an `n`-sphere gives a ball**, for spheres of dimension `m`. -/
def DelBall (V : Type*) [DecidableEq V] (m : ℕ) : Prop :=
  ∀ S : SComplex V, IsSB false (m + 1) S → ∀ z : V, {z} ∈ S → IsNBall (m + 1) (S.del {z})

lemma isSB_true_of_false {m : ℕ} {L : SComplex V} (h : IsSB false m L) : IsSB true m L :=
  h.elim .inl (fun h => absurd h.1 (by simp))

lemma del_of_notMem {K : SComplex V} {w : V} (h : {w} ∉ K) : K.del {w} = K := by
  refine ext_mem fun s => ?_
  rw [mem_del]
  exact ⟨fun h' => h'.1, fun hs => ⟨hs, fun hw => h (down_mem hs hw)⟩⟩

/-- Links of nonempty faces of an `n`-sphere are spheres. -/
lemma link_sphere [Infinite V] {n : ℕ} {U : SComplex V} (hU : IsSB false (n + 1) U) {σ : Finset V}
    (hσ : σ ∈ U) (hne : σ.Nonempty) : ∃ m, m + #σ = n + 1 ∧ IsSB false m (U.link σ) :=
  (isMfdIn_main false n).1 U ((isMfdIn_main false n).2 U hU) σ hσ hne

/-- The link in a deletion: if `w` is in the link of `σ` it is a ball, by induction. -/
lemma link_del_ball [Infinite V] {n : ℕ} (hlow : ∀ m < n, DelBall V m) {U : SComplex V}
    (hU : IsSB false (n + 1) U) {σ : Finset V} {w : V} (hσ : σ ∈ U) (hne : σ.Nonempty)
    (hw : {w} ∈ U.link σ) : ∃ m, m + #σ = n + 1 ∧ IsNBall m ((U.link σ).del {w}) := by
  obtain ⟨m, hm, hs⟩ := link_sphere hU hσ hne
  rcases m with _ | m'
  · exact absurd (mem_verts.2 hw) (by rw [hs.verts_eq_empty]; simp)
  · have hc : 0 < #σ := card_pos.2 hne
    exact ⟨m' + 1, hm, hlow m' (by omega) _ hs w hw⟩

/-- A deletion `U.del {w}` of a sphere is a combinatorial manifold with boundary. -/
theorem del_isMfd [Infinite V] {n : ℕ} (hlow : ∀ m < n, DelBall V m) {U : SComplex V}
    (hU : IsSB false (n + 1) U) {w : V} (hw : {w} ∈ U) : IsMfdIn true n (U.del {w}) := by
  intro y hy
  have hyU : {y} ∈ U := down_mem (mem_del.1 (mem_verts.1 hy)).1 subset_rfl
  have hyw : w ∉ ({y} : Finset V) := fun h => (mem_del.1 (mem_verts.1 hy)).2 (by simpa using h)
  rw [link_del_singleton hyw]
  by_cases h : {w} ∈ U.link {y}
  · obtain ⟨m, hm, hb⟩ := link_del_ball hlow hU hyU (singleton_nonempty y) h
    have : m = n := by simpa using hm
    exact this ▸ hb.1
  · rw [del_of_notMem h]
    obtain ⟨m, hm, hs⟩ := link_sphere hU hyU (singleton_nonempty y)
    have : m = n := by simpa using hm
    exact this ▸ isSB_true_of_false hs

/-- **The boundary of a deletion** is the link of the vertex. -/
theorem bd_del_eq [Infinite V] {n : ℕ} (hlow : ∀ m < n, DelBall V m) {U : SComplex V}
    (hU : IsSB false (n + 1) U) {w : V} (hw : {w} ∈ U) : (U.del {w}).bd = U.link {w} := by
  have hX := del_isMfd hlow hU hw
  refine ext_mem fun σ => ?_
  rw [mem_link']
  constructor
  · intro h
    have hσ := mem_del.1 (bd_subset h)
    have hwσ : w ∉ σ := fun h' => hσ.2 (singleton_subset_iff.2 h')
    refine ⟨disjoint_singleton_left.2 hwσ, ?_⟩
    rcases σ.eq_empty_or_nonempty with rfl | hne
    · simpa using hw
    · rw [hX.mem_bd_iff (bd_subset h) hne, link_del_singleton hwσ] at h
      by_contra hn
      have hn' : {w} ∉ U.link σ := fun h' => hn (by
        rw [mem_link'] at h'; rw [Finset.union_comm]; exact h'.2)
      rw [del_of_notMem hn'] at h
      obtain ⟨m, hm, hs⟩ := link_sphere hU hσ.1 hne
      obtain ⟨A, hA, hLA⟩ := hs.resolve_right (by simp)
      exact IsSB.not_isBallIn hA hLA h
  · rintro ⟨hd, hU'⟩
    have hwσ : w ∉ σ := disjoint_singleton_left.1 hd
    have hσU : σ ∈ U := down_mem hU' subset_union_right
    have hσX : σ ∈ U.del {w} := mem_del.2 ⟨hσU, fun h => hwσ (singleton_subset_iff.1 h)⟩
    rcases σ.eq_empty_or_nonempty with rfl | hne
    · exact mem_bd.2 ⟨hσX, .inl rfl⟩
    · refine (hX.mem_bd_iff hσX hne).2 ?_
      rw [link_del_singleton hwσ]
      obtain ⟨m, hm, hb⟩ := link_del_ball hlow hU hσU hne
        (mem_link'.2 ⟨hd.symm, by rwa [Finset.union_comm] at hU'⟩)
      exact hb.2

/-! ## Balls from joins with a simplex -/

/-- The join of a nonempty simplex with a sphere or ball model is a ball. -/
lemma isNBall_simplex_join [Infinite V] {m : ℕ} {L : SComplex V} (hL : IsSB true m L)
    {D : Finset V} (hD : D.Nonempty) (hdis : Disjoint D L.verts) :
    IsNBall (m + #D) ((simplex D).join L) := by
  have hS := isSB_simplex_join hL D hdis
  refine ⟨hS, (hS.isBallIn_iff).2 ?_⟩
  rw [signedCount_join (by rwa [verts_simplex]), signedCount_simplex hD, zero_mul]

/-- **Deleting a nonempty face** from an `m`-sphere gives a ball, given the vertex case. -/
theorem delBall_face [Infinite V] {m : ℕ} (h : DelBall V m) {S : SComplex V}
    (hS : IsSB false (m + 1) S) {B : Finset V} (hB : B ∈ S) (hne : B.Nonempty) :
    IsNBall (m + 1) (S.del B) := by
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset S.verts
  have e := StellarEquivIn.starAt hB hne hb
  have hS' : IsSB false (m + 1) (S.starAt B b) := hS.of_stellarEquivIn e
  have := h _ hS' b (mem_verts.1 (apex_mem_verts hB hne))
  rwa [del_starAt_apex hb] at this

/-! ## The ball attached when subdividing a face through the deleted vertex -/

/-- `ballPart` is an `n`-ball model: a simplex joined with a sphere (the link of `C`). -/
lemma ballPart_isNBall [Infinite V] {n : ℕ} {U : SComplex V} (hU : IsSB false (n + 1) U)
    {C : Finset V} {w : V} (hC : C ∈ U) (hw : w ∈ C) (hB : (C.erase w).Nonempty) :
    IsNBall n (ballPart U C w) := by
  obtain ⟨m, hm, hs⟩ := link_sphere hU hC ⟨w, hw⟩
  have hd : Disjoint (C.erase w) (U.link C).verts :=
    Disjoint.mono_left (erase_subset w C) (disjoint_verts_link U C)
  have := isNBall_simplex_join (isSB_true_of_false hs) hB hd
  have hc : #(C.erase w) + 1 = #C := card_erase_add_one hw
  have : m + #(C.erase w) = n := by omega
  rw [← this]
  exact isNBall_simplex_join (isSB_true_of_false hs) hB hd

/-- The ball `ballPart` is an `(n+1)`-ball model when `U` is an `(n+2)`-sphere. -/
lemma ballPart_isNBall' [Infinite V] {n : ℕ} {U : SComplex V} (hU : IsSB false (n + 2) U)
    {C : Finset V} {w : V} (hC : C ∈ U) (hw : w ∈ C) (hB : (C.erase w).Nonempty) :
    IsNBall (n + 1) (ballPart U C w) :=
  ballPart_isNBall hU hC hw hB

/-- The boundary faces of `ballPart`: a face not containing the whole `C.erase w` is in the
boundary. -/
lemma ballPart_bd [Infinite V] {n : ℕ} {U : SComplex V} (hU : IsSB false (n + 2) U)
    {C : Finset V} {w : V} (hC : C ∈ U) (hw : w ∈ C) {A : Finset V}
    (hA : A ∈ ballPart U C w) (hBA : ¬ C.erase w ⊆ A) : A ∈ (ballPart U C w).bd := by
  rcases A.eq_empty_or_nonempty with he | hne
  · exact mem_bd.2 ⟨hA, .inl he⟩
  have hB : (C.erase w).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    exact hBA (h ▸ empty_subset _)
  have hN := ballPart_isNBall' hU hC hw hB
  have hmfd : IsMfdIn true n (ballPart U C w) := (isMfdIn_main true n).2 _ hN.1
  refine (hmfd.mem_bd_iff hA hne).2 ?_
  set B := C.erase w with hBdef
  have hBC : B ⊆ C := erase_subset w C
  obtain ⟨hwA, hCA⟩ := (mem_ballPart hw).1 hA
  have ht : A ∩ B ∈ simplex B := by rw [mem_simplex]; exact inter_subset_right
  have hlC : C ∪ (A \ B) = C ∪ A := by
    ext x; simp only [mem_union, mem_sdiff]
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact .inr h.1
    · rintro (h | h)
      · exact .inl h
      · by_cases hx : x ∈ B
        · exact .inl (hBC hx)
        · exact .inr ⟨h, hx⟩
  have hu : A \ B ∈ U.link C := by
    refine mem_link'.2 ⟨?_, by rw [hlC]; exact hCA⟩
    rw [Finset.disjoint_left]
    intro x hxC hxl
    rw [mem_sdiff] at hxl
    by_cases hxw : x = w
    · exact hwA (hxw ▸ hxl.1)
    · exact hxl.2 (mem_erase.2 ⟨hxw, hxC⟩)
  have hAdec : A = (A ∩ B) ∪ (A \ B) := by
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have hdisj : Disjoint (simplex B).verts (U.link C).verts := by
    rw [verts_simplex]
    exact Disjoint.mono_left hBC (disjoint_verts_link U C)
  have hlk : (ballPart U C w).link A = ((simplex B).link (A ∩ B)).join ((U.link C).link (A \ B)) := by
    conv_lhs => rw [hAdec]
    exact link_join hdisj ht hu
  rw [hlk, link_simplex inter_subset_right]
  have hCl : C ∪ (A \ B) ∈ U := by rw [hlC]; exact hCA
  have hcne : (C ∪ (A \ B)).Nonempty := ⟨w, mem_union_left _ hw⟩
  obtain ⟨m, hm, hs⟩ := link_sphere hU hCl hcne
  have hdd : Disjoint C (A \ B) := (mem_link'.1 hu).1
  rw [link_link U hdd]
  have hD : (B \ (A ∩ B)).Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hh
    exact hBA (fun x hx => (mem_inter.1 (hh hx)).1)
  have hd2 : Disjoint (B \ (A ∩ B)) (U.link (C ∪ (A \ B))).verts :=
    Disjoint.mono_left (sdiff_subset.trans hBC |>.trans subset_union_left)
      (disjoint_verts_link U _)
  exact (isNBall_simplex_join (isSB_true_of_false hs) hD hd2).2

/-- **The collar hypotheses hold** for the deleted sphere `U.del {w}` and the ball `ballPart`,
when the sphere's vertex deletions are balls in lower dimension. -/
theorem collarHyp_ballPart [Infinite V] {n : ℕ} (hlow : ∀ m < n + 1, DelBall V m)
    {U : SComplex V} (hU : IsSB false (n + 2) U) {C : Finset V} {w : V} (hC : C ∈ U)
    (hw : w ∈ C) (hB : (C.erase w).Nonempty) {c : V} (hc : c ∉ U.verts) :
    CollarHyp n c (U.del {w}) (ballPart U C w) := by
  have hwU : {w} ∈ U := down_mem hC (singleton_subset_iff.2 hw)
  have hN := ballPart_isNBall' hU hC hw hB
  have hbd := bd_del_eq hlow hU hwU
  have hsub : ∀ s ∈ ballPart U C w, s ∈ (U.del {w}).bd := by
    intro s hs
    obtain ⟨hws, hCs⟩ := (mem_ballPart hw).1 hs
    rw [hbd, mem_link']
    refine ⟨disjoint_singleton_left.2 hws, down_mem hCs ?_⟩
    intro x hx
    rw [mem_union] at hx ⊢
    rcases hx with h | h
    · exact .inl (by rw [mem_singleton.1 h]; exact hw)
    · exact .inr h
  refine ⟨del_isMfd hlow hU hwU, hN.1, hN.2, ?_, hsub, ?_, ?_⟩
  · exact (mem_ballPart hw).2 ⟨by simp, by simpa using hC⟩
  · intro h
    exact hc (mem_verts.2 (mem_del.1 (mem_verts.1 h)).1 |> fun h' =>
      mem_verts.2 (by exact (mem_verts.1 h')))
  · intro A hA hAn s hs hAs
    have hBA : C.erase w ⊆ A := by
      by_contra hh
      exact hAn (ballPart_bd hU hC hw hA hh)
    rw [hbd, mem_link'] at hs
    obtain ⟨hdis, hws⟩ := hs
    refine (mem_ballPart hw).2 ⟨fun h => ?_, ?_⟩
    · exact (disjoint_singleton_left.1 hdis) h
    · refine down_mem hws ?_
      intro x hx
      rw [mem_union] at hx ⊢
      rcases hx with h | h
      · by_cases hxw : x = w
        · exact .inl (by rw [hxw]; exact mem_singleton_self w)
        · exact .inr (hAs (hBA (mem_erase.2 ⟨hxw, h⟩)))
      · exact .inr h

/-- **A stellar move at a face with at least two vertices** does not change the deletion of a
vertex of that face, up to stellar equivalence. -/
theorem del_starAt_equiv [Infinite V] {n : ℕ} (hlow : ∀ m < n + 1, DelBall V m)
    {U : SComplex V} (hU : IsSB false (n + 2) U) {C : Finset V} {w : V} (hC : C ∈ U)
    (hw : w ∈ C) (hB : (C.erase w).Nonempty) {c : V} (hc : c ∉ U.verts) :
    StellarEquivIn ((U.starAt C c).del {w}) (U.del {w}) := by
  rw [del_starAt_of_mem hC hw hc, SComplex.union_comm]
  exact collar_lemma (collarHyp_ballPart hlow hU hC hw hB hc)

/-! ## Deleting a face with several vertices -/

/-- The link of a face in a deletion is a deletion in the link. -/
lemma link_del_eq (K : SComplex V) (E A : Finset V) :
    (K.del E).link A = (K.link A).del (E \ A) := by
  refine ext_mem fun u => ?_
  simp only [mem_link', mem_del]
  have : E ⊆ A ∪ u ↔ E \ A ⊆ u := by
    constructor
    · intro h x hx
      rcases mem_union.1 (h (mem_sdiff.1 hx).1) with h' | h'
      · exact absurd h' (mem_sdiff.1 hx).2
      · exact h'
    · intro h x hx
      by_cases hxA : x ∈ A
      · exact mem_union_left _ hxA
      · exact mem_union_right _ (h (mem_sdiff.2 ⟨hx, hxA⟩))
  rw [this]
  tauto

/-- In a sphere, deleting a nonempty face `E` and then looking at the link of a nonempty face
`A` of the result that meets `E` in a face of the sphere gives a ball. -/
lemma link_delFace_ball [Infinite V] {k : ℕ} (hlow : ∀ m < k, DelBall V m) {L : SComplex V}
    (hL : IsSB false (k + 1) L) {E A : Finset V} (hAne : A.Nonempty) (hAE : A ∪ E ∈ L)
    (hEA : ¬ E ⊆ A) : IsBallIn ((L.del E).link A) := by
  rw [link_del_eq]
  have hAL : A ∈ L := down_mem hAE subset_union_left
  obtain ⟨m, hm, hs⟩ := link_sphere hL hAL hAne
  have hdis : Disjoint A (E \ A) := Finset.disjoint_sdiff
  have hmem : E \ A ∈ L.link A :=
    mem_link'.2 ⟨hdis, by rwa [union_sdiff_self_eq_union]⟩
  have hne : (E \ A).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    rw [sdiff_eq_empty_iff_subset] at h
    exact hEA h
  have hc : 0 < #A := card_pos.2 hAne
  rcases m with _ | m'
  · obtain ⟨x, hx⟩ := hne
    have : x ∈ (L.link A).verts := mem_verts.2 (down_mem hmem (singleton_subset_iff.2 hx))
    rw [hs.verts_eq_empty] at this
    simp at this
  · exact (delBall_face (hlow m' (by omega)) hs hmem hne).2

/-- Deleting a face `C` is deleting the vertex `w` of `C` and adding a cone from `w` over the
deletion of `C \ {w}` in the link of `w`. -/
theorem del_face_decomp {S : SComplex V} {C : Finset V} {w : V} (hw : w ∈ C) :
    S.del C = (S.del {w}).union (cone w ((S.link {w}).del (C.erase w))) := by
  have hvz : w ∉ ((S.link {w}).del (C.erase w)).verts := by
    intro h
    have := (mem_del.1 (mem_verts.1 h)).1
    rw [mem_link'] at this
    exact (disjoint_singleton_left.1 this.1) (mem_singleton_self w)
  refine ext_mem fun t => ?_
  rw [mem_union_iff, mem_del, mem_del, mem_cone_iff_erase hvz, mem_del, mem_link']
  by_cases hwt : w ∈ t
  · have hu : {w} ∪ t.erase w = t := by
      ext x; simp only [mem_union, mem_singleton, mem_erase]
      constructor
      · rintro (rfl | h); exact hwt; exact h.2
      · intro hx; by_cases h : x = w; exact .inl h; exact .inr ⟨h, hx⟩
    have hCt : C ⊆ t ↔ C.erase w ⊆ t.erase w := by
      constructor
      · intro h x hx
        exact mem_erase.2 ⟨(mem_erase.1 hx).1, h (mem_of_mem_erase hx)⟩
      · intro h x hx
        by_cases hxw : x = w
        · rw [hxw]; exact hwt
        · exact mem_of_mem_erase (h (mem_erase.2 ⟨hxw, hx⟩))
    rw [hu, ← hCt]
    have h1 : w ∉ t.erase w := Finset.notMem_erase w t
    have h2 : Disjoint {w} (t.erase w) := disjoint_singleton_left.2 h1
    have h3 : ¬ ({w} : Finset V) ⊆ t → False := fun h => h (singleton_subset_iff.2 hwt)
    tauto
  · have : t.erase w = t := erase_eq_of_notMem hwt
    rw [this]
    have hnC : ¬ C ⊆ t := fun h => hwt (h hw)
    have h2 : Disjoint {w} t := disjoint_singleton_left.2 hwt
    have h4 : ¬ ({w} : Finset V) ⊆ t := fun h => hwt (singleton_subset_iff.1 h)
    constructor
    · intro h; exact .inl ⟨h.1, h4⟩
    · rintro (h | h)
      · exact ⟨h.1, hnC⟩
      · exact ⟨down_mem h.1.2 subset_union_right, hnC⟩

/-- **Collar hypotheses for a face deletion**: the vertex deletion of a sphere together with the
ball cut out of the link of the vertex by the rest of the face. -/
theorem collarHyp_delFace [Infinite V] {n : ℕ} (hlow : ∀ m < n + 1, DelBall V m)
    {S : SComplex V} (hS : IsSB false (n + 2) S) {C : Finset V} {w : V} (hC : C ∈ S)
    (hw : w ∈ C) (hE : (C.erase w).Nonempty) :
    CollarHyp n w (S.del {w}) ((S.link {w}).del (C.erase w)) := by
  have hwS : {w} ∈ S := down_mem hC (singleton_subset_iff.2 hw)
  obtain ⟨m, hm, hL⟩ := link_sphere hS hwS (singleton_nonempty w)
  have hm' : m = n + 1 := by simpa using hm
  subst hm'
  set L := S.link {w} with hLdef
  have hEL : C.erase w ∈ L := by
    refine mem_link'.2 ⟨disjoint_singleton_left.2 (notMem_erase w C), ?_⟩
    have : {w} ∪ C.erase w = C := by
      ext x; simp only [mem_union, mem_singleton, mem_erase]
      constructor
      · rintro (rfl | h); exact hw; exact h.2
      · intro hx; by_cases h : x = w; exact .inl h; exact .inr ⟨h, hx⟩
    rwa [this]
  have hN := delBall_face (hlow n (by omega)) hL hEL hE
  have hbd := bd_del_eq hlow hS hwS
  refine ⟨del_isMfd hlow hS hwS, hN.1, hN.2, ?_, ?_, ?_, ?_⟩
  · exact mem_del.2 ⟨down_mem hEL (empty_subset _), fun h => by
      obtain ⟨x, hx⟩ := hE; exact notMem_empty x (h hx)⟩
  · intro s hs
    rw [hbd]; exact (mem_del.1 hs).1
  · intro h
    have := mem_del.1 (mem_verts.1 h)
    exact this.2 (subset_refl _)
  · intro A hA hAn s hs hAs
    rw [hbd] at hs
    refine mem_del.2 ⟨hs, fun hEs => hAn ?_⟩
    have hAE : A ∪ C.erase w ∈ L := down_mem hs (union_subset hAs hEs)
    have hEA : ¬ C.erase w ⊆ A := (mem_del.1 hA).2
    rcases A.eq_empty_or_nonempty with he | hne
    · exact mem_bd.2 ⟨hA, .inl he⟩
    · have hZmfd : IsMfdIn true n ((L.del (C.erase w))) := (isMfdIn_main true n).2 _ hN.1
      exact (hZmfd.mem_bd_iff hA hne).2 (link_delFace_ball (fun m hm => hlow m (by omega)) hL hne hAE hEA)

/-- **Deleting a face with at least two vertices** gives a complex stellar equivalent to the
deletion of one of its vertices. -/
theorem del_face_equiv [Infinite V] {n : ℕ} (hlow : ∀ m < n + 1, DelBall V m)
    {S : SComplex V} (hS : IsSB false (n + 2) S) {C : Finset V} {w : V} (hC : C ∈ S)
    (hw : w ∈ C) (hE : (C.erase w).Nonempty) : StellarEquivIn (S.del C) (S.del {w}) := by
  rw [del_face_decomp hw, SComplex.union_comm]
  exact collar_lemma (collarHyp_delFace hlow hS hC hw hE)

/-! ## One stellar move preserves "every vertex deletion is a ball" -/

/-- Every vertex deletion of `T` is a ball of index `k`. -/
def DelOK (k : ℕ) (T : SComplex V) : Prop := ∀ z : V, {z} ∈ T → IsNBall k (T.del {z})

/-- Deleting the whole face `C` is a ball when deleting one of its vertices is. -/
lemma isNBall_del_face [Infinite V] {n : ℕ} (hlow : ∀ m < n + 1, DelBall V m)
    {S : SComplex V} (hS : IsSB false (n + 2) S) {C : Finset V} {w : V} (hC : C ∈ S)
    (hw : w ∈ C) (h : IsNBall (n + 2) (S.del {w})) : IsNBall (n + 2) (S.del C) := by
  by_cases hE : (C.erase w).Nonempty
  · exact h.of_stellarEquivIn (del_face_equiv hlow hS hC hw hE).symm
  · have : C = {w} := by
      rw [not_nonempty_iff_eq_empty] at hE
      ext x; simp only [mem_singleton]
      constructor
      · intro hx; by_contra hxw
        have : x ∈ C.erase w := mem_erase.2 ⟨hxw, hx⟩
        rw [hE] at this; simp at this
      · rintro rfl; exact hw
    rw [this]; exact h

/-- A vertex of `S` outside `C` stays a vertex of the subdivision. -/
lemma singleton_mem_starAt {S : SComplex V} {C : Finset V} {c z : V} (hC : C ∈ S)
    (hne : C.Nonempty) (hc : c ∉ S.verts) (hz : {z} ∈ S) (hCz : ¬ C ⊆ {z}) :
    {z} ∈ S.starAt C c := by
  have := (mem_verts_starAt hC hne hc (x := z)).2 (.inr ⟨mem_verts.2 hz, hCz⟩)
  exact mem_verts.1 this

/-- Subdividing at a face `C` does not change a vertex deletion away from `C`, up to stellar
equivalence. -/
lemma starAt_del_equiv_outside [Infinite V] {S : SComplex V} {C : Finset V} {c z : V}
    (hC : C ∈ S) (hne : C.Nonempty) (hc : c ∉ S.verts) (hz : z ∉ C) (hcz : c ≠ z) :
    StellarEquivIn ((S.starAt C c).del {z}) (S.del {z}) := by
  rw [del_starAt_of_notMem hz hcz]
  have hCd : C ∈ S.del {z} := mem_del.2 ⟨hC, fun h => hz (singleton_subset_iff.1 h)⟩
  have hcd : c ∉ (S.del {z}).verts := fun h =>
    hc (mem_verts.2 (mem_del.1 (mem_verts.1 h)).1)
  exact (StellarEquivIn.starAt hCd hne hcd).symm

/-- **One stellar move preserves the vertex-deletion property**, for spheres of one dimension,
given the lower dimensions. -/
theorem delOK_starAt_iff [Infinite V] {n : ℕ} (hlow : ∀ m < n + 1, DelBall V m)
    {S : SComplex V} (hS : IsSB false (n + 2) S) {C : Finset V} {c : V} (hC : C ∈ S)
    (hne : C.Nonempty) (hc : c ∉ S.verts) :
    DelOK (n + 2) S ↔ DelOK (n + 2) (S.starAt C c) := by
  have hvT : ∀ z, {z} ∈ S.starAt C c ↔ z = c ∨ ({z} ∈ S ∧ ¬ C ⊆ {z}) := fun z => by
    rw [← mem_verts, mem_verts_starAt hC hne hc, mem_verts]
  have hcT : {c} ∈ S.starAt C c := (hvT c).2 (.inl rfl)
  have hcz : ∀ z, {z} ∈ S → c ≠ z := fun z hz e => hc (e ▸ mem_verts.2 hz)
  -- the deletion at the new vertex
  have hdc : (S.starAt C c).del {c} = S.del C := del_starAt_apex hc
  constructor
  · intro h z hz
    rcases (hvT z).1 hz with rfl | ⟨hzS, hCz⟩
    · rw [hdc]
      obtain ⟨w, hw⟩ := hne
      have hwS : {w} ∈ S := down_mem hC (singleton_subset_iff.2 hw)
      exact isNBall_del_face hlow hS hC hw (h w hwS)
    · by_cases hzC : z ∈ C
      · have hE : (C.erase z).Nonempty := by
          rw [nonempty_iff_ne_empty]; intro e
          exact hCz (fun x hx => by
            by_contra hx'
            have : x ∈ C.erase z := mem_erase.2 ⟨fun h => hx' (by rw [h]; exact mem_singleton_self z), hx⟩
            rw [e] at this; simp at this)
        exact (h z hzS).of_stellarEquivIn
          (del_starAt_equiv hlow hS hC hzC hE hc).symm
      · exact (h z hzS).of_stellarEquivIn
          (starAt_del_equiv_outside hC hne hc hzC (hcz z hzS)).symm
  · intro h z hz
    by_cases hzC : z ∈ C
    · by_cases hE : (C.erase z).Nonempty
      · have hCz : ¬ C ⊆ {z} := by
          intro hs
          obtain ⟨x, hx⟩ := hE
          obtain ⟨hxz, hxC⟩ := mem_erase.1 hx
          exact hxz (mem_singleton.1 (hs hxC))
        exact (h z ((hvT z).2 (.inr ⟨hz, hCz⟩))).of_stellarEquivIn
          (del_starAt_equiv hlow hS hC hzC hE hc)
      · have hCeq : C = {z} := by
          rw [not_nonempty_iff_eq_empty] at hE
          ext x; simp only [mem_singleton]
          constructor
          · intro hx; by_contra hxz
            have : x ∈ C.erase z := mem_erase.2 ⟨hxz, hx⟩
            rw [hE] at this; simp at this
          · rintro rfl; exact hzC
        have hh := h c hcT
        rw [hdc, hCeq] at hh
        exact hh
    · have hCz : ¬ C ⊆ {z} := by
        intro hs
        obtain ⟨x, hx⟩ := hne
        exact hzC (by rw [← mem_singleton.1 (hs hx)]; exact hx)
      exact (h z ((hvT z).2 (.inr ⟨hz, hCz⟩))).of_stellarEquivIn
        (starAt_del_equiv_outside hC hne hc hzC (hcz z hz))

/-- The vertex deletions of the boundary of a simplex are simplices. -/
theorem delOK_boundary {k : ℕ} (hk : 0 < k) {A : Finset V} (hA : #A = k + 1) : DelOK k (boundary A) := by
  intro z hz
  have hzA : z ∈ A := (mem_boundary.1 hz).1 (mem_singleton_self z)
  have hdel : (boundary A).del {z} = simplex (A.erase z) := by
    refine ext_mem fun t => ?_
    rw [mem_del, mem_boundary, mem_simplex, singleton_subset_iff]
    constructor
    · rintro ⟨h, hzt⟩
      intro x hx
      exact mem_erase.2 ⟨fun e => hzt (e ▸ hx), h.1 hx⟩
    · intro h
      refine ⟨⟨fun x hx => mem_of_mem_erase (h hx), fun hAt => ?_⟩, fun hzt => ?_⟩
      · exact notMem_erase z A (h (hAt hzA))
      · exact notMem_erase z A (h hzt)
  have hc : #(A.erase z) = k := by rw [card_erase_of_mem hzA]; omega
  rw [hdel]
  have hne : (A.erase z).Nonempty := by
    rw [← card_pos]; omega
  have hS : IsSB true k (simplex (A.erase z)) := .inr ⟨rfl, A.erase z, hc, Relation.EqvGen.refl _⟩
  exact ⟨hS, (hS.isBallIn_iff).2 (signedCount_simplex hne)⟩

/-- Stellar equivalence transports the vertex-deletion property between spheres. -/
theorem delOK_of_equiv [Infinite V] {n : ℕ} (hlow : ∀ m < n + 1, DelBall V m)
    {S T : SComplex V} (h : StellarEquivIn S T) :
    IsSB false (n + 2) S → (DelOK (n + 2) S ↔ DelOK (n + 2) T) := by
  induction h with
  | rel x y hxy =>
    intro hx
    cases hxy with
    | starAt hA hne ha => exact delOK_starAt_iff hlow hx hA hne ha
  | refl x => intro _; exact Iff.rfl
  | symm x y hxy ih =>
    intro hy
    exact (ih (hy.of_stellarEquivIn hxy.symm)).symm
  | trans x y z hxy hyz ih1 ih2 =>
    intro hx
    exact (ih1 hx).trans (ih2 (hx.of_stellarEquivIn hxy))

/-- **The case of dimension zero**: deleting a point from a `0`-sphere leaves a point. -/
theorem delBall_zero [Infinite V] : DelBall V 0 := by
  intro S hS z hz
  have hS' : ∃ A : Finset V, #A = 1 + 1 ∧ StellarEquivIn S (boundary A) :=
    hS.elim id (fun h => absurd h.1 (by simp))
  obtain ⟨A, hA, hSA⟩ := hS'
  have hAne : A.Nonempty := by rw [← card_pos]; omega
  have hcnt : S.signedCount = -1 := by
    rw [hSA.signedCount_eq, signedCount_boundary hAne, hA]; norm_num
  have hsing : ∀ t ∈ S, t.Nonempty → #t = 1 := by
    intro t ht htne
    obtain ⟨m, hm, -⟩ := link_sphere (n := 0) hS ht htne
    have : 0 < #t := card_pos.2 htne
    omega
  have h0 : (∅ : Finset V) ∈ S := down_mem hz (empty_subset _)
  set N := S.faces.erase ∅ with hN
  have hsum : S.signedCount = 1 - (#N : ℤ) := by
    unfold signedCount
    rw [← Finset.add_sum_erase _ _ (mem_faces.2 h0), ← hN]
    have : ∀ s ∈ N, ((-1 : ℤ) ^ #s) = -1 := by
      intro s hs
      rw [hN, mem_erase, mem_faces] at hs
      rw [hsing s hs.2 (nonempty_iff_ne_empty.2 hs.1), pow_one]
    rw [Finset.sum_congr rfl this]
    simp
    ring
  have hNc : #N = 2 := by
    have : (#N : ℤ) = 2 := by linarith
    exact_mod_cast this
  obtain ⟨p, q, hpq, hNpq⟩ := Finset.card_eq_two.1 hNc
  have hp : p ∈ N := by rw [hNpq]; simp
  have hq : q ∈ N := by rw [hNpq]; simp
  have hpS : p ∈ S ∧ p ≠ ∅ := by
    rw [hN, mem_erase, mem_faces] at hp; exact ⟨hp.2, hp.1⟩
  have hqS : q ∈ S ∧ q ≠ ∅ := by
    rw [hN, mem_erase, mem_faces] at hq; exact ⟨hq.2, hq.1⟩
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (hsing p hpS.1 (nonempty_iff_ne_empty.2 hpS.2))
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.1 (hsing q hqS.1 (nonempty_iff_ne_empty.2 hqS.2))
  have key : ∀ x y : V, x ≠ y → N = {{x}, {y}} → S.del {x} = simplex {y} := by
    intro x y hxy hNxy
    refine ext_mem fun t => ?_
    rw [mem_del, mem_simplex]
    constructor
    · rintro ⟨ht, hxt⟩
      rcases t.eq_empty_or_nonempty with rfl | htne
      · exact empty_subset _
      · have : t ∈ N := by rw [hN, mem_erase, mem_faces]; exact ⟨htne.ne_empty, ht⟩
        rw [hNxy] at this
        rcases mem_insert.1 this with h | h
        · exact absurd (h ▸ subset_rfl) hxt
        · exact (mem_singleton.1 h).le
    · intro ht
      have hy : {y} ∈ S := by
        have : {y} ∈ N := by rw [hNxy]; simp
        rw [hN, mem_erase, mem_faces] at this; exact this.2
      refine ⟨down_mem hy ht, fun hxt => ?_⟩
      have := ht (hxt (mem_singleton_self x))
      exact hxy (mem_singleton.1 this)
  have hzN : {z} ∈ N := by
    rw [hN, mem_erase, mem_faces]; exact ⟨singleton_ne_empty z, hz⟩
  have hab : a ≠ b := fun e => hpq (by rw [e])
  have hdel : ∃ y : V, S.del {z} = simplex {y} := by
    rw [hNpq] at hzN
    rcases mem_insert.1 hzN with h | h
    · exact ⟨b, by rw [h]; exact key a b hab hNpq⟩
    · exact ⟨a, by rw [mem_singleton.1 h]; exact key b a hab.symm (by rw [hNpq]; exact Finset.pair_comm _ _)⟩
  obtain ⟨y, hy⟩ := hdel
  rw [hy]
  have hS1 : IsSB true 1 (simplex ({y} : Finset V)) :=
    .inr ⟨rfl, {y}, card_singleton y, Relation.EqvGen.refl _⟩
  exact ⟨hS1, (hS1.isBallIn_iff).2 (signedCount_simplex (singleton_nonempty y))⟩

/-- **Lickorish's Lemma 3.8 (vertex form)**: deleting a vertex from a PL sphere of any dimension
leaves a PL ball, that is, the complement of the open star of a vertex in a stellar sphere is a
stellar ball. -/
theorem delBall_all [Infinite V] (m : ℕ) : DelBall V m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | n
    · exact delBall_zero
    · intro S hS z hz
      have hS' : ∃ A : Finset V, #A = n + 1 + 1 + 1 ∧ StellarEquivIn S (boundary A) :=
        hS.elim id (fun h => absurd h.1 (by simp))
      obtain ⟨A, hA, hSA⟩ := hS'
      have hS2 : IsSB false (n + 2) S := hS
      have hlow : ∀ k < n + 1, DelBall V k := fun k hk => ih k (by omega)
      have := (delOK_of_equiv hlow hSA hS2).2 (delOK_boundary (k := n + 2) (by omega) (by omega))
      exact this z hz

/-- **Deleting any nonempty face from a PL sphere leaves a PL ball.** -/
theorem delBall_face_all [Infinite V] {m : ℕ} {S : SComplex V} (hS : IsSB false (m + 1) S)
    {B : Finset V} (hB : B ∈ S) (hne : B.Nonempty) : IsNBall (m + 1) (S.del B) :=
  delBall_face (delBall_all m) hS hB hne

/-- Non-vacuity: removing a vertex from the boundary of a triangle leaves a ball (an arc). -/
example : IsNBall 2 ((boundary ({0, 1, 2} : Finset ℕ)).del {0}) :=
  delBall_all 1 _ (.inl ⟨{0, 1, 2}, by decide, Relation.EqvGen.refl _⟩) 0
    (mem_boundary.2 (by decide))

/-- Wrong-model check: the boundary of a triangle itself is not a ball. -/
example : ¬ IsNBall 2 (boundary ({0, 1, 2} : Finset ℕ)) := by
  intro h
  have := (h.1.isBallIn_iff).1 h.2
  rw [signedCount_boundary (by decide)] at this
  simp at this

end SComplex
end Lightlike.PL
