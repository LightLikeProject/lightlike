import Lightlike.PL.BallJoin
import Lightlike.PL.SphereBall
import Lightlike.PL.Collar

/-!
# Replacing the cone on a sphere inside a complex

Facts about cones on spheres used when a cell is cut: the boundary of the cone on a PL sphere is
that sphere, and the sphere is not a ball.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V] [Infinite V]

/-- **The boundary of a cone on a sphere is the sphere.** -/
theorem bd_cone_sphere {n : ℕ} {F : SComplex V} (hF : IsSB false (n + 1) F) {w : V}
    (hw : w ∉ F.verts) (h0 : ∅ ∈ F) : (cone w F).bd = F := by
  refine ext_mem fun σ => ?_
  rw [mem_bd]
  constructor
  · rintro ⟨hσ, h | ⟨τ, hτ, hστ, hne, hb⟩⟩
    · subst h; exact h0
    · obtain ⟨t, ht, hτt⟩ := mem_cone.1 hτ
      rcases hτt with rfl | rfl
      · exact down_mem ht hστ
      · -- `τ` passes through the apex: its link is a sphere, not a ball
        exfalso
        have hl := link_cone_insert hw ht
        rw [hl] at hb
        rcases t.eq_empty_or_nonempty with rfl | htne
        · have hF' : IsSB false (n + 1) (F.link ∅) := by rwa [link_empty]
          obtain ⟨A, hA, hFA⟩ := hF.resolve_right (by simp)
          exact IsSB.not_isBallIn hA hFA (by rwa [link_empty] at hb)
        · obtain ⟨m, hm, hs⟩ := link_sphere hF ht htne
          obtain ⟨A, hA, hFA⟩ := hs.resolve_right (by simp)
          exact IsSB.not_isBallIn hA hFA hb
  · intro hσ
    refine ⟨mem_cone.2 ⟨σ, hσ, .inl rfl⟩, ?_⟩
    rcases σ.eq_empty_or_nonempty with rfl | hne
    · exact .inl rfl
    · refine .inr ⟨σ, mem_cone.2 ⟨σ, hσ, .inl rfl⟩, subset_rfl, hne, ?_⟩
      obtain ⟨m, hm, hs⟩ := link_sphere hF hσ hne
      rw [link_cone_of_mem hw hσ]
      exact isBallIn_cone (isSB_true_of_false hs) (fun h => hw (verts_link_subset F σ h))


omit [Infinite V] in
/-- The void complex `{∅}` is stellar equivalent only to itself. -/
lemma eq_simplex_empty_of_stellarEquivIn {K : SComplex V} (h : StellarEquivIn K (simplex ∅)) :
    K = simplex ∅ := by
  have key : ∀ X Y : SComplex V, StellarEquivIn X Y → (X = simplex ∅ ↔ Y = simplex ∅) := by
    intro X Y hXY
    induction hXY with
    | rel X Y hs =>
      obtain ⟨hA, hne, ha⟩ := hs
      rename_i A a
      constructor
      · rintro rfl
        obtain ⟨x, hx⟩ := hne
        have := mem_simplex.1 hA
        simp at this
        subst this
        simp at hx
      · intro hY
        have h1 := apex_mem_verts hA hne (a := a)
        rw [hY] at h1
        rw [mem_verts, mem_simplex] at h1
        simp at h1
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key _ _ h).2 rfl

/-- **The boundary of a cone on a sphere is the sphere**, for spheres of every dimension,
including the `0`-sphere's predecessor, the void complex. -/
theorem bd_cone_sphere' {n : ℕ} {F : SComplex V} (hF : IsSB false n F) {w : V}
    (hw : w ∉ F.verts) (h0 : ∅ ∈ F) : (cone w F).bd = F := by
  cases n with
  | succ n => exact bd_cone_sphere hF hw h0
  | zero =>
    obtain ⟨A, hA, hFA⟩ := hF.resolve_right (by simp)
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hA
    rw [boundary_singleton] at hFA
    have hF := eq_simplex_empty_of_stellarEquivIn hFA
    refine ext_mem fun σ => ?_
    rw [mem_bd]
    constructor
    · rintro ⟨hσ, h | ⟨τ, hτ, hστ, hne, hb⟩⟩
      · subst h; exact h0
      · exfalso
        obtain ⟨t, ht, hτt⟩ := mem_cone.1 hτ
        rw [hF, mem_simplex, subset_empty] at ht
        subst ht
        rcases hτt with rfl | rfl
        · exact absurd rfl hne.ne_empty
        · have hl := link_cone_insert hw (show (∅ : Finset V) ∈ F from h0)
          rw [hl, link_empty, hF] at hb
          exact not_isBallIn_simplex_empty hb
    · intro hσ
      refine ⟨mem_cone.2 ⟨σ, hσ, .inl rfl⟩, ?_⟩
      rw [hF, mem_simplex, subset_empty] at hσ
      exact .inl hσ


/-- The vertex conditions of `stellarEquivIn_replace_ball_join` follow from the face conditions,
by applying the latter to singletons. -/
theorem stellarEquivIn_replace_ball_join_faces {m : ℕ} {B B' Z R : SComplex V}
    (hB : IsSB true m B) (hbb : IsBallIn B) (hB' : IsSB true m B') (hbb' : IsBallIn B')
    (hbd : B.bd = B'.bd) (hZ : ∅ ∈ Z) (hBZ : Disjoint B.verts Z.verts)
    (hBZ' : Disjoint B'.verts Z.verts)
    (hf : ∀ s ∈ B.join Z, s ∈ R → s ∈ B.bd.join Z)
    (hf' : ∀ s ∈ B'.join Z, s ∈ R → s ∈ B.bd.join Z) :
    StellarEquivIn ((B.join Z).union R) ((B'.join Z).union R) :=
  stellarEquivIn_replace_ball_join hB hbb hB' hbb' hbd hZ hBZ hBZ'
    (fun _ hxR hxB => mem_verts.2 (hf _ (mem_verts.1 hxB) (mem_verts.1 hxR)))
    hf
    (fun _ hxR hxB => mem_verts.2 (hf' _ (mem_verts.1 hxB) (mem_verts.1 hxR)))
    hf'

omit [Infinite V] in
/-- **The apex lemma.** A face of `cone w S * Z` that lies in a complex `R` not containing `w` as a
vertex already lies in `S * Z`. -/
lemma mem_join_of_mem_cone_join {S Z R : SComplex V} {w : V} (hw : w ∉ R.verts) {s : Finset V}
    (hs : s ∈ (cone w S).join Z) (hR : s ∈ R) : s ∈ S.join Z := by
  obtain ⟨t, ht, u, hu, rfl⟩ := mem_join.1 hs
  have hwt : w ∉ t := fun h =>
    hw (subset_verts hR (mem_union_left _ h))
  obtain ⟨r, hr, he | he⟩ := mem_cone.1 ht
  · exact mem_join.2 ⟨t, he ▸ hr, u, hu, rfl⟩
  · exact absurd (he ▸ mem_insert_self _ _) hwt

omit [Infinite V] in
/-- **Joins with a common complex intersect in the join of the intersection**, when the vertices
of the two factors avoid those of the common complex. -/
lemma mem_join_inter {X₁ X₂ T Z : SComplex V} (h1 : Disjoint X₁.verts Z.verts)
    (h2 : Disjoint X₂.verts Z.verts) (hT : ∀ x, x ∈ X₁ → x ∈ X₂ → x ∈ T) {s : Finset V}
    (hs1 : s ∈ X₁.join Z) (hs2 : s ∈ X₂.join Z) : s ∈ T.join Z := by
  obtain ⟨t₁, ht₁, u₁, hu₁, rfl⟩ := mem_join.1 hs1
  obtain ⟨t₂, ht₂, u₂, hu₂, he⟩ := mem_join.1 hs2
  have key : t₁ = t₂ := by
    ext x
    constructor
    · intro hx
      have : x ∈ t₂ ∪ u₂ := he ▸ mem_union_left _ hx
      rcases mem_union.1 this with h | h
      · exact h
      · exact absurd (subset_verts hu₂ h) (Finset.disjoint_left.1 h1 (subset_verts ht₁ hx))
    · intro hx
      have : x ∈ t₁ ∪ u₁ := he.symm ▸ mem_union_left _ hx
      rcases mem_union.1 this with h | h
      · exact h
      · exact absurd (subset_verts hu₁ h) (Finset.disjoint_left.1 h2 (subset_verts ht₂ hx))
  subst key
  exact mem_join.2 ⟨t₁, hT _ ht₁ ht₂, u₁, hu₁, rfl⟩

omit [Infinite V] in
/-- A complex is the deletion of a vertex together with the cone on its link. -/
lemma eq_del_union_cone_link (S : SComplex V) (z : V) :
    S = (S.del {z}).union (cone z (S.link {z})) := by
  have := del_union_star S {z}
  rw [star_eq_join] at this
  exact this

omit [Infinite V] in
/-- The deleted vertex is not a vertex of the deletion. -/
lemma notMem_verts_del (S : SComplex V) (z : V) : z ∉ (S.del {z}).verts := by
  intro h
  have := (mem_del.1 (mem_verts.1 h)).2
  exact this subset_rfl

/-- The deletion of a vertex from a sphere is a ball whose boundary is the link of the vertex. -/
lemma isNBall_del_bd {n : ℕ} {S : SComplex V} (hS : IsSB false (n + 1) S) {z : V}
    (hz : {z} ∈ S) :
    IsNBall (n + 1) (S.del {z}) ∧ (S.del {z}).bd = S.link {z} ∧
      IsSB false (n) (S.link {z}) := by
  refine ⟨delBall_all (n) S hS z hz, bd_del_eq (fun m _ => delBall_all m) hS hz, ?_⟩
  obtain ⟨m, hm, hs⟩ := link_sphere hS hz (singleton_nonempty z)
  have : m = n := by simpa using hm
  exact this ▸ hs

/-- **The cone on the deletion of a vertex from a sphere** is a ball whose boundary is the sphere. -/
lemma bd_cone_del {n : ℕ} {S : SComplex V} (hS : IsSB false (n + 1) S) {z : V}
    (hz : {z} ∈ S) : (cone z (S.del {z})).bd = S := by
  obtain ⟨hB, hbd, -⟩ := isNBall_del_bd hS hz
  have h0 : ∅ ∈ S.del {z} := mem_del.2 ⟨empty_mem hz, fun h => by simp at h⟩
  rw [bd_cone hB.1 hB.2 h0 (notMem_verts_del S z), hbd]
  exact (eq_del_union_cone_link S z).symm

/-- **Two deletions glued along their common link form a sphere.** If `Sp` and `Sm` are spheres
that have the same link of `z`, and their deletions of `z` meet only inside that link, then the union
of the two deletions is a sphere. -/
lemma isSB_del_union {n : ℕ} {Sp Sm : SComplex V} (hp : IsSB false (n + 1) Sp)
    (hm : IsSB false (n + 1) Sm) {z : V} (hzp : {z} ∈ Sp) (hzm : {z} ∈ Sm)
    (hG : Sp.link {z} = Sm.link {z})
    (hint : ∀ s, s ∈ Sp.del {z} → s ∈ Sm.del {z} → s ∈ Sp.link {z}) :
    IsSB false (n + 1) ((Sp.del {z}).union (Sm.del {z})) := by
  obtain ⟨hBp, hbdp, hGs⟩ := isNBall_del_bd hp hzp
  obtain ⟨hBm, hbdm, -⟩ := isNBall_del_bd hm hzm
  have hzG : z ∉ (Sp.link {z}).verts := fun h =>
    (Finset.disjoint_singleton_left.1 (mem_link.1 (mem_verts.1 h)).2.1) (mem_singleton_self z)
  have h0G : ∅ ∈ Sp.link {z} := mem_link.2 ⟨empty_mem hzp, by simp, by simpa using hzp⟩
  have hcone : IsSB true (n + 1) (cone z (Sp.link {z})) := isSB_cone (isSB_true_of_false hGs) hzG
  have hconeB : IsBallIn (cone z (Sp.link {z})) := isBallIn_cone (isSB_true_of_false hGs) hzG
  have hbdc : (cone z (Sp.link {z})).bd = Sp.link {z} := bd_cone_sphere' hGs hzG h0G
  have hbd : (Sm.del {z}).bd = Sp.link {z} := hbdm.trans hG.symm
  have e : StellarEquivIn ((Sm.del {z}).union (Sp.del {z}))
      ((cone z (Sp.link {z})).union (Sp.del {z})) := by
    refine stellarEquivIn_replace_ball hBm.1 hBm.2 hcone hconeB (hbd.trans hbdc.symm) ?_ ?_ ?_ ?_
    · intro x hxR hxB
      exact mem_verts.2 (hbd ▸ hint _ (mem_verts.1 hxR) (mem_verts.1 hxB))
    · intro s hs hsR
      exact hbd ▸ hint _ hsR hs
    · intro x hxR hxB
      have hxz : x ≠ z := fun e => notMem_verts_del Sp z (e ▸ hxR)
      obtain ⟨t, ht, h | h⟩ := mem_cone.1 (mem_verts.1 hxB)
      · exact mem_verts.2 (hbd ▸ h ▸ ht)
      · exact absurd ((h ▸ mem_insert_self z t : z ∈ ({x} : Finset V)) |> mem_singleton.1).symm hxz
    · intro s hs hsR
      obtain ⟨t, ht, h | h⟩ := mem_cone.1 hs
      · exact hbd ▸ h ▸ ht
      · exfalso
        exact (mem_del.1 hsR).2 (by
          rw [h]; exact singleton_subset_iff.2 (mem_insert_self z t))
  have hS : (cone z (Sp.link {z})).union (Sp.del {z}) = Sp := by
    rw [union_comm]; exact (eq_del_union_cone_link Sp z).symm
  rw [hS] at e
  rw [union_comm]
  exact hp.of_stellarEquivIn e.symm

omit [Infinite V] in
/-- The vertices of a deletion are vertices of the complex. -/
lemma verts_del_subset (S : SComplex V) (A : Finset V) : (S.del A).verts ⊆ S.verts :=
  fun _ hx => mem_verts.2 (mem_del.1 (mem_verts.1 hx)).1

omit [Infinite V] in
/-- A cone on a complex whose vertices avoid `Z`, with apex outside `Z`, also avoids `Z`. -/
lemma disjoint_cone_verts {X Z : SComplex V} {w : V} (hw : w ∉ Z.verts)
    (h : Disjoint X.verts Z.verts) : Disjoint (cone w X).verts Z.verts := by
  refine Finset.disjoint_left.2 fun x hx hxZ => ?_
  rcases mem_insert.1 (verts_cone_subset X w hx) with rfl | hxX
  · exact hw hxZ
  · exact Finset.disjoint_left.1 h hxX hxZ

omit [Infinite V] in
/-- A face of two cones whose apex is a vertex of neither factor lies in the first base. -/
lemma mem_of_mem_cone_cone {X Y : SComplex V} {u w : V} (huY : u ∉ Y.verts) (huw : u ≠ w)
    {x : Finset V} (h1 : x ∈ cone u X) (h2 : x ∈ cone w Y) : x ∈ X := by
  obtain ⟨t, ht, e | e⟩ := mem_cone.1 h1
  · exact e ▸ ht
  · exfalso
    have hux : u ∈ x := e ▸ mem_insert_self u t
    obtain ⟨t', ht', e' | e'⟩ := mem_cone.1 h2
    · exact huY (subset_verts ht' (e' ▸ hux))
    · rcases mem_insert.1 (e' ▸ hux) with h | h
      · exact huw h
      · exact huY (subset_verts ht' h)

omit [Infinite V] in
/-- A face of the cone on a deletion that lies in the other sphere lies in the first sphere, when
the deletions meet only inside the common link. -/
lemma mem_of_mem_cone_del {A B : SComplex V} {z : V}
    (hint : ∀ s, s ∈ A.del {z} → s ∈ B.del {z} → s ∈ A.link {z}) {x : Finset V}
    (h1 : x ∈ cone z (A.del {z})) (h2 : x ∈ B) : x ∈ A := by
  obtain ⟨t, ht, e | e⟩ := mem_cone.1 h1
  · exact e ▸ (mem_del.1 ht).1
  · have htB : t ∈ B := down_mem (e ▸ h2) (e ▸ subset_insert z t)
    have hzt : ¬ {z} ⊆ t := (mem_del.1 ht).2
    have := hint t ht (mem_del.2 ⟨htB, hzt⟩)
    rw [mem_link'] at this
    rw [e]
    simpa using this.2

omit [Infinite V] in
/-- The cones on the two deletions meet only inside both spheres. -/
lemma mem_of_mem_cone_del_cone_del {A B : SComplex V} {z : V}
    (hint : ∀ s, s ∈ A.del {z} → s ∈ B.del {z} → s ∈ A.link {z}) {x : Finset V}
    (h1 : x ∈ cone z (A.del {z})) (h2 : x ∈ cone z (B.del {z})) : x ∈ A := by
  obtain ⟨t, ht, e | e⟩ := mem_cone.1 h1
  · exact e ▸ (mem_del.1 ht).1
  · obtain ⟨t', ht', e' | e'⟩ := mem_cone.1 h2
    · exact absurd (e' ▸ e ▸ singleton_subset_iff.2 (mem_insert_self z t)) (mem_del.1 ht').2
    · have hzt : z ∉ t := fun h => (mem_del.1 ht).2 (singleton_subset_iff.2 h)
      have hzt' : z ∉ t' := fun h => (mem_del.1 ht').2 (singleton_subset_iff.2 h)
      have htt : t = t' := by
        have := e.symm.trans e'
        rw [← Finset.erase_insert hzt, this, Finset.erase_insert hzt']
      have := hint t ht (htt ▸ ht')
      rw [mem_link'] at this
      rw [e]
      simpa using this.2

omit [Infinite V] in
/-- Reordering three disjuncts. -/
lemma or_reorder₁ (P Q T : Prop) : (P ∨ Q) ∨ T ↔ Q ∨ (P ∨ T) := by tauto

/-- Reordering three disjuncts. -/
lemma or_reorder₂ (P Q T : Prop) : P ∨ (Q ∨ T) ↔ Q ∨ (P ∨ T) := by tauto

/-- Reordering three disjuncts. -/
lemma or_reorder₃ (P Q T : Prop) : P ∨ (Q ∨ T) ↔ (P ∨ Q) ∨ T := by tauto

omit [Infinite V] in
/-- A join is monotone in its first factor. -/
lemma mem_join_mono {X Y Z : SComplex V} (h : ∀ x ∈ X, x ∈ Y) {s : Finset V} (hs : s ∈ X.join Z) :
    s ∈ Y.join Z := by
  obtain ⟨t, ht, w, hw, rfl⟩ := mem_join.1 hs
  exact mem_join.2 ⟨t, h t ht, w, hw, rfl⟩

/-- **The cut swap.** Inside a join with `Z` and a complex `R` that avoids the apexes, the cone on the
union `F` of the two deletions of `z` is exchanged, by three ball swaps, for the two cones on the
spheres `Sp` and `Sm`. -/
theorem stellarEquivIn_cut_swap {n : ℕ} {Sp Sm Z R : SComplex V}
    (hp : IsSB false (n + 1) Sp) (hm : IsSB false (n + 1) Sm) {z a u v : V}
    (hzp : {z} ∈ Sp) (hzm : {z} ∈ Sm) (hG : Sp.link {z} = Sm.link {z})
    (hint : ∀ s, s ∈ Sp.del {z} → s ∈ Sm.del {z} → s ∈ Sp.link {z})
    (hZ : ∅ ∈ Z) (hZp : Disjoint Sp.verts Z.verts) (hZm : Disjoint Sm.verts Z.verts)
    (haZ : a ∉ Z.verts) (huZ : u ∉ Z.verts) (hvZ : v ∉ Z.verts)
    (haSp : a ∉ Sp.verts) (haSm : a ∉ Sm.verts) (huSp : u ∉ Sp.verts) (huSm : u ∉ Sm.verts)
    (hvSp : v ∉ Sp.verts) (hvSm : v ∉ Sm.verts) (huv : u ≠ v)
    (hzR : z ∉ R.verts) (haR : a ∉ R.verts) (huR : u ∉ R.verts) (hvR : v ∉ R.verts) :
    StellarEquivIn (((cone a ((Sp.del {z}).union (Sm.del {z}))).join Z).union R)
      ((((cone u Sp).union (cone v Sm)).join Z).union R) := by
  have hzSp : z ∈ Sp.verts := mem_verts.2 hzp
  have hzSm : z ∈ Sm.verts := mem_verts.2 hzm
  have hzZ : z ∉ Z.verts := fun h => Finset.disjoint_left.1 hZp hzSp h
  have hFs := isSB_del_union hp hm hzp hzm hG hint
  obtain ⟨hBp, hbdp, hGs⟩ := isNBall_del_bd hp hzp
  obtain ⟨hBm, hbdm, -⟩ := isNBall_del_bd hm hzm
  have hFv : ∀ x ∈ ((Sp.del {z}).union (Sm.del {z})).verts, x ∈ Sp.verts ∨ x ∈ Sm.verts := by
    intro x hx
    rw [verts_union] at hx
    rcases mem_union.1 hx with h | h
    · exact .inl (verts_del_subset _ _ h)
    · exact .inr (verts_del_subset _ _ h)
  have hF0 : ∅ ∈ (Sp.del {z}).union (Sm.del {z}) :=
    mem_union_iff.2 (.inl (mem_del.2 ⟨empty_mem hzp, fun h => by simp at h⟩))
  have haF : a ∉ ((Sp.del {z}).union (Sm.del {z})).verts := fun h =>
    (hFv a h).elim haSp haSm
  have hzF : z ∉ ((Sp.del {z}).union (Sm.del {z})).verts := by
    rw [verts_union]
    exact fun h => (mem_union.1 h).elim (notMem_verts_del Sp z) (notMem_verts_del Sm z)
  have hZF : Disjoint ((Sp.del {z}).union (Sm.del {z})).verts Z.verts :=
    Finset.disjoint_left.2 fun x hx hxZ => (hFv x hx).elim
      (fun h => Finset.disjoint_left.1 hZp h hxZ) (fun h => Finset.disjoint_left.1 hZm h hxZ)
  -- the four balls and their boundaries
  have hFB := isSB_true_of_false hFs
  have hbdaF : (cone a ((Sp.del {z}).union (Sm.del {z}))).bd = (Sp.del {z}).union (Sm.del {z}) :=
    bd_cone_sphere hFs haF hF0
  have hbdzF : (cone z ((Sp.del {z}).union (Sm.del {z}))).bd = (Sp.del {z}).union (Sm.del {z}) :=
    bd_cone_sphere hFs hzF hF0
  have hCp := bd_cone_del hp hzp
  have hCm := bd_cone_del hm hzm
  have hbdu : (cone u Sp).bd = Sp := bd_cone_sphere (n := n) hp huSp (empty_mem hzp)
  have hbdv : (cone v Sm).bd = Sm := bd_cone_sphere (n := n) hm hvSm (empty_mem hzm)
  -- step 1: replace the apex `a` by `z`
  have step1 : StellarEquivIn
      (((cone a ((Sp.del {z}).union (Sm.del {z}))).join Z).union R)
      (((cone z ((Sp.del {z}).union (Sm.del {z}))).join Z).union R) := by
    refine stellarEquivIn_replace_ball_join_faces (isSB_cone hFB haF) (isBallIn_cone hFB haF)
      (isSB_cone hFB hzF) (isBallIn_cone hFB hzF) (hbdaF.trans hbdzF.symm) hZ
      (disjoint_cone_verts haZ hZF) (disjoint_cone_verts hzZ hZF) ?_ ?_
    · intro s hs hsR
      rw [hbdaF]; exact mem_join_of_mem_cone_join haR hs hsR
    · intro s hs hsR
      rw [hbdaF]; exact mem_join_of_mem_cone_join hzR hs hsR
  have hZΦp : Disjoint (Sp.del {z}).verts Z.verts :=
    Finset.disjoint_left.2 fun x hx hxZ => Finset.disjoint_left.1 hZp (verts_del_subset _ _ hx) hxZ
  have hZΦm : Disjoint (Sm.del {z}).verts Z.verts :=
    Finset.disjoint_left.2 fun x hx hxZ => Finset.disjoint_left.1 hZm (verts_del_subset _ _ hx) hxZ
  have hint' : ∀ s, s ∈ Sm.del {z} → s ∈ Sp.del {z} → s ∈ Sm.link {z} :=
    fun s h1 h2 => hG ▸ hint s h2 h1
  have hvΦp : v ∉ (Sp.del {z}).verts := fun h => hvSp (verts_del_subset _ _ h)
  have huΦm : u ∉ (Sm.del {z}).verts := fun h => huSm (verts_del_subset _ _ h)
  have hvz : v ≠ z := fun e => hvSm (e ▸ hzSm)
  have eq1 : ((cone z ((Sp.del {z}).union (Sm.del {z}))).join Z).union R =
      ((cone z (Sm.del {z})).join Z).union (((cone z (Sp.del {z})).join Z).union R) := by
    rw [cone_union, join_union_left]
    exact ext_mem fun s => by simp only [mem_union_iff]; exact or_reorder₁ _ _ _
  -- step 2: replace the cone on the deletion of `Sm` by the cone on `Sm`
  have step2 : StellarEquivIn
      (((cone z (Sm.del {z})).join Z).union (((cone z (Sp.del {z})).join Z).union R))
      (((cone v Sm).join Z).union (((cone z (Sp.del {z})).join Z).union R)) := by
    refine stellarEquivIn_replace_ball_join_faces
      (isSB_cone hBm.1 (notMem_verts_del Sm z)) (isBallIn_cone hBm.1 (notMem_verts_del Sm z))
      (isSB_cone (isSB_true_of_false hm) hvSm) (isBallIn_cone (isSB_true_of_false hm) hvSm)
      (hCm.trans hbdv.symm) hZ (disjoint_cone_verts hzZ hZΦm) (disjoint_cone_verts hvZ hZm)
      ?_ ?_
    · intro s hs hsR
      rw [hCm]
      rcases mem_union_iff.1 hsR with h | h
      · exact mem_join_inter (disjoint_cone_verts hzZ hZΦm) (disjoint_cone_verts hzZ hZΦp)
          (fun x h1 h2 => mem_of_mem_cone_del_cone_del hint' h1 h2) hs h
      · exact mem_join_mono (fun x hx => (mem_del.1 hx).1) (mem_join_of_mem_cone_join hzR hs h)
    · intro s hs hsR
      rw [hCm]
      rcases mem_union_iff.1 hsR with h | h
      · exact mem_join_inter (disjoint_cone_verts hvZ hZm) (disjoint_cone_verts hzZ hZΦp)
          (fun x h1 h2 => mem_of_mem_cone_cone hvΦp hvz h1 h2) hs h
      · exact mem_join_of_mem_cone_join hvR hs h
  have eq2 : ((cone v Sm).join Z).union (((cone z (Sp.del {z})).join Z).union R) =
      ((cone z (Sp.del {z})).join Z).union (((cone v Sm).join Z).union R) :=
    ext_mem fun s => by simp only [mem_union_iff]; exact or_reorder₂ _ _ _
  -- step 3: replace the cone on the deletion of `Sp` by the cone on `Sp`
  have step3 : StellarEquivIn
      (((cone z (Sp.del {z})).join Z).union (((cone v Sm).join Z).union R))
      (((cone u Sp).join Z).union (((cone v Sm).join Z).union R)) := by
    refine stellarEquivIn_replace_ball_join_faces
      (isSB_cone hBp.1 (notMem_verts_del Sp z)) (isBallIn_cone hBp.1 (notMem_verts_del Sp z))
      (isSB_cone (isSB_true_of_false hp) huSp) (isBallIn_cone (isSB_true_of_false hp) huSp)
      (hCp.trans hbdu.symm) hZ (disjoint_cone_verts hzZ hZΦp) (disjoint_cone_verts huZ hZp)
      ?_ ?_
    · intro s hs hsR
      rw [hCp]
      rcases mem_union_iff.1 hsR with h | h
      · exact mem_join_inter (disjoint_cone_verts hzZ hZΦp) (disjoint_cone_verts hvZ hZm)
          (fun x h1 h2 => mem_of_mem_cone_del hint h1
            (mem_of_mem_cone_cone hvΦp hvz h2 h1)) hs h
      · exact mem_join_mono (fun x hx => (mem_del.1 hx).1) (mem_join_of_mem_cone_join hzR hs h)
    · intro s hs hsR
      rw [hCp]
      rcases mem_union_iff.1 hsR with h | h
      · exact mem_join_inter (disjoint_cone_verts huZ hZp) (disjoint_cone_verts hvZ hZm)
          (fun x h1 h2 => mem_of_mem_cone_cone huSm huv h1 h2) hs h
      · exact mem_join_of_mem_cone_join huR hs h
  have eq3 : ((cone u Sp).join Z).union (((cone v Sm).join Z).union R) =
      ((((cone u Sp).union (cone v Sm)).join Z).union R) := by
    rw [join_union_left]
    exact ext_mem fun s => by simp only [mem_union_iff]; exact or_reorder₃ _ _ _
  refine step1.trans ?_
  rw [eq1]
  refine step2.trans ?_
  rw [eq2]
  refine step3.trans ?_
  rw [eq3]

end SComplex
end Lightlike.PL
