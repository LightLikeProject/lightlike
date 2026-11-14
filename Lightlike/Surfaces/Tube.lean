import Lightlike.Surfaces.Chains

/-!
# Moving the far end of a tube, and closing a handle

This file turns the checked chains of `Chains.lean` into statements about an arbitrary closed
surface. A **tube** `tube c₀ c₁ c₂ p q r` is a triangulated annulus with one boundary triangle
`{c₀, c₁, c₂}` and the other `{p, q, r}`; the vertices `cᵢ` are new.

* `tube_slide`: if `{p, q, r}` and `{q, r, s}` are adjacent triangles of the surface, the far end of
  a tube attached at `{p, q, r}` can be slid across the edge `{q, r}` to `{q, s, r}` by 2D moves.
* `walk`: by repeating the slide along a dual path, the far end reaches any triangle.

The vertex set `V` is arbitrary and the moves are bistellar moves of `Move2`.
-/

open Finset Relation

namespace Lightlike.Surfaces

open Lightlike.PR

set_option maxRecDepth 100000

variable {V : Type*} [DecidableEq V]

section helpers

lemma union_insert_of_mem {R U T : Finset (Finset V)} {e : Finset V} (he : e ∈ R) :
    (R.erase e ∪ U) ∪ insert e T = R ∪ U ∪ T := by
  ext t
  simp only [mem_union, mem_insert, mem_erase]
  by_cases h : t = e
  · subst h; simp [he]
  · simp [h]

lemma union_insert_swap (R U T : Finset (Finset V)) (x : Finset V) :
    (R ∪ U) ∪ insert x T = insert x R ∪ U ∪ T := by
  ext t; simp only [mem_union, mem_insert]; tauto

lemma insert_erase_erase {M : Finset (Finset V)} {e e' : Finset V} (he : e ∈ M) (hne : e ≠ e') :
    insert e ((M.erase e).erase e') = M.erase e' := by
  ext t
  simp only [mem_insert, mem_erase]
  constructor
  · rintro (rfl | ⟨h1, -, h3⟩)
    · exact ⟨hne, he⟩
    · exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    by_cases h : t = e
    · exact Or.inl h
    · exact Or.inr ⟨h1, h, h2⟩

omit [DecidableEq V] in
lemma nodup_3_4 {C W : Finset V} {c₀ c₁ c₂ p q r s : V} (h0 : c₀ ∈ C) (h1 : c₁ ∈ C)
    (h2 : c₂ ∈ C) (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (hp : p ∈ W) (hq : q ∈ W)
    (hr : r ∈ W) (hs : s ∈ W) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) (hCW : ∀ c ∈ C, c ∉ W) : [c₀, c₁, c₂, p, q, r, s].Nodup := by
  have n : ∀ {c x}, c ∈ C → x ∈ W → c ≠ x := fun hc hx h => hCW _ hc (h ▸ hx)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, not_or,
    and_true, not_false_eq_true]
  exact ⟨⟨h01, h02, n h0 hp, n h0 hq, n h0 hr, n h0 hs⟩, ⟨h12, n h1 hp, n h1 hq, n h1 hr, n h1 hs⟩,
    ⟨n h2 hp, n h2 hq, n h2 hr, n h2 hs⟩, ⟨hpq, hpr, hps⟩, ⟨hqr, hqs⟩, hrs⟩

end helpers

/-- **Sliding the far end of a tube across an edge.** The tube `tube c₀ c₁ c₂ p q r` is glued to
the rest `R ∪ U` along `{p, q, r}`; `{q, r, s}` is the other triangle of `R` at the edge `{q, r}`.
The new vertices `cᵢ` (in `C`) are not vertices of `R`, and a triangle of `U` never contains both a
new vertex and a vertex of `W ⊇ {p, q, r, s}`. Then 2D moves replace the end `{p, q, r}` by
`{q, s, r}`, restoring `{p, q, r}` to `R` and removing `{q, r, s}`. -/
theorem tube_slide [Infinite V] {R U : Finset (Finset V)} {C W : Finset V} {c₀ c₁ c₂ p q r s : V}
    (h0 : c₀ ∈ C) (h1 : c₁ ∈ C) (h2 : c₂ ∈ C) (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂)
    (hp : p ∈ W) (hq : q ∈ W) (hr : r ∈ W) (hs : s ∈ W) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (hCW : ∀ c ∈ C, c ∉ W)
    (hCR : ∀ c ∈ C, c ∉ verts2 R) (hUC : ∀ t ∈ U, ∀ c ∈ C, c ∈ t → ∀ x ∈ W, x ∉ t)
    (he : ({q, r, s} : Finset V) ∈ R) (hR : ∀ t ∈ R, ({q, r} : Finset V) ⊆ t → t = {q, r, s})
    (hU : ∀ t ∈ U, ¬ ({q, r} : Finset V) ⊆ t) :
    EqvGen Move2 (R ∪ U ∪ tube c₀ c₁ c₂ p q r)
      (insert {p, q, r} (R.erase {q, r, s}) ∪ U ∪ tube c₀ c₁ c₂ q s r) := by
  set A := R.erase {q, r, s} ∪ U with hA
  obtain ⟨F, hF, hFo⟩ := exists_emb _ (nodup_3_4 h0 h1 h2 h01 h02 h12 hp hq hr hs hpq hpr hps hqr
    hqs hrs hCW) (verts2 A)
  have F0 : F 0 = c₀ := hF 0 (by simp)
  have F1 : F 1 = c₁ := hF 1 (by simp)
  have F2 : F 2 = c₂ := hF 2 (by simp)
  have F3 : F 3 = p := hF 3 (by simp)
  have F4 : F 4 = q := hF 4 (by simp)
  have F5 : F 5 = r := hF 5 (by simp)
  have F6 : F 6 = s := hF 6 (by simp)
  -- no triangle of `A` contains a new vertex together with a vertex of `W`
  have key : ∀ t ∈ A, ∀ c ∈ C, c ∈ t → ∀ x ∈ W, x ∉ t := by
    intro t ht c hc hct x hx hxt
    rcases mem_union.mp ht with ht | ht
    · exact hCR c hc (mem_verts2.mpr ⟨t, mem_of_mem_erase ht, hct⟩)
    · exact hUC t ht c hc hct x hx hxt
  have hC : Ctx A F {0, 1, 2, 3, 4, 5, 6}
      [(4, 5), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4),
        (2, 5), (2, 6)] := by
    refine ⟨fun n hn => hFo n ?_, ?_⟩
    · simp only [mem_insert, mem_singleton, not_or] at hn
      simp only [List.length_cons, List.length_nil]; omega
    · intro pr hpr t ht hsub
      have hsub' : ∀ {a b}, ({a, b} : Finset V) ⊆ t → a ∈ t ∧ b ∈ t := fun h =>
        ⟨h (by simp), h (by simp)⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [F4, F5] at hsub
        rcases mem_union.mp ht with ht | ht
        · exact (mem_erase.mp ht).1 (hR t (mem_of_mem_erase ht) hsub)
        · exact hU t ht hsub
      all_goals
        simp only [F0, F1, F2, F3, F4, F5, F6] at hsub
        obtain ⟨ha, hb⟩ := hsub' hsub
      · exact key t ht _ h0 ha _ hp hb
      · exact key t ht _ h0 ha _ hq hb
      · exact key t ht _ h0 ha _ hr hb
      · exact key t ht _ h0 ha _ hs hb
      · exact key t ht _ h1 ha _ hp hb
      · exact key t ht _ h1 ha _ hq hb
      · exact key t ht _ h1 ha _ hr hb
      · exact key t ht _ h1 ha _ hs hb
      · exact key t ht _ h2 ha _ hp hb
      · exact key t ht _ h2 ha _ hq hb
      · exact key t ht _ h2 ha _ hr hb
      · exact key t ht _ h2 ha _ hs hb
  have hD : Disj A F (insert {4, 5, 6} (tube 0 1 2 3 4 5)) := by
    intro t ht hA'
    have hmem : ∀ {a b c : ℕ}, ({a, b, c} : Finset ℕ) = t → F a ∈ t.map F ∧ F b ∈ t.map F ∧
        F c ∈ t.map F := by
      rintro a b c rfl; simp
    simp only [tube, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [map_tri, F4, F5, F6] at hA'
      rcases mem_union.mp hA' with h | h
      · exact (mem_erase.mp h).1 rfl
      · exact hU _ h (by simp [insert_subset_iff])
    · obtain ⟨ha, -, hb⟩ := hmem rfl; rw [F0] at ha; rw [F3] at hb
      exact key _ hA' _ h0 ha _ hp hb
    · obtain ⟨ha, hb, -⟩ := hmem rfl; rw [F1] at ha; rw [F3] at hb
      exact key _ hA' _ h1 ha _ hp hb
    · obtain ⟨ha, -, hb⟩ := hmem rfl; rw [F1] at ha; rw [F4] at hb
      exact key _ hA' _ h1 ha _ hq hb
    · obtain ⟨ha, hb, -⟩ := hmem rfl; rw [F2] at ha; rw [F4] at hb
      exact key _ hA' _ h2 ha _ hq hb
    · obtain ⟨ha, -, hb⟩ := hmem rfl; rw [F2] at ha; rw [F5] at hb
      exact key _ hA' _ h2 ha _ hr hb
    · obtain ⟨ha, hb, -⟩ := hmem rfl; rw [F0] at ha; rw [F5] at hb
      exact key _ hA' _ h0 ha _ hr hb
  have h := checkChain_sound hC _ hD chain_tslide
  rw [liftK_insert, liftK_insert, map_tri, map_tri, liftK_tube, liftK_tube, F0, F1, F2, F3, F4,
    F5, F6, hA, union_insert_of_mem he, union_insert_swap] at h
  exact h

/-! ## Walking the far end of a tube -/

/-- A **walk state**: the surface `L'` without its triangles `σ` and `{p, q, r}`, the rest `U` of a
tube system starting at `σ`, and a last tube from `{c₀, c₁, c₂}` ending at `{p, q, r}`. -/
def wst (L' U : Finset (Finset V)) (σ : Finset V) (c₀ c₁ c₂ p q r : V) : Finset (Finset V) :=
  (L'.erase σ).erase {p, q, r} ∪ U ∪ tube c₀ c₁ c₂ p q r

omit [DecidableEq V] in
lemma tri_rot [DecidableEq V] (a b c : V) : ({a, b, c} : Finset V) = {b, c, a} := by
  ext; simp only [mem_insert, mem_singleton]; tauto

lemma wst_rot (L' U : Finset (Finset V)) (σ : Finset V) (c₀ c₁ c₂ p q r : V) :
    wst L' U σ c₀ c₁ c₂ p q r = wst L' U σ c₁ c₂ c₀ q r p := by
  rw [wst, wst, tube_rot c₀ c₁ c₂ p q r, tri_rot p q r]

/-- The **conditions for walking**: `L'` is a surface containing `σ`; the vertices in `C` are new;
a triangle of `U` with a vertex in `C` has no vertex of `L'`, and the only vertices of `L'` in
triangles of `U` are those of `σ`. -/
structure WalkCtx (L' U : Finset (Finset V)) (σ C : Finset V) : Prop where
  surf : IsSurface L'
  mem : σ ∈ L'
  cw : ∀ c ∈ C, c ∉ verts2 L'
  uc : ∀ t ∈ U, ∀ c ∈ C, c ∈ t → ∀ x ∈ t, x ∉ verts2 L'
  ue : ∀ t ∈ U, ∀ x ∈ t, x ∈ verts2 L' → x ∈ σ

/-- **One step of the walk** across the edge `{q, r}` from `{p, q, r}` to `{q, r, s}`. -/
theorem walk_qr [Infinite V] {L' U : Finset (Finset V)} {σ C : Finset V} (W : WalkCtx L' U σ C)
    {c₀ c₁ c₂ p q r s : V} (h0 : c₀ ∈ C) (h1 : c₁ ∈ C) (h2 : c₂ ∈ C) (h01 : c₀ ≠ c₁)
    (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (hρ : ({p, q, r} : Finset V) ∈ L')
    (hρσ : ({p, q, r} : Finset V) ≠ σ) (hρ' : ({q, r, s} : Finset V) ∈ L')
    (hρ'σ : ({q, r, s} : Finset V) ≠ σ) (hps : p ≠ s) :
    EqvGen Move2 (wst L' U σ c₀ c₁ c₂ p q r) (wst L' U σ c₀ c₁ c₂ q s r) := by
  obtain ⟨hpq, hpr, hqr⟩ := tri_ne (W.surf.card _ hρ)
  obtain ⟨-, hqs, hrs⟩ := tri_ne (W.surf.card _ hρ')
  obtain ⟨hp, hq, hr⟩ := mem_verts2_of_mem hρ
  obtain ⟨-, -, hs⟩ := mem_verts2_of_mem hρ'
  have hne : ({p, q, r} : Finset V) ≠ {q, r, s} := by
    intro h
    have : p ∈ ({q, r, s} : Finset V) := h ▸ mem_insert_self _ _
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h | h
    exacts [hpq h, hpr h, hps h]
  have hrot : ({q, r, p} : Finset V) = {p, q, r} := (tri_rot p q r).symm
  have hedge := W.surf.tris_at_edge (hrot ▸ hρ) hρ' hps
  have hmem : ({p, q, r} : Finset V) ∈ L'.erase σ := mem_erase.mpr ⟨hρσ, hρ⟩
  have h := tube_slide (R := (L'.erase σ).erase {p, q, r}) (U := U) (W := verts2 L') h0 h1 h2 h01
    h02 h12 hp hq hr hs hpq hpr hps hqr hqs hrs W.cw
    (fun c hc hcR => W.cw c hc (verts2_mono ((erase_subset _ _).trans (erase_subset _ _)) hcR))
    (fun t ht c hc hct x hx hxt => W.uc t ht c hc hct x hxt hx)
    (mem_erase.mpr ⟨hne.symm, mem_erase.mpr ⟨hρ'σ, hρ'⟩⟩)
    (fun t ht hsub => by
      rcases hedge t (mem_of_mem_erase (mem_of_mem_erase ht)) hsub with h | h
      · exact absurd (h.trans hrot) (mem_erase.mp ht).1
      · exact h)
    (fun t ht hsub => by
      have hqσ := W.ue t ht q (hsub (by simp)) hq
      have hrσ := W.ue t ht r (hsub (by simp)) hr
      rcases hedge σ W.mem (insert_subset_iff.mpr ⟨hqσ, singleton_subset_iff.mpr hrσ⟩) with h | h
      · exact hρσ (hrot.symm.trans h.symm)
      · exact hρ'σ h.symm)
  rw [insert_erase_erase hmem hne,
    show ({q, r, s} : Finset V) = {q, s, r} from congrArg (insert q) (pair_comm r s)] at h
  exact h

/-- The three ways a triangle `ρ'` can be adjacent to `{p, q, r}`. -/
lemma adj_cases {M : Finset (Finset V)} (hT : IsTri2 M) {p q r : V} {ρ' : Finset V}
    (h : DAdj M {p, q, r} ρ') :
    ∃ z, (ρ' = {q, r, z} ∧ z ≠ p) ∨ (ρ' = {r, p, z} ∧ z ≠ q) ∨ (ρ' = {p, q, z} ∧ z ≠ r) := by
  obtain ⟨w, x, y, z, hs, rfl, hwz, hxy, hwx, hwy, hzx, hzy⟩ := h.split hT
  have hw : w ∈ ({p, q, r} : Finset V) := by rw [hs]; simp
  have hx : x ∈ ({p, q, r} : Finset V) := by rw [hs]; simp
  have hy : y ∈ ({p, q, r} : Finset V) := by rw [hs]; simp
  simp only [mem_insert, mem_singleton] at hw hx hy
  refine ⟨z, ?_⟩
  rcases hw with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hwx | exact absurd rfl hwy | exact absurd rfl hxy
    | exact Or.inl ⟨rfl, hwz.symm⟩ | exact Or.inl ⟨insert_comm _ _ _, hwz.symm⟩
    | exact Or.inr (Or.inl ⟨rfl, hwz.symm⟩) | exact Or.inr (Or.inl ⟨insert_comm _ _ _, hwz.symm⟩)
    | exact Or.inr (Or.inr ⟨rfl, hwz.symm⟩) | exact Or.inr (Or.inr ⟨insert_comm _ _ _, hwz.symm⟩)

/-- **One step of the walk** to any triangle `ρ' ≠ σ` adjacent to the current end. -/
theorem walk_step [Infinite V] {L' U : Finset (Finset V)} {σ C : Finset V} (W : WalkCtx L' U σ C)
    {c₀ c₁ c₂ p q r : V} (h0 : c₀ ∈ C) (h1 : c₁ ∈ C) (h2 : c₂ ∈ C) (h01 : c₀ ≠ c₁)
    (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂) (hρσ : ({p, q, r} : Finset V) ≠ σ) {ρ' : Finset V}
    (hadj : DAdj L' {p, q, r} ρ') (hρ'σ : ρ' ≠ σ) :
    ∃ p' q' r', ρ' = {p', q', r'} ∧
      EqvGen Move2 (wst L' U σ c₀ c₁ c₂ p q r) (wst L' U σ c₀ c₁ c₂ p' q' r') := by
  have hρ := hadj.1
  have hρ' := hadj.2.1
  have e3 : ∀ a b c : V, ({a, b, c} : Finset V) = {c, b, a} := fun a b c => by
    ext; simp only [mem_insert, mem_singleton]; tauto
  obtain ⟨z, ⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨rfl, hz⟩⟩ := adj_cases W.surf.card hadj
  · exact ⟨q, z, r, congrArg (insert q) (pair_comm r z),
      walk_qr W h0 h1 h2 h01 h02 h12 hρ hρσ hρ' hρ'σ hz.symm⟩
  · refine ⟨p, r, z, insert_comm _ _ _, ?_⟩
    rw [wst_rot L' U σ c₀ c₁ c₂ p q r, ← wst_rot L' U σ c₂ c₀ c₁ z p r,
      ← wst_rot L' U σ c₁ c₂ c₀ r z p]
    rw [tri_rot p q r] at hρ hρσ
    exact walk_qr W h1 h2 h0 h12 h01.symm h02.symm hρ hρσ hρ' hρ'σ hz.symm
  · refine ⟨z, q, p, e3 p q z, ?_⟩
    rw [wst_rot L' U σ c₀ c₁ c₂ p q r, wst_rot L' U σ c₁ c₂ c₀ q r p,
      ← wst_rot L' U σ c₂ c₀ c₁ p z q]
    rw [tri_rot p q r, tri_rot q r p] at hρ hρσ
    exact walk_qr W h2 h0 h1 h02.symm h12.symm h01 hρ hρσ hρ' hρ'σ hz.symm

/-- **The walk.** Along a dual path avoiding `σ`, the far end of the last tube moves from
`{p, q, r}` to the end of the path. -/
theorem walk [Infinite V] {L' U : Finset (Finset V)} {σ C : Finset V} (W : WalkCtx L' U σ C)
    {c₀ c₁ c₂ : V} (h0 : c₀ ∈ C) (h1 : c₁ ∈ C) (h2 : c₂ ∈ C) (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂)
    (h12 : c₁ ≠ c₂) {ρ ρ' : Finset V}
    (hpath : ReflTransGen (fun a b => DAdj L' a b ∧ a ≠ σ ∧ b ≠ σ) ρ ρ') {p q r : V}
    (hρ : ρ = {p, q, r}) :
    ∃ p' q' r', ρ' = {p', q', r'} ∧
      EqvGen Move2 (wst L' U σ c₀ c₁ c₂ p q r) (wst L' U σ c₀ c₁ c₂ p' q' r') := by
  induction hpath with
  | refl => exact ⟨p, q, r, hρ, EqvGen.refl _⟩
  | tail _ hbc ih =>
    obtain ⟨p', q', r', rfl, hE⟩ := ih
    obtain ⟨hadj, hbσ, hcσ⟩ := hbc
    obtain ⟨p'', q'', r'', hc, hE'⟩ := walk_step W h0 h1 h2 h01 h02 h12 hbσ hadj hcσ
    exact ⟨p'', q'', r'', hc, EqvGen.trans _ _ _ hE hE'⟩

/-! ## Closing the tube -/

set_option linter.unusedTactic false in
/-- Every triangle of a three-ring tube has a vertex among `3, …, 8`. -/
lemma finX_fresh (o₀ o₁ o₂ : ℕ) :
    ∀ t ∈ finX o₀ o₁ o₂, ∃ n ∈ t, n ∉ ({0, 1, 2, 9} : Finset ℕ) := by
  intro t ht
  simp only [finX, tube, mem_union, mem_insert, mem_singleton] at ht
  rcases ht with ((h | h | h | h | h | h) | (h | h | h | h | h | h)) | (h | h | h | h | h | h) <;>
    subst h <;>
    first
    | (refine ⟨3, ?_, ?_⟩ <;> (simp; done)) | (refine ⟨4, ?_, ?_⟩ <;> (simp; done))
    | (refine ⟨5, ?_, ?_⟩ <;> (simp; done)) | (refine ⟨6, ?_, ?_⟩ <;> (simp; done))
    | (refine ⟨7, ?_, ?_⟩ <;> (simp; done)) | (refine ⟨8, ?_, ?_⟩ <;> (simp; done))

/-- The relabelling `π` of a closing chain fixes `0, 1, 2` and sends the other vertices of the
piece `P` away from the labels `0, 1, 2, 9` of the surrounding surface. -/
def FinOK (P : Finset (Finset ℕ)) (π : ℕ ↪ ℕ) : Prop :=
  (π 0 = 0 ∧ π 1 = 1 ∧ π 2 = 2) ∧
    ∀ n ∈ verts2 P, n ∉ ({0, 1, 2} : Finset ℕ) → π n ∉ ({0, 1, 2, 9} : Finset ℕ)

lemma T9_mem012 : ({0, 1, 2} : Finset ℕ) ∈ T9 := by decide +kernel
lemma KB_mem012 : ({0, 1, 2} : Finset ℕ) ∈ KB := by decide +kernel

lemma fok_019 : FinOK T9 (tabE [0, 1, 2, 3, 4, 5, 6, 8, 7] 0 (by decide)) := by
  unfold FinOK; decide +kernel
lemma fok_190 : FinOK T9 (tabE [0, 1, 2, 6, 3, 5, 4, 8, 7] 0 (by decide)) := by
  unfold FinOK; decide +kernel
lemma fok_901 : FinOK T9 (tabE [0, 1, 2, 8, 4, 3, 7, 6, 5] 0 (by decide)) := by
  unfold FinOK; decide +kernel
lemma fok_091 : FinOK KB (tabE [0, 1, 2, 5, 4, 7, 3, 6, 8] 0 (by decide)) := by
  unfold FinOK; decide +kernel
lemma fok_109 : FinOK KB (tabE [0, 1, 2, 5, 4, 8, 3, 7, 6] 0 (by decide)) := by
  unfold FinOK; decide +kernel

/-- **Closing a tube at a neighbour of its start.** The tube system runs from `σ = {a₀, a₁, a₂}`
through new triangles `{b₀, b₁, b₂}` and `{c₀, c₁, c₂}` to `{p, q, r} = {a₀, a₁, w}`, a triangle
adjacent to `σ` along `{a₀, a₁}`. A checked closing chain turns it into the connected sum of `L'`
with the piece `P` at `σ`. -/
theorem final_gen [Infinite V] {L' : Finset (Finset V)} (hS : IsSurface L')
    {a₀ a₁ a₂ w b₀ b₁ b₂ c₀ c₁ c₂ p q r : V} (hσ : ({a₀, a₁, a₂} : Finset V) ∈ L')
    (he : ({a₀, a₁, w} : Finset V) ∈ L') (hw : w ≠ a₂) (hb₀ : b₀ ∉ verts2 L')
    (hb₁ : b₁ ∉ verts2 L') (hb₂ : b₂ ∉ verts2 L') (hc₀ : c₀ ∉ verts2 L') (hc₁ : c₁ ∉ verts2 L')
    (hc₂ : c₂ ∉ verts2 L') (hbc : [b₀, b₁, b₂, c₀, c₁, c₂].Nodup)
    (hpqr : ({p, q, r} : Finset V) = {a₀, a₁, w}) {P : Finset (Finset ℕ)} {π : ℕ ↪ ℕ}
    {o₀ o₁ o₂ : ℕ} {ms : List Mv}
    (hchain : checkChain {0, 1, 2, 9} [(0, 1)] (finX o₀ o₁ o₂) ms =
      some (insert {0, 1, 9} (liftK π (P.erase {0, 1, 2}))))
    (hF : ∀ F : ℕ → V, F 0 = a₀ → F 1 = a₁ → F 9 = w → F o₀ = p ∧ F o₁ = q ∧ F o₂ = r)
    (hP0 : ({0, 1, 2} : Finset ℕ) ∈ P) (hok : FinOK P π) :
    ∃ h, IsGlue L' {a₀, a₁, a₂} P {0, 1, 2} h ∧
      EqvGen Move2 (wst L' (tube a₀ a₁ a₂ b₀ b₁ b₂ ∪ tube b₀ b₁ b₂ c₀ c₁ c₂) {a₀, a₁, a₂} c₀ c₁ c₂
        p q r) (csum L' {a₀, a₁, a₂} P {0, 1, 2} h) := by
  obtain ⟨ha01, ha02, ha12⟩ := tri_ne (hS.card _ hσ)
  obtain ⟨-, hw0, hw1⟩ := tri_ne (hS.card _ he)
  obtain ⟨ha0, ha1, ha2⟩ := mem_verts2_of_mem hσ
  obtain ⟨-, -, hwv⟩ := mem_verts2_of_mem he
  have hnd : [a₀, a₁, a₂, b₀, b₁, b₂, c₀, c₁, c₂, w].Nodup := by
    have hperm : [a₀, a₁, a₂, b₀, b₁, b₂, c₀, c₁, c₂, w].Perm
        ([a₀, a₁, a₂, w] ++ [b₀, b₁, b₂, c₀, c₁, c₂]) :=
      (((List.perm_append_singleton w [b₀, b₁, b₂, c₀, c₁, c₂]).cons a₂).cons a₁).cons a₀
    refine hperm.nodup_iff.mpr (List.nodup_append.mpr ⟨?_, hbc, ?_⟩)
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨ha01, ha02, hw0⟩, ⟨ha12, hw1⟩, hw.symm⟩
    · intro x hx y hy hxy
      subst hxy
      have hxv : x ∈ verts2 L' := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> contradiction
  obtain ⟨F, hF', hFo⟩ := exists_emb _ hnd (verts2 L')
  have F0 : F 0 = a₀ := hF' 0 (by simp)
  have F1 : F 1 = a₁ := hF' 1 (by simp)
  have F2 : F 2 = a₂ := hF' 2 (by simp)
  have F3 : F 3 = b₀ := hF' 3 (by simp)
  have F4 : F 4 = b₁ := hF' 4 (by simp)
  have F5 : F 5 = b₂ := hF' 5 (by simp)
  have F6 : F 6 = c₀ := hF' 6 (by simp)
  have F7 : F 7 = c₁ := hF' 7 (by simp)
  have F8 : F 8 = c₂ := hF' 8 (by simp)
  have F9 : F 9 = w := hF' 9 (by simp)
  have hfr : ∀ n, n ∉ ({0, 1, 2, 9} : Finset ℕ) → F n ∉ verts2 L' := by
    intro n hn
    by_cases h10 : n < 10
    · interval_cases n
      all_goals first
        | (simp at hn; done)
        | (simp only [F3, F4, F5, F6, F7, F8]; assumption)
    · exact hFo n (by simp only [List.length_cons, List.length_nil]; omega)
  have hedge := hS.tris_at_edge hσ he hw.symm
  have hC : Ctx ((L'.erase {a₀, a₁, a₂}).erase {a₀, a₁, w}) F {0, 1, 2, 9} [(0, 1)] := by
    refine ⟨fun n hn hv =>
      hfr n hn (verts2_mono ((erase_subset _ _).trans (erase_subset _ _)) hv), ?_⟩
    intro pr hpr t ht hsub
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
    subst hpr
    simp only [F0, F1] at hsub
    rcases hedge t (mem_of_mem_erase (mem_of_mem_erase ht)) hsub with h | h
    · exact (mem_erase.mp (mem_of_mem_erase ht)).1 h
    · exact (mem_erase.mp ht).1 h
  have hD : Disj ((L'.erase {a₀, a₁, a₂}).erase {a₀, a₁, w}) F (finX o₀ o₁ o₂) := fun t ht => by
    obtain ⟨n, hn, hnB⟩ := finX_fresh o₀ o₁ o₂ t ht
    exact hC.map_notMem_of_fresh hn hnB
  have h := checkChain_sound hC ms hD hchain
  obtain ⟨Fp, Fq, Fr⟩ := hF F F0 F1 F9
  have hne : ({a₀, a₁, w} : Finset V) ≠ {a₀, a₁, a₂} := by
    intro h'
    have : w ∈ ({a₀, a₁, a₂} : Finset V) := by rw [← h']; simp
    simp only [mem_insert, mem_singleton] at this
    rcases this with h'' | h'' | h''
    exacts [hw0 h''.symm, hw1 h''.symm, hw h'']
  rw [finX, liftK_union, liftK_union, liftK_tube, liftK_tube, liftK_tube, liftK_insert, map_tri,
    ← liftK_trans, F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, Fp, Fq, Fr, union_insert,
    ← insert_union, insert_erase (mem_erase.mpr ⟨hne, he⟩)] at h
  refine ⟨π.trans F, ⟨hσ, hP0, ?_, fun n hn hn' => hfr _ (hok.2 n hn hn')⟩, ?_⟩
  · simp only [map_insert, map_singleton, Function.Embedding.trans_apply, hok.1.1, hok.1.2.1,
      hok.1.2.2, F0, F1, F2]
  · rw [wst, hpqr, union_assoc _ (tube a₀ a₁ a₂ b₀ b₁ b₂ ∪ tube b₀ b₁ b₂ c₀ c₁ c₂), csum]
    exact h

/-- **Closing a tube along any edge order.** As `final_gen`, for each of the six orders in which
the end `{p, q, r}` of the tube system can list the triangle `{a₀, a₁, w}`: the result is a
connected sum with the torus piece `T9` or with the Klein bottle piece `KB`. -/
theorem final_edge [Infinite V] {L' : Finset (Finset V)} (hS : IsSurface L')
    {a₀ a₁ a₂ w b₀ b₁ b₂ c₀ c₁ c₂ p q r : V} (hσ : ({a₀, a₁, a₂} : Finset V) ∈ L')
    (he : ({a₀, a₁, w} : Finset V) ∈ L') (hw : w ≠ a₂) (hb₀ : b₀ ∉ verts2 L')
    (hb₁ : b₁ ∉ verts2 L') (hb₂ : b₂ ∉ verts2 L') (hc₀ : c₀ ∉ verts2 L') (hc₁ : c₁ ∉ verts2 L')
    (hc₂ : c₂ ∉ verts2 L') (hbc : [b₀, b₁, b₂, c₀, c₁, c₂].Nodup)
    (hpqr : ({p, q, r} : Finset V) = {a₀, a₁, w}) :
    (∃ h, IsGlue L' {a₀, a₁, a₂} T9 {0, 1, 2} h ∧
      EqvGen Move2 (wst L' (tube a₀ a₁ a₂ b₀ b₁ b₂ ∪ tube b₀ b₁ b₂ c₀ c₁ c₂) {a₀, a₁, a₂} c₀ c₁ c₂
        p q r) (csum L' {a₀, a₁, a₂} T9 {0, 1, 2} h)) ∨
    (∃ h, IsGlue L' {a₀, a₁, a₂} KB {0, 1, 2} h ∧
      EqvGen Move2 (wst L' (tube a₀ a₁ a₂ b₀ b₁ b₂ ∪ tube b₀ b₁ b₂ c₀ c₁ c₂) {a₀, a₁, a₂} c₀ c₁ c₂
        p q r) (csum L' {a₀, a₁, a₂} KB {0, 1, 2} h)) := by
  have h3 : #({p, q, r} : Finset V) = 3 := by rw [hpqr]; exact hS.card _ he
  obtain ⟨hpq, hpr, hqr⟩ := tri_ne h3
  have hp : p ∈ ({a₀, a₁, w} : Finset V) := by rw [← hpqr]; simp
  have hq : q ∈ ({a₀, a₁, w} : Finset V) := by rw [← hpqr]; simp
  have hr : r ∈ ({a₀, a₁, w} : Finset V) := by rw [← hpqr]; simp
  simp only [mem_insert, mem_singleton] at hp hq hr
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hpq | exact absurd rfl hpr | exact absurd rfl hqr
    | exact Or.inl (final_gen hS hσ he hw hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hbc hpqr chain_final_019
        (fun _ h0 h1 h9 => ⟨h0, h1, h9⟩) T9_mem012 fok_019)
    | exact Or.inl (final_gen hS hσ he hw hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hbc hpqr chain_final_190
        (fun _ h0 h1 h9 => ⟨h1, h9, h0⟩) T9_mem012 fok_190)
    | exact Or.inl (final_gen hS hσ he hw hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hbc hpqr chain_final_901
        (fun _ h0 h1 h9 => ⟨h9, h0, h1⟩) T9_mem012 fok_901)
    | exact Or.inr (final_gen hS hσ he hw hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hbc hpqr chain_final_091
        (fun _ h0 h1 h9 => ⟨h0, h9, h1⟩) KB_mem012 fok_091)
    | exact Or.inr (final_gen hS hσ he hw hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hbc hpqr chain_final_109
        (fun _ h0 h1 h9 => ⟨h1, h0, h9⟩) KB_mem012 fok_109)
    | exact Or.inr (final_gen hS hσ he hw hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hbc hpqr chain_final_910
        (fun _ h0 h1 h9 => ⟨h9, h1, h0⟩) KB_mem012 fok_091)

/-! ## The Klein bottle piece as two projective planes -/

lemma KB_erase : KB.erase {0, 1, 2} =
    (P6.erase {0, 1, 2}).erase {1, 3, 4} ∪ liftK e134 (P6.erase {0, 1, 2}) := by decide +kernel
lemma P6_mem012 : ({0, 1, 2} : Finset ℕ) ∈ P6 := by decide +kernel
lemma P6_mem134 : ({1, 3, 4} : Finset ℕ) ∈ P6.erase {0, 1, 2} := by decide +kernel
lemma verts2_P6_KB : ∀ n ∈ verts2 P6, n ∈ verts2 KB := by decide +kernel
lemma three_mem_KB : 3 ∈ verts2 KB := by decide +kernel
lemma e134_KB : ∀ n ∈ verts2 P6, n ∉ ({0, 1, 2} : Finset ℕ) →
    e134 n ∈ verts2 KB ∧ e134 n ∉ ({0, 1, 2} : Finset ℕ) ∧ e134 n ∉ verts2 P6 := by
  decide +kernel
lemma e134_012 : e134 0 = 1 ∧ e134 1 = 3 ∧ e134 2 = 4 := by decide +kernel

/-- **A Klein bottle summand is two projective-plane summands.** Gluing `KB` at `σ` is the same
complex as gluing `P6` at `σ` and then a second `P6` at the image of its triangle `134`; both
gluings are valid. -/
theorem twist_of_KB {L' : Finset (Finset V)} {σ : Finset V} {h : ℕ ↪ V}
    (hg : IsGlue L' σ KB {0, 1, 2} h) :
    IsGlue L' σ P6 {0, 1, 2} h ∧
      IsGlue (csum L' σ P6 {0, 1, 2} h) (({1, 3, 4} : Finset ℕ).map h) P6 {0, 1, 2}
        (e134.trans h) ∧
      csum L' σ KB {0, 1, 2} h =
        csum (csum L' σ P6 {0, 1, 2} h) (({1, 3, 4} : Finset ℕ).map h) P6 {0, 1, 2}
          (e134.trans h) := by
  have h3 : h 3 ∉ verts2 L' := hg.fresh 3 three_mem_KB (by decide)
  have ht : (({1, 3, 4} : Finset ℕ).map h) ∉ L'.erase σ := fun H =>
    h3 (mem_verts2.mpr ⟨_, mem_of_mem_erase H, mem_map_of_mem h (by simp)⟩)
  refine ⟨⟨hg.mem, P6_mem012, hg.map, fun n hn hn' => hg.fresh n (verts2_P6_KB n hn) hn'⟩,
    ⟨mem_union_right _ (map_mem_liftK.mpr P6_mem134), P6_mem012, ?_, ?_⟩, ?_⟩
  · simp only [map_insert, map_singleton, Function.Embedding.trans_apply, e134_012]
  · intro n hn hn'
    obtain ⟨hK, h012, hP⟩ := e134_KB n hn hn'
    rw [Function.Embedding.trans_apply, csum, verts2_union, mem_union, not_or, verts2_liftK,
      mem_map']
    exact ⟨fun H => hg.fresh _ hK h012 (verts2_mono (erase_subset _ _) H),
      fun H => hP (verts2_mono (erase_subset _ _) H)⟩
  · rw [csum_csum ht, csum, KB_erase]

/-! ## Closing the tube next to its start -/

/-- **Closing at an adjacent triangle.** If the end `{p, q, r}` of the tube system is a triangle of
`L'` other than `σ = {a₀, a₁, a₂}` that contains `a₀` and `a₁`, the tube system closes up into a
connected sum with `T9` or `KB` at `σ`. -/
theorem close_at [Infinite V] {L' : Finset (Finset V)} (hS : IsSurface L')
    {a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ p q r : V} (hσ : ({a₀, a₁, a₂} : Finset V) ∈ L')
    (he : ({p, q, r} : Finset V) ∈ L') (hne : ({p, q, r} : Finset V) ≠ {a₀, a₁, a₂})
    (h0 : a₀ ∈ ({p, q, r} : Finset V)) (h1 : a₁ ∈ ({p, q, r} : Finset V))
    (hb₀ : b₀ ∉ verts2 L') (hb₁ : b₁ ∉ verts2 L') (hb₂ : b₂ ∉ verts2 L') (hc₀ : c₀ ∉ verts2 L')
    (hc₁ : c₁ ∉ verts2 L') (hc₂ : c₂ ∉ verts2 L') (hbc : [b₀, b₁, b₂, c₀, c₁, c₂].Nodup) :
    (∃ h, IsGlue L' {a₀, a₁, a₂} T9 {0, 1, 2} h ∧
      EqvGen Move2 (wst L' (tube a₀ a₁ a₂ b₀ b₁ b₂ ∪ tube b₀ b₁ b₂ c₀ c₁ c₂) {a₀, a₁, a₂} c₀ c₁ c₂
        p q r) (csum L' {a₀, a₁, a₂} T9 {0, 1, 2} h)) ∨
    (∃ h, IsGlue L' {a₀, a₁, a₂} KB {0, 1, 2} h ∧
      EqvGen Move2 (wst L' (tube a₀ a₁ a₂ b₀ b₁ b₂ ∪ tube b₀ b₁ b₂ c₀ c₁ c₂) {a₀, a₁, a₂} c₀ c₁ c₂
        p q r) (csum L' {a₀, a₁, a₂} KB {0, 1, 2} h)) := by
  obtain ⟨ha01, -, -⟩ := tri_ne (hS.card _ hσ)
  obtain ⟨w, -, -, hpqr⟩ := tri_of_two (hS.card _ he) ha01 h0 h1
  have hpqr' : ({p, q, r} : Finset V) = {a₀, a₁, w} := by
    rw [hpqr]; ext; simp only [mem_insert, mem_singleton]; tauto
  have hw : w ≠ a₂ := by
    rintro rfl; apply hne; rw [hpqr']
  exact final_edge hS hσ (by rw [← hpqr']; exact he) hw hb₀ hb₁ hb₂ hc₀ hc₁ hc₂ hbc hpqr'

/-- `L` is related by moves to a connected sum `L' # T9` or `L' # KB` at some triangle `σ` of a
closed surface `L'` with Euler characteristic larger by two: **`L` has a handle**. -/
def HandleOf (L : Finset (Finset V)) : Prop :=
  ∃ (L' : Finset (Finset V)) (σ : Finset V) (h : ℕ ↪ V), IsSurface L' ∧
    euler2 L' = euler2 L + 2 ∧
    ((IsGlue L' σ T9 {0, 1, 2} h ∧ EqvGen Move2 L (csum L' σ T9 {0, 1, 2} h)) ∨
      (IsGlue L' σ KB {0, 1, 2} h ∧ EqvGen Move2 L (csum L' σ KB {0, 1, 2} h)))

lemma handleOf_of {L L' X : Finset (Finset V)} {σ : Finset V} (hS : IsSurface L')
    (hχ : euler2 L' = euler2 L + 2) (hE : EqvGen Move2 L X)
    (hR : (∃ h, IsGlue L' σ T9 {0, 1, 2} h ∧ EqvGen Move2 X (csum L' σ T9 {0, 1, 2} h)) ∨
      (∃ h, IsGlue L' σ KB {0, 1, 2} h ∧ EqvGen Move2 X (csum L' σ KB {0, 1, 2} h))) :
    HandleOf L := by
  rcases hR with ⟨h, hg, hX⟩ | ⟨h, hg, hX⟩
  · exact ⟨L', σ, h, hS, hχ, Or.inl ⟨hg, EqvGen.trans _ _ _ hE hX⟩⟩
  · exact ⟨L', σ, h, hS, hχ, Or.inr ⟨hg, EqvGen.trans _ _ _ hE hX⟩⟩

/-- An edge `ab` of a template `K` that lies in two of its triangles lies in no triangle of the
rest `A` of the surface `A ∪ liftK g K`. -/
lemma safe_of_edge {K : Finset (Finset ℕ)} {A : Finset (Finset V)} {g : ℕ ↪ V}
    (hS : IsSurface (A ∪ liftK g K)) (hd : Disjoint A (liftK g K)) {a b x y : ℕ}
    (hx : ({a, b, x} : Finset ℕ) ∈ K) (hy : ({a, b, y} : Finset ℕ) ∈ K) (hxy : x ≠ y) :
    ∀ t ∈ A, ¬({g a, g b} : Finset V) ⊆ t := by
  have hx' : ({g a, g b, g x} : Finset V) ∈ A ∪ liftK g K :=
    mem_union_right _ (by rw [← map_tri]; exact map_mem_liftK.mpr hx)
  have hy' : ({g a, g b, g y} : Finset V) ∈ A ∪ liftK g K :=
    mem_union_right _ (by rw [← map_tri]; exact map_mem_liftK.mpr hy)
  intro t ht hsub
  rcases hS.tris_at_edge hx' hy' (g.injective.ne hxy) t (mem_union_left _ ht) hsub with rfl | rfl
  · exact disjoint_left.mp hd ht (by rw [← map_tri]; exact map_mem_liftK.mpr hx)
  · exact disjoint_left.mp hd ht (by rw [← map_tri]; exact map_mem_liftK.mpr hy)

lemma erase_erase_pair {A : Finset (Finset V)} {s t : Finset V} (hs : s ∉ A)
    (ht : t ∉ A) : ((A ∪ {s, t}).erase s).erase t = A := by
  ext x
  simp only [mem_erase, mem_union, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hxt, hxs, hx | hx | hx⟩
    exacts [hx, absurd hx hxs, absurd hx hxt]
  · intro hx
    exact ⟨fun h => ht (h ▸ hx), fun h => hs (h ▸ hx), Or.inl hx⟩

/-- The first two tubes of the layered tube, from `012` through `678` to `9 10 11`. -/
def U₀ : Finset (Finset ℕ) := tube 0 1 2 6 7 8 ∪ tube 6 7 8 9 10 11

lemma U₀_c : ∀ t ∈ U₀, ∀ c ∈ ({9, 10, 11} : Finset ℕ), c ∈ t → ∀ x ∈ t, 6 ≤ x := by
  decide +kernel
lemma U₀_e : ∀ t ∈ U₀, ∀ x ∈ t, 6 ≤ x ∨ x ∈ ({0, 1, 2} : Finset ℕ) := by decide +kernel

/-- **A two-sided cut gives a handle.** After a two-sided cut along a 3-cycle, the tube is
lengthened by two layers, its far end walks along a dual path to a neighbour of its start, and the
closing chain turns the result into a connected sum of the cut surface with `T9` or `KB`. -/
theorem handle_of_cut [Infinite V] {L A : Finset (Finset V)} {g : ℕ ↪ V} (hS : IsSurface L)
    (hc : CutTo L cutTube cutEnds [(0, 4), (1, 5), (2, 3)] 2 A g) : HandleOf L := by
  have hK₀ : IsSurface (A ∪ liftK g cutTube) := (isSurface_iff_of_eqvGen hc.eqv).mp hS
  -- two more layers
  have hC : Ctx A g {0, 1, 2, 3, 4, 5}
      [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)] := by
    refine ⟨fun n hn => hc.fresh n (by simp only [mem_insert, mem_singleton] at hn; omega), ?_⟩
    intro pr hpr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact safe_of_edge hK₀ hc.disjX (x := 1) (y := 5) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact hc.safe _ (by simp)
    · exact safe_of_edge hK₀ hc.disjX (x := 2) (y := 3) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 0) (y := 4) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 3) (y := 2) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact hc.safe _ (by simp)
    · exact hc.safe _ (by simp)
    · exact safe_of_edge hK₀ hc.disjX (x := 1) (y := 5) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 4) (y := 0) (by decide +kernel) (by decide +kernel)
        (by decide)
  have hD : Disj A g (tube 0 1 2 3 4 5) := fun t ht hA =>
    disjoint_left.mp hc.disjX hA (map_mem_liftK.mpr ht)
  have hlay := checkChain_sound hC _ hD chain_layer
  have h0 := hc.eqv
  rw [cutTube_eq] at h0
  -- the cut surface and the walk
  have hL'v : ∀ n, 6 ≤ n → g n ∉ verts2 (A ∪ liftK g cutEnds) := by
    intro n hn
    rw [verts2_union, mem_union, not_or, verts2_liftK, mem_map', verts2_cutEnds]
    exact ⟨hc.fresh n hn, by simp only [mem_insert, mem_singleton]; omega⟩
  have hends : liftK g cutEnds = {{g 0, g 1, g 2}, {g 3, g 4, g 5}} := by
    simp only [cutEnds, liftK, image_insert, image_singleton, map_insert, map_singleton]
  have hσA : ({g 0, g 1, g 2} : Finset V) ∉ A := fun h =>
    disjoint_left.mp hc.disjY h (by rw [hends]; simp)
  have hσ'A : ({g 3, g 4, g 5} : Finset V) ∉ A := fun h =>
    disjoint_left.mp hc.disjY h (by rw [hends]; simp)
  have hσL : ({g 0, g 1, g 2} : Finset V) ∈ A ∪ liftK g cutEnds :=
    mem_union_right _ (by rw [hends]; simp)
  have hσ'L : ({g 3, g 4, g 5} : Finset V) ∈ A ∪ liftK g cutEnds :=
    mem_union_right _ (by rw [hends]; simp)
  have hA : ((A ∪ liftK g cutEnds).erase {g 0, g 1, g 2}).erase {g 3, g 4, g 5} = A := by
    rw [hends]; exact erase_erase_pair hσA hσ'A
  have hU : liftK g U₀ =
      tube (g 0) (g 1) (g 2) (g 6) (g 7) (g 8) ∪ tube (g 6) (g 7) (g 8) (g 9) (g 10) (g 11) := by
    rw [U₀, liftK_union, liftK_tube, liftK_tube]
  have hstart : A ∪ liftK g (tube 0 1 2 6 7 8 ∪ tube 6 7 8 9 10 11 ∪ tube 9 10 11 3 4 5) =
      wst (A ∪ liftK g cutEnds) (liftK g U₀) {g 0, g 1, g 2} (g 9) (g 10) (g 11)
        (g 3) (g 4) (g 5) := by
    rw [wst, hA, hU]
    simp only [liftK_union, liftK_tube, union_assoc]
  rw [hstart] at hlay
  have W : WalkCtx (A ∪ liftK g cutEnds) (liftK g U₀) {g 0, g 1, g 2}
      (({9, 10, 11} : Finset ℕ).map g) := by
    refine ⟨hc.surf, hσL, ?_, ?_, ?_⟩
    · intro c hc'
      obtain ⟨n, hn, rfl⟩ := mem_map.mp hc'
      exact hL'v n (by simp only [mem_insert, mem_singleton] at hn; omega)
    · intro t ht c hc' hct x hx
      obtain ⟨t₀, ht₀, rfl⟩ := mem_liftK.mp ht
      obtain ⟨c₀, hc₀, rfl⟩ := mem_map.mp hc'
      obtain ⟨x₀, hx₀, rfl⟩ := mem_map.mp hx
      exact hL'v x₀ (U₀_c t₀ ht₀ c₀ hc₀ ((mem_map' g).mp hct) x₀ hx₀)
    · intro t ht x hx hxv
      obtain ⟨t₀, ht₀, rfl⟩ := mem_liftK.mp ht
      obtain ⟨x₀, hx₀, rfl⟩ := mem_map.mp hx
      rcases U₀_e t₀ ht₀ x₀ hx₀ with h | h
      · exact absurd hxv (hL'v x₀ h)
      · simp only [mem_insert, mem_singleton] at h
        rcases h with rfl | rfl | rfl <;> simp
  have hC9 : ∀ n ∈ ({9, 10, 11} : Finset ℕ), g n ∈ (({9, 10, 11} : Finset ℕ).map g) :=
    fun n hn => mem_map_of_mem g hn
  have hσσ' : ({g 3, g 4, g 5} : Finset V) ≠ {g 0, g 1, g 2} := by
    intro h
    have : g 3 ∈ ({g 0, g 1, g 2} : Finset V) := by rw [← h]; simp
    revert this
    simp [g.injective.eq_iff]
  obtain ⟨e, hadj, hpath⟩ := hc.surf.exists_path_avoid hσL hσ'L hσσ'
  obtain ⟨p', q', r', rfl, hwalk⟩ := walk W (hC9 9 (by simp)) (hC9 10 (by simp))
    (hC9 11 (by simp)) (g.injective.ne (by decide)) (g.injective.ne (by decide))
    (g.injective.ne (by decide)) hpath (p := g 3) (q := g 4) (r := g 5) rfl
  have hE : EqvGen Move2 L (wst (A ∪ liftK g cutEnds)
      (tube (g 0) (g 1) (g 2) (g 6) (g 7) (g 8) ∪ tube (g 6) (g 7) (g 8) (g 9) (g 10) (g 11))
      {g 0, g 1, g 2} (g 9) (g 10) (g 11) p' q' r') := by
    rw [← hU]; exact EqvGen.trans _ _ _ h0 (EqvGen.trans _ _ _ hlay hwalk)
  obtain ⟨he, -, hne, x, y, hxy, hxe, hye, hxσ, hyσ⟩ := hadj
  have rot0 : g 0 ∈ ({p', q', r'} : Finset V) → g 1 ∈ ({p', q', r'} : Finset V) →
      HandleOf L := fun h0 h1 =>
    handleOf_of hc.surf hc.euler hE (close_at hc.surf hσL he hne h0 h1 (hL'v 6 (by norm_num))
      (hL'v 7 (by norm_num)) (hL'v 8 (by norm_num)) (hL'v 9 (by norm_num))
      (hL'v 10 (by norm_num)) (hL'v 11 (by norm_num))
      (List.Nodup.map g.injective (by decide : [6, 7, 8, 9, 10, 11].Nodup)))
  have rot1 : g 1 ∈ ({p', q', r'} : Finset V) → g 2 ∈ ({p', q', r'} : Finset V) →
      HandleOf L := by
    intro h1 h2
    have hE' := hE
    rw [wst_rot _ _ _ (g 9) (g 10) (g 11) p' q' r', tube_rot (g 0) (g 1) (g 2) (g 6) (g 7) (g 8),
      tube_rot (g 6) (g 7) (g 8) (g 9) (g 10) (g 11), tri_rot (g 0) (g 1) (g 2)] at hE'
    rw [tri_rot p' q' r'] at he hne h1 h2
    rw [tri_rot (g 0) (g 1) (g 2)] at hσL hne
    exact handleOf_of hc.surf hc.euler hE' (close_at hc.surf hσL he hne h1 h2
      (hL'v 7 (by norm_num)) (hL'v 8 (by norm_num)) (hL'v 6 (by norm_num))
      (hL'v 10 (by norm_num)) (hL'v 11 (by norm_num)) (hL'v 9 (by norm_num))
      (List.Nodup.map g.injective (by decide : [7, 8, 6, 10, 11, 9].Nodup)))
  have rot2 : g 2 ∈ ({p', q', r'} : Finset V) → g 0 ∈ ({p', q', r'} : Finset V) →
      HandleOf L := by
    intro h2 h0
    have hE' := hE
    rw [wst_rot _ _ _ (g 9) (g 10) (g 11) p' q' r', wst_rot _ _ _ (g 10) (g 11) (g 9) q' r' p',
      tube_rot (g 0) (g 1) (g 2) (g 6) (g 7) (g 8), tube_rot (g 1) (g 2) (g 0) (g 7) (g 8) (g 6),
      tube_rot (g 6) (g 7) (g 8) (g 9) (g 10) (g 11),
      tube_rot (g 7) (g 8) (g 6) (g 10) (g 11) (g 9), tri_rot (g 0) (g 1) (g 2),
      tri_rot (g 1) (g 2) (g 0)] at hE'
    rw [tri_rot p' q' r', tri_rot q' r' p'] at he hne h2 h0
    rw [tri_rot (g 0) (g 1) (g 2), tri_rot (g 1) (g 2) (g 0)] at hσL hne
    exact handleOf_of hc.surf hc.euler hE' (close_at hc.surf hσL he hne h2 h0
      (hL'v 8 (by norm_num)) (hL'v 6 (by norm_num)) (hL'v 7 (by norm_num))
      (hL'v 11 (by norm_num)) (hL'v 9 (by norm_num)) (hL'v 10 (by norm_num))
      (List.Nodup.map g.injective (by decide : [8, 6, 7, 11, 9, 10].Nodup)))
  simp only [mem_insert, mem_singleton] at hxσ hyσ
  rcases hxσ with rfl | rfl | rfl <;> rcases hyσ with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact rot0 hxe hye
  · exact rot2 hye hxe
  · exact rot0 hye hxe
  · exact absurd rfl hxy
  · exact rot1 hxe hye
  · exact rot2 hxe hye
  · exact rot1 hye hxe
  · exact absurd rfl hxy

/-! ## A one-sided cut gives a crosscap -/

lemma cc_mem : ({3, 2, 0} : Finset ℕ) ∈ cutCap := by decide +kernel
lemma cc_verts : ∀ n ∈ verts2 cutCap, n < 6 := by decide +kernel
lemma cc_e : ∀ n ∈ verts2 P6, n ∉ ({0, 1, 2} : Finset ℕ) →
    6 ≤ tabE [3, 2, 0] 3 (by decide) n := by decide +kernel
lemma cc_012 : tabE [3, 2, 0] 3 (by decide) 0 = 3 ∧ tabE [3, 2, 0] 3 (by decide) 1 = 2 ∧
    tabE [3, 2, 0] 3 (by decide) 2 = 0 := by decide +kernel

/-- `L` is related by moves to a connected sum `L' # P6` at some triangle `σ` of a closed surface
`L'` with Euler characteristic larger by one: **`L` has a crosscap**. -/
def CrosscapOf (L : Finset (Finset V)) : Prop :=
  ∃ (L' : Finset (Finset V)) (σ : Finset V) (h : ℕ ↪ V), IsSurface L' ∧
    euler2 L' = euler2 L + 1 ∧ IsGlue L' σ P6 {0, 1, 2} h ∧
    EqvGen Move2 L (csum L' σ P6 {0, 1, 2} h)

/-- **A one-sided cut gives a crosscap.** After a one-sided cut along a 3-cycle, the checked
crosscap chain turns the Möbius band into a projective-plane piece `P6` glued to the capped
surface. -/
theorem crosscap_of_cut [Infinite V] {L A : Finset (Finset V)} {g : ℕ ↪ V} (hS : IsSurface L)
    (hc : CutTo L cutBand cutCap [(3, 2), (3, 1)] 1 A g) : CrosscapOf L := by
  have hK₀ : IsSurface (A ∪ liftK g cutBand) := (isSurface_iff_of_eqvGen hc.eqv).mp hS
  have hC : Ctx A g {0, 1, 2, 3, 4, 5}
      [(0, 3), (0, 4), (0, 5), (1, 4), (4, 5), (2, 5), (3, 2), (3, 1)] := by
    refine ⟨fun n hn => hc.fresh n (by simp only [mem_insert, mem_singleton] at hn; omega), ?_⟩
    intro pr hpr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
    rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact safe_of_edge hK₀ hc.disjX (x := 4) (y := 5) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 3) (y := 1) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 3) (y := 2) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 0) (y := 5) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 1) (y := 2) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact safe_of_edge hK₀ hc.disjX (x := 0) (y := 4) (by decide +kernel) (by decide +kernel)
        (by decide)
    · exact hc.safe _ (by simp)
    · exact hc.safe _ (by simp)
  have hD : Disj A g cutBand := fun t ht hA =>
    disjoint_left.mp hc.disjX hA (map_mem_liftK.mpr ht)
  have hcc := checkChain_sound hC _ hD chain_cc
  have hσA : ({3, 2, 0} : Finset ℕ).map g ∉ A := fun h =>
    disjoint_left.mp hc.disjY h (map_mem_liftK.mpr cc_mem)
  rw [liftK_union, ← liftK_trans, ← union_assoc, liftK_erase,
    ← union_erase_of_notMem hσA] at hcc
  have hL'v : ∀ n, 6 ≤ n → g n ∉ verts2 (A ∪ liftK g cutCap) := by
    intro n hn
    rw [verts2_union, mem_union, not_or, verts2_liftK, mem_map']
    exact ⟨hc.fresh n hn, fun h => by have := cc_verts n h; omega⟩
  refine ⟨A ∪ liftK g cutCap, ({3, 2, 0} : Finset ℕ).map g,
    (tabE [3, 2, 0] 3 (by decide)).trans g, hc.surf, hc.euler,
    ⟨mem_union_right _ (map_mem_liftK.mpr cc_mem), P6_mem012, ?_, ?_⟩,
    EqvGen.trans _ _ _ hc.eqv hcc⟩
  · simp only [map_insert, map_singleton, Function.Embedding.trans_apply, cc_012]
  · intro n hn hn'
    exact hL'v _ (cc_e n hn hn')

end Lightlike.Surfaces
