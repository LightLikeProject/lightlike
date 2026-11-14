module

public import Lightlike.PonzanoRegge.GaugeFixed

/-!
# Changing the gauge set: exact invariance under triangle exchanges

The gauge-fixed amplitude `amplitudeGF K T cut` puts spin `0` on the gauge edges `T`. Freidel and
Louapre show that, for a maximal tree, the result does not depend on the choice of tree. This file
proves the exact version of that statement that holds for **every** complex and **every** cutoff:

* `amplitudeGF_exchange`: let `uvw` be a triangle of `K` whose edges `uv` and `vw` are gauge edges
  and `uw` is not. Exchanging `uv` for `uw` does not change the amplitude. The reason is the
  triangle inequality: in both sums, two edges of `uvw` carry spin `0`, which forces spin `0` on the
  third, so both sums run over the same colourings.
* `IsMaxTree.exchange`: such an exchange turns a maximal tree into a maximal tree.
* `TreeExchange`, `amplitudeGF_eqvGen_exchange`, `isMaxTree_iff_of_eqvGen_exchange`: the amplitude
  is the same for all gauge sets connected by a chain of exchanges, and maximal trees stay maximal
  along the chain.

**What this does not show.** Two maximal trees need not be connected by triangle exchanges: an
exchange only adds the boundary of a triangle to the cycles that the non-tree edges close in the
tree, so on a complex with non-contractible loops some pairs of trees are not connected. For those
pairs the amplitude with finite cutoffs does depend on the tree:
`Lightlike/Tests/TreeDependence.lean` proves this for a ring of three tetrahedra (amplitudes `-7`
and `-15`). Further numerical evidence (exact arithmetic, `scripts/pr_tree_check.py`): on a solid
torus triangulated as a ring of three prisms, all trees connected to a given one by exchanges give
the same amplitude, while other trees give different values (`-15, -31, -63, -127` with cutoff ½).
On a 6-vertex triangulation of the 3-sphere, all 864 maximal trees are connected by exchanges, and
all give the amplitude `1`.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- **The weight vanishes when a triangle violates the triangle inequality**: if a triangle
`pqr` of `K` has spin `0` on `pr` and `qr` but not on `pq`. -/
lemma weight_eq_zero_of_tri {K : Complex3 V} {col : Colouring V} {p q r : V} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hτ : {p, q, r} ∈ K.tris) (h1 : col {p, r} = 0)
    (h2 : col {q, r} = 0) (h3 : col {q, p} ≠ 0) : weight K col = 0 := by
  obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_tris.mp hτ
  have hcard : #t = 4 := K.card_eq t ht
  obtain ⟨z, hz, hzn⟩ : ∃ z ∈ t, z ∉ ({p, q, r} : Finset V) :=
    exists_mem_notMem_of_card_lt_card (by rw [hcard, card_three hpq hpr hqr]; norm_num)
  simp only [mem_insert, mem_singleton, not_or] at hzn
  obtain ⟨hzp, hzq, hzr⟩ := hzn
  have hp : p ∈ t := hsub (by simp)
  have hq : q ∈ t := hsub (by simp)
  have hr : r ∈ t := hsub (by simp)
  rw [weight, prod_eq_zero ht, mul_zero]
  rw [tetW_eq_tetAmp col hcard (p := ![z, q, p, r])
    (injective_vec4 hzq hzp hzr hpq.symm hqr hpr) (by intro i; fin_cases i <;> simp [hz, hp, hq, hr]),
    tetAmp_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  exact sixJSym_vanishes_beyond_range (by rw [h1, h2]; omega)

/-- Summing over the spins of `insert a S` collapses to `S` when every nonzero spin on `a` gives
`0`. -/
lemma sum_pi_insert_collapse {S : Finset (Finset V)} {a : Finset V} (ha : a ∉ S)
    (cut : Finset V → ℕ) (F : Colouring V → ℝ)
    (hF : ∀ σ ∈ S.pi (fun e => range (cut e + 1)), ∀ x, x ≠ 0 →
      F (Function.update (extS S σ) a x) = 0) :
    ∑ σ ∈ (insert a S).pi (fun e => range (cut e + 1)), F (extS (insert a S) σ) =
      ∑ σ ∈ S.pi (fun e => range (cut e + 1)), F (extS S σ) := by
  rw [sum_pi_insert ha]
  refine sum_congr rfl fun σ hσ => ?_
  rw [sum_eq_single 0 (fun x _ hx => hF σ hσ x hx) (fun h => absurd (by simp) h),
    Function.update_eq_self_iff.mpr (extS_of_not_mem ha).symm]

/-- **Triangle exchange of a gauge edge.** If `uvw` is a triangle of `K`, `uv` and `vw` are gauge
edges and `uw` is not, then replacing `uv` by `uw` in the gauge set leaves the gauge-fixed
amplitude unchanged, for every cutoff. -/
theorem amplitudeGF_exchange (K : Complex3 V) {T : Finset (Finset V)} (hT : T ⊆ K.edges)
    {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) (hτ : {u, v, w} ∈ K.tris)
    (he : {u, v} ∈ T) (hg : {v, w} ∈ T) (hf : {u, w} ∉ T) (cut : Finset V → ℕ) :
    amplitudeGF K (insert {u, w} (T.erase {u, v})) cut = amplitudeGF K T cut := by
  obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_tris.mp hτ
  have hfK : ({u, w} : Finset V) ∈ K.edges :=
    Complex3.mem_edges.mpr ⟨t, ht, (by small_subset : ({u, w} : Finset V) ⊆ {u, v, w}).trans hsub,
      card_pair huw⟩
  have hef : ({u, v} : Finset V) ≠ {u, w} := fun h => hvw (by
    have : v ∈ ({u, w} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact absurd h'.symm huv
    · exact h')
  have hgf : ({v, w} : Finset V) ≠ {u, w} := fun h => huv (by
    have : u ∈ ({v, w} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h'
    · exact absurd h' huw)
  have hge : ({v, w} : Finset V) ≠ {u, v} := fun h => huw (by
    have : w ∈ ({u, v} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h'.symm
    · exact absurd h'.symm hvw)
  set S := K.edges \ insert {u, w} T with hS
  have hfS : ({u, w} : Finset V) ∉ S := by simp [hS]
  have heS : ({u, v} : Finset V) ∉ S := by simp [hS, he]
  have hgS : ({v, w} : Finset V) ∉ S := by simp [hS, hg]
  have h1 : K.edges \ T = insert {u, w} S := by
    ext x
    simp only [hS, mem_sdiff, mem_insert]
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hxf : x = {u, w}
      · exact Or.inl hxf
      · exact Or.inr ⟨hx, fun h => h.elim hxf hxT⟩
    · rintro (rfl | ⟨hx, hxT⟩)
      · exact ⟨hfK, hf⟩
      · exact ⟨hx, fun h => hxT (Or.inr h)⟩
  have h2 : K.edges \ insert {u, w} (T.erase {u, v}) = insert {u, v} S := by
    ext x
    simp only [hS, mem_sdiff, mem_insert, mem_erase]
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hxe : x = {u, v}
      · exact Or.inl hxe
      · exact Or.inr ⟨hx, fun h => h.elim (fun h' => hxT (Or.inl h'))
          (fun h' => hxT (Or.inr ⟨hxe, h'⟩))⟩
    · rintro (rfl | ⟨hx, hxT⟩)
      · exact ⟨hT he, fun h => h.elim (fun h' => hef h') (fun h' => h'.1 rfl)⟩
      · exact ⟨hx, fun h => hxT (h.elim Or.inl (fun h' => Or.inr h'.2))⟩
  have hτ' : ({u, w, v} : Finset V) ∈ K.tris := by rwa [pair_comm w v]
  simp only [amplitudeGF]
  rw [h1, h2, sum_pi_insert_collapse heS, sum_pi_insert_collapse hfS]
  · -- gauge set `T`: a nonzero spin on `uw` violates the triangle inequality at `v`
    intro σ _ x hx
    refine weight_eq_zero_of_tri huw huv hvw.symm hτ' ?_ ?_ ?_
    · rw [Function.update_of_ne hef, extS_of_not_mem heS]
    · rw [pair_comm w v, Function.update_of_ne hgf, extS_of_not_mem hgS]
    · rwa [pair_comm w u, Function.update_self]
  · -- gauge set `T - uv + uw`: a nonzero spin on `uv` violates the triangle inequality at `w`
    intro σ _ x hx
    refine weight_eq_zero_of_tri huv huw hvw hτ ?_ ?_ ?_
    · rw [Function.update_of_ne hef.symm, extS_of_not_mem hfS]
    · rw [Function.update_of_ne hge, extS_of_not_mem hgS]
    · rwa [pair_comm v u, Function.update_self]

/-- **A triangle exchange turns a maximal tree into a maximal tree.** -/
theorem IsMaxTree.exchange {K : Complex3 V} {T : Finset (Finset V)} (hT : IsMaxTree K T)
    {u v w : V} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w) (hτ : {u, v, w} ∈ K.tris)
    (he : {u, v} ∈ T) (hg : {v, w} ∈ T) (hf : {u, w} ∉ T) :
    IsMaxTree K (insert {u, w} (T.erase {u, v})) := by
  obtain ⟨hTK, hsp⟩ := hT
  obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_tris.mp hτ
  have hfK : ({u, w} : Finset V) ∈ K.edges :=
    Complex3.mem_edges.mpr ⟨t, ht, (by small_subset : ({u, w} : Finset V) ⊆ {u, v, w}).trans hsub,
      card_pair huw⟩
  have hu : u ∈ K.verts := (hsp.edge _ he).1 (by simp)
  have hw : w ∈ K.verts := (hsp.edge _ hg).1 (by simp)
  have hge : ({v, w} : Finset V) ≠ {u, v} := fun h => huw (by
    have : w ∈ ({u, v} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h'.symm
    · exact absurd h'.symm hvw)
  set T' := insert ({u, w} : Finset V) (T.erase {u, v}) with hT'
  have huw' : ({u, w} : Finset V) ∈ T' := mem_insert_self _ _
  have hwu' : ({w, u} : Finset V) ∈ T' := by rw [pair_comm]; exact huw'
  have hvw' : ({v, w} : Finset V) ∈ T' := mem_insert_of_mem (mem_erase.mpr ⟨hge, hg⟩)
  have hwv' : ({w, v} : Finset V) ∈ T' := by rw [pair_comm]; exact hvw'
  -- every step of a path in `T` becomes a path in `T'` (the step `uv` becomes `u w v`)
  have hstep : ∀ a b, ({a, b} : Finset V) ∈ T →
      Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T') a b := by
    intro a b hab
    by_cases h : ({a, b} : Finset V) = {u, v}
    · rcases pair_eq_pair_iff'.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .tail (.single huw') hwv'
      · exact .tail (.single hvw') hwu'
    · exact .single (mem_insert_of_mem (mem_erase.mpr ⟨h, hab⟩))
  refine ⟨?_, ⟨fun e he' => ?_, fun x hx y hy => ?_, ?_⟩⟩
  · intro e he'
    rcases mem_insert.mp he' with rfl | he'
    · exact hfK
    · exact hTK (mem_of_mem_erase he')
  · rcases mem_insert.mp he' with rfl | he'
    · exact ⟨insert_subset hu (by simpa using hw), card_pair huw⟩
    · exact hsp.edge e (mem_of_mem_erase he')
  · have key : ∀ a b, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T) a b →
        Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ T') a b := by
      intro a b hab
      induction hab with
      | refl => exact .refl
      | tail _ hcd ih => exact ih.trans (hstep _ _ hcd)
    exact key x y (hsp.conn x hx y hy)
  · have hfT : ({u, w} : Finset V) ∉ T.erase {u, v} := fun h => hf (mem_of_mem_erase h)
    rw [hT', card_insert_of_notMem hfT, card_erase_of_mem he, ← hsp.card]
    have : 0 < #T := card_pos.mpr ⟨_, he⟩
    omega

/-- One **triangle exchange** of a gauge edge: in a triangle `uvw` of `K` with gauge edges `uv`,
`vw` and non-gauge edge `uw`, replace `uv` by `uw`. -/
inductive TreeExchange (K : Complex3 V) : Finset (Finset V) → Finset (Finset V) → Prop
  | mk {T : Finset (Finset V)} (hT : T ⊆ K.edges) {u v w : V} (huv : u ≠ v) (hvw : v ≠ w)
      (huw : u ≠ w) (hτ : {u, v, w} ∈ K.tris) (he : {u, v} ∈ T) (hg : {v, w} ∈ T)
      (hf : {u, w} ∉ T) : TreeExchange K T (insert {u, w} (T.erase {u, v}))

/-- **The gauge-fixed amplitude is the same for all gauge sets connected by triangle exchanges**
(in either direction), for every cutoff. -/
theorem amplitudeGF_eqvGen_exchange (K : Complex3 V) {T T' : Finset (Finset V)}
    (h : Relation.EqvGen (TreeExchange K) T T') (cut : Finset V → ℕ) :
    amplitudeGF K T cut = amplitudeGF K T' cut := by
  induction h with
  | rel _ _ hs =>
    obtain ⟨hT, huv, hvw, huw, hτ, he, hg, hf⟩ := hs
    exact (amplitudeGF_exchange K hT huv hvw huw hτ he hg hf cut).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The reverse of a triangle exchange is again one (with the roles of `v` and `w` swapped). -/
theorem TreeExchange.symm {K : Complex3 V} {T T' : Finset (Finset V)} (h : TreeExchange K T T')
    (hT' : T' ⊆ K.edges) : TreeExchange K T' T := by
  obtain @⟨hT, u, v, w, huv, hvw, huw, hτ, he, hg, hf⟩ := h
  have hge : ({v, w} : Finset V) ≠ {u, v} := fun h => huw (by
    have : w ∈ ({u, v} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h'.symm
    · exact absurd h'.symm hvw)
  have hrev : insert ({u, v} : Finset V) ((insert {u, w} (T.erase {u, v})).erase {u, w}) = T := by
    rw [erase_insert (fun h => hf (mem_of_mem_erase h)), insert_erase he]
  have := TreeExchange.mk (K := K) hT' huw hvw.symm huv (by rwa [pair_comm w v])
    (mem_insert_self _ _) (by rw [pair_comm w v]; exact mem_insert_of_mem (mem_erase.mpr ⟨hge, hg⟩))
    (fun h => (mem_insert.mp h).elim
      (fun h' => huw.symm (by
        have : v ∈ ({u, w} : Finset V) := h' ▸ (by simp)
        simp only [mem_insert, mem_singleton] at this
        exact this.elim (fun h'' => absurd h''.symm huv) (fun h'' => absurd h'' hvw)))
      (fun h' => (mem_erase.mp h').1 rfl))
  rwa [hrev] at this

/-- **Maximal trees stay maximal along chains of triangle exchanges.** -/
theorem isMaxTree_iff_of_eqvGen_exchange {K : Complex3 V} {T T' : Finset (Finset V)}
    (h : Relation.EqvGen (TreeExchange K) T T') : IsMaxTree K T ↔ IsMaxTree K T' := by
  induction h with
  | rel T₀ _ hs =>
    obtain @⟨hT, u, v, w, huv, hvw, huw, hτ, he, hg, hf⟩ := hs
    refine ⟨fun h => h.exchange huv hvw huw hτ he hg hf, fun h => ?_⟩
    have hge : ({v, w} : Finset V) ≠ {u, v} := fun h => huw (by
      have : w ∈ ({u, v} : Finset V) := h ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact h'.symm
      · exact absurd h'.symm hvw)
    have hrev : insert ({u, v} : Finset V) ((insert {u, w} (T₀.erase {u, v})).erase {u, w}) = T₀ := by
      rw [erase_insert (fun h => hf (mem_of_mem_erase h)), insert_erase he]
    have := h.exchange huw hvw.symm huv (by rwa [pair_comm w v]) (mem_insert_self _ _)
      (by rw [pair_comm w v]; exact mem_insert_of_mem (mem_erase.mpr ⟨hge, hg⟩))
      (fun h => (mem_insert.mp h).elim
        (fun h' => huw.symm (by
          have : v ∈ ({u, w} : Finset V) := h' ▸ (by simp)
          simp only [mem_insert, mem_singleton] at this
          exact this.elim (fun h'' => absurd h''.symm huv) (fun h'' => absurd h'' hvw)))
        (fun h' => (mem_erase.mp h').1 rfl))
    rwa [hrev] at this
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Lightlike.PR
