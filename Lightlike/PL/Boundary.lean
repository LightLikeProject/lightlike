import Lightlike.PL.Starring
import Lightlike.PL.Manifold
import Lightlike.PL.Join
import Lightlike.PL.Euler
import Lightlike.PL.Links

/-!
# The boundary of a stellar manifold

For a combinatorial manifold the boundary is the set of faces whose link is a PL ball: a face of
the boundary is a face of `K` that lies in a nonempty face `τ` with `lk(τ, K)` a PL ball (for
example, the boundary of a manifold with boundary consists of the faces in the boundary
simplices). This is the boundary used in Lickorish's Theorem 3.6 (*Simplicial moves on complexes
and manifolds*, 1999, §3).

## Definitions

* `IsBallIn L`: `L` is a PL ball of some dimension, inside `V`.
* `bd K`: the faces of `K` that are empty or lie in a nonempty face whose link is a PL ball.
-/

open Finset

namespace Lightlike.PL
namespace SComplex
variable {V : Type*} [DecidableEq V]

/-- `L` is a PL ball of some dimension, inside `V`. -/
def IsBallIn (L : SComplex V) : Prop := ∃ n, IsPLBallIn n L

open Classical in
/-- The **boundary** of `K`: the empty face and the faces of `K` contained in a nonempty face
`τ` of `K` whose link is a PL ball. -/
noncomputable def bd (K : SComplex V) : SComplex V where
  faces := K.faces.filter fun σ =>
    σ = ∅ ∨ ∃ τ ∈ K, σ ⊆ τ ∧ τ.Nonempty ∧ IsBallIn (K.link τ)
  down s hs t ht := by
    simp only [mem_filter, mem_faces] at hs ⊢
    refine ⟨down_mem hs.1 ht, ?_⟩
    rcases eq_empty_or_nonempty t with rfl | hne
    · exact .inl rfl
    · rcases hs.2 with rfl | ⟨τ, hτ, hsτ, hτne, hb⟩
      · exact absurd (subset_empty.1 ht ▸ hne) (by simp)
      · exact .inr ⟨τ, hτ, ht.trans hsτ, hτne, hb⟩

open Classical in
lemma mem_bd {K : SComplex V} {σ : Finset V} :
    σ ∈ K.bd ↔ σ ∈ K ∧ (σ = ∅ ∨ ∃ τ ∈ K, σ ⊆ τ ∧ τ.Nonempty ∧ IsBallIn (K.link τ)) := by
  change σ ∈ K.faces.filter _ ↔ _
  simp

lemma bd_subset {K : SComplex V} {σ : Finset V} (h : σ ∈ K.bd) : σ ∈ K := (mem_bd.1 h).1

/-! ## Balls and spheres by the signed count -/

/-- A PL ball has signed count `0`. -/
lemma IsBallIn.signedCount_eq_zero {L : SComplex V} (h : IsBallIn L) : L.signedCount = 0 := by
  obtain ⟨n, A, hA, hLA⟩ := h
  rw [hLA.signedCount_eq]
  exact signedCount_simplex (card_pos.1 (by omega))

/-- A complex that is a PL sphere or ball (model `IsSB`) is a ball exactly when its signed count
vanishes: spheres have signed count `±1`. -/
lemma IsSB.isBallIn_iff {b : Bool} {m : ℕ} {L : SComplex V} (h : IsSB b m L) :
    IsBallIn L ↔ L.signedCount = 0 := by
  refine ⟨IsBallIn.signedCount_eq_zero, fun h0 => ?_⟩
  rcases h with ⟨A, hA, hLA⟩ | ⟨-, A, hA, hLA⟩
  · rw [hLA.signedCount_eq, signedCount_boundary (card_pos.1 (by omega))] at h0
    simp at h0
  · rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [hLA.signedCount_eq] at h0
      simp [signedCount, simplex] at h0
    · exact ⟨#A - 1, A, by have := card_pos.2 hne; omega, hLA⟩

/-- A PL sphere is not a ball. -/
lemma IsSB.not_isBallIn {m : ℕ} {L : SComplex V} {A : Finset V} (hA : #A = m + 1)
    (hLA : StellarEquivIn L (boundary A)) : ¬ IsBallIn L := by
  intro h
  have := h.signedCount_eq_zero
  rw [hLA.signedCount_eq, signedCount_boundary (card_pos.1 (by omega))] at this
  simp at this

/-- A sphere-or-ball that is not a ball is a sphere. -/
lemma IsSB.isSB_false_of_not_isBallIn [Infinite V] {b : Bool} {m : ℕ} {L : SComplex V}
    (h : IsSB b m L) (hn : ¬ IsBallIn L) : IsSB false m L := by
  rcases h with hs | ⟨-, A, hA, hLA⟩
  · exact .inl hs
  · rcases A.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨x⟩ := (inferInstance : Nonempty V)
      refine .inl ⟨{x}, by simp at hA ⊢; omega, ?_⟩
      rwa [← boundary_singleton x] at hLA
    · exact absurd ⟨#A - 1, A, by have := card_pos.2 hne; omega, hLA⟩ hn

/-- **Boundary faces of a manifold**: a nonempty face `σ` of a combinatorial manifold lies in the
boundary exactly when its link is a PL ball. -/
theorem IsMfdIn.mem_bd_iff [Infinite V] {n : ℕ} {K : SComplex V} (hK : IsMfdIn true n K)
    {σ : Finset V} (hσ : σ ∈ K) (hne : σ.Nonempty) : σ ∈ K.bd ↔ IsBallIn (K.link σ) := by
  classical
  refine ⟨fun h => ?_, fun h => mem_bd.2 ⟨hσ, .inr ⟨σ, hσ, subset_rfl, hne, h⟩⟩⟩
  rcases (mem_bd.1 h).2 with rfl | ⟨τ, hτ, hστ, hτne, hb⟩
  · exact absurd hne (by simp)
  by_contra hn
  obtain ⟨m, hm, hSB⟩ := (isMfdIn_main true n).1 K hK σ hσ hne
  have hsph := hSB.isSB_false_of_not_isBallIn hn
  have hdis : Disjoint σ (τ \ σ) := disjoint_sdiff
  have hlk : (K.link σ).link (τ \ σ) = K.link τ := by
    rw [link_link K hdis, union_sdiff_of_subset hστ]
  rcases (τ \ σ).eq_empty_or_nonempty with hρ | hρ
  · have : σ = τ := by
      have := union_sdiff_of_subset hστ
      rwa [hρ, union_empty] at this
    subst this
    exact hn hb
  · have hρL : τ \ σ ∈ K.link σ := mem_link'.2 ⟨hdis, by rwa [union_sdiff_of_subset hστ]⟩
    rcases m with _ | m'
    · have := hsph.verts_eq_empty
      obtain ⟨x, hx⟩ := hρ
      exact absurd (subset_verts hρL (by exact hx)) (by rw [this]; exact notMem_empty x)
    · have hMfd := (isMfdIn_main false m').2 _ hsph
      obtain ⟨m'', -, hs2⟩ := (isMfdIn_main false m').1 _ hMfd _ hρL hρ
      rw [hlk] at hs2
      rcases hs2 with ⟨A, hA, hLA⟩ | ⟨hf, -⟩
      · exact IsSB.not_isBallIn hA hLA hb
      · exact absurd hf (by simp)

/-! ## Links of faces in a stellar subdivision -/

lemma sdiff_subset_iff' {A τ w : Finset V} : A \ τ ⊆ w ↔ A ⊆ τ ∪ w := by
  constructor
  · intro h x hx
    by_cases hxτ : x ∈ τ
    · exact mem_union_left _ hxτ
    · exact mem_union_right _ (h (mem_sdiff.2 ⟨hx, hxτ⟩))
  · intro h x hx
    obtain ⟨hxA, hxτ⟩ := mem_sdiff.1 hx
    exact (mem_union.1 (h hxA)).resolve_left hxτ

/-- **Links of old faces in a subdivision**: for a face `τ` not containing the new vertex
`a`, `lk(τ, (A, a) K) = (A ∖ τ, a) lk(τ, K)`. -/
theorem link_starAt_of_notMem {K : SComplex V} {A τ : Finset V} {a : V} (ha : a ∉ K.verts)
    (haτ : a ∉ τ) :
    (K.starAt A a).link τ = (K.link τ).starAt (A \ τ) a := by
  have hset : ∀ w : Finset V, τ ∪ ((A \ τ) ∪ w) = A ∪ (τ ∪ w) := fun w => by
    ext x; simp only [mem_union, mem_sdiff]; tauto
  refine ext_mem fun u => ?_
  rw [mem_link']
  by_cases hau : a ∈ u
  · have hu : u = insert a (u.erase a) := (insert_erase hau).symm
    have hat : a ∉ u.erase a := notMem_erase a u
    set w := u.erase a with hw
    have hτw : a ∉ τ ∪ w := by simp [haτ, hat]
    have hunion : τ ∪ u = insert a (τ ∪ w) := by rw [hu, union_insert]
    rw [hunion, hu, mem_starAt, mem_starAt]
    constructor
    · rintro ⟨hd, h | ⟨t, ht, h₁, h₂, he⟩⟩
      · exact absurd (subset_verts h.1 (mem_insert_self _ _)) ha
      have hat' : a ∉ t := fun h => ha (subset_verts ht h)
      have := insert_cancel hat' hτw he
      subst this
      refine .inr ⟨w, mem_link'.2 ⟨(disjoint_insert_right.1 hd).2, ht⟩, ?_, ?_, rfl⟩
      · rw [sdiff_subset_iff']; exact h₁
      · refine mem_link'.2 ⟨disjoint_union_right.2 ⟨disjoint_sdiff, (disjoint_insert_right.1 hd).2⟩, ?_⟩
        rw [hset]; exact h₂
    · rintro (⟨h, -⟩ | ⟨t, ht, h₁, h₂, he⟩)
      · exact absurd (subset_verts (mem_link'.1 h).2 (by simp)) ha
      · have hat' : a ∉ t := fun h => ha (subset_verts (mem_link'.1 ht).2 (mem_union_right _ h))
        have := insert_cancel hat' hat he
        subst this
        obtain ⟨hd, ht⟩ := mem_link'.1 ht
        obtain ⟨-, h₂⟩ := mem_link'.1 h₂
        rw [hset] at h₂
        refine ⟨disjoint_insert_right.2 ⟨haτ, hd⟩, .inr ⟨τ ∪ w, ht, ?_, h₂, rfl⟩⟩
        · rwa [← sdiff_subset_iff']
  · have hunion : a ∉ τ ∪ u := by simp [haτ, hau]
    rw [mem_starAt_of_notMem hunion, mem_starAt_of_notMem hau, mem_link', sdiff_subset_iff']
    constructor
    · rintro ⟨hd, h₁, h₂⟩
      exact ⟨⟨hd, h₁⟩, h₂⟩
    · rintro ⟨⟨hd, h₁⟩, h₂⟩
      exact ⟨hd, h₁, h₂⟩

lemma IsBallIn.of_stellarEquivIn {K L : SComplex V} (h : IsBallIn K) (hKL : StellarEquivIn K L) :
    IsBallIn L :=
  let ⟨n, hn⟩ := h
  ⟨n, hn.of_stellarEquivIn hKL⟩

/-- Stellar equivalence inside `V` preserves being a ball. -/
lemma isBallIn_iff_of_stellarEquivIn {K L : SComplex V} (h : StellarEquivIn K L) :
    IsBallIn K ↔ IsBallIn L :=
  ⟨fun hK => hK.of_stellarEquivIn h, fun hL => hL.of_stellarEquivIn h.symm⟩

/-- **Links of old faces keep their type**: the link of a face `σ` not containing the new vertex
`a` and not containing `A` is a ball in `(A, a) K` exactly when it is in `K`. -/
theorem isBallIn_link_starAt_iff {K : SComplex V} {A σ : Finset V} {a : V} (ha : a ∉ K.verts)
    (haσ : a ∉ σ) (hAσ : ¬ A ⊆ σ) :
    IsBallIn ((K.starAt A a).link σ) ↔ IsBallIn (K.link σ) := by
  rw [link_starAt_of_notMem ha haσ]
  have hne : (A \ σ).Nonempty := by
    obtain ⟨x, hxA, hxσ⟩ := not_subset.1 hAσ
    exact ⟨x, mem_sdiff.2 ⟨hxA, hxσ⟩⟩
  by_cases hB : A \ σ ∈ K.link σ
  · have haL : a ∉ (K.link σ).verts := fun hx =>
      ha (mem_verts.2 (mem_link.1 (mem_verts.1 hx)).1)
    exact (isBallIn_iff_of_stellarEquivIn (StellarEquivIn.starAt hB hne haL)).symm
  · rw [starAt_of_notMem hB]

/-- **Links of faces through the new vertex**: `lk(a ∪ ρ, (A, a) K) = lk(ρ, ∂A * lk(A, K))`. -/
theorem link_starAt_insert {K : SComplex V} {A ρ : Finset V} {a : V} (ha : a ∉ K.verts)
    (haρ : a ∉ ρ) :
    (K.starAt A a).link (insert a ρ) = ((boundary A).join (K.link A)).link ρ := by
  have hdis : Disjoint ({a} : Finset V) ρ := disjoint_singleton_left.2 haρ
  rw [← link_starAt_apex ha, link_link _ hdis, ← insert_eq]

/-! ## The boundary near a vertex -/

/-- The link of a vertex of a combinatorial manifold is a combinatorial manifold (of one lower
dimension). -/
lemma IsMfdIn.link_vertex [Infinite V] {n : ℕ} {K : SComplex V} (hK : IsMfdIn true n K) {v : V}
    (hv : v ∈ K.verts) : IsMfdIn true (n - 1) (K.link {v}) := by
  rcases n with _ | n
  · have := (hK v hv).verts_eq_empty
    intro x hx
    rw [this] at hx
    exact absurd hx (notMem_empty x)
  · exact (isMfdIn_main true n).2 _ (hK v hv)

/-- **The boundary at a vertex**: a face `v ∪ ρ` with `ρ` nonempty lies in the boundary of a
combinatorial manifold exactly when `ρ` lies in the boundary of the link of `v`. -/
theorem IsMfdIn.insert_mem_bd_iff [Infinite V] {n : ℕ} {K : SComplex V} (hK : IsMfdIn true n K)
    {v : V} {ρ : Finset V} (hv : v ∈ K.verts) (hρ : ρ.Nonempty) (hvρ : v ∉ ρ) :
    insert v ρ ∈ K.bd ↔ ρ ∈ (K.link {v}).bd := by
  have hJ := hK.link_vertex hv
  have hdis : Disjoint ({v} : Finset V) ρ := disjoint_singleton_left.2 hvρ
  by_cases hmem : ρ ∈ K.link {v}
  · have hσ : insert v ρ ∈ K := by
      have := (mem_link'.1 hmem).2
      rwa [← insert_eq] at this
    rw [hK.mem_bd_iff hσ (insert_nonempty v ρ), hJ.mem_bd_iff hmem hρ,
      link_link K hdis, insert_eq]
  · have hσ : insert v ρ ∉ K := fun h => hmem (mem_link'.2 ⟨hdis, by rwa [insert_eq] at h⟩)
    exact ⟨fun h => absurd (bd_subset h) hσ, fun h => absurd (bd_subset h) hmem⟩

/-- **The boundary away from the new vertex**: for a face `σ` of the subdivision `(A, a) K` of a
combinatorial manifold that does not contain `a`, being in the boundary does not change. -/
theorem IsMfdIn.mem_bd_starAt_of_notMem [Infinite V] {n : ℕ} {K : SComplex V}
    (hK : IsMfdIn true n K) {A σ : Finset V} {a : V} (hA : A ∈ K) (hAne : A.Nonempty)
    (ha : a ∉ K.verts) (hσ : σ ∈ K.starAt A a) (hσne : σ.Nonempty) (haσ : a ∉ σ) :
    σ ∈ (K.starAt A a).bd ↔ σ ∈ K.bd := by
  have hK' : IsMfdIn true n (K.starAt A a) :=
    (isMfdIn_starAt_iff (fun L hL τ hτ hne => (isMfdIn_main true n).1 L hL τ hτ hne) hA hAne
      ha).2 hK
  obtain ⟨hσK, hAσ⟩ := (mem_starAt_of_notMem haσ).1 hσ
  rw [hK'.mem_bd_iff hσ hσne, hK.mem_bd_iff hσK hσne, isBallIn_link_starAt_iff ha haσ hAσ]

/-! ## The link of the apex -/

/-- **Joining with the boundary of a simplex preserves being a ball**: for a sphere-or-ball `L`
without vertices in the nonempty set `A`, `∂A * L` is a ball exactly when `L` is. -/
theorem IsSB.isBallIn_boundary_join_iff [Infinite V] {m : ℕ} {A : Finset V} {L : SComplex V}
    (hL : IsSB true m L) (hA : A.Nonempty) (hdis : Disjoint A L.verts) :
    IsBallIn ((boundary A).join L) ↔ IsBallIn L := by
  have hJ := hL.boundary_join hA hdis
  rw [hJ.isBallIn_iff, hL.isBallIn_iff,
    signedCount_join (Disjoint.mono_left (verts_boundary_subset A) hdis),
    signedCount_boundary hA]
  simp

/-- **The new vertex is a boundary vertex exactly when `A` is a boundary face**. -/
theorem IsMfdIn.apex_mem_bd_starAt_iff [Infinite V] {n : ℕ} {K : SComplex V}
    (hK : IsMfdIn true n K) {A : Finset V} {a : V} (hA : A ∈ K) (hAne : A.Nonempty)
    (ha : a ∉ K.verts) : {a} ∈ (K.starAt A a).bd ↔ A ∈ K.bd := by
  have hK' : IsMfdIn true n (K.starAt A a) :=
    (isMfdIn_starAt_iff (fun L hL τ hτ hne => (isMfdIn_main true n).1 L hL τ hτ hne) hA hAne
      ha).2 hK
  have hav : {a} ∈ K.starAt A a := by
    have h := (insert_mem_starAt (A := A) ha (s := ∅) (notMem_empty a)).2
      ⟨down_mem hA (empty_subset _), fun h => by
        obtain ⟨x, hx⟩ := hAne; exact notMem_empty x (h hx), by rwa [union_empty]⟩
    rwa [insert_empty] at h
  rw [hK'.mem_bd_iff hav (singleton_nonempty a), hK.mem_bd_iff hA hAne,
    link_starAt_apex ha]
  obtain ⟨m, -, hm⟩ := (isMfdIn_main true n).1 K hK A hA hAne
  refine hm.isBallIn_boundary_join_iff hAne ?_
  rw [Finset.disjoint_left]
  intro x hxA hxL
  have := (mem_link'.1 (mem_verts.1 hxL)).1
  exact disjoint_singleton_right.1 this hxA

/-! ## Links in a join -/

/-- A face of a join of complexes with disjoint vertex sets splits uniquely along the vertex
sets. -/
lemma inter_verts_union {P Q : SComplex V} (h : Disjoint P.verts Q.verts) {r₁ r₂ : Finset V}
    (h₁ : r₁ ∈ P) (h₂ : r₂ ∈ Q) : (r₁ ∪ r₂) ∩ P.verts = r₁ := by
  ext x
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨hx | hx, hxP⟩
    · exact hx
    · exact absurd hxP (Finset.disjoint_right.1 h (subset_verts h₂ hx))
  · intro hx
    exact ⟨.inl hx, subset_verts h₁ hx⟩

/-- **Links in a join**: for complexes with disjoint vertex sets and faces `t ∈ P`, `u ∈ Q`,
`lk(t ∪ u, P * Q) = lk(t, P) * lk(u, Q)`. -/
theorem link_join {P Q : SComplex V} (h : Disjoint P.verts Q.verts) {t u : Finset V} (ht : t ∈ P)
    (hu : u ∈ Q) : (P.join Q).link (t ∪ u) = (P.link t).join (Q.link u) := by
  have hQP : Disjoint Q.verts P.verts := h.symm
  refine ext_mem fun s => ?_
  rw [mem_link', mem_join]
  constructor
  · rintro ⟨hd, hmem⟩
    obtain ⟨r₁, hr₁, r₂, hr₂, he⟩ := hmem
    have e₁ : (t ∪ u ∪ s) ∩ P.verts = r₁ := by rw [← he]; exact inter_verts_union h hr₁ hr₂
    have e₂ : (t ∪ u ∪ s) ∩ Q.verts = r₂ := by
      rw [← he, Finset.union_comm r₁ r₂]; exact inter_verts_union hQP hr₂ hr₁
    have hsub : s ⊆ P.verts ∪ Q.verts := by
      intro x hx
      have : x ∈ r₁ ∪ r₂ := by rw [he]; simp [hx]
      rcases mem_union.1 this with h' | h'
      · exact mem_union_left _ (subset_verts hr₁ h')
      · exact mem_union_right _ (subset_verts hr₂ h')
    have htP := subset_verts ht
    have huQ := subset_verts hu
    have uP : u ∩ P.verts = ∅ := by
      ext x; simp only [mem_inter, notMem_empty, iff_false, not_and]
      exact fun hx hxP => Finset.disjoint_right.1 h (huQ hx) hxP
    have tQ : t ∩ Q.verts = ∅ := by
      ext x; simp only [mem_inter, notMem_empty, iff_false, not_and]
      exact fun hx hxQ => Finset.disjoint_left.1 h (htP hx) hxQ
    refine mem_join.2 ⟨s ∩ P.verts, ?_, s ∩ Q.verts, ?_, ?_⟩
    · refine mem_link'.2 ⟨Finset.disjoint_left.2 fun x hxt hxs => ?_, ?_⟩
      · exact Finset.disjoint_left.1 hd (mem_union_left _ hxt) (mem_of_mem_inter_left hxs)
      · have : t ∪ s ∩ P.verts = r₁ := by
          rw [← e₁]; ext x
          simp only [mem_union, mem_inter]
          constructor
          · rintro (hx | ⟨hx, hxP⟩)
            · exact ⟨.inl (.inl hx), htP hx⟩
            · exact ⟨.inr hx, hxP⟩
          · rintro ⟨((hx | hx) | hx), hxP⟩
            · exact .inl hx
            · exact absurd hxP (Finset.disjoint_right.1 h (huQ hx))
            · exact .inr ⟨hx, hxP⟩
        rwa [this]
    · refine mem_link'.2 ⟨Finset.disjoint_left.2 fun x hxt hxs => ?_, ?_⟩
      · exact Finset.disjoint_left.1 hd (mem_union_right _ hxt) (mem_of_mem_inter_left hxs)
      · have : u ∪ s ∩ Q.verts = r₂ := by
          rw [← e₂]; ext x
          simp only [mem_union, mem_inter]
          constructor
          · rintro (hx | ⟨hx, hxP⟩)
            · exact ⟨.inl (.inr hx), huQ hx⟩
            · exact ⟨.inr hx, hxP⟩
          · rintro ⟨((hx | hx) | hx), hxP⟩
            · exact absurd hxP (Finset.disjoint_left.1 h (htP hx))
            · exact .inl hx
            · exact .inr ⟨hx, hxP⟩
        rwa [this]
    · ext x
      simp only [mem_union, mem_inter]
      constructor
      · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · intro hx
        rcases mem_union.1 (hsub hx) with h' | h'
        · exact .inl ⟨hx, h'⟩
        · exact .inr ⟨hx, h'⟩
  · intro hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := mem_join.1 hs
    obtain ⟨hd₁, h₁⟩ := mem_link'.1 hs₁
    obtain ⟨hd₂, h₂⟩ := mem_link'.1 hs₂
    have htP := subset_verts ht
    have huQ := subset_verts hu
    have s₁P := subset_verts (down_mem h₁ subset_union_right)
    have s₂Q := subset_verts (down_mem h₂ subset_union_right)
    refine ⟨?_, ?_⟩
    · refine Finset.disjoint_left.2 fun x hx hx' => ?_
      rcases mem_union.1 hx with hxt | hxu <;> rcases mem_union.1 hx' with hx1 | hx2
      · exact Finset.disjoint_left.1 hd₁ hxt hx1
      · exact Finset.disjoint_left.1 h (htP hxt) (s₂Q hx2)
      · exact Finset.disjoint_left.1 h (s₁P hx1) (huQ hxu)
      · exact Finset.disjoint_left.1 hd₂ hxu hx2
    · exact ⟨t ∪ s₁, h₁, u ∪ s₂, h₂, by ext x; simp only [mem_union]; tauto⟩

/-- **The boundary through the new vertex**: for a combinatorial manifold `K`, a face `A` and a
new vertex `a`, the face `a ∪ ρ` of the subdivision `(A, a) K` lies in the boundary exactly when
`A ⊄ ρ` and `A ∪ ρ` lies in the boundary of `K`. -/
theorem IsMfdIn.insert_apex_mem_bd_starAt_iff [Infinite V] {n : ℕ} {K : SComplex V}
    (hK : IsMfdIn true n K) {A ρ : Finset V} {a : V} (hA : A ∈ K) (hAne : A.Nonempty)
    (ha : a ∉ K.verts) (haρ : a ∉ ρ) :
    insert a ρ ∈ (K.starAt A a).bd ↔ ¬ A ⊆ ρ ∧ A ∪ ρ ∈ K.bd := by
  have hK' : IsMfdIn true n (K.starAt A a) :=
    (isMfdIn_starAt_iff (fun L hL τ hτ hne => (isMfdIn_main true n).1 L hL τ hτ hne) hA hAne
      ha).2 hK
  by_cases hmem : insert a ρ ∈ K.starAt A a
  · obtain ⟨hρK, hAρ, hAρK⟩ := (insert_mem_starAt ha haρ).1 hmem
    have hne : (A ∪ ρ).Nonempty := hAne.mono subset_union_left
    rw [hK'.mem_bd_iff hmem (insert_nonempty a ρ), hK.mem_bd_iff hAρK hne,
      link_starAt_insert ha haρ]
    refine Iff.trans ?_ (and_iff_right hAρ).symm
    set t := ρ ∩ A with ht
    set u := ρ \ A with hu
    have htρ : t ∪ u = ρ := by
      ext x; simp only [ht, hu, mem_union, mem_inter, mem_sdiff]; tauto
    have htA : t ⊂ A := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨inter_subset_right, fun h => hAρ ?_⟩
      rw [← h]; exact inter_subset_left
    have hdisu : Disjoint A u := disjoint_sdiff_self_right
    have hAu : A ∪ u = A ∪ ρ := by rw [hu, union_sdiff_self_eq_union]
    have huL : u ∈ K.link A := mem_link'.2 ⟨hdisu, by rw [hAu]; exact hAρK⟩
    have hdis : Disjoint (boundary A).verts (K.link A).verts :=
      Disjoint.mono_left (verts_boundary_subset A) (disjoint_verts_link K A)
    have hlk : ((boundary A).join (K.link A)).link ρ =
        (boundary (A \ t)).join (K.link (A ∪ ρ)) := by
      conv_lhs => rw [← htρ]
      rw [link_join hdis (mem_boundary.2 htA) huL, link_boundary htA, link_link K hdisu, hAu]
    rw [hlk]
    obtain ⟨m, -, hm⟩ := (isMfdIn_main true n).1 K hK (A ∪ ρ) hAρK hne
    have hBne : (A \ t).Nonempty := by
      obtain ⟨x, hx⟩ := Finset.exists_of_ssubset htA
      exact ⟨x, mem_sdiff.2 hx⟩
    have hdisB : Disjoint (A \ t) (K.link (A ∪ ρ)).verts :=
      Disjoint.mono_left (sdiff_subset.trans subset_union_left) (disjoint_verts_link K (A ∪ ρ))
    exact (hm.isBallIn_boundary_join_iff hBne hdisB)
  · constructor
    · exact fun h => absurd (bd_subset h) hmem
    · rintro ⟨hAρ, hb⟩
      exact absurd ((insert_mem_starAt ha haρ).2
        ⟨down_mem (bd_subset hb) subset_union_right, hAρ, bd_subset hb⟩) hmem

/-- **Faces of the boundary of a subdivision of a manifold.** -/
theorem IsMfdIn.mem_bd_starAt_iff [Infinite V] {n : ℕ} {K : SComplex V}
    (hK : IsMfdIn true n K) {A σ : Finset V} {a : V} (hA : A ∈ K) (hAne : A.Nonempty)
    (ha : a ∉ K.verts) :
    σ ∈ (K.starAt A a).bd ↔ σ = ∅ ∨ (σ ≠ ∅ ∧
      ((a ∉ σ ∧ σ ∈ K.bd ∧ ¬ A ⊆ σ) ∨ (a ∈ σ ∧ ¬ A ⊆ σ.erase a ∧ A ∪ σ.erase a ∈ K.bd))) := by
  rcases σ.eq_empty_or_nonempty with rfl | hne
  · refine iff_of_true ?_ (.inl rfl)
    refine mem_bd.2 ⟨mem_starAt.2 (.inl ⟨down_mem hA (empty_subset _), fun h => ?_⟩), .inl rfl⟩
    obtain ⟨x, hx⟩ := hAne
    exact notMem_empty x (h hx)
  have key : σ ∈ (K.starAt A a).bd ↔
      ((a ∉ σ ∧ σ ∈ K.bd ∧ ¬ A ⊆ σ) ∨ (a ∈ σ ∧ ¬ A ⊆ σ.erase a ∧ A ∪ σ.erase a ∈ K.bd)) := by
    by_cases haσ : a ∈ σ
    · have hσ : σ = insert a (σ.erase a) := (insert_erase haσ).symm
      have haρ : a ∉ σ.erase a := notMem_erase a σ
      conv_lhs => rw [hσ]
      rw [hK.insert_apex_mem_bd_starAt_iff hA hAne ha haρ]
      constructor
      · exact fun h => .inr ⟨haσ, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd haσ h
        · exact h
    · constructor
      · intro h
        exact .inl ⟨haσ, (hK.mem_bd_starAt_of_notMem hA hAne ha (bd_subset h) hne haσ).1 h,
          ((mem_starAt_of_notMem haσ).1 (bd_subset h)).2⟩
      · rintro (⟨-, h, hAσ⟩ | ⟨h, -⟩)
        · have hσK : σ ∈ K.starAt A a := (mem_starAt_of_notMem haσ).2 ⟨bd_subset h, hAσ⟩
          exact (hK.mem_bd_starAt_of_notMem hA hAne ha hσK hne haσ).2 h
        · exact absurd h haσ
  exact ⟨fun h => .inr ⟨hne.ne_empty, key.1 h⟩,
    fun h => h.elim (fun h0 => absurd h0 hne.ne_empty) (fun h => key.2 h.2)⟩

/-- **The boundary of a subdivision** (Lickorish): for a combinatorial manifold `K` and a nonempty
face `A`, the boundary of `(A, a) K` is `(A, a)` of the boundary of `K` (which is `bd K` itself when
`A` is not a boundary face). -/
theorem IsMfdIn.bd_starAt_of_mem [Infinite V] {n : ℕ} {K : SComplex V} (hK : IsMfdIn true n K)
    {A : Finset V} {a : V} (hA : A ∈ K) (hAne : A.Nonempty) (ha : a ∉ K.verts) :
    (K.starAt A a).bd = K.bd.starAt A a := by
  have hav : a ∉ K.bd.verts := fun h => ha (mem_verts.2 (bd_subset (mem_verts.1 h)))
  refine ext_mem fun σ => ?_
  rw [hK.mem_bd_starAt_iff hA hAne ha, mem_starAt]
  by_cases hσ : σ = ∅
  · subst hσ
    refine iff_of_true (.inl rfl) (.inl ⟨mem_bd.2 ⟨down_mem hA (empty_subset _), .inl rfl⟩, fun h => ?_⟩)
    obtain ⟨x, hx⟩ := hAne
    exact notMem_empty x (h hx)
  · simp only [hσ, false_or, ne_eq, not_false_eq_true, true_and]
    constructor
    · rintro (⟨-, h₁, h₂⟩ | ⟨haσ, h₁, h₂⟩)
      · exact .inl ⟨h₁, h₂⟩
      · refine .inr ⟨σ.erase a, down_mem h₂ subset_union_right, h₁, h₂, insert_erase haσ⟩
    · rintro (⟨h₁, h₂⟩ | ⟨t, ht, h₁, h₂, rfl⟩)
      · have haσ : a ∉ σ := fun h => hav (subset_verts h₁ h)
        exact .inl ⟨haσ, h₁, h₂⟩
      · have hat : a ∉ t := fun h => hav (subset_verts ht h)
        refine .inr ⟨mem_insert_self a t, ?_, ?_⟩ <;> rw [erase_insert hat] <;> assumption

/-- **The boundary of a subdivision elsewhere**: if `A` is not a face of the boundary of `K`, the
boundary of `(A, a) K` is the boundary of `K`. -/
theorem IsMfdIn.bd_starAt_of_notMem [Infinite V] {n : ℕ} {K : SComplex V} (hK : IsMfdIn true n K)
    {A : Finset V} {a : V} (hA : A ∈ K) (hAne : A.Nonempty) (ha : a ∉ K.verts)
    (hAb : A ∉ K.bd) : (K.starAt A a).bd = K.bd := by
  refine ext_mem fun σ => ?_
  rw [hK.mem_bd_starAt_iff hA hAne ha]
  by_cases hσ : σ = ∅
  · subst hσ
    exact iff_of_true (.inl rfl) (mem_bd.2 ⟨down_mem hA (empty_subset _), .inl rfl⟩)
  · simp only [hσ, false_or, ne_eq, not_false_eq_true, true_and]
    constructor
    · rintro (⟨-, h, -⟩ | ⟨-, -, h⟩)
      · exact h
      · exact absurd (down_mem h subset_union_left) hAb
    · intro h
      have haσ : a ∉ σ := fun h' => ha (subset_verts (bd_subset h) h')
      exact .inl ⟨haσ, h, fun hs => hAb (down_mem h hs)⟩

end SComplex
end Lightlike.PL
