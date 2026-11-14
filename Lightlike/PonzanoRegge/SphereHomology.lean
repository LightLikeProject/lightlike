module

public import Lightlike.PonzanoRegge.SphereConverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

/-!
# Mod-2 homology of a triangulated 2-sphere

For a 2-complex `L` (a finite set of triangles) the chains with coefficients in a field `K` of
characteristic `2` (for example `ℤ/2`) are the functions on its triangles, edges and vertices.
`bd2 K L` sends a 2-chain to its boundary (each triangle to its three edges) and `bd1 K L` a 1-chain
to its boundary (each edge to its two vertices). Characteristic `2` makes orientations unnecessary.

* `bd1_bd2`: the boundary of a boundary is `0`.
* `IsSurfaceSphere.ker_bd2`: the only 2-cycles are `0` and the sum of all triangles (the vertex
  links are connected, so a 2-cycle is constant around every vertex, and the 1-skeleton is
  connected).
* `mem_range_bd1_of_sum_eq_zero`: every 0-chain with coefficient sum `0` is a boundary (the
  1-skeleton is connected).
* `IsSurfaceSphere.range_bd2`, `IsSurfaceSphere.exists_bd2_eq`: **every 1-cycle is a boundary**
  (`H₁(L; K) = 0`). The dimensions of the cycles and boundaries agree because the Euler
  characteristic is `2`.

The coefficient field is a variable rather than `ZMod 2` itself: with the concrete `ZMod 2`,
Mathlib's dimension lemmas (already `finrank_span_singleton`) run out of time unifying the ring
structure of `ZMod 2` with the one derived from its field structure.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V] {K : Type*} [Field K]

section chains

variable (K) (L : Finset (Finset V))

/-- The boundary of a 2-chain: the sum, over the triangles containing an edge, of their
coefficients. -/
noncomputable def bd2 : (L → K) →ₗ[K] (edges2 L → K) :=
  LinearMap.pi fun e => ∑ τ ∈ Finset.filter (fun τ : L => (e : Finset V) ⊆ (τ : Finset V)) univ,
    (LinearMap.proj τ : (L → K) →ₗ[K] K)

/-- The boundary of a 1-chain: the sum, over the edges containing a vertex, of their
coefficients. -/
noncomputable def bd1 : (edges2 L → K) →ₗ[K] (verts2 L → K) :=
  LinearMap.pi fun v => ∑ e ∈ Finset.filter (fun e : edges2 L => (v : V) ∈ (e : Finset V)) univ,
    (LinearMap.proj e : (edges2 L → K) →ₗ[K] K)

variable {K} {L}

lemma bd2_apply (σ : L → K) (e : edges2 L) :
    bd2 K L σ e = ∑ τ ∈ Finset.filter (fun τ : L => (e : Finset V) ⊆ (τ : Finset V)) univ, σ τ := by
  simp [bd2]

lemma bd1_apply (c : edges2 L → K) (v : verts2 L) :
    bd1 K L c v = ∑ e ∈ Finset.filter (fun e : edges2 L => (v : V) ∈ (e : Finset V)) univ, c e := by
  simp [bd1]

end chains

variable [CharP K 2]

/-! ## Sums over subtypes -/

/-- Extend a function on the elements of `S` by `0`. -/
noncomputable def extFn {α : Type*} [DecidableEq α] {S : Finset α} (f : S → K) : α → K :=
  fun x => if h : x ∈ S then f ⟨x, h⟩ else 0

omit [DecidableEq V] [CharP K 2] in
lemma extFn_coe {α : Type*} [DecidableEq α] {S : Finset α} (f : S → K) (x : S) :
    extFn f x = f x := by
  simp [extFn]

omit [DecidableEq V] [CharP K 2] in
/-- A sum over the elements of `S` satisfying `P` is the sum over `S.filter P`. -/
lemma sum_filter_univ_coe {α : Type*} [DecidableEq α] {S : Finset α} (P : α → Prop)
    [DecidablePred P] (f : S → K) :
    ∑ x ∈ Finset.filter (fun x : S => P x) univ, f x = ∑ x ∈ S.filter P, extFn f x := by
  rw [sum_filter, sum_filter]
  rw [← Finset.sum_coe_sort S]
  refine sum_congr rfl fun x _ => ?_
  rw [extFn_coe]

omit [DecidableEq V] in
lemma card_filter_univ_coe {α : Type*} [DecidableEq α] {S : Finset α} (P : α → Prop)
    [DecidablePred P] : #(Finset.filter (fun x : S => P x) univ) = #(S.filter P) := by
  rw [card_filter, card_filter, ← Finset.sum_coe_sort S]

/-! ## Edges with two triangles -/

omit [DecidableEq V] in
lemma char2_add_eq_zero (a b : K) : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- In a closed 2-complex an edge lies in exactly two triangles. -/
lemma two_tris {L : Finset (Finset V)} (hc : IsClosed2 L) {e : Finset V} (he : e ∈ edges2 L) :
    ∃ t₁ ∈ L, ∃ t₂ ∈ L, t₁ ≠ t₂ ∧ L.filter (e ⊆ ·) = {t₁, t₂} := by
  obtain ⟨t₁, t₂, hne, h⟩ := card_eq_two.mp (hc e he)
  have h1 : t₁ ∈ L.filter (e ⊆ ·) := by rw [h]; simp
  have h2 : t₂ ∈ L.filter (e ⊆ ·) := by rw [h]; simp
  exact ⟨t₁, (mem_filter.mp h1).1, t₂, (mem_filter.mp h2).1, hne, h⟩

/-- **If the boundary of a 2-chain vanishes on an edge, its two triangles have the same
coefficient.** -/
lemma eq_of_bd2_eq_zero {L : Finset (Finset V)} (hc : IsClosed2 L) {σ : L → K}
    {e : edges2 L} (h0 : bd2 K L σ e = 0) {τ τ' : L} (hτ : (e : Finset V) ⊆ τ)
    (hτ' : (e : Finset V) ⊆ τ') : σ τ = σ τ' := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hne, hf⟩ := two_tris hc e.2
  rw [bd2_apply, sum_filter_univ_coe (fun τ => (e : Finset V) ⊆ τ), hf, sum_pair hne,
    char2_add_eq_zero] at h0
  have m : ∀ x : L, (e : Finset V) ⊆ x → (x : Finset V) = t₁ ∨ (x : Finset V) = t₂ := fun x hx => by
    have : (x : Finset V) ∈ L.filter ((e : Finset V) ⊆ ·) := mem_filter.mpr ⟨x.2, hx⟩
    rw [hf] at this
    simpa using this
  rw [← extFn_coe σ τ, ← extFn_coe σ τ']
  rcases m τ hτ with h | h <;> rcases m τ' hτ' with h' | h' <;> rw [h, h']
  · exact h0
  · exact h0.symm

lemma pair_subset_of_mem {τ : Finset V} {u w : V} (hu : u ∈ τ) (hw : w ∈ τ) :
    ({u, w} : Finset V) ⊆ τ :=
  insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hw⟩

/-- A vertex of a 3-element set has another vertex next to it. -/
lemma exists_other {τ : Finset V} (hc : #τ = 3) (u : V) : ∃ w ∈ τ, w ≠ u := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have : τ ⊆ {u} := fun w hw => mem_singleton.mpr (h w hw)
  have := card_le_card this
  rw [card_singleton] at this
  omega

/-- **A 2-chain whose boundary vanishes on every edge through `u` is constant on the triangles
around `u`**: the link of `u` is connected, and the two triangles at each edge through `u` have the
same coefficient. -/
lemma const_around {L : Finset (Finset V)} (hS : IsSurfaceSphere L) {σ : L → K} {u : V}
    (h0 : ∀ e : edges2 L, u ∈ (e : Finset V) → bd2 K L σ e = 0) {τ τ' : L}
    (hτ : u ∈ (τ : Finset V)) (hτ' : u ∈ (τ' : Finset V)) : σ τ = σ τ' := by
  have hu : u ∈ verts2 L := mem_verts2.mpr ⟨τ, τ.2, hτ⟩
  obtain ⟨w, hw, hwu⟩ := exists_other (hS.card τ τ.2) u
  obtain ⟨w', hw', hw'u⟩ := exists_other (hS.card τ' τ'.2) u
  have step_edge : ∀ y : V, y ≠ u → ∀ t₁ t₂ : L, ({u, y} : Finset V) ⊆ t₁ →
      ({u, y} : Finset V) ⊆ t₂ → σ t₁ = σ t₂ := by
    intro y hy t₁ t₂ h1 h2
    have he : ({u, y} : Finset V) ∈ edges2 L := mem_edges2.mpr ⟨t₁, t₁.2, h1, card_pair hy.symm⟩
    exact eq_of_bd2_eq_zero hS.closed (e := ⟨_, he⟩) (h0 ⟨_, he⟩ (by simp)) h1 h2
  have lkMem : ∀ t : L, ∀ y ∈ (t : Finset V), u ∈ (t : Finset V) → y ≠ u → y ∈ verts2 (lk2 L u) :=
    fun t y hy hut hyu => mem_verts2.mpr ⟨(t : Finset V).erase u,
      mem_lk2.mpr ⟨notMem_erase _ _, by rw [insert_erase hut]; exact t.2⟩, mem_erase.mpr ⟨hyu, hy⟩⟩
  have path := hS.link u hu w (lkMem τ w hw hτ hwu) w' (lkMem τ' w' hw' hτ' hw'u)
  have key : ∀ y, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ lk2 L u) w y →
      y ≠ u → ∀ t : L, ({u, y} : Finset V) ⊆ t → σ t = σ τ := by
    intro y hy
    induction hy with
    | refl => exact fun _ t ht => step_edge w hwu t τ ht (pair_subset_of_mem hτ hw)
    | @tail p q _ hpq ih =>
      intro hq t ht
      obtain ⟨hupq, hT⟩ := mem_lk2.mp hpq
      have hpu : p ≠ u := fun h => hupq (h ▸ by simp)
      let T : L := ⟨insert u {p, q}, hT⟩
      have hT1 : ({u, p} : Finset V) ⊆ T := pair_subset_of_mem (by simp [T]) (by simp [T])
      have hT2 : ({u, q} : Finset V) ⊆ T := pair_subset_of_mem (by simp [T]) (by simp [T])
      rw [step_edge q hq t T ht hT2]
      exact ih hpu T hT1
  exact (key w' path hw'u τ' (pair_subset_of_mem hτ' hw')).symm

/-- **The 2-cycles of a triangulated 2-sphere are constant.** -/
lemma const_of_bd2_eq_zero {L : Finset (Finset V)} (hS : IsSurfaceSphere L) {σ : L → K}
    (h0 : bd2 K L σ = 0) (τ τ' : L) : σ τ = σ τ' := by
  have hz : ∀ (u : V) (e : edges2 L), u ∈ (e : Finset V) → bd2 K L σ e = 0 := fun _ e _ => by
    rw [h0]; rfl
  obtain ⟨u, hu⟩ : (τ : Finset V).Nonempty := card_pos.mp (by rw [hS.card τ τ.2]; norm_num)
  obtain ⟨u', hu'⟩ : (τ' : Finset V).Nonempty := card_pos.mp (by rw [hS.card τ' τ'.2]; norm_num)
  have hconn := hS.connected u (mem_verts2.mpr ⟨τ, τ.2, hu⟩) u' (mem_verts2.mpr ⟨τ', τ'.2, hu'⟩)
  have key : ∀ y, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ edges2 L) u y →
      ∀ t : L, y ∈ (t : Finset V) → σ t = σ τ := by
    intro y hy
    induction hy with
    | refl => exact fun t ht => const_around hS (hz u) ht hu
    | @tail p q _ hpq ih =>
      intro t ht
      obtain ⟨T, hTL, hsub, -⟩ := mem_edges2.mp hpq
      have h1 := ih ⟨T, hTL⟩ (hsub (by simp))
      rw [const_around hS (hz q) ht (show q ∈ ((⟨T, hTL⟩ : L) : Finset V) from hsub (by simp))]
      exact h1
  exact (key u' hconn τ' hu').symm

/-! ## The 2-cycles -/

/-- **The 2-cycles of a triangulated 2-sphere are `0` and the sum of all triangles.** -/
theorem IsSurfaceSphere.ker_bd2 {L : Finset (Finset V)} (hS : IsSurfaceSphere L) :
    LinearMap.ker (bd2 K L) = Submodule.span (K) {fun _ => 1} := by
  apply le_antisymm
  · intro σ hσ
    rw [LinearMap.mem_ker] at hσ
    rw [Submodule.mem_span_singleton]
    by_cases hL : L.Nonempty
    · obtain ⟨τ₀, hτ₀⟩ := hL
      refine ⟨σ ⟨τ₀, hτ₀⟩, funext fun τ => ?_⟩
      simp [const_of_bd2_eq_zero hS hσ τ ⟨τ₀, hτ₀⟩]
    · refine ⟨0, funext fun τ => absurd ⟨τ.1, τ.2⟩ hL⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    funext e
    obtain ⟨t₁, ht₁, t₂, ht₂, hne, hf⟩ := two_tris hS.closed e.2
    rw [bd2_apply, sum_filter_univ_coe (fun τ => (e : Finset V) ⊆ τ), hf, sum_pair hne]
    simp only [extFn, ht₁, ht₂, dite_true, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero 1

theorem IsSurfaceSphere.finrank_ker_bd2 {L : Finset (Finset V)} (hS : IsSurfaceSphere L)
    (hL : L.Nonempty) : Module.finrank (K) (LinearMap.ker (bd2 K L)) = 1 := by
  obtain ⟨τ₀, hτ₀⟩ := hL
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have h1 : (fun _ => (1 : K) : L → K) ≠ 0 := fun h => h10 (congrFun h ⟨τ₀, hτ₀⟩)
  exact (LinearEquiv.ofEq _ _ hS.ker_bd2).finrank_eq.trans (finrank_span_singleton h1)

/-! ## The boundary of a boundary -/

/-- The 2-element subsets of a 3-element set `{x, y, z}`. -/
lemma powersetCard_two_three {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    powersetCard 2 ({x, y, z} : Finset V) = {{x, y}, {x, z}, {y, z}} := by
  ext e
  rw [mem_powersetCard]
  constructor
  · rintro ⟨hsub, hc⟩
    rcases pair_of_sub3 hsub hc with rfl | rfl | rfl <;> simp
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨pair_subset_of_mem (by simp) (by simp), card_pair hxy⟩
    · exact ⟨pair_subset_of_mem (by simp) (by simp), card_pair hxz⟩
    · exact ⟨pair_subset_of_mem (by simp) (by simp), card_pair hyz⟩

/-- The edges of a set `τ` through a vertex `v` of `τ` are the pairs `{v, w}`, `w ∈ τ`, `w ≠ v`. -/
lemma filter_powersetCard_two {τ : Finset V} {v : V} (hv : v ∈ τ) :
    (τ.powersetCard 2).filter (v ∈ ·) = (τ.erase v).image (fun w => ({v, w} : Finset V)) := by
  ext e
  simp only [mem_filter, mem_powersetCard, mem_image, mem_erase]
  constructor
  · rintro ⟨⟨hsub, hc⟩, hve⟩
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hc
    simp only [mem_insert, mem_singleton] at hve
    rcases hve with rfl | rfl
    · exact ⟨b, ⟨hab.symm, hsub (by simp)⟩, rfl⟩
    · exact ⟨a, ⟨hab, hsub (by simp)⟩, pair_comm _ _⟩
  · rintro ⟨w, ⟨hwv, hw⟩, rfl⟩
    exact ⟨⟨pair_subset_of_mem hv hw, card_pair hwv.symm⟩, by simp⟩

/-- In a triangle, a vertex lies in exactly two of the three edges (or in none). -/
lemma card_edges_through {τ : Finset V} (hc : #τ = 3) (v : V) :
    #((τ.powersetCard 2).filter (v ∈ ·)) = if v ∈ τ then 2 else 0 := by
  by_cases hv : v ∈ τ
  · rw [filter_powersetCard_two hv, card_image_of_injOn, card_erase_of_mem hv, hc]
    · simp [hv]
    · intro w hw w' hw' h
      have : w ∈ ({v, w'} : Finset V) := (show ({v, w} : Finset V) = {v, w'} from h) ▸ (by simp)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h'
      · exact absurd h' (mem_erase.mp hw).1
      · exact h'
  · simp only [hv, ite_false]
    rw [card_eq_zero, filter_eq_empty_iff]
    intro e he hve
    exact hv ((mem_powersetCard.mp he).1 hve)

/-- The edges of `L` through `v` inside a triangle `τ` of `L` are the 2-element subsets of `τ`
that contain `v`. -/
lemma filter_edges2_through {L : Finset (Finset V)} {τ : Finset V} (hτ : τ ∈ L) (v : V) :
    (edges2 L).filter (fun e => v ∈ e ∧ e ⊆ τ) = (τ.powersetCard 2).filter (v ∈ ·) := by
  ext e
  simp only [mem_filter, mem_edges2, mem_powersetCard]
  constructor
  · rintro ⟨⟨-, -, -, hc⟩, hv, hsub⟩
    exact ⟨⟨hsub, hc⟩, hv⟩
  · rintro ⟨⟨hsub, hc⟩, hv⟩
    exact ⟨⟨τ, hτ, hsub, hc⟩, hv, hsub⟩

omit [CharP K 2] in
/-- `bd1 ∘ bd2` at a vertex `v`: each triangle is counted once for every edge through `v` in it. -/
lemma bd1_bd2_apply {L : Finset (Finset V)} (σ : L → K) (v : verts2 L) :
    bd1 K L (bd2 K L σ) v = ∑ τ : L, (#(Finset.filter (fun e : edges2 L =>
      (v : V) ∈ (e : Finset V) ∧ (e : Finset V) ⊆ τ) univ) : K) * σ τ := by
  rw [bd1_apply]
  simp_rw [bd2_apply]
  rw [Finset.sum_comm' (t' := univ) (s' := fun τ : L => Finset.filter (fun e : edges2 L =>
    (v : V) ∈ (e : Finset V) ∧ (e : Finset V) ⊆ τ) univ) (fun e τ => by simp)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The boundary of a boundary is `0`**: in a complex of triangles, a vertex of a triangle lies
in two of its edges, and `2 = 0` in characteristic `2`. -/
theorem bd1_bd2 {L : Finset (Finset V)} (hcard : ∀ τ ∈ L, #τ = 3) :
    (bd1 K L).comp (bd2 K L) = 0 := by
  refine LinearMap.ext fun σ => funext fun v => ?_
  rw [LinearMap.comp_apply, bd1_bd2_apply, LinearMap.zero_apply, Pi.zero_apply]
  refine Finset.sum_eq_zero fun τ _ => ?_
  rw [card_filter_univ_coe (fun e : Finset V => (v : V) ∈ e ∧ e ⊆ (τ : Finset V)),
    filter_edges2_through τ.2,
    card_edges_through (hcard τ τ.2)]
  split_ifs <;> simp [CharTwo.two_eq_zero]

/-! ## The 0-boundaries -/

omit [CharP K 2] in
/-- The boundary of a single edge `e` is `1` on the vertices of `e`. -/
lemma bd1_single {L : Finset (Finset V)} (e : edges2 L) (v : verts2 L) :
    bd1 K L (Pi.single e 1) v = if (v : V) ∈ (e : Finset V) then 1 else 0 := by
  rw [bd1_apply, Finset.sum_filter]
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ e) h)]
  simp

lemma single_add_self {L : Finset (Finset V)} (u : verts2 L) :
    (Pi.single u (1 : K) : verts2 L → K) + Pi.single u 1 = 0 := by
  funext v
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

omit [CharP K 2] in
/-- The boundary of the edge `{p, q}` is `δ_p + δ_q`. -/
lemma bd1_single_pair {L : Finset (Finset V)} {p q : V} (hpq : p ≠ q)
    (he : ({p, q} : Finset V) ∈ edges2 L) (hp : p ∈ verts2 L) (hq : q ∈ verts2 L) :
    bd1 K L (Pi.single ⟨_, he⟩ 1) = Pi.single ⟨p, hp⟩ 1 + Pi.single ⟨q, hq⟩ 1 := by
  funext v
  rw [bd1_single, Pi.add_apply, Pi.single_apply, Pi.single_apply]
  simp only [mem_insert, mem_singleton, Subtype.ext_iff]
  by_cases hvp : (v : V) = p
  · simp [hvp, hpq]
  · by_cases hvq : (v : V) = q <;> simp [hvp, hvq, Ne.symm hpq]

/-- **Every 0-chain `δ_u + δ_{u₀}` is a boundary**: join `u₀` to `u` by a path of edges. -/
lemma single_add_mem_range {L : Finset (Finset V)} (hS : IsSurfaceSphere L) (u₀ u : verts2 L) :
    (Pi.single u (1 : K) + Pi.single u₀ 1 : verts2 L → K) ∈ LinearMap.range (bd1 K L) := by
  have key : ∀ y, Relation.ReflTransGen (fun x y => ({x, y} : Finset V) ∈ edges2 L) (u₀ : V) y →
      ∀ hy : y ∈ verts2 L,
        (Pi.single ⟨y, hy⟩ (1 : K) + Pi.single u₀ 1 : verts2 L → K) ∈ LinearMap.range (bd1 K L) := by
    intro y hy
    induction hy with
    | refl =>
      intro hy
      rw [show (⟨(u₀ : V), hy⟩ : verts2 L) = u₀ from rfl, single_add_self]
      exact zero_mem _
    | @tail p q _ hpq ih =>
      intro hq
      obtain ⟨τ, hτ, hsub, hc⟩ := mem_edges2.mp hpq
      have hpv : p ∈ verts2 L := mem_verts2_of_sub hτ hsub (by simp)
      have hpq' : p ≠ q := by
        rintro rfl
        simp at hc
      have h := add_mem (ih hpv) (LinearMap.mem_range_self (bd1 K L) (Pi.single ⟨_, hpq⟩ 1))
      rw [bd1_single_pair hpq' hpq hpv hq] at h
      convert h using 1
      calc _ = (Pi.single ⟨p, hpv⟩ (1 : K) + Pi.single ⟨p, hpv⟩ 1) +
            (Pi.single ⟨q, hq⟩ 1 + Pi.single u₀ 1 : verts2 L → K) := by
              rw [single_add_self, zero_add]
        _ = _ := by abel
  exact key u (hS.connected u₀ u₀.2 u u.2) u.2

/-- **The 0-chains with coefficient sum `0` are boundaries.** -/
lemma mem_range_bd1_of_sum_eq_zero {L : Finset (Finset V)} (hS : IsSurfaceSphere L)
    (u₀ : verts2 L) {f : verts2 L → K} (hf : ∑ v, f v = 0) : f ∈ LinearMap.range (bd1 K L) := by
  have hrepr : f = ∑ u, f u • (Pi.single u (1 : K) + Pi.single u₀ 1 : verts2 L → K) := by
    funext v
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hf, zero_mul, add_zero]
    simp [Pi.single_apply]
  rw [hrepr]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (single_add_mem_range hS u₀ u)

/-! ## The first homology vanishes -/

/-- **The 1-cycles of a triangulated 2-sphere are exactly the boundaries.** The boundaries of
2-chains have dimension `F - 1` (the 2-cycles are `0` and the sum of all triangles), the 1-cycles
have dimension at most `E - (V - 1)` (every 0-chain with coefficient sum `0` is a boundary), and
`V - E + F = 2`. -/
theorem IsSurfaceSphere.range_bd2 {L : Finset (Finset V)} (hS : IsSurfaceSphere L) :
    LinearMap.range (bd2 K L) = LinearMap.ker (bd1 K L) := by
  have hL : L.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have := hS.euler
    simp [euler2, verts2, edges2] at this
  obtain ⟨τ₀, hτ₀⟩ := hL
  obtain ⟨x₀, hx₀⟩ : τ₀.Nonempty := card_pos.mp (by rw [hS.card τ₀ hτ₀]; norm_num)
  let u₀ : verts2 L := ⟨x₀, mem_verts2.mpr ⟨τ₀, hτ₀, hx₀⟩⟩
  let φ : (verts2 L → K) →ₗ[K] K := ∑ v : verts2 L, LinearMap.proj v
  have hφ : ∀ f, φ f = ∑ v, f v := fun f => by simp [φ]
  have hW : LinearMap.ker φ ≤ LinearMap.range (bd1 K L) := fun f hf =>
    mem_range_bd1_of_sum_eq_zero hS u₀ (by rw [← hφ]; exact hf)
  have hφs : LinearMap.range φ = ⊤ :=
    LinearMap.range_eq_top.mpr fun c => ⟨Pi.single u₀ c, by simp [hφ]⟩
  have r0 := LinearMap.finrank_range_add_finrank_ker φ
  have r1 := LinearMap.finrank_range_add_finrank_ker (bd1 K L)
  have r2 := LinearMap.finrank_range_add_finrank_ker (bd2 K L)
  rw [hφs, finrank_top, Module.finrank_self] at r0
  have k2 := hS.finrank_ker_bd2 (K := K) ⟨τ₀, hτ₀⟩
  have mW := Submodule.finrank_mono hW
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at r0 r1 r2
  have he := hS.euler
  simp only [euler2] at he
  apply Submodule.eq_of_le_of_finrank_le (LinearMap.range_le_ker_iff.mpr (bd1_bd2 hS.card))
  omega

/-- **Every 1-cycle of a triangulated 2-sphere is the boundary of a 2-chain**
(`H₁(L; K) = 0` for a field `K` of characteristic `2`). -/
theorem IsSurfaceSphere.exists_bd2_eq {L : Finset (Finset V)} (hS : IsSurfaceSphere L)
    {c : edges2 L → K} (hc : bd1 K L c = 0) : ∃ σ, bd2 K L σ = c := by
  have h : c ∈ LinearMap.range (bd2 K L) := by
    rw [hS.range_bd2]
    exact hc
  exact LinearMap.mem_range.mp h

/-! ## The crossing lemma -/

omit [CharP K 2] in
/-- If a 2-chain has boundary `1` on an edge `e`, the coefficients of the two triangles at `e`
add up to `1`. -/
lemma add_eq_one_of_bd2_eq_one {L : Finset (Finset V)} (hc : IsClosed2 L) {σ : L → K}
    {e : edges2 L} (h1 : bd2 K L σ e = 1) {τ τ' : L} (hne : τ ≠ τ') (hτ : (e : Finset V) ⊆ τ)
    (hτ' : (e : Finset V) ⊆ τ') : σ τ + σ τ' = 1 := by
  have hne' : (τ : Finset V) ≠ τ' := fun h => hne (Subtype.ext h)
  have hf : L.filter ((e : Finset V) ⊆ ·) = {(τ : Finset V), (τ' : Finset V)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter.mpr ⟨τ.2, hτ⟩
      · exact mem_filter.mpr ⟨τ'.2, hτ'⟩
    · rw [hc e e.2, card_pair hne']
  rw [bd2_apply, sum_filter_univ_coe (fun x => (e : Finset V) ⊆ x), hf, sum_pair hne', extFn_coe,
    extFn_coe] at h1
  exact h1

omit [DecidableEq V] in
lemma tri_ne {a b c : V} [DecidableEq V] (h : #({a, b, c} : Finset V) = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨fun hab => ?_, fun hac => ?_, fun hbc => ?_⟩
  · subst hab
    rw [insert_eq_of_mem (mem_insert_self a {c})] at h
    have := card_le_two (a := a) (b := c)
    omega
  · subst hac
    rw [show ({a, b, a} : Finset V) = {a, b} by ext; simp only [mem_insert, mem_singleton]; tauto] at h
    have := card_le_two (a := a) (b := b)
    omega
  · subst hbc
    rw [show ({a, b, b} : Finset V) = {a, b} by ext; simp only [mem_insert, mem_singleton]; tauto] at h
    have := card_le_two (a := a) (b := b)
    omega

lemma ne_of_mem_edges2 {L : Finset (Finset V)} {a b : V} (h : ({a, b} : Finset V) ∈ edges2 L) :
    a ≠ b := by
  rintro rfl
  obtain ⟨-, -, -, hc⟩ := mem_edges2.mp h
  simp at hc

/-- An edge containing `u` differs from an edge `{a, b}` with `u ∉ {a, b}`. -/
lemma edge_ne {L : Finset (Finset V)} {e : edges2 L} {u a b : V} (hu : u ∈ (e : Finset V))
    (hab : ({a, b} : Finset V) ∈ edges2 L) (ha : u ≠ a) (hb : u ≠ b) : e ≠ ⟨_, hab⟩ := by
  intro h
  have he : (e : Finset V) = {a, b} := congrArg Subtype.val h
  rw [he] at hu
  simp only [mem_insert, mem_singleton] at hu
  tauto

include K in
/-- **The crossing lemma**, over any field `K` of characteristic `2`. Around a vertex `v` with
consecutive link vertices `v₁, v₂, v₃, v₄` (triangles `v v₁ v₂`, `v v₂ v₃`, `v v₃ v₄`, `v₁ ≠ v₄`),
the diagonals `v₁v₃` and `v₂v₄` are not both edges. The cycle `v v₁ v₃` bounds a 2-chain
(`H₁ = 0`), which is constant around `v₂` and around `v₄` because no edge of the cycle passes
through them; but its two triangles `v v₂ v₃` and `v v₃ v₄` at the cycle edge `v v₃` differ, and a
triangle through `v₂ v₄` would have to equal both. -/
theorem IsSurfaceSphere.not_crossing_of {L : Finset (Finset V)} (hS : IsSurfaceSphere L)
    {v v₁ v₂ v₃ v₄ : V} (h12 : ({v, v₁, v₂} : Finset V) ∈ L) (h23 : ({v, v₂, v₃} : Finset V) ∈ L)
    (h34 : ({v, v₃, v₄} : Finset V) ∈ L) (h14 : v₁ ≠ v₄)
    (e13 : ({v₁, v₃} : Finset V) ∈ edges2 L) (e24 : ({v₂, v₄} : Finset V) ∈ edges2 L) : False := by
  obtain ⟨hv1, hv2, h12'⟩ := tri_ne (hS.card _ h12)
  obtain ⟨-, hv3, h23'⟩ := tri_ne (hS.card _ h23)
  obtain ⟨-, hv4, h34'⟩ := tri_ne (hS.card _ h34)
  have h13 : v₁ ≠ v₃ := ne_of_mem_edges2 e13
  have h24 : v₂ ≠ v₄ := ne_of_mem_edges2 e24
  have ev1 : ({v, v₁} : Finset V) ∈ edges2 L :=
    mem_edges2.mpr ⟨_, h12, pair_subset_of_mem (by simp) (by simp), card_pair hv1⟩
  have ev3 : ({v, v₃} : Finset V) ∈ edges2 L :=
    mem_edges2.mpr ⟨_, h23, pair_subset_of_mem (by simp) (by simp), card_pair hv3⟩
  have mv : v ∈ verts2 L := mem_verts2.mpr ⟨_, h12, by simp⟩
  have mv1 : v₁ ∈ verts2 L := mem_verts2.mpr ⟨_, h12, by simp⟩
  have mv3 : v₃ ∈ verts2 L := mem_verts2.mpr ⟨_, h23, by simp⟩
  -- the cycle `v v₁ v₃` as a 1-chain
  let c : edges2 L → K := Pi.single ⟨_, ev1⟩ 1 + Pi.single ⟨_, e13⟩ 1 + Pi.single ⟨_, ev3⟩ 1
  have hc : bd1 K L c = 0 := by
    simp only [c, map_add, bd1_single_pair hv1 ev1 mv mv1, bd1_single_pair h13 e13 mv1 mv3,
      bd1_single_pair hv3 ev3 mv mv3]
    calc _ = (Pi.single ⟨v, mv⟩ (1 : K) + Pi.single ⟨v, mv⟩ 1) +
          (Pi.single ⟨v₁, mv1⟩ 1 + Pi.single ⟨v₁, mv1⟩ 1) +
          (Pi.single ⟨v₃, mv3⟩ 1 + Pi.single ⟨v₃, mv3⟩ 1 : verts2 L → K) := by abel
      _ = 0 := by rw [single_add_self, single_add_self, single_add_self, add_zero, add_zero]
  obtain ⟨σ, hσ⟩ := hS.exists_bd2_eq hc
  -- the boundary vanishes on every edge through a vertex off the cycle
  have hzero : ∀ u, u ≠ v → u ≠ v₁ → u ≠ v₃ → ∀ e : edges2 L, u ∈ (e : Finset V) →
      bd2 K L σ e = 0 := by
    intro u hu hu1 hu3 e he
    rw [hσ]
    simp only [c, Pi.add_apply]
    rw [Pi.single_eq_of_ne (edge_ne he ev1 hu hu1), Pi.single_eq_of_ne (edge_ne he e13 hu1 hu3),
      Pi.single_eq_of_ne (edge_ne he ev3 hu hu3)]
    simp
  -- the boundary is `1` on the cycle edge `v v₃`
  have h1 : bd2 K L σ ⟨_, ev3⟩ = 1 := by
    rw [hσ]
    simp only [c, Pi.add_apply]
    rw [Pi.single_eq_of_ne (edge_ne (u := v₃) (by simp) ev1 hv3.symm h13.symm),
      Pi.single_eq_of_ne (edge_ne (u := v) (by simp) e13 hv1 hv3)]
    simp
  let T23 : L := ⟨_, h23⟩
  let T34 : L := ⟨_, h34⟩
  have hne : T23 ≠ T34 := by
    intro h
    have h' : ({v, v₂, v₃} : Finset V) = {v, v₃, v₄} := congrArg Subtype.val h
    have hm : v₂ ∈ ({v, v₃, v₄} : Finset V) := by
      rw [← h']
      simp
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with hm | hm | hm
    exacts [hv2 hm.symm, h23' hm, h24 hm]
  have hsum := add_eq_one_of_bd2_eq_one hS.closed h1 hne
    (pair_subset_of_mem (by simp [T23]) (by simp [T23]))
    (pair_subset_of_mem (by simp [T34]) (by simp [T34]))
  obtain ⟨T, hT, hsub, -⟩ := mem_edges2.mp e24
  have a2 := const_around hS (hzero v₂ hv2.symm h12'.symm h23') (τ := ⟨T, hT⟩) (τ' := T23)
    (hsub (by simp)) (by simp [T23])
  have a4 := const_around hS (hzero v₄ hv4.symm h14.symm h34'.symm) (τ := ⟨T, hT⟩) (τ' := T34)
    (hsub (by simp)) (by simp [T34])
  rw [← a2, ← a4, CharTwo.add_self_eq_zero] at hsum
  exact zero_ne_one hsum

/-- **The crossing lemma** (coefficients `ℤ/2`): around a vertex of a triangulated 2-sphere, two
interleaved diagonals of its link are not both edges. -/
theorem IsSurfaceSphere.not_crossing {L : Finset (Finset V)} (hS : IsSurfaceSphere L)
    {v v₁ v₂ v₃ v₄ : V} (h12 : ({v, v₁, v₂} : Finset V) ∈ L) (h23 : ({v, v₂, v₃} : Finset V) ∈ L)
    (h34 : ({v, v₃, v₄} : Finset V) ∈ L) (h14 : v₁ ≠ v₄)
    (e13 : ({v₁, v₃} : Finset V) ∈ edges2 L) (e24 : ({v₂, v₄} : Finset V) ∈ edges2 L) : False :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  hS.not_crossing_of (K := ZMod 2) h12 h23 h34 h14 e13 e24

end Lightlike.PR
