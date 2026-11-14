import Lightlike.Surfaces.Check
import Lightlike.Surfaces.Homology

/-!
# Connected sums

The **connected sum** `csum L σ P τ₀ f` removes the triangle `σ` from `L` and the triangle `τ₀` from
a piece `P` with natural-number labels, and glues the rest of `P`, placed in `V` by the embedding
`f`, along the boundary of `σ`. The gluing conditions (`IsGlue`): `f` sends `τ₀` onto `σ` and the
other vertices of `P` outside `L`.

* `euler2_csum`: `χ(L # P) = χ(L) + χ(P) − 2` for closed `L` and `P`.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- The **connected sum** of `L` (at its triangle `σ`) and the piece `P` (at its triangle `τ₀`),
the piece placed in `V` by `f`. -/
def csum (L : Finset (Finset V)) (σ : Finset V) (P : Finset (Finset ℕ)) (τ₀ : Finset ℕ)
    (f : ℕ ↪ V) : Finset (Finset V) :=
  L.erase σ ∪ liftK f (P.erase τ₀)

/-- The **gluing conditions** for a connected sum: `σ` and `τ₀` are triangles, `f` sends `τ₀` onto
`σ`, and the other vertices of `P` outside `L`. -/
structure IsGlue (L : Finset (Finset V)) (σ : Finset V) (P : Finset (Finset ℕ)) (τ₀ : Finset ℕ)
    (f : ℕ ↪ V) : Prop where
  mem : σ ∈ L
  mem₀ : τ₀ ∈ P
  map : τ₀.map f = σ
  fresh : ∀ n ∈ verts2 P, n ∉ τ₀ → f n ∉ verts2 L

/-! ## Vertices and edges -/

section closed

variable {W : Type*} [DecidableEq W]

/-- In a closed complex, every vertex and every edge of a triangle `σ` lies in another triangle. -/
lemma exists_other_tri {L : Finset (Finset W)} (hc : IsClosed2 L) {σ : Finset W}
    (hσ : σ ∈ L) {e : Finset W} (he : e ⊆ σ) (he2 : #e = 2) : ∃ t ∈ L, t ≠ σ ∧ e ⊆ t := by
  have hm : e ∈ edges2 L := mem_edges2.mpr ⟨σ, hσ, he, he2⟩
  obtain ⟨t₁, ht₁, t₂, ht₂, hne, hf⟩ := two_tris hc hm
  have h1 : t₁ ∈ L.filter (e ⊆ ·) := by rw [hf]; simp
  have h2 : t₂ ∈ L.filter (e ⊆ ·) := by rw [hf]; simp
  by_cases h : t₁ = σ
  · exact ⟨t₂, ht₂, fun h' => hne (h.trans h'.symm), (mem_filter.mp h2).2⟩
  · exact ⟨t₁, ht₁, h, (mem_filter.mp h1).2⟩

lemma edges2_erase {L : Finset (Finset W)} (hc : IsClosed2 L) {σ : Finset W}
    (hσ : σ ∈ L) : edges2 (L.erase σ) = edges2 L := by
  ext e
  simp only [mem_edges2, mem_erase]
  constructor
  · rintro ⟨t, ⟨-, ht⟩, hs, hc2⟩
    exact ⟨t, ht, hs, hc2⟩
  · rintro ⟨t, ht, hs, hc2⟩
    by_cases h : t = σ
    · subst h
      obtain ⟨t', ht', hne, hs'⟩ := exists_other_tri hc ht hs hc2
      exact ⟨t', ⟨hne, ht'⟩, hs', hc2⟩
    · exact ⟨t, ⟨h, ht⟩, hs, hc2⟩

lemma verts2_erase {L : Finset (Finset W)} (hc : IsClosed2 L) (hT : IsTri2 L) {σ : Finset W}
    (hσ : σ ∈ L) : verts2 (L.erase σ) = verts2 L := by
  ext x
  simp only [mem_verts2, mem_erase]
  constructor
  · rintro ⟨t, ⟨-, ht⟩, hx⟩
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    by_cases h : t = σ
    · subst h
      obtain ⟨y, hy, hyx⟩ := exists_other (hT t ht) x
      obtain ⟨t', ht', hne, hs'⟩ := exists_other_tri hc ht (pair_subset_of_mem hx hy)
        (card_pair hyx.symm)
      exact ⟨t', ⟨hne, ht'⟩, hs' (by simp)⟩
    · exact ⟨t, ⟨h, ht⟩, hx⟩

end closed

lemma verts2_liftK (f : ℕ ↪ V) (K : Finset (Finset ℕ)) :
    verts2 (liftK f K) = (verts2 K).map f := by
  ext x
  simp only [mem_verts2, mem_liftK, mem_map]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hx⟩
    obtain ⟨n, hn, rfl⟩ := mem_map.mp hx
    exact ⟨n, ⟨t, ht, hn⟩, rfl⟩
  · rintro ⟨n, ⟨t, ht, hn⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, mem_map_of_mem f hn⟩

lemma edges2_liftK (f : ℕ ↪ V) (K : Finset (Finset ℕ)) :
    edges2 (liftK f K) = (edges2 K).image (Finset.map f) := by
  ext e
  simp only [mem_edges2, mem_liftK, mem_image]
  constructor
  · rintro ⟨s, ⟨t, ht, rfl⟩, hs, hc⟩
    refine ⟨t.filter (f · ∈ e), ⟨t, ht, filter_subset _ _, ?_⟩, ?_⟩
    · rw [← hc, ← card_map f]
      congr 1
      ext y
      simp only [mem_map, mem_filter]
      constructor
      · rintro ⟨n, ⟨-, hn⟩, rfl⟩
        exact hn
      · intro hy
        obtain ⟨n, hn, rfl⟩ := mem_map.mp (hs hy)
        exact ⟨n, ⟨hn, hy⟩, rfl⟩
    · ext y
      simp only [mem_map, mem_filter]
      constructor
      · rintro ⟨n, ⟨-, hn⟩, rfl⟩
        exact hn
      · intro hy
        obtain ⟨n, hn, rfl⟩ := mem_map.mp (hs hy)
        exact ⟨n, ⟨hn, hy⟩, rfl⟩
  · rintro ⟨e', ⟨t, ht, hs, hc⟩, rfl⟩
    exact ⟨t.map f, ⟨t, ht, rfl⟩, map_subset_map.mpr hs, by rw [card_map, hc]⟩

lemma verts2_csum {L : Finset (Finset V)} {σ : Finset V} {P : Finset (Finset ℕ)}
    {τ₀ : Finset ℕ} {f : ℕ ↪ V} (hLc : IsClosed2 L) (hLt : IsTri2 L) (hPc : IsClosed2 P)
    (hPt : IsTri2 P) (hg : IsGlue L σ P τ₀ f) :
    verts2 (csum L σ P τ₀ f) = verts2 L ∪ (verts2 P).map f := by
  rw [csum, verts2_union, verts2_erase hLc hLt hg.mem, verts2_liftK,
    verts2_erase hPc hPt hg.mem₀]

/-! ## The Euler characteristic of a connected sum -/

/-- **The Euler characteristic of a connected sum**: `χ(L # P) = χ(L) + χ(P) − 2`. -/
theorem euler2_csum {L : Finset (Finset V)} {σ : Finset V} {P : Finset (Finset ℕ)}
    {τ₀ : Finset ℕ} {f : ℕ ↪ V} (hLc : IsClosed2 L) (hLt : IsTri2 L) (hPc : IsClosed2 P)
    (hPt : IsTri2 P) (hg : IsGlue L σ P τ₀ f) :
    euler2 (csum L σ P τ₀ f) = euler2 L + euler2 P - 2 := by
  have hσ3 : #σ = 3 := hLt σ hg.mem
  have hτ3 : #τ₀ = 3 := hPt τ₀ hg.mem₀
  -- points of `P` that land in `L` come from `τ₀`
  have hland : ∀ n ∈ verts2 P, f n ∈ verts2 L → n ∈ τ₀ := fun n hn hL => by
    by_contra h
    exact hg.fresh n hn h hL
  have hτP : τ₀ ⊆ verts2 P := fun n hn => mem_verts2.mpr ⟨τ₀, hg.mem₀, hn⟩
  have hσL : σ ⊆ verts2 L := fun x hx => mem_verts2.mpr ⟨σ, hg.mem, hx⟩
  -- vertices
  have hV : verts2 (csum L σ P τ₀ f) = verts2 L ∪ (verts2 P).map f := by
    rw [csum, verts2_union, verts2_erase hLc hLt hg.mem, verts2_liftK,
      verts2_erase hPc hPt hg.mem₀]
  have hVi : verts2 L ∩ (verts2 P).map f = σ := by
    ext x
    simp only [mem_inter, mem_map]
    constructor
    · rintro ⟨hx, n, hn, rfl⟩
      rw [← hg.map]
      exact mem_map_of_mem f (hland n hn hx)
    · intro hx
      refine ⟨hσL hx, ?_⟩
      rw [← hg.map] at hx
      obtain ⟨n, hn, rfl⟩ := mem_map.mp hx
      exact ⟨n, hτP hn, rfl⟩
  -- edges
  have hE : edges2 (csum L σ P τ₀ f) = edges2 L ∪ (edges2 P).image (Finset.map f) := by
    rw [csum, edges2, union_biUnion, ← edges2, ← edges2, edges2_erase hLc hg.mem,
      edges2_liftK, edges2_erase hPc hg.mem₀]
  have hEi : edges2 L ∩ (edges2 P).image (Finset.map f) = σ.powersetCard 2 := by
    ext e
    simp only [mem_inter, mem_image, mem_powersetCard]
    constructor
    · rintro ⟨he, e', he', rfl⟩
      obtain ⟨t, ht, hs, hc⟩ := mem_edges2.mp he'
      refine ⟨?_, by rw [card_map, hc]⟩
      rw [← hg.map]
      refine map_subset_map.mpr fun n hn => hland n (mem_verts2.mpr ⟨t, ht, hs hn⟩) ?_
      obtain ⟨u, hu, hsu, -⟩ := mem_edges2.mp he
      exact mem_verts2.mpr ⟨u, hu, hsu (mem_map_of_mem f hn)⟩
    · rintro ⟨hs, hc⟩
      refine ⟨mem_edges2.mpr ⟨σ, hg.mem, hs, hc⟩, τ₀.filter (f · ∈ e), ?_, ?_⟩
      · refine mem_edges2.mpr ⟨τ₀, hg.mem₀, filter_subset _ _, ?_⟩
        rw [← hc, ← card_map f]
        congr 1
        ext y
        simp only [mem_map, mem_filter]
        constructor
        · rintro ⟨n, ⟨-, hn⟩, rfl⟩
          exact hn
        · intro hy
          have : y ∈ τ₀.map f := hg.map ▸ hs hy
          obtain ⟨n, hn, rfl⟩ := mem_map.mp this
          exact ⟨n, ⟨hn, hy⟩, rfl⟩
      · ext y
        simp only [mem_map, mem_filter]
        constructor
        · rintro ⟨n, ⟨-, hn⟩, rfl⟩
          exact hn
        · intro hy
          have : y ∈ τ₀.map f := hg.map ▸ hs hy
          obtain ⟨n, hn, rfl⟩ := mem_map.mp this
          exact ⟨n, ⟨hn, hy⟩, rfl⟩
  -- triangles
  have hF : #(csum L σ P τ₀ f) = (#L - 1) + (#P - 1) := by
    rw [csum, card_union_of_disjoint, card_erase_of_mem hg.mem, liftK,
      card_image_of_injective _ (map_injective f), card_erase_of_mem hg.mem₀]
    rw [disjoint_left]
    intro t ht ht'
    obtain ⟨u, hu, rfl⟩ := mem_liftK.mp ht'
    obtain ⟨hne, htL⟩ := mem_erase.mp ht
    obtain ⟨hu0, huP⟩ := mem_erase.mp hu
    apply hne
    have hsub : u ⊆ τ₀ := fun n hn =>
      hland n (mem_verts2.mpr ⟨u, huP, hn⟩) (mem_verts2.mpr ⟨_, htL, mem_map_of_mem f hn⟩)
    have : u = τ₀ := eq_of_subset_of_card_le hsub (by rw [hτ3, hPt u huP])
    rw [this, hg.map]
  have hL1 : 1 ≤ #L := card_pos.mpr ⟨σ, hg.mem⟩
  have hP1 : 1 ≤ #P := card_pos.mpr ⟨τ₀, hg.mem₀⟩
  have cV := card_union_add_card_inter (verts2 L) ((verts2 P).map f)
  have cE := card_union_add_card_inter (edges2 L) ((edges2 P).image (Finset.map f))
  rw [hVi, hσ3, card_map] at cV
  rw [hEi, card_powersetCard, hσ3, card_image_of_injective _ (map_injective f)] at cE
  simp only [euler2, hV, hE, hF]
  push_cast [hL1, hP1, Nat.cast_sub]
  norm_num at cE
  omega

/-! ## Orientations of a connected sum -/

open Classical in
/-- An orientation of a piece, placed in `V` by `f` (`0` off the image of `f`). -/
noncomputable def pushO (f : ℕ ↪ V) (o : ℕ → ℕ → ℕ → ℤ) (x y z : V) : ℤ :=
  if x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f then
    o (Function.invFun f x) (Function.invFun f y) (Function.invFun f z) else 0

section push

variable {f : ℕ ↪ V} {o : ℕ → ℕ → ℕ → ℤ}

omit [DecidableEq V] in
lemma pushO_apply (a b c : ℕ) : pushO f o (f a) (f b) (f c) = o a b c := by
  simp only [pushO, Set.mem_range_self, and_self, ite_true,
    Function.leftInverse_invFun f.injective a, Function.leftInverse_invFun f.injective b,
    Function.leftInverse_invFun f.injective c]

omit [DecidableEq V] in
lemma pushO_eq_zero {x y z : V}
    (h : ¬ (x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f)) : pushO f o x y z = 0 := by
  simp only [pushO, h, ite_false]

omit [DecidableEq V] in
lemma pushO_rot (hrot : ∀ x y z, o y z x = o x y z) (x y z : V) :
    pushO f o y z x = pushO f o x y z := by
  by_cases h : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [pushO_apply, pushO_apply, hrot]
  · rw [pushO_eq_zero h, pushO_eq_zero (by tauto)]

omit [DecidableEq V] in
lemma pushO_swap (hswap : ∀ x y z, o y x z = - o x y z) (x y z : V) :
    pushO f o y x z = - pushO f o x y z := by
  by_cases h : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
  · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [pushO_apply, pushO_apply, hswap]
  · rw [pushO_eq_zero h, pushO_eq_zero (by tauto), neg_zero]

lemma otri_map (a b c x y z : ℕ) :
    otri (f a) (f b) (f c) (f x) (f y) (f z) = otri a b c x y z := by
  simp only [otri, ind, f.injective.eq_iff]

end push

lemma tri_map (f : ℕ ↪ V) (a b c : ℕ) : ({a, b, c} : Finset ℕ).map f = {f a, f b, f c} := by simp

/-- **A connected sum of orientable closed surfaces is orientable**, for any gluing (the piece's
orientation is reversed if necessary). -/
theorem isOrientable_csum {L : Finset (Finset V)} {σ : Finset V} {P : Finset (Finset ℕ)}
    {τ₀ : Finset ℕ} {f : ℕ ↪ V} (hLc : IsClosed2 L) (hLt : IsTri2 L) (hPc : IsClosed2 P)
    (hPt : IsTri2 P) (hg : IsGlue L σ P τ₀ f) (hL : IsOrientable L) (hP : IsOrientable P) :
    IsOrientable (csum L σ P τ₀ f) := by
  obtain ⟨oL, hoL⟩ := hL
  obtain ⟨oP, hoP⟩ := hP
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp (hPt τ₀ hg.mem₀)
  have hσ : σ = {f p, f q, f r} := by rw [← hg.map, tri_map]
  have fpq : f p ≠ f q := f.injective.ne hpq
  have fpr : f p ≠ f r := f.injective.ne hpr
  have fqr : f q ≠ f r := f.injective.ne hqr
  set sL := oL (f p) (f q) (f r) with hsL_def
  set sP := oP p q r with hsP_def
  have hsL : sL = 1 ∨ sL = -1 := hoL.unit _ _ _ (hσ ▸ hg.mem)
  have hsP : sP = 1 ∨ sP = -1 := hoP.unit p q r hg.mem₀
  set ε := -sL * sP with hε_def
  have hε : ε * sP = -sL := by
    rw [hε_def]
    rcases hsP with h | h <;> rw [h] <;> ring
  have hεu : ε = 1 ∨ ε = -1 := by
    rw [hε_def]
    rcases hsL with h | h <;> rcases hsP with h' | h' <;> rw [h, h'] <;> norm_num
  -- vertices of `P` landing in `L` come from `τ₀`
  have hland : ∀ n ∈ verts2 P, f n ∈ verts2 L → n ∈ ({p, q, r} : Finset ℕ) := fun n hn hL => by
    by_contra h
    exact hg.fresh n hn h hL
  -- a triangle of `L` with vertices in the image of `P` is `σ`
  have hLP : ∀ {a b c : ℕ}, ({f a, f b, f c} : Finset V) ∈ L → ({a, b, c} : Finset ℕ) ∈ P →
      ({f a, f b, f c} : Finset V) = σ := by
    intro a b c hL hP
    have hsub : ({a, b, c} : Finset ℕ) ⊆ {p, q, r} := by
      intro n hn
      refine hland n (mem_verts2.mpr ⟨_, hP, hn⟩) (mem_verts2.mpr ⟨_, hL, ?_⟩)
      rw [← tri_map]
      exact mem_map_of_mem f hn
    have : ({a, b, c} : Finset ℕ) = {p, q, r} :=
      eq_of_subset_of_card_le hsub (by rw [hPt _ hP, hPt _ hg.mem₀])
    rw [← tri_map, this, tri_map, hσ]
  let oC : V → V → V → ℤ := fun x y z => oL x y z - sL * otri (f p) (f q) (f r) x y z +
    ε * (pushO f oP x y z - sP * otri (f p) (f q) (f r) x y z)
  refine ⟨oC, fun x y z => ?_, fun x y z => ?_, fun x y z h => ?_, fun x y z h => ?_,
    fun u v => ?_⟩
  · simp only [oC]
    rw [hoL.rot, otri_rot, pushO_rot hoP.rot, otri_rot]
  · simp only [oC]
    rw [hoL.swap, otri_swap, pushO_swap hoP.swap, otri_swap]
    ring
  · simp only [oC] at h
    by_cases hs : ({x, y, z} : Finset V) = σ
    · exfalso
      apply h
      rw [hσ] at hs
      rw [hoL.perm fpq fpr fqr hs]
      have hx : x ∈ Set.range f := by
        have : x ∈ ({f p, f q, f r} : Finset V) := hs ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl <;> exact Set.mem_range_self _
      have hy : y ∈ Set.range f := by
        have : y ∈ ({f p, f q, f r} : Finset V) := hs ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl <;> exact Set.mem_range_self _
      have hz : z ∈ Set.range f := by
        have : z ∈ ({f p, f q, f r} : Finset V) := hs ▸ by simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with rfl | rfl | rfl <;> exact Set.mem_range_self _
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      obtain ⟨c, rfl⟩ := hz
      have hs' : ({a, b, c} : Finset ℕ) = {p, q, r} := by
        apply map_injective f
        rw [tri_map, tri_map, hs]
      rw [pushO_apply, hoP.perm hpq hpr hqr hs', otri_map]
      ring
    · rw [otri_eq_zero (hσ ▸ hs)] at h
      simp only [mul_zero, sub_zero] at h
      by_cases hoxyz : oL x y z = 0
      · rw [hoxyz, zero_add] at h
        have hpz : pushO f oP x y z ≠ 0 := fun h' => h (by rw [h', mul_zero])
        by_cases hr : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
        · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := hr
          rw [pushO_apply] at hpz
          have hP' := hoP.supp a b c hpz
          have hne : ({a, b, c} : Finset ℕ) ≠ {p, q, r} := fun e => hs (by rw [← tri_map, e,
            tri_map, hσ])
          refine mem_union_right _ (mem_liftK.mpr ⟨_, mem_erase.mpr ⟨hne, hP'⟩, tri_map f a b c⟩)
        · exact absurd (pushO_eq_zero hr) hpz
      · exact mem_union_left _ (mem_erase.mpr ⟨hs, hoL.supp x y z hoxyz⟩)
  · simp only [oC]
    have hmem : ∀ {x a b c : V}, x ∈ ({a, b, c} : Finset V) → x = a ∨ x = b ∨ x = c := by
      intro x a b c hx
      simpa using hx
    rcases mem_union.mp h with h | h
    · obtain ⟨hs, hL⟩ := mem_erase.mp h
      have hpz : pushO f oP x y z = 0 := by
        by_cases hr : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
        · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := hr
          rw [pushO_apply]
          exact hoP.eq_zero_of_notMem fun hP' => hs (hLP hL hP')
        · exact pushO_eq_zero hr
      rw [otri_eq_zero (hσ ▸ hs), hpz]
      simpa using hoL.unit x y z hL
    · obtain ⟨t, ht, he⟩ := mem_liftK.mp h
      obtain ⟨htne, htP⟩ := mem_erase.mp ht
      have hr : ∀ {w : V}, w ∈ ({x, y, z} : Finset V) → w ∈ Set.range f := by
        intro w hw
        rw [← he] at hw
        obtain ⟨n, -, rfl⟩ := mem_map.mp hw
        exact Set.mem_range_self n
      obtain ⟨a, rfl⟩ := hr (show x ∈ ({x, y, z} : Finset V) by simp)
      obtain ⟨b, rfl⟩ := hr (show y ∈ ({f a, y, z} : Finset V) by simp)
      obtain ⟨c, rfl⟩ := hr (show z ∈ ({f a, f b, z} : Finset V) by simp)
      have hte : t = {a, b, c} := by
        apply map_injective f
        rw [he, tri_map]
      subst hte
      have hs : ({f a, f b, f c} : Finset V) ≠ σ := fun e => htne (by
        apply map_injective f
        rw [tri_map, tri_map, e, hσ])
      have hoL0 : oL (f a) (f b) (f c) = 0 :=
        hoL.eq_zero_of_notMem fun hL => hs (hLP hL htP)
      rw [hoL0, otri_eq_zero (hσ ▸ hs), pushO_apply]
      rcases hoP.unit a b c htP with h' | h' <;> rw [h'] <;> rcases hεu with h'' | h'' <;>
        rw [h''] <;> norm_num
  · have hV := verts2_csum hLc hLt hPc hPt hg
    set S := verts2 (csum L σ P ({p, q, r} : Finset ℕ) f) with hS
    have hσS : ∀ w ∈ σ, w ∈ S := fun w hw => by
      rw [hV]; exact mem_union_left _ (mem_verts2.mpr ⟨σ, hg.mem, hw⟩)
    have e1 : ∑ w ∈ S, oL u v w = 0 := by
      rw [← sum_subset (show verts2 L ⊆ S by rw [hV]; exact subset_union_left)
        (fun w _ hw => hoL.eq_zero_of_notMem_verts hw)]
      exact hoL.cycle u v
    have e2 : ∑ w ∈ S, otri (f p) (f q) (f r) u v w =
        edir (f p) (f q) u v + edir (f q) (f r) u v + edir (f r) (f p) u v :=
      sum_otri (hσS _ (by simp [hσ])) (hσS _ (by simp [hσ])) (hσS _ (by simp [hσ])) u v
    have e3 : ∑ w ∈ S, pushO f oP u v w = 0 := by
      by_cases huv : u ∈ Set.range f ∧ v ∈ Set.range f
      · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := huv
        rw [← sum_subset (show (verts2 P).map f ⊆ S by rw [hV]; exact subset_union_right)
          (fun w _ hw => ?_), sum_map]
        · simp only [pushO_apply]
          exact hoP.cycle a b
        · by_cases hw' : w ∈ Set.range f
          · obtain ⟨n, rfl⟩ := hw'
            rw [pushO_apply]
            exact hoP.eq_zero_of_notMem_verts fun hn => hw (mem_map_of_mem f hn)
          · exact pushO_eq_zero (by tauto)
      · exact sum_eq_zero fun w _ => pushO_eq_zero (by tauto)
    simp only [oC]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, ← mul_sum, e1,
      e2, e3]
    linear_combination (-(edir (f p) (f q) u v + edir (f q) (f r) u v + edir (f r) (f p) u v)) * hε

/-! ## A connected sum of closed complexes is closed -/

section closedSum

variable {L : Finset (Finset V)} {σ : Finset V} {P : Finset (Finset ℕ)} {τ₀ : Finset ℕ}
  {f : ℕ ↪ V}

lemma IsGlue.land (hg : IsGlue L σ P τ₀ f) {n : ℕ} (hn : n ∈ verts2 P) (hL : f n ∈ verts2 L) :
    n ∈ τ₀ := by
  by_contra h
  exact hg.fresh n hn h hL

/-- A triangle of the piece whose image lies in `L` is the gluing triangle. -/
lemma IsGlue.sub_of_mem (hg : IsGlue L σ P τ₀ f) {t : Finset ℕ} (ht : t ∈ P)
    (hL : ∀ n ∈ t, f n ∈ verts2 L) : t ⊆ τ₀ :=
  fun n hn => hg.land (mem_verts2.mpr ⟨t, ht, hn⟩) (hL n hn)

/-- A connected sum of two complexes of triangles is a complex of triangles. -/
theorem isTri2_csum (hLt : IsTri2 L) (hPt : IsTri2 P) : IsTri2 (csum L σ P τ₀ f) := by
  intro t ht
  rcases mem_union.mp ht with ht | ht
  · exact hLt t (mem_of_mem_erase ht)
  · obtain ⟨u, hu, rfl⟩ := mem_liftK.mp ht
    rw [card_map]
    exact hPt u (mem_of_mem_erase hu)

/-- **A connected sum of closed complexes is closed**: an edge of the gluing triangle keeps one
triangle on each side, the other edges keep both of theirs. -/
theorem isClosed2_csum (hLc : IsClosed2 L) (hPc : IsClosed2 P)
    (hPt : IsTri2 P) (hg : IsGlue L σ P τ₀ f) : IsClosed2 (csum L σ P τ₀ f) := by
  intro e he
  -- the triangles of the two parts at `e`
  have hdisj : Disjoint ((L.erase σ).filter (e ⊆ ·)) ((liftK f (P.erase τ₀)).filter (e ⊆ ·)) := by
    rw [disjoint_left]
    intro t ht ht'
    obtain ⟨htL, -⟩ := mem_filter.mp ht
    obtain ⟨htB, -⟩ := mem_filter.mp ht'
    obtain ⟨u, hu, rfl⟩ := mem_liftK.mp htB
    obtain ⟨hne, htL⟩ := mem_erase.mp htL
    obtain ⟨hu0, huP⟩ := mem_erase.mp hu
    have hsub := hg.sub_of_mem huP fun n hn => mem_verts2.mpr ⟨_, htL, mem_map_of_mem f hn⟩
    have : u = τ₀ := eq_of_subset_of_card_le hsub (by rw [hPt _ hg.mem₀, hPt u huP])
    exact hne (by rw [this, hg.map])
  have hsplit : (csum L σ P τ₀ f).filter (e ⊆ ·) =
      (L.erase σ).filter (e ⊆ ·) ∪ (liftK f (P.erase τ₀)).filter (e ⊆ ·) := filter_union _ _ _
  rw [hsplit, card_union_of_disjoint hdisj]
  -- the count on the side of `L`
  have cL : #((L.erase σ).filter (e ⊆ ·)) = #(L.filter (e ⊆ ·)) - if e ⊆ σ then 1 else 0 := by
    rw [filter_erase]
    split_ifs with h
    · rw [card_erase_of_mem (mem_filter.mpr ⟨hg.mem, h⟩)]
    · rw [erase_eq_of_notMem (fun h' => h (mem_filter.mp h').2), Nat.sub_zero]
  -- the count on the side of the piece, through the preimage of `e`
  have cP : ∀ e' : Finset ℕ, e = e'.map f →
      #((liftK f (P.erase τ₀)).filter (e ⊆ ·)) = #(P.filter (e' ⊆ ·)) -
        if e' ⊆ τ₀ then 1 else 0 := by
    rintro e' rfl
    have : (liftK f (P.erase τ₀)).filter (e'.map f ⊆ ·) =
        ((P.erase τ₀).filter (e' ⊆ ·)).image (Finset.map f) := by
      ext t
      simp only [mem_filter, mem_liftK, mem_image]
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hs⟩
        exact ⟨u, ⟨hu, (map_subset_map (f := f)).mp hs⟩, rfl⟩
      · rintro ⟨u, ⟨hu, hs⟩, rfl⟩
        exact ⟨⟨u, hu, rfl⟩, (map_subset_map (f := f)).mpr hs⟩
    rw [this, card_image_of_injective _ (map_injective f), filter_erase]
    split_ifs with h
    · rw [card_erase_of_mem (mem_filter.mpr ⟨hg.mem₀, h⟩)]
    · rw [erase_eq_of_notMem (fun h' => h (mem_filter.mp h').2), Nat.sub_zero]
  rw [edges2, csum, union_biUnion, ← edges2, ← edges2, edges2_erase hLc hg.mem, edges2_liftK,
    edges2_erase hPc hg.mem₀, mem_union] at he
  by_cases heL : e ∈ edges2 L
  · have he := heL
    by_cases heP : ∃ e', e' ∈ edges2 P ∧ e'.map f = e
    · -- an edge of the gluing triangle
      obtain ⟨e', he', rfl⟩ := heP
      obtain ⟨t, ht, hs, hc⟩ := mem_edges2.mp he'
      have he'τ : e' ⊆ τ₀ := fun n hn => hg.land (mem_verts2.mpr ⟨t, ht, hs hn⟩) (by
        obtain ⟨u, hu, hsu, -⟩ := mem_edges2.mp he
        exact mem_verts2.mpr ⟨u, hu, hsu (mem_map_of_mem f hn)⟩)
      have heσ : e'.map f ⊆ σ := by rw [← hg.map]; exact map_subset_map.mpr he'τ
      rw [cL, cP e' rfl, hLc _ he, hPc _ he']
      simp [heσ, he'τ]
    · have hP0 : (liftK f (P.erase τ₀)).filter (e ⊆ ·) = ∅ := by
        refine filter_eq_empty_iff.mpr fun t ht hs => heP ?_
        obtain ⟨u, hu, rfl⟩ := mem_liftK.mp ht
        refine ⟨u.filter (f · ∈ e), mem_edges2.mpr ⟨u, mem_of_mem_erase hu, filter_subset _ _, ?_⟩, ?_⟩
        · obtain ⟨_, _, _, hc⟩ := mem_edges2.mp he
          rw [← hc, ← card_map f]
          congr 1
          ext y
          simp only [mem_map, mem_filter]
          constructor
          · rintro ⟨n, ⟨-, hn⟩, rfl⟩; exact hn
          · intro hy
            obtain ⟨n, hn, rfl⟩ := mem_map.mp (hs hy)
            exact ⟨n, ⟨hn, hy⟩, rfl⟩
        · ext y
          simp only [mem_map, mem_filter]
          constructor
          · rintro ⟨n, ⟨-, hn⟩, rfl⟩; exact hn
          · intro hy
            obtain ⟨n, hn, rfl⟩ := mem_map.mp (hs hy)
            exact ⟨n, ⟨hn, hy⟩, rfl⟩
      have heσ : ¬ e ⊆ σ := fun h => heP (by
        rw [← hg.map] at h
        refine ⟨τ₀.filter (f · ∈ e), mem_edges2.mpr ⟨τ₀, hg.mem₀, filter_subset _ _, ?_⟩, ?_⟩
        · obtain ⟨_, _, _, hc⟩ := mem_edges2.mp he
          rw [← hc, ← card_map f]
          congr 1
          ext y
          simp only [mem_map, mem_filter]
          constructor
          · rintro ⟨n, ⟨-, hn⟩, rfl⟩; exact hn
          · intro hy
            obtain ⟨n, hn, rfl⟩ := mem_map.mp (h hy)
            exact ⟨n, ⟨hn, hy⟩, rfl⟩
        · ext y
          simp only [mem_map, mem_filter]
          constructor
          · rintro ⟨n, ⟨-, hn⟩, rfl⟩; exact hn
          · intro hy
            obtain ⟨n, hn, rfl⟩ := mem_map.mp (h hy)
            exact ⟨n, ⟨hn, hy⟩, rfl⟩)
      rw [hP0, card_empty, add_zero, cL, hLc _ he]
      simp [heσ]
  · have hei : e ∈ (edges2 P).image (Finset.map f) := he.resolve_left heL
    obtain ⟨e', he', rfl⟩ := mem_image.mp hei
    have he'τ : ¬ e' ⊆ τ₀ := by
      intro h
      apply heL
      obtain ⟨_, _, _, hc⟩ := mem_edges2.mp he'
      exact mem_edges2.mpr ⟨σ, hg.mem, by rw [← hg.map]; exact map_subset_map.mpr h,
        by rw [card_map, hc]⟩
    have hL0 : (L.erase σ).filter (e'.map f ⊆ ·) = ∅ := by
      refine filter_eq_empty_iff.mpr fun t ht hs => heL ?_
      obtain ⟨_, _, _, hc⟩ := mem_edges2.mp he'
      exact mem_edges2.mpr ⟨t, mem_of_mem_erase ht, hs, by rw [card_map, hc]⟩
    rw [hL0, card_empty, zero_add, cP e' rfl, hPc _ he']
    simp [he'τ]

end closedSum

end Lightlike.Surfaces
