import Lightlike.Surfaces.Basic

/-!
# Local structure of closed surfaces

The triangles at an edge and at a vertex whose link is a triangle, for closed surfaces
(`IsSurface`). These are the statements of `Lightlike/PonzanoRegge/SphereRecognition.lean` for
intrinsic 2-spheres, whose proofs use only that triangles have three vertices, that every edge lies
in two triangles and that vertex links are connected; they are restated here without the Euler
characteristic.

* `IsSurface.other_tri`, `IsSurface.tris_at_edge`: every edge lies in exactly two triangles.
* `IsSurface.link_triangle`: if the link of `v` contains a triangle, the three triangles are all
  the triangles at `v`.
* `IsSurface.flip_lowers`, `IsSurface.remove_deg3`, `IsSurface.eq_bdry`,
  `IsSurface.local_structure`: the steps of the degree-lowering argument.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- **The other triangle at an edge.** In a closed surface, the edge `vw` of a triangle
`{v, w, a}` lies in exactly one more triangle `{v, w, b}`, `b ≠ a`; there are no others. -/
lemma IsSurface.other_tri {L : Finset (Finset V)} (hS : IsSurface L) {v w a : V}
    (hτ : ({v, w, a} : Finset V) ∈ L) :
    ∃ b, b ≠ a ∧ b ≠ v ∧ b ≠ w ∧ ({v, w, b} : Finset V) ∈ L ∧
      ∀ τ ∈ L, ({v, w} : Finset V) ⊆ τ → τ = {v, w, a} ∨ τ = {v, w, b} := by
  obtain ⟨hvw, hva, hwa⟩ := tri_ne (hS.card _ hτ)
  have he : ({v, w} : Finset V) ∈ edges2 L :=
    mem_edges2.mpr ⟨_, hτ, pair_subset_of_mem (by simp) (by simp), card_pair hvw⟩
  obtain ⟨t₁, t₂, hne, hf⟩ := card_eq_two.mp (hS.closed _ he)
  have hmem : ∀ τ, τ ∈ L.filter (({v, w} : Finset V) ⊆ ·) ↔ τ ∈ L ∧ ({v, w} : Finset V) ⊆ τ :=
    fun τ => mem_filter
  have hτf : ({v, w, a} : Finset V) ∈ L.filter (({v, w} : Finset V) ⊆ ·) :=
    (hmem _).mpr ⟨hτ, pair_subset_of_mem (by simp) (by simp)⟩
  -- the triangle other than `{v, w, a}`
  obtain ⟨τ', hτ'f, hτ'ne⟩ : ∃ τ' ∈ L.filter (({v, w} : Finset V) ⊆ ·), τ' ≠ {v, w, a} := by
    rw [hf] at hτf ⊢
    simp only [mem_insert, mem_singleton] at hτf
    rcases hτf with h | h
    · exact ⟨t₂, by simp, fun h' => hne (h'.trans h).symm⟩
    · exact ⟨t₁, by simp, fun h' => hne (h'.trans h)⟩
  obtain ⟨hτ'L, hsub⟩ := (hmem _).mp hτ'f
  obtain ⟨b, hbv, hbw, rfl⟩ := eq_tri_of_mem (hS.card _ hτ'L) (hsub (by simp)) (hsub (by simp)) hvw
  have hba : b ≠ a := fun h => hτ'ne (by rw [h])
  refine ⟨b, hba, hbv, hbw, hτ'L, fun τ hτL hτs => ?_⟩
  have h2 : L.filter (({v, w} : Finset V) ⊆ ·) = {{v, w, a}, {v, w, b}} := by
    symm
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      exacts [hτf, hτ'f]
    · rw [hS.closed _ he, card_pair (Ne.symm hτ'ne)]
  have : τ ∈ L.filter (({v, w} : Finset V) ⊆ ·) := (hmem _).mpr ⟨hτL, hτs⟩
  rw [h2] at this
  simpa using this

/-- **The two triangles at an edge.** If `{v, w, x}` and `{v, w, y}` are triangles with `x ≠ y`,
every triangle containing `v` and `w` is one of them. -/
lemma IsSurface.tris_at_edge {L : Finset (Finset V)} (hS : IsSurface L) {v w x y : V}
    (hx : ({v, w, x} : Finset V) ∈ L) (hy : ({v, w, y} : Finset V) ∈ L) (hxy : x ≠ y) :
    ∀ τ ∈ L, ({v, w} : Finset V) ⊆ τ → τ = {v, w, x} ∨ τ = {v, w, y} := by
  obtain ⟨hvw, hvx, hwx⟩ := tri_ne (hS.card _ hx)
  have he : ({v, w} : Finset V) ∈ edges2 L :=
    mem_edges2.mpr ⟨_, hx, pair_subset_of_mem (by simp) (by simp), card_pair hvw⟩
  have hne : ({v, w, x} : Finset V) ≠ {v, w, y} :=
    ne_of_mem_notMem (y := x) (by simp) (by simp [hvx.symm, hwx.symm, hxy])
  have h2 : L.filter (({v, w} : Finset V) ⊆ ·) = {{v, w, x}, {v, w, y}} := by
    symm
    apply eq_of_subset_of_card_le
    · intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact mem_filter.mpr ⟨hx, pair_subset_of_mem (by simp) (by simp)⟩
      · exact mem_filter.mpr ⟨hy, pair_subset_of_mem (by simp) (by simp)⟩
    · rw [hS.closed _ he, card_pair hne]
  intro τ hτ hsub
  have : τ ∈ L.filter (({v, w} : Finset V) ⊆ ·) := mem_filter.mpr ⟨hτ, hsub⟩
  rw [h2] at this
  simpa using this

/-- **A vertex whose link is a triangle.** If `{v, a, b}`, `{v, b, c}` and `{v, c, a}` are
triangles of a closed surface, they are all the triangles at `v`: the link of `v` is
connected, and from each of `a, b, c` its two link edges lead back into `{a, b, c}`. -/
lemma IsSurface.link_triangle {L : Finset (Finset V)} (hS : IsSurface L)
    {v a b c : V} (hab : ({v, a, b} : Finset V) ∈ L) (hbc : ({v, b, c} : Finset V) ∈ L)
    (hca : ({v, c, a} : Finset V) ∈ L) :
    ∀ τ ∈ L, v ∈ τ → τ = {v, a, b} ∨ τ = {v, b, c} ∨ τ = {v, c, a} := by
  obtain ⟨hva, hvb, hab'⟩ := tri_ne (hS.card _ hab)
  obtain ⟨-, hvc, hbc'⟩ := tri_ne (hS.card _ hbc)
  have hac' : a ≠ c := (tri_ne (hS.card _ hca)).2.2.symm
  have hv : v ∈ verts2 L := mem_verts2.mpr ⟨_, hab, by simp⟩
  -- a link edge `{p, q}` at `v` is a triangle `{v, p, q}` with `p ≠ q`, both `≠ v`
  have lk : ∀ {p q : V}, ({p, q} : Finset V) ∈ lk2 L v →
      ({v, p, q} : Finset V) ∈ L ∧ p ≠ v ∧ q ≠ v ∧ p ≠ q := by
    intro p q h
    obtain ⟨hvpq, hT⟩ := mem_lk2.mp h
    obtain ⟨-, -, hpq⟩ := tri_ne (hS.card _ hT)
    simp only [mem_insert, mem_singleton, not_or] at hvpq
    exact ⟨hT, Ne.symm hvpq.1, Ne.symm hvpq.2, hpq⟩
  -- the link vertices reachable from `a` stay in `{a, b, c}`
  have closedS : ∀ {p q : V}, p = a ∨ p = b ∨ p = c → ({p, q} : Finset V) ∈ lk2 L v →
      q = a ∨ q = b ∨ q = c := by
    intro p q hp hpq
    obtain ⟨hT, -, hqv, hpq'⟩ := lk hpq
    rcases hp with rfl | rfl | rfl
    · rcases hS.tris_at_edge hab (show ({v, p, c} : Finset V) ∈ L by rw [tri_swap]; exact hca)
        hbc' _ hT (pair_subset_of_mem (by simp) (by simp)) with h | h
      · exact Or.inr (Or.inl (eq_of_tri_eq h hqv hpq'.symm))
      · exact Or.inr (Or.inr (eq_of_tri_eq h hqv hpq'.symm))
    · rcases hS.tris_at_edge (show ({v, p, a} : Finset V) ∈ L by rw [tri_swap]; exact hab) hbc
        hac' _ hT (pair_subset_of_mem (by simp) (by simp)) with h | h
      · exact Or.inl (eq_of_tri_eq h hqv hpq'.symm)
      · exact Or.inr (Or.inr (eq_of_tri_eq h hqv hpq'.symm))
    · rcases hS.tris_at_edge hca (show ({v, p, b} : Finset V) ∈ L by rw [tri_swap]; exact hbc)
        hab' _ hT (pair_subset_of_mem (by simp) (by simp)) with h | h
      · exact Or.inl (eq_of_tri_eq h hqv hpq'.symm)
      · exact Or.inr (Or.inl (eq_of_tri_eq h hqv hpq'.symm))
  have ha : a ∈ verts2 (lk2 L v) :=
    mem_verts2.mpr ⟨{a, b}, mem_lk2.mpr ⟨by simp [hva, hvb], hab⟩, by simp⟩
  have reach' : ∀ y, Relation.ReflTransGen (fun p q => ({p, q} : Finset V) ∈ lk2 L v) a y →
      y = a ∨ y = b ∨ y = c := by
    intro y path
    induction path with
    | refl => exact Or.inl rfl
    | tail _ hpq ih => exact closedS ih hpq
  have reach : ∀ y ∈ verts2 (lk2 L v), y = a ∨ y = b ∨ y = c :=
    fun y hy => reach' y (hS.link v hv a ha y hy)
  intro τ hτ hvτ
  obtain ⟨p, hp, hpv⟩ := exists_other (hS.card τ hτ) v
  obtain ⟨q, hqv, hqp, rfl⟩ := eq_tri_of_mem (hS.card τ hτ) hvτ hp hpv.symm
  have hlk : ∀ {x y : V}, ({v, x, y} : Finset V) ∈ L → x ≠ v → y ≠ v → x ∈ verts2 (lk2 L v) :=
    fun {x y} hT hx hy => mem_verts2.mpr ⟨{x, y}, mem_lk2.mpr ⟨by simp [hx.symm, hy.symm], hT⟩,
      by simp⟩
  have rp := reach p (hlk hτ hpv hqv)
  have rq := reach q (hlk (by rw [tri_swap]; exact hτ) hqv hpv)
  rcases rp with rfl | rfl | rfl <;> rcases rq with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hqp
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (tri_swap _ _ _)
    | exact Or.inr (Or.inl (tri_swap _ _ _))
    | exact Or.inr (Or.inr (tri_swap _ _ _))

/-! ## Lowering degrees -/

/-- **A flip lowering the degree of `b`.** If `{b, c, d}` and `{b, c, e}` are triangles and `de` is
not an edge, flipping `bc` to `de` keeps the number of triangles and lowers the degree of `b` by
one. -/
lemma IsSurface.flip_lowers {L : Finset (Finset V)} (hS : IsSurface L) {b c d e : V}
    (h₁ : ({b, c, d} : Finset V) ∈ L) (h₂ : ({b, c, e} : Finset V) ∈ L) (hde : d ≠ e)
    (hfresh : ∀ τ ∈ L, ¬ ({d, e} : Finset V) ⊆ τ) :
    ∃ L', Move2 L L' ∧ #L' = #L ∧ deg2 L' b + 1 = deg2 L b ∧ b ∈ verts2 L' := by
  obtain ⟨hbc, hbd, hcd⟩ := tri_ne (hS.card _ h₁)
  obtain ⟨-, hbe, hce⟩ := tri_ne (hS.card _ h₂)
  refine ⟨_, Move2.flip22 hbc hbd hbe hcd hce hde h₁ h₂ (hS.tris_at_edge h₁ h₂ hde) hfresh,
    ?_, ?_, mem_verts2.mpr ⟨{b, d, e}, mem_insert_self _ _, by simp⟩⟩
  · have hne : ({b, c, d} : Finset V) ≠ {b, c, e} :=
      ne_of_mem_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hde])
    have hdeS : ∀ x : V, ({d, e} : Finset V) ⊆ {x, d, e} :=
      fun x => pair_subset_of_mem (by simp) (by simp)
    have n1 : ({c, d, e} : Finset V) ∉ (L.erase {b, c, d}).erase {b, c, e} :=
      fun h => hfresh _ (mem_of_mem_erase (mem_of_mem_erase h)) (hdeS c)
    have n2 : ({b, d, e} : Finset V) ∉ insert {c, d, e} ((L.erase {b, c, d}).erase {b, c, e}) := by
      rw [mem_insert, not_or]
      refine ⟨fun h => ?_, fun h => hfresh _ (mem_of_mem_erase (mem_of_mem_erase h)) (hdeS b)⟩
      have : b ∈ ({c, d, e} : Finset V) := by rw [← h]; simp
      simp only [mem_insert, mem_singleton] at this
      rcases this with h' | h' | h'
      exacts [hbc h', hbd h', hbe h']
    have h2' : ({b, c, e} : Finset V) ∈ L.erase {b, c, d} := mem_erase.mpr ⟨hne.symm, h₂⟩
    have hc2 : 2 ≤ #L := by
      have := card_le_card (show ({{b, c, d}, {b, c, e}} : Finset (Finset V)) ⊆ L from
        insert_subset_iff.mpr ⟨h₁, singleton_subset_iff.mpr h₂⟩)
      rwa [card_pair hne] at this
    rw [card_insert_of_notMem n2, card_insert_of_notMem n1, card_erase_of_mem h2',
      card_erase_of_mem h₁]
    omega
  · have hne : ({b, c, d} : Finset V) ≠ {b, c, e} :=
      ne_of_mem_notMem (y := d) (by simp) (by simp [hbd.symm, hcd.symm, hde])
    have m1 : b ∈ ({b, d, e} : Finset V) := by simp
    have m2 : b ∉ ({c, d, e} : Finset V) := by simp [hbc, hbd, hbe]
    unfold deg2
    simp only [filter_insert, m1, m2, ite_true, ite_false, filter_erase]
    have f1 : ({b, c, d} : Finset V) ∈ L.filter (b ∈ ·) := mem_filter.mpr ⟨h₁, by simp⟩
    have f2 : ({b, c, e} : Finset V) ∈ (L.filter (b ∈ ·)).erase {b, c, d} :=
      mem_erase.mpr ⟨hne.symm, mem_filter.mpr ⟨h₂, by simp⟩⟩
    have n3 : ({b, d, e} : Finset V) ∉ ((L.filter (b ∈ ·)).erase {b, c, d}).erase {b, c, e} :=
      fun h => hfresh _ (mem_filter.mp (mem_of_mem_erase (mem_of_mem_erase h))).1
        (pair_subset_of_mem (by simp) (by simp))
    have hc2 : 2 ≤ #(L.filter (b ∈ ·)) := by
      have := card_le_card (show ({{b, c, d}, {b, c, e}} : Finset (Finset V)) ⊆ L.filter (b ∈ ·)
        from insert_subset_iff.mpr ⟨f1, singleton_subset_iff.mpr (mem_of_mem_erase f2)⟩)
      rwa [card_pair hne] at this
    rw [card_insert_of_notMem n3, card_erase_of_mem f2, card_erase_of_mem f1]
    omega

/-- **Removing a vertex of degree 3.** If the triangles at `v` are `vab`, `vbc`, `vca` and `abc` is
not a face, an inverse 1-3 move replaces them by `abc`, with two triangles fewer. -/
lemma IsSurface.remove_deg3 {L : Finset (Finset V)} (hS : IsSurface L) {v a b c : V}
    (hab : ({v, a, b} : Finset V) ∈ L) (hbc : ({v, b, c} : Finset V) ∈ L)
    (hca : ({v, c, a} : Finset V) ∈ L) (habc : ({a, b, c} : Finset V) ∉ L) :
    ∃ L₀, Move2 L₀ L ∧ #L₀ < #L := by
  obtain ⟨hva, hvb, hab'⟩ := tri_ne (hS.card _ hab)
  obtain ⟨-, hvc, hbc'⟩ := tri_ne (hS.card _ hbc)
  have hac' : a ≠ c := (tri_ne (hS.card _ hca)).2.2.symm
  have hall := hS.link_triangle hab hbc hca
  have n12 : ({v, a, b} : Finset V) ≠ {v, b, c} :=
    ne_of_mem_notMem (y := a) (by simp) (by simp [hva.symm, hab', hac'])
  have n13 : ({v, a, b} : Finset V) ≠ {v, c, a} :=
    ne_of_mem_notMem (y := b) (by simp) (by simp [hvb.symm, hbc', hab'.symm])
  have n23 : ({v, b, c} : Finset V) ≠ {v, c, a} :=
    ne_of_mem_notMem (y := b) (by simp) (by simp [hvb.symm, hbc', hab'.symm])
  have h2 : ({v, b, c} : Finset V) ∈ L.erase {v, a, b} := mem_erase.mpr ⟨n12.symm, hbc⟩
  have h3 : ({v, c, a} : Finset V) ∈ (L.erase {v, a, b}).erase {v, b, c} :=
    mem_erase.mpr ⟨n23.symm, mem_erase.mpr ⟨n13.symm, hca⟩⟩
  set E := ((L.erase {v, a, b}).erase {v, b, c}).erase {v, c, a} with hE
  have habcE : ({a, b, c} : Finset V) ∉ E :=
    fun h => habc (mem_of_mem_erase (mem_of_mem_erase (mem_of_mem_erase h)))
  have hxv : v ∉ verts2 (insert {a, b, c} E) := by
    rw [mem_verts2]
    rintro ⟨τ, hτ, hvτ⟩
    rw [mem_insert] at hτ
    rcases hτ with rfl | hτ
    · simp only [mem_insert, mem_singleton] at hvτ
      rcases hvτ with h | h | h
      exacts [hva h, hvb h, hvc h]
    · have hτ3 := mem_erase.mp hτ
      have hτ2 := mem_erase.mp hτ3.2
      have hτ1 := mem_erase.mp hτ2.2
      rcases hall τ hτ1.2 hvτ with h | h | h
      exacts [hτ1.1 h, hτ2.1 h, hτ3.1 h]
  refine ⟨insert {a, b, c} E, ?_, ?_⟩
  · have hmv := Move2.sub13 hab' hac' hbc' (mem_insert_self ({a, b, c} : Finset V) E) hxv
    rw [erase_insert habcE] at hmv
    have e1 : ({a, b, v} : Finset V) = {v, a, b} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    have e2 : ({b, c, v} : Finset V) = {v, b, c} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    have e3 : ({a, c, v} : Finset V) = {v, c, a} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    rw [e1, e2, e3, hE, insert_erase h3, insert_erase h2, insert_erase hab] at hmv
    exact hmv
  · have p1 := card_pos.mpr ⟨_, hab⟩
    have p2 := card_pos.mpr ⟨_, h2⟩
    have p3 := card_pos.mpr ⟨_, h3⟩
    rw [card_insert_of_notMem habcE, hE, card_erase_of_mem h3, card_erase_of_mem h2,
      card_erase_of_mem hab]
    rw [card_erase_of_mem h2, card_erase_of_mem hab] at p3
    rw [card_erase_of_mem hab] at p2
    omega


/-- **Recognising the boundary of a tetrahedron.** If the triangles at `v` are `vab`, `vbc`, `vca`
and `abc` is a face, the complex is the boundary of the tetrahedron `vabc`: the links of `a`, `b`,
`c` are triangles too, and the 1-skeleton is connected. -/
lemma IsSurface.eq_bdry {L : Finset (Finset V)} (hS : IsSurface L) {v a b c : V}
    (hab : ({v, a, b} : Finset V) ∈ L) (hbc : ({v, b, c} : Finset V) ∈ L)
    (hca : ({v, c, a} : Finset V) ∈ L) (habc : ({a, b, c} : Finset V) ∈ L) :
    L = bdry v a b c := by
  have Tv := hS.link_triangle hab hbc hca
  have Ta := hS.link_triangle (v := a) (a := v) (b := b) (c := c)
    (mem_of_eq_tri hab (by ext; simp only [mem_insert, mem_singleton]; tauto)) habc
    (mem_of_eq_tri hca (by ext; simp only [mem_insert, mem_singleton]; tauto))
  have Tb := hS.link_triangle (v := b) (a := v) (b := c) (c := a)
    (mem_of_eq_tri hbc (by ext; simp only [mem_insert, mem_singleton]; tauto))
    (mem_of_eq_tri habc (by ext; simp only [mem_insert, mem_singleton]; tauto))
    (mem_of_eq_tri hab (by ext; simp only [mem_insert, mem_singleton]; tauto))
  have Tc := hS.link_triangle (v := c) (a := v) (b := a) (c := b)
    (mem_of_eq_tri hca (by ext; simp only [mem_insert, mem_singleton]; tauto))
    (mem_of_eq_tri habc (by ext; simp only [mem_insert, mem_singleton]; tauto))
    (mem_of_eq_tri hbc (by ext; simp only [mem_insert, mem_singleton]; tauto))
  -- every triangle at a vertex of the tetrahedron lies in the tetrahedron's vertex set
  have sub : ∀ u, (u = v ∨ u = a ∨ u = b ∨ u = c) → ∀ τ ∈ L, u ∈ τ →
      ∀ t ∈ τ, t = v ∨ t = a ∨ t = b ∨ t = c := by
    intro u hu τ hτ huτ t ht
    rcases hu with rfl | rfl | rfl | rfl
    · rcases Tv τ hτ huτ with rfl | rfl | rfl <;>
        (simp only [mem_insert, mem_singleton] at ht; tauto)
    · rcases Ta τ hτ huτ with rfl | rfl | rfl <;>
        (simp only [mem_insert, mem_singleton] at ht; tauto)
    · rcases Tb τ hτ huτ with rfl | rfl | rfl <;>
        (simp only [mem_insert, mem_singleton] at ht; tauto)
    · rcases Tc τ hτ huτ with rfl | rfl | rfl <;>
        (simp only [mem_insert, mem_singleton] at ht; tauto)
  have hv : v ∈ verts2 L := mem_verts2.mpr ⟨_, hab, by simp⟩
  have reach : ∀ y, Relation.ReflTransGen (fun x z => ({x, z} : Finset V) ∈ edges2 L) v y →
      y = v ∨ y = a ∨ y = b ∨ y = c := by
    intro y path
    induction path with
    | refl => exact Or.inl rfl
    | tail _ hpq ih =>
      obtain ⟨T, hT, hsub, -⟩ := mem_edges2.mp hpq
      exact sub _ ih T hT (hsub (by simp)) _ (hsub (by simp))
  ext τ
  constructor
  · intro hτ
    by_cases hvτ : v ∈ τ
    · simp only [bdry, mem_insert, mem_singleton]
      rcases Tv τ hτ hvτ with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl (tri_swap _ _ _))
    · obtain ⟨y, hy⟩ : τ.Nonempty := card_pos.mp (by rw [hS.card τ hτ]; norm_num)
      have hyS := reach y (hS.connected v hv y (mem_verts2.mpr ⟨τ, hτ, hy⟩))
      have hsub : τ ⊆ {a, b, c} := by
        intro t ht
        rcases sub y hyS τ hτ hy t ht with h | h | h | h
        · exact absurd (h ▸ ht) hvτ
        all_goals simp [h]
      have : τ = {a, b, c} := eq_of_subset_of_card_le hsub (by rw [hS.card τ hτ]; exact card_le_three)
      simp [bdry, this]
  · intro hτ
    simp only [bdry, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl
    exacts [hab, mem_of_eq_tri hca (tri_swap _ _ _), hbc, habc]



/-- Around any vertex `v` of a closed surface: three consecutive triangles `v v₁ v₂`,
`v v₂ v₃`, `v v₃ v₄` with `v₁ ≠ v₃` and `v₄ ≠ v₂`. -/
lemma IsSurface.local_structure {L : Finset (Finset V)} (hS : IsSurface L) {v : V}
    (hv : v ∈ verts2 L) : ∃ v₁ v₂ v₃ v₄ : V, ({v, v₁, v₂} : Finset V) ∈ L ∧
      ({v, v₂, v₃} : Finset V) ∈ L ∧ ({v, v₃, v₄} : Finset V) ∈ L ∧ v₁ ≠ v₃ ∧ v₄ ≠ v₂ := by
  obtain ⟨τ, hτ, hvτ⟩ := mem_verts2.mp hv
  obtain ⟨p, hp, hpv⟩ := exists_other (hS.card τ hτ) v
  obtain ⟨q, hqv, hqp, rfl⟩ := eq_tri_of_mem (hS.card τ hτ) hvτ hp hpv.symm
  obtain ⟨v₁, h1q, -, -, h1, -⟩ := hS.other_tri hτ
  obtain ⟨v₄, h4p, -, -, h4, -⟩ :=
    hS.other_tri (show ({v, q, p} : Finset V) ∈ L by rw [tri_swap]; exact hτ)
  exact ⟨v₁, p, q, v₄, by rw [tri_swap]; exact h1, hτ, h4, h1q, h4p⟩


/-- A closed surface has a vertex. -/
lemma IsSurface.verts_nonempty {L : Finset (Finset V)} (hS : IsSurface L) :
    (verts2 L).Nonempty := by
  obtain ⟨τ, hτ⟩ := hS.nonempty
  obtain ⟨x, hx⟩ : τ.Nonempty := card_pos.mp (by rw [hS.card τ hτ]; norm_num)
  exact ⟨x, mem_verts2.mpr ⟨τ, hτ, hx⟩⟩

end Lightlike.Surfaces
