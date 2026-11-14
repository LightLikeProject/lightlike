import Lightlike.PL.Join

/-!
# Links of all simplices in combinatorial manifolds

A combinatorial manifold is defined by its vertex links (`Lightlike/PL/Manifold.lean`). Here we
prove that the link of *every* simplex is then a PL sphere or ball of the right dimension, and that
PL spheres and balls are themselves combinatorial manifolds (Lickorish 1999, §1; Hudson, *Piecewise
Linear Topology*, 1969, §1). The three statements are proven together, by induction on the
dimension:

* (links) in a combinatorial `n`-manifold the link of a face `σ` is a PL `(n − #σ)`-sphere or
  ball: `lk(σ, K) = lk(σ ∖ v, lk(v, K))`, and the vertex link `lk(v, K)` is a PL `(n−1)`-sphere or
  ball, hence by induction a combinatorial `(n−1)`-manifold;
* (invariance) a stellar subdivision of a combinatorial `n`-manifold is one, and conversely: the
  link of an old vertex changes by a stellar move (`link_starAt_of_ne`), and the link of the new
  vertex is `∂A * lk(A, K)`, a join of a sphere with a sphere or ball (`IsSB.boundary_join`);
* (models) hence every PL `n`-sphere or ball is a combinatorial `n`-manifold, since the boundary of
  a simplex and the simplex are.

The flag `b` of `IsSB` and `IsMfdIn` treats closed manifolds (`b = false`: spheres only) and
manifolds with boundary (`b = true`) at once.

## Main results

* `link_starAt_of_ne`: `lk(v, (A, a) K) = (A ∖ v, a) lk(v, K)` for `v ≠ a`.
* `IsPLSphere.isClosedCombManifold`, `IsPLBall.isCombManifold`: PL spheres and balls are
  combinatorial manifolds.
* `IsClosedCombManifold.link_face`, `IsCombManifold.link_face`: the link of every nonempty face
  `σ` is stellar equivalent to the boundary of a simplex on `n + 2 − #σ` vertices (or, with
  boundary, to a simplex on `n + 1 − #σ` vertices); `IsClosedCombManifold.isPLSphere_link`,
  `IsCombManifold.isPLSphere_or_isPLBall_link`: in the language of PL spheres and balls.
* `IsClosedCombManifold.card_le`, `IsCombManifold.card_le`: faces of an `n`-manifold have at most
  `n + 1` vertices.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-! ## Links in a subdivision -/

/-- Subdividing at a set that is not a face changes nothing. -/
lemma starAt_of_notMem {K : SComplex V} {A : Finset V} {a : V} (hA : A ∉ K) :
    K.starAt A a = K := ext_mem fun s => by
  rw [mem_starAt]
  constructor
  · rintro (⟨hs, -⟩ | ⟨t, -, -, hAt, -⟩)
    · exact hs
    · exact absurd (down_mem hAt subset_union_left) hA
  · intro hs
    exact .inl ⟨hs, fun h => hA (down_mem hs h)⟩

/-- The vertices of a link are vertices of the complex. -/
lemma verts_link_subset (K : SComplex V) (σ : Finset V) : (K.link σ).verts ⊆ K.verts :=
  fun _ hx => mem_verts.2 (mem_link.1 (mem_verts.1 hx)).1

/-- The faces of a link are disjoint from the face. -/
lemma disjoint_verts_link (K : SComplex V) (σ : Finset V) : Disjoint σ (K.link σ).verts := by
  refine disjoint_left.2 fun x hxσ hx => ?_
  have := (mem_link.1 (mem_verts.1 hx)).2.1
  exact disjoint_left.1 this hxσ (mem_singleton_self x)

/-- `insert v ((A ∖ v) ∪ t) = A ∪ insert v t`. -/
lemma insert_erase_union (A t : Finset V) (v : V) :
    insert v (A.erase v ∪ t) = A ∪ insert v t := by
  ext z
  simp only [mem_insert, mem_union, mem_erase]
  by_cases hz : z = v
  · simp [hz]
  · simp [hz]

/-- **Links of old vertices in a subdivision**: for a vertex `v ≠ a`, where `a` is not a vertex of
`K`, `lk(v, (A, a) K) = (A ∖ v, a) lk(v, K)`. -/
theorem link_starAt_of_ne {K : SComplex V} {A : Finset V} {a v : V} (ha : a ∉ K.verts)
    (hva : v ≠ a) : (K.starAt A a).link {v} = (K.link {v}).starAt (A.erase v) a := by
  have hlk : ∀ {t : Finset V}, t ∈ K.link {v} ↔ v ∉ t ∧ insert v t ∈ K := by
    intro t
    rw [mem_link', disjoint_singleton_left, ← insert_eq]
  refine ext_mem fun u => ?_
  rw [mem_link', disjoint_singleton_left, ← insert_eq]
  by_cases hau : a ∈ u
  · -- `u` is a cone face `insert a t`
    have hat : a ∉ u.erase a := notMem_erase a u
    have hu : u = insert a (u.erase a) := (insert_erase hau).symm
    have hav : a ∉ insert v (u.erase a) := by
      rw [mem_insert, not_or]
      exact ⟨Ne.symm hva, hat⟩
    rw [hu, insert_comm, insert_mem_starAt ha hav, mem_starAt]
    constructor
    · rintro ⟨hvu, h₁, h₂, h₃⟩
      have hvt : v ∉ u.erase a := fun h => hvu (mem_insert_of_mem h)
      refine .inr ⟨u.erase a, hlk.2 ⟨hvt, h₁⟩, fun h => h₂ (subset_insert_iff.2 h), ?_, rfl⟩
      refine hlk.2 ⟨?_, by rwa [insert_erase_union]⟩
      rw [mem_union, not_or]
      exact ⟨notMem_erase v A, hvt⟩
    · rintro (⟨h₁, -⟩ | ⟨t, ht, h₂, h₃, he⟩)
      · exact absurd (subset_verts (hlk.1 h₁).2 (mem_insert_of_mem (mem_insert_self a _))) ha
      · have hat' : a ∉ t := fun h => ha (subset_verts (hlk.1 ht).2 (mem_insert_of_mem h))
        have := insert_cancel hat' hat he
        subst this
        obtain ⟨hvt, ht⟩ := hlk.1 ht
        refine ⟨?_, ht, fun h => h₂ (subset_insert_iff.1 h), ?_⟩
        · rw [mem_insert, not_or]
          exact ⟨hva, hvt⟩
        · rw [← insert_erase_union]
          exact (hlk.1 h₃).2
  · -- `u` does not contain the new vertex
    have hav : a ∉ insert v u := by
      rw [mem_insert, not_or]
      exact ⟨Ne.symm hva, hau⟩
    rw [mem_starAt_of_notMem hav, mem_starAt]
    constructor
    · rintro ⟨hvu, h₁, h₂⟩
      exact .inl ⟨hlk.2 ⟨hvu, h₁⟩, fun h => h₂ (subset_insert_iff.2 h)⟩
    · rintro (⟨h₁, h₂⟩ | ⟨t, -, -, -, rfl⟩)
      · obtain ⟨hvu, h₁⟩ := hlk.1 h₁
        exact ⟨hvu, h₁, fun h => h₂ (subset_insert_iff.1 h)⟩
      · exact absurd (mem_insert_self a t) hau

/-! ## Combinatorial manifolds inside an infinite type -/

/-- `K` is a combinatorial `n`-manifold inside `V`, closed when `b` is false: every vertex link is
`IsSB b n`. -/
def IsMfdIn (b : Bool) (n : ℕ) (K : SComplex V) : Prop := ∀ v ∈ K.verts, IsSB b n (K.link {v})

lemma isMfdIn_false_iff {n : ℕ} {K : SComplex V} :
    IsMfdIn false n K ↔ IsClosedCombManifoldIn n K := by
  simp [IsMfdIn, IsSB, IsClosedCombManifoldIn]

lemma isMfdIn_true_iff {n : ℕ} {K : SComplex V} : IsMfdIn true n K ↔ IsCombManifoldIn n K := by
  simp [IsMfdIn, IsSB, IsCombManifoldIn]

/-- A complex that is a sphere or ball on `0` model vertices (the `(−1)`-sphere `{∅}`) has no
vertices. -/
lemma IsSB.verts_eq_empty {b : Bool} {L : SComplex V} (h : IsSB b 0 L) : L.verts = ∅ := by
  have hmax : L.maxCard = 0 := by
    rcases h with ⟨A, hA, hLA⟩ | ⟨-, A, hA, hLA⟩
    · rw [hLA.maxCard_eq, maxCard_boundary (card_pos.1 (by omega)), hA]
    · rw [hLA.maxCard_eq, maxCard_simplex, hA]
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have := card_le_maxCard (mem_verts.1 hx)
  rw [card_singleton, hmax] at this
  omega

/-- The link of a face, given the statements in lower dimensions. -/
lemma IsMfdIn.link_face {b : Bool} {n : ℕ}
    (hA : ∀ n', n = n' + 1 → ∀ L : SComplex V, IsSB b (n' + 1) L → IsMfdIn b n' L)
    (hB : ∀ n', n = n' + 1 → ∀ L : SComplex V, IsMfdIn b n' L → ∀ τ ∈ L, τ.Nonempty →
      ∃ m, m + #τ = n' + 1 ∧ IsSB b m (L.link τ))
    {K : SComplex V} (hK : IsMfdIn b n K) {σ : Finset V} (hσ : σ ∈ K) (hne : σ.Nonempty) :
    ∃ m, m + #σ = n + 1 ∧ IsSB b m (K.link σ) := by
  obtain ⟨v, hv⟩ := hne
  have hvK : v ∈ K.verts := subset_verts hσ hv
  have hσ' : σ = {v} ∪ σ.erase v := by rw [← insert_eq, insert_erase hv]
  have hdis : Disjoint ({v} : Finset V) (σ.erase v) := disjoint_singleton_left.2 (notMem_erase v σ)
  have hlk : K.link σ = (K.link {v}).link (σ.erase v) := by
    rw [link_link K hdis, ← hσ']
  have hcard : #σ = #(σ.erase v) + 1 := by
    rw [card_erase_of_mem hv]; have := card_pos.2 ⟨v, hv⟩; omega
  rcases (σ.erase v).eq_empty_or_nonempty with hτ | hτ
  · refine ⟨n, by rw [hcard, hτ, card_empty], ?_⟩
    rw [hlk, hτ, link_empty]
    exact hK v hvK
  · have hτK : σ.erase v ∈ K.link {v} := mem_link'.2 ⟨hdis, by rwa [← hσ']⟩
    obtain ⟨x, hx⟩ := hτ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have := (hK v hvK).verts_eq_empty
      exact absurd (subset_verts hτK hx) (by rw [this]; exact notMem_empty x)
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hL := hA n' rfl _ (hK v hvK)
      obtain ⟨m, hm, hm'⟩ := hB n' rfl _ hL _ hτK ⟨x, hx⟩
      exact ⟨m, by omega, hlk ▸ hm'⟩

/-- **Stellar subdivision preserves combinatorial manifolds**, in both directions, given that links
of faces of `n`-manifolds are spheres or balls. -/
lemma isMfdIn_starAt_iff [Infinite V] {b : Bool} {n : ℕ}
    (hB : ∀ L : SComplex V, IsMfdIn b n L → ∀ τ ∈ L, τ.Nonempty →
      ∃ m, m + #τ = n + 1 ∧ IsSB b m (L.link τ))
    {K : SComplex V} {A : Finset V} {a : V} (hA : A ∈ K) (hne : A.Nonempty) (ha : a ∉ K.verts) :
    IsMfdIn b n (K.starAt A a) ↔ IsMfdIn b n K := by
  -- old vertices: the link changes by a stellar move
  have hstep : ∀ v ∈ K.verts, ¬ A ⊆ {v} →
      StellarEquivIn (K.link {v}) ((K.starAt A a).link {v}) := by
    intro v hv hAv
    have hva : v ≠ a := fun e => ha (e ▸ hv)
    rw [link_starAt_of_ne ha hva]
    by_cases hAl : A.erase v ∈ K.link {v}
    · refine StellarEquivIn.starAt hAl ?_ (fun h => ha (verts_link_subset K {v} h))
      rcases (A.erase v).eq_empty_or_nonempty with h | h
      · have : A ⊆ insert v ∅ := subset_insert_iff.2 (by simp [h])
        rw [insert_empty] at this
        exact absurd this hAv
      · exact h
    · rw [starAt_of_notMem hAl]
  have hapex := link_starAt_apex (A := A) ha
  constructor
  · intro h v hv
    by_cases hAv : A ⊆ {v}
    · have hA1 : A = {v} := (subset_singleton_iff.1 hAv).resolve_left hne.ne_empty
      have := h a (apex_mem_verts hA hne)
      rwa [hapex, hA1, boundary_singleton, simplex_empty_join] at this
    · exact (isSB_iff_of_stellarEquivIn (hstep v hv hAv)).2
        (h v ((mem_verts_starAt hA hne ha).2 (.inr ⟨hv, hAv⟩)))
  · intro h v hv
    rcases (mem_verts_starAt hA hne ha).1 hv with rfl | ⟨hvK, hAv⟩
    · rw [hapex]
      obtain ⟨m, hm, hm'⟩ := hB K h A hA hne
      have := hm'.boundary_join hne (disjoint_verts_link K A)
      rwa [show m + #A - 1 = n by omega] at this
    · exact (isSB_iff_of_stellarEquivIn (hstep v hvK hAv)).1 (h v hvK)

/-- Being a combinatorial manifold is invariant under stellar equivalence, given that links of
faces of `n`-manifolds are spheres or balls. -/
lemma isMfdIn_iff_of_stellarEquivIn [Infinite V] {b : Bool} {n : ℕ}
    (hB : ∀ L : SComplex V, IsMfdIn b n L → ∀ τ ∈ L, τ.Nonempty →
      ∃ m, m + #τ = n + 1 ∧ IsSB b m (L.link τ))
    {K L : SComplex V} (h : StellarEquivIn K L) : IsMfdIn b n K ↔ IsMfdIn b n L := by
  induction h with
  | rel K L h =>
    obtain ⟨hA, hne, ha⟩ := h
    exact (isMfdIn_starAt_iff hB hA hne ha).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The models: the boundary of a simplex on `n + 2` vertices is a closed `n`-manifold. -/
lemma isMfdIn_boundary {b : Bool} {n : ℕ} {A : Finset V} (hA : #A = n + 2) :
    IsMfdIn b n (boundary A) := by
  intro v hv
  refine .inl ⟨A.erase v, ?_, by rw [link_boundary_vertex hv]⟩
  rw [verts_boundary (by omega)] at hv
  rw [card_erase_of_mem hv, hA]; rfl

/-- The models: the simplex on `n + 1` vertices is an `n`-manifold with boundary. -/
lemma isMfdIn_simplex {n : ℕ} {A : Finset V} (hA : #A = n + 1) : IsMfdIn true n (simplex A) := by
  intro v hv
  rw [verts_simplex] at hv
  refine .inr ⟨rfl, A.erase v, by rw [card_erase_of_mem hv, hA]; rfl, ?_⟩
  rw [link_simplex (singleton_subset_iff.2 hv), sdiff_singleton_eq_erase]

/-- **The main induction**: in every dimension `n`, links of nonempty faces of combinatorial
`n`-manifolds are spheres or balls of dimension `n − #σ`, and PL `n`-spheres and balls are
combinatorial `n`-manifolds (inside an infinite vertex type). -/
theorem isMfdIn_main [Infinite V] (b : Bool) (n : ℕ) :
    (∀ K : SComplex V, IsMfdIn b n K → ∀ σ ∈ K, σ.Nonempty →
      ∃ m, m + #σ = n + 1 ∧ IsSB b m (K.link σ)) ∧
    (∀ K : SComplex V, IsSB b (n + 1) K → IsMfdIn b n K) := by
  induction n with
  | zero =>
    have hB : ∀ K : SComplex V, IsMfdIn b 0 K → ∀ σ ∈ K, σ.Nonempty →
        ∃ m, m + #σ = 0 + 1 ∧ IsSB b m (K.link σ) := fun K hK σ hσ hne =>
      hK.link_face (fun n' h => absurd h (by omega)) (fun n' h => absurd h (by omega)) hσ hne
    refine ⟨hB, fun K hK => ?_⟩
    rcases hK with ⟨A, hA, hKA⟩ | ⟨hb, A, hA, hKA⟩
    · exact (isMfdIn_iff_of_stellarEquivIn hB hKA).2 (isMfdIn_boundary hA)
    · subst hb
      exact (isMfdIn_iff_of_stellarEquivIn hB hKA).2 (isMfdIn_simplex hA)
  | succ n ih =>
    have hB : ∀ K : SComplex V, IsMfdIn b (n + 1) K → ∀ σ ∈ K, σ.Nonempty →
        ∃ m, m + #σ = n + 1 + 1 ∧ IsSB b m (K.link σ) := fun K hK σ hσ hne =>
      hK.link_face (fun n' h => by rw [show n' = n by omega]; exact ih.2)
        (fun n' h => by rw [show n' = n by omega]; exact ih.1) hσ hne
    refine ⟨hB, fun K hK => ?_⟩
    rcases hK with ⟨A, hA, hKA⟩ | ⟨hb, A, hA, hKA⟩
    · exact (isMfdIn_iff_of_stellarEquivIn hB hKA).2 (isMfdIn_boundary hA)
    · subst hb
      exact (isMfdIn_iff_of_stellarEquivIn hB hKA).2 (isMfdIn_simplex hA)

/-! ## The main notions -/

/-- The lift of a face is a face of the lift. -/
lemma map_inl_mem_lift {K : SComplex V} {σ : Finset V} (hσ : σ ∈ K) :
    σ.map Function.Embedding.inl ∈ K.lift :=
  map_mem_map.2 hσ

/-- **A PL `n`-sphere is a closed combinatorial `n`-manifold.** -/
theorem IsPLSphere.isClosedCombManifold {n : ℕ} {K : SComplex V} (h : IsPLSphere n K) :
    IsClosedCombManifold n K :=
  isMfdIn_false_iff.1 ((isMfdIn_main false n).2 K.lift (.inl h))

/-- **A PL `n`-ball is a combinatorial `n`-manifold.** -/
theorem IsPLBall.isCombManifold {n : ℕ} {K : SComplex V} (h : IsPLBall n K) :
    IsCombManifold n K :=
  isMfdIn_true_iff.1 ((isMfdIn_main true n).2 K.lift (.inr ⟨rfl, h⟩))

/-- **Links of all faces of a closed combinatorial `n`-manifold are spheres**: the link of a
nonempty face `σ` is stellar equivalent to the boundary of a simplex on `n + 2 − #σ` vertices (for
a face with `n + 1` vertices, the `(−1)`-sphere `{∅}`). -/
theorem IsClosedCombManifold.link_face {n : ℕ} {K : SComplex V} (h : IsClosedCombManifold n K)
    {σ : Finset V} (hσ : σ ∈ K) (hne : σ.Nonempty) :
    ∃ A : Finset (V ⊕ ℕ), #A + #σ = n + 2 ∧ StellarEquivIn (K.link σ).lift (boundary A) := by
  obtain ⟨m, hm, hm'⟩ := (isMfdIn_main false n).1 K.lift (isMfdIn_false_iff.2 h) _
    (map_inl_mem_lift hσ) hne.map
  rw [link_lift] at hm'
  rcases hm' with ⟨A, hA, hLA⟩ | ⟨hb, -⟩
  · exact ⟨A, by rw [card_map] at hm; omega, hLA⟩
  · exact absurd hb (by decide)

/-- **Links of all faces of a combinatorial `n`-manifold are spheres or balls**: the link of a
nonempty face `σ` is stellar equivalent to the boundary of a simplex on `n + 2 − #σ` vertices or
to a simplex on `n + 1 − #σ` vertices. -/
theorem IsCombManifold.link_face {n : ℕ} {K : SComplex V} (h : IsCombManifold n K)
    {σ : Finset V} (hσ : σ ∈ K) (hne : σ.Nonempty) :
    (∃ A : Finset (V ⊕ ℕ), #A + #σ = n + 2 ∧ StellarEquivIn (K.link σ).lift (boundary A)) ∨
      ∃ A : Finset (V ⊕ ℕ), #A + #σ = n + 1 ∧ StellarEquivIn (K.link σ).lift (simplex A) := by
  obtain ⟨m, hm, hm'⟩ := (isMfdIn_main true n).1 K.lift (isMfdIn_true_iff.2 h) _
    (map_inl_mem_lift hσ) hne.map
  rw [link_lift, card_map] at *
  rcases hm' with ⟨A, hA, hLA⟩ | ⟨-, A, hA, hLA⟩
  · exact .inl ⟨A, by omega, hLA⟩
  · exact .inr ⟨A, by omega, hLA⟩

/-- Faces of a closed combinatorial `n`-manifold have at most `n + 1` vertices. -/
theorem IsClosedCombManifold.card_le {n : ℕ} {K : SComplex V} (h : IsClosedCombManifold n K)
    {σ : Finset V} (hσ : σ ∈ K) : #σ ≤ n + 1 := by
  rcases σ.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨m, hm, -⟩ := (isMfdIn_main false n).1 K.lift (isMfdIn_false_iff.2 h) _
      (map_inl_mem_lift hσ) hne.map
    rw [card_map] at hm
    omega

/-- Faces of a combinatorial `n`-manifold have at most `n + 1` vertices. -/
theorem IsCombManifold.card_le {n : ℕ} {K : SComplex V} (h : IsCombManifold n K)
    {σ : Finset V} (hσ : σ ∈ K) : #σ ≤ n + 1 := by
  rcases σ.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨m, hm, -⟩ := (isMfdIn_main true n).1 K.lift (isMfdIn_true_iff.2 h) _
      (map_inl_mem_lift hσ) hne.map
    rw [card_map] at hm
    omega

/-- In a closed combinatorial `n`-manifold the link of a nonempty face `σ` with at most `n` vertices
is a PL `(n − #σ)`-sphere. -/
theorem IsClosedCombManifold.isPLSphere_link {n : ℕ} {K : SComplex V}
    (h : IsClosedCombManifold n K) {σ : Finset V} (hσ : σ ∈ K) (hne : σ.Nonempty)
    (hle : #σ ≤ n) : IsPLSphere (n - #σ) (K.link σ) := by
  obtain ⟨A, hA, hLA⟩ := h.link_face hσ hne
  exact ⟨A, by omega, hLA⟩

/-- In a combinatorial `n`-manifold the link of a nonempty face `σ` with at most `n` vertices is a
PL `(n − #σ)`-sphere or ball. -/
theorem IsCombManifold.isPLSphere_or_isPLBall_link {n : ℕ} {K : SComplex V}
    (h : IsCombManifold n K) {σ : Finset V} (hσ : σ ∈ K) (hne : σ.Nonempty) (hle : #σ ≤ n) :
    IsPLSphere (n - #σ) (K.link σ) ∨ IsPLBall (n - #σ) (K.link σ) := by
  rcases h.link_face hσ hne with ⟨A, hA, hLA⟩ | ⟨A, hA, hLA⟩
  · exact .inl ⟨A, by omega, hLA⟩
  · exact .inr ⟨A, by omega, hLA⟩

end SComplex

end Lightlike.PL
