import Lightlike.Surfaces.Classify

/-!
# Trust checks for the classification of surfaces

Known examples and deliberately wrong inputs for `classify` and `classify_unique`:

* `isSurface_of_cert`: a closed surface certificate checked by kernel computation
  (reachability searches in each vertex link and in the 1-skeleton). With it, `isSurface_P6`,
  `isSurface_T9` and `isSurface_T7` are **non-vacuity** examples for `classify`.
* **Known values.** `P6_model`: the 6-vertex projective plane is related by moves to
  `stdModel false 0` (one crosscap). `T9_model` and `T7_model`: the 9-vertex torus and
  Möbius' 7-vertex torus (`T7`, an independent triangulation not used anywhere in the proof) are
  related by moves to `stdModel true 1` (one handle). `isSphere2_of_classify`: for `χ = 2` the
  classification reproduces the independently proven sphere recognition `Lightlike.PR.IsSphere2`.
* **Wrong models.** `T7_not_klein`: the torus `T7` has the Euler characteristic `0` of the Klein
  bottle `stdModel false 1` but is not related to it, since orientability tells them apart.
  `T7_not_sphere`: nor to the sphere. `torus_not_klein`: the two standard models with `χ = 0` are
  not related, however they are placed.
* **Wrong inputs.** `triangle_no_model`: a single triangle (not closed) has no model.
  `two_spheres_no_model`: two disjoint tetrahedron boundaries (closed, with connected vertex
  links, but disconnected) have `χ = 4 > 2` and no model.
-/

open Finset Relation

namespace Lightlike.Surfaces

open Lightlike.PR

/-! ## Surface certificates -/

/-- **A connectivity certificate**: if the reachability search from `a` finds every vertex of an
edge set, the edge set is connected. -/
lemma isConnEdges_of_reach {E : Finset (Finset ℕ)} (hE : ∀ e ∈ E, #e = 2) {a : ℕ}
    (h : ∀ m ∈ verts2 E, m ∈ reachAll E a) : IsConnEdges E :=
  fun u hu w hw => (rtg_pair_symm (reachAll_sound hE (h u hu))).trans (reachAll_sound hE (h w hw))

/-- **A closed-surface certificate** for complexes on `ℕ`, in decidable form: triangles, every
edge in two triangles, and reachability searches that find every vertex of each vertex link and
of the 1-skeleton. -/
theorem isSurface_of_cert {X : Finset (Finset ℕ)} (hne : X.Nonempty) (hT : IsTri2 X)
    (hC : IsClosed2 X)
    (hlk : ∀ v ∈ verts2 X, ∃ a ∈ verts2 (lk2 X v),
      ∀ m ∈ verts2 (lk2 X v), m ∈ reachAll (lk2 X v) a)
    (hcon : ∃ a ∈ verts2 X, ∀ m ∈ verts2 X, m ∈ reachAll (edges2 X) a) : IsSurface X where
  nonempty := hne
  card := hT
  closed := hC
  link v hv := by
    obtain ⟨a, -, ha⟩ := hlk v hv
    refine isConnEdges_of_reach (fun e he => ?_) ha
    obtain ⟨τ, hτ, rfl⟩ := mem_image.mp he
    obtain ⟨hτX, hvτ⟩ := mem_filter.mp hτ
    rw [card_erase_of_mem hvτ, hT τ hτX]
  connected u hu w hw := by
    obtain ⟨a, -, ha⟩ := hcon
    have hE : ∀ e ∈ edges2 X, #e = 2 := fun e he => card_of_mem_edges2 he
    exact (rtg_pair_symm (reachAll_sound hE (ha u hu))).trans (reachAll_sound hE (ha w hw))

lemma P6_link : ∀ v ∈ verts2 P6, ∃ a ∈ verts2 (lk2 P6 v),
    ∀ m ∈ verts2 (lk2 P6 v), m ∈ reachAll (lk2 P6 v) a := by decide +kernel
lemma P6_conn : ∃ a ∈ verts2 P6, ∀ m ∈ verts2 P6, m ∈ reachAll (edges2 P6) a := by decide +kernel

/-- The 6-vertex projective plane is a closed surface. -/
theorem isSurface_P6 : IsSurface P6 :=
  isSurface_of_cert (by decide) isTri2_P6 isClosed2_P6 P6_link P6_conn

lemma T9_link : ∀ v ∈ verts2 T9, ∃ a ∈ verts2 (lk2 T9 v),
    ∀ m ∈ verts2 (lk2 T9 v), m ∈ reachAll (lk2 T9 v) a := by decide +kernel
lemma T9_conn : ∃ a ∈ verts2 T9, ∀ m ∈ verts2 T9, m ∈ reachAll (edges2 T9) a := by decide +kernel

/-- The 9-vertex torus is a closed surface. -/
theorem isSurface_T9 : IsSurface T9 :=
  isSurface_of_cert (by decide) isTri2_T9 isClosed2_T9 T9_link T9_conn

/-! ## Möbius' 7-vertex torus -/

/-- **Möbius' 7-vertex torus**: the triangles `{i, i+1, i+3}` and `{i, i+2, i+3}` mod `7`. Every
pair of its 7 vertices is an edge (21 edges, 14 triangles). It is not used in the proof of the
classification, so it is an independent test. -/
def T7 : Finset (Finset ℕ) :=
  {{0, 1, 3}, {0, 1, 5}, {0, 2, 3}, {0, 2, 6}, {0, 4, 5}, {0, 4, 6}, {1, 2, 4}, {1, 2, 6},
    {1, 3, 4}, {1, 5, 6}, {2, 3, 5}, {2, 4, 5}, {3, 4, 6}, {3, 5, 6}}

lemma isTri2_T7 : IsTri2 T7 := by unfold IsTri2; decide +kernel
lemma isClosed2_T7 : IsClosed2 T7 := by unfold IsClosed2; decide +kernel
lemma T7_link : ∀ v ∈ verts2 T7, ∃ a ∈ verts2 (lk2 T7 v),
    ∀ m ∈ verts2 (lk2 T7 v), m ∈ reachAll (lk2 T7 v) a := by decide +kernel
lemma T7_conn : ∃ a ∈ verts2 T7, ∀ m ∈ verts2 T7, m ∈ reachAll (edges2 T7) a := by decide +kernel

/-- Möbius' 7-vertex torus is a closed surface. -/
theorem isSurface_T7 : IsSurface T7 :=
  isSurface_of_cert (by decide) isTri2_T7 isClosed2_T7 T7_link T7_conn

/-- Möbius' torus has Euler characteristic `7 - 21 + 14 = 0`. -/
theorem euler2_T7 : euler2 T7 = 0 := by decide +kernel

/-- A coherent orientation of `T7`, one ordered triple per triangle. -/
def T7or : List (ℕ × ℕ × ℕ) :=
  [(0, 3, 1), (0, 1, 5), (0, 2, 3), (0, 6, 2), (4, 0, 5), (0, 4, 6), (1, 4, 2), (2, 6, 1),
    (1, 3, 4), (5, 1, 6), (3, 2, 5), (2, 4, 5), (6, 4, 3), (5, 6, 3)]

lemma T7or_mem : ∀ t ∈ T7or, ({t.1, t.2.1, t.2.2} : Finset ℕ) ∈ T7 := by decide +kernel
lemma T7_lt : ∀ τ ∈ T7, ∀ v ∈ τ, v < 7 := by decide +kernel
lemma T7_unit : ∀ x < 7, ∀ y < 7, ∀ z < 7, ({x, y, z} : Finset ℕ) ∈ T7 →
    olist T7or x y z = 1 ∨ olist T7or x y z = -1 := by decide +kernel
lemma T7_edges : ∀ u < 7, ∀ v < 7,
    (T7or.map fun t => edir t.1 t.2.1 u v + edir t.2.1 t.2.2 u v + edir t.2.2 t.1 u v).sum = 0 := by
  decide +kernel

/-- **Möbius' torus is orientable.** -/
theorem isOrientable_T7 : IsOrientable T7 :=
  ⟨_, isOrientation_olist T7or_mem T7_lt T7_unit T7_edges⟩

/-! ## Known values -/

lemma P6_loc : ∀ n ∈ ({3, 4, 5} : Finset ℕ), ∀ t ∈ P6, n ∈ t → t ∈ P6.erase {0, 1, 2} := by
  decide +kernel

/-- The 6-vertex projective plane is not orientable. -/
theorem not_isOrientable_P6 : ¬ IsOrientable P6 :=
  not_isOrientable_of_P6 (f := Function.Embedding.refl ℕ)
    (by rw [liftK_refl]; exact erase_subset _ _)
    (fun n hn t ht hnt => by rw [liftK_refl]; exact P6_loc n hn t ht hnt)

/-- **Known value: the projective plane.** `P6` is related by moves to `stdModel false 0`, one
crosscap. -/
theorem P6_model : ∃ f : ℕ ↪ ℕ, EqvGen Move2 P6 (liftK f (stdModel false 0)) :=
  (exists_eqvGen_stdModel_iff isSurface_P6 false 0).mpr
    ⟨iff_of_false not_isOrientable_P6 (by decide), by
      rw [euler2_P6, euler2_stdModel_false]; norm_num⟩

/-- **Known value: the 9-vertex torus** is related by moves to `stdModel true 1`, one handle. -/
theorem T9_model : ∃ f : ℕ ↪ ℕ, EqvGen Move2 T9 (liftK f (stdModel true 1)) :=
  (exists_eqvGen_stdModel_iff isSurface_T9 true 1).mpr
    ⟨iff_of_true isOrientable_T9 rfl, by rw [euler2_T9, euler2_stdModel_true]; norm_num⟩

/-- **Known value: Möbius' 7-vertex torus** is related by moves to `stdModel true 1`, one
handle. -/
theorem T7_model : ∃ f : ℕ ↪ ℕ, EqvGen Move2 T7 (liftK f (stdModel true 1)) :=
  (exists_eqvGen_stdModel_iff isSurface_T7 true 1).mpr
    ⟨iff_of_true isOrientable_T7 rfl, by rw [euler2_T7, euler2_stdModel_true]; norm_num⟩

/-- **Agreement with sphere recognition.** The classification alone shows that a closed surface
with Euler characteristic `2` is a combinatorial 2-sphere (`Lightlike.PR.IsSphere2`), independently of
the proof of `Lightlike.PR.isSphere2_iff_isSurfaceSphere`: a crosscap model has `χ ≤ 1`, and the handle
model with `χ = 2` is the boundary of a tetrahedron. -/
theorem isSphere2_of_classify {V : Type*} [DecidableEq V] [Infinite V] {L : Finset (Finset V)}
    (hS : IsSurface L) (he : euler2 L = 2) : IsSphere2 L := by
  obtain ⟨b, n, f, h⟩ := classify hS
  have he' := ((exists_eqvGen_stdModel_iff hS b n).mp ⟨f, h⟩).2
  cases b with
  | false => rw [euler2_stdModel_false] at he'; omega
  | true =>
    rw [euler2_stdModel_true] at he'
    obtain rfl : n = 0 := by omega
    rw [show stdModel true 0 = bdry 0 1 2 3 from rfl, liftK_bdry] at h
    exact ⟨f 0, f 1, f 2, f 3, f.injective.ne (by decide), f.injective.ne (by decide),
      f.injective.ne (by decide), f.injective.ne (by decide), f.injective.ne (by decide),
      f.injective.ne (by decide), EqvGen.symm _ _ h⟩

/-! ## Wrong models and wrong inputs -/

/-- **Wrong model: the Klein bottle.** Möbius' torus has the Euler characteristic `0` of the
Klein bottle `stdModel false 1`, but it is not related to it by moves: orientability tells them
apart. -/
theorem T7_not_klein (f : ℕ ↪ ℕ) : ¬ EqvGen Move2 T7 (liftK f (stdModel false 1)) := fun h =>
  absurd (((exists_eqvGen_stdModel_iff isSurface_T7 false 1).mp ⟨f, h⟩).1.mp isOrientable_T7)
    (by decide)

/-- **Wrong model: the sphere.** Möbius' torus is not related to the sphere `stdModel true 0`:
the Euler characteristics `0` and `2` differ. -/
theorem T7_not_sphere (f : ℕ ↪ ℕ) : ¬ EqvGen Move2 T7 (liftK f (stdModel true 0)) := fun h => by
  have := ((exists_eqvGen_stdModel_iff isSurface_T7 true 0).mp ⟨f, h⟩).2
  rw [euler2_T7, euler2_stdModel_true] at this
  norm_num at this

/-- **The torus and the Klein bottle are different**: the two standard models with `χ = 0` are
not related by moves, however they are placed. -/
theorem torus_not_klein (f f' : ℕ ↪ ℕ) :
    ¬ EqvGen Move2 (liftK f (stdModel true 1)) (liftK f' (stdModel false 1)) := fun h =>
  absurd (classify_unique (EqvGen.refl _) h).1 (by decide)

/-- **Wrong input: a single triangle** is not closed, so it is related to no standard model. -/
theorem triangle_no_model : ¬ ∃ (b : Bool) (n : ℕ) (f : ℕ ↪ ℕ),
    EqvGen Move2 ({{0, 1, 2}} : Finset (Finset ℕ)) (liftK f (stdModel b n)) := fun h =>
  (show ¬ IsClosed2 ({{0, 1, 2}} : Finset (Finset ℕ)) by unfold IsClosed2; decide +kernel)
    (isSurface_iff_classify.mpr h).closed

/-- **Wrong input: two disjoint spheres** (closed, with connected vertex links, but disconnected)
have Euler characteristic `4 > 2`, so they are related to no standard model. -/
theorem two_spheres_no_model : ¬ ∃ (b : Bool) (n : ℕ) (f : ℕ ↪ ℕ),
    EqvGen Move2 (bdry 0 1 2 3 ∪ bdry 4 5 6 7 : Finset (Finset ℕ)) (liftK f (stdModel b n)) :=
  fun h => by
    have hle := (isSurface_iff_classify.mpr h).euler_le
    have h4 : euler2 (bdry 0 1 2 3 ∪ bdry 4 5 6 7 : Finset (Finset ℕ)) = 4 := by decide +kernel
    omega

end Lightlike.Surfaces
