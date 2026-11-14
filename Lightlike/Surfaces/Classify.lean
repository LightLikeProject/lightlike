import Lightlike.Surfaces.Tube
import Lightlike.Surfaces.Add
import Lightlike.Surfaces.Slides
import Lightlike.Surfaces.Homology
import Lightlike.Surfaces.Local

/-!
# The classification of closed surfaces

The main theorem `classify`: **every closed triangulated surface is related by 2D bistellar
moves to exactly one standard model** `stdModel b n` (placed in the vertex type by an embedding):
the sphere with `n` handles (`b = true`, a connected sum of `n` tori `T9`) or the connected sum of
`n + 1` projective planes `P6` (`b = false`). The model is determined by orientability and the
Euler characteristic (`classify_unique`), and conversely everything related to a model is a
closed surface (`isSurface_iff_classify`).

The proof follows the classical strategy (Brahana; Francis–Weeks, "Conway's ZIP proof"), made
combinatorial with the bistellar moves of Lickorish's treatment: by induction on `2 - χ`, the
number of triangles and the degree of a vertex.

* At a vertex of degree `3` the surface is the boundary of a tetrahedron, or a vertex can be
  removed (`IsSurface.eq_bdry`, `IsSurface.remove_deg3`).
* An edge at a vertex whose far side is not an edge can be flipped, lowering the degree
  (`IsSurface.flip_lowers`).
* Otherwise the link of the vertex crosses itself, and the surface is cut along a curve through
  the vertex (`IsSurface.cut`). The cut removes a handle (a torus or Klein bottle summand,
  `handle_of_cut`) or a crosscap (a projective-plane summand, `crosscap_of_cut`), raising `χ`.

The summands are put back with the moves of `GoodPiece.add` and `GoodPiece.homog` (a connected
sum with a good piece is well defined up to moves). The Klein bottle is two projective planes
(`twist_of_KB`), and **Dyck's relation** `P6 # T9 ~ P6 # P6 # P6` (`dyck_step`, from the checked
flip chain `chain_dyck`) turns a torus summand on a non-orientable surface into two crosscaps.

## References

* H. R. Brahana, *Systems of circuits on two-dimensional manifolds*, Ann. of Math. 23 (1921).
* G. K. Francis and J. R. Weeks, *Conway's ZIP proof*, Amer. Math. Monthly 106 (1999).
* W. B. R. Lickorish, *Simplicial moves on complexes and manifolds*, Geom. Topol. Monogr. 2 (1999).
-/

open Finset Relation

namespace Lightlike.Surfaces

open Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-! ## Placing the models -/

/-- Any piece with the triangle `012` can be glued at the current gluing site of a model. -/
lemma isGlue_model' {P Q : Finset (Finset ℕ)} (hP : IsPiece P) (hQ : ({0, 1, 2} : Finset ℕ) ∈ Q)
    (j : ℕ) : IsGlue (model P j) (triOf (site j)) Q {0, 1, 2} (gl j) := by
  obtain ⟨-, -, hlt, hs⟩ := model_spec hP j
  refine ⟨hs, hQ, triOf_site_map j, fun n hn hn0 hv => ?_⟩
  have := hlt _ hv
  simp only [gl, Function.Embedding.coeFn_mk, glFun] at this
  simp only [mem_insert, mem_singleton, not_or] at hn0
  simp only [hn0.1, hn0.2.1, hn0.2.2, ite_false] at this
  omega

/-- Placing the boundary of a tetrahedron. -/
lemma liftK_bdry (f : ℕ ↪ V) (a b c d : ℕ) :
    liftK f (bdry a b c d) = bdry (f a) (f b) (f c) (f d) := by
  simp [liftK, bdry]

/-- Placing a complex by the identity changes nothing. -/
lemma liftK_refl (K : Finset (Finset ℕ)) : liftK (Function.Embedding.refl ℕ) K = K := by
  ext t
  simp [liftK]

/-- **The models are closed surfaces**, wherever they are placed. -/
theorem isSurface_liftK_model {P : Finset (Finset ℕ)} {k : ℕ} (hG : GoodPiece P k)
    (hP : IsPiece P) (f : ℕ ↪ V) : ∀ j, IsSurface (liftK f (model P j))
  | 0 => by
    rw [model, liftK_bdry]
    exact IsSurfaceSphere.isSurface (isSurfaceSphere_bdry (f.injective.ne (by decide))
      (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide))
      (f.injective.ne (by decide)) (f.injective.ne (by decide)))
  | j + 1 => by
    rw [model, csum_map]
    exact hG.isSurface_csum (isSurface_liftK_model hG hP f j) ((isGlue_model hP j).relabel f)

/-- **The standard models are closed surfaces**, wherever they are placed. -/
theorem isSurface_liftK_stdModel (f : ℕ ↪ V) : ∀ b n, IsSurface (liftK f (stdModel b n))
  | true, n => isSurface_liftK_model goodPiece_T9 isPiece_T9 f n
  | false, n => isSurface_liftK_model goodPiece_P6 isPiece_P6 f (n + 1)

/-- **The standard models are closed surfaces.** -/
theorem isSurface_stdModel (b : Bool) (n : ℕ) : IsSurface (stdModel b n) := by
  simpa only [liftK_refl] using isSurface_liftK_stdModel (Function.Embedding.refl ℕ) b n

/-- **Adding a summand to a model.** If `M` is related by moves to a placed model `model P j`,
then `M # P`, glued anywhere, is related by moves to the placed `model P (j + 1)`. -/
theorem add_model [Infinite V] {P : Finset (Finset ℕ)} {k : ℕ} (hG : GoodPiece P k)
    (hP : IsPiece P) {M : Finset (Finset V)} {σ : Finset V} {f h : ℕ ↪ V} {j : ℕ}
    (hM : IsSurface M) (he : EqvGen Move2 M (liftK f (model P j)))
    (hg : IsGlue M σ P {0, 1, 2} h) :
    EqvGen Move2 (csum M σ P {0, 1, 2} h) (liftK f (model P (j + 1))) := by
  rw [model, csum_map]
  exact hG.add he hM hg ((isGlue_model hP j).relabel f)

/-! ## Dyck's relation -/

lemma eDyck_012 : ({0, 1, 2} : Finset ℕ).map eDyck = {1, 3, 4} := by decide +kernel
lemma e134_map : ({0, 1, 2} : Finset ℕ).map e134 = {1, 3, 4} := by decide +kernel
lemma eDyck_T9 : ∀ m ∈ verts2 T9, m ∉ ({0, 1, 2} : Finset ℕ) →
    3 ≤ eDyck m ∧ eDyck m ∉ verts2 P6 := by decide +kernel
lemma e134_KB' : ∀ m ∈ verts2 KB, m ∉ ({0, 1, 2} : Finset ℕ) →
    3 ≤ e134 m ∧ e134 m ∉ verts2 P6 := by decide +kernel
lemma X_inner : ∀ t ∈ (P6.erase {0, 1, 2}).erase {1, 3, 4} ∪ liftK eDyck (T9.erase {0, 1, 2}),
    ∃ m ∈ t, 3 ≤ m := by decide +kernel

/-- A vertex outside both summands stays outside their connected sum. -/
lemma fresh_csum {M : Finset (Finset V)} {s : Finset V} {P : Finset (Finset ℕ)} {τ₀ : Finset ℕ}
    {F : ℕ ↪ V} {m : ℕ} (hM : F m ∉ verts2 M) (hm : m ∉ verts2 P) :
    F m ∉ verts2 (csum M s P τ₀ F) := by
  rw [csum, verts2_union, mem_union, not_or, verts2_liftK, mem_map']
  exact ⟨fun H => hM (verts2_mono (erase_subset _ _) H),
    fun H => hm (verts2_mono (erase_subset _ _) H)⟩

/-- **Dyck's relation** `P6 # T9 ~ P6 # P6 # P6`, inside a surface. A projective plane glued at
`s` with a torus glued at its triangle `134` is related by moves to three projective planes, each
glued at the triangle `134` of the one before. -/
theorem dyck_step [Infinite V] {M₀ : Finset (Finset V)} {s : Finset V} {h₁ h₂ : ℕ ↪ V}
    (hM₀ : IsSurface M₀) (hs : IsGlue M₀ s P6 {0, 1, 2} h₁)
    (ht : IsGlue (csum M₀ s P6 {0, 1, 2} h₁) (({1, 3, 4} : Finset ℕ).map h₁) T9 {0, 1, 2} h₂) :
    ∃ F : ℕ ↪ V, IsGlue M₀ s P6 {0, 1, 2} F ∧
      IsGlue (csum M₀ s P6 {0, 1, 2} F) (({1, 3, 4} : Finset ℕ).map F) P6 {0, 1, 2}
        (e134.trans F) ∧
      IsGlue (csum (csum M₀ s P6 {0, 1, 2} F) (({1, 3, 4} : Finset ℕ).map F) P6 {0, 1, 2}
          (e134.trans F)) (({1, 3, 4} : Finset ℕ).map (e134.trans F)) P6 {0, 1, 2}
        (e134.trans (e134.trans F)) ∧
      EqvGen Move2 (csum (csum M₀ s P6 {0, 1, 2} h₁) (({1, 3, 4} : Finset ℕ).map h₁) T9
          {0, 1, 2} h₂)
        (csum (csum (csum M₀ s P6 {0, 1, 2} F) (({1, 3, 4} : Finset ℕ).map F) P6 {0, 1, 2}
          (e134.trans F)) (({1, 3, 4} : Finset ℕ).map (e134.trans F)) P6 {0, 1, 2}
          (e134.trans (e134.trans F))) := by
  obtain ⟨F, hF, hFf⟩ := exists_glue goodPiece_P6 hM₀.card hs.mem (verts2 M₀)
  have hM₁ := goodPiece_P6.isSurface_csum hM₀ hs
  have hnot : ({1, 3, 4} : Finset ℕ).map F ∉ M₀.erase s := fun H =>
    hFf 3 le_rfl (mem_verts2.mpr ⟨_, mem_of_mem_erase H, mem_map_of_mem F (by simp)⟩)
  have hT2 : IsGlue (csum M₀ s P6 {0, 1, 2} F) (({1, 3, 4} : Finset ℕ).map F) T9 {0, 1, 2}
      (eDyck.trans F) :=
    ⟨mem_union_right _ (map_mem_liftK.mpr P6_mem134), T9_mem012,
      by rw [← Finset.map_map, eDyck_012], fun m hm hm0 => by
        obtain ⟨h3, hP⟩ := eDyck_T9 m hm hm0
        rw [Function.Embedding.trans_apply]
        exact fresh_csum (hFf _ h3) hP⟩
  have hKB : IsGlue (csum M₀ s P6 {0, 1, 2} F) (({1, 3, 4} : Finset ℕ).map F) KB {0, 1, 2}
      (e134.trans F) :=
    ⟨mem_union_right _ (map_mem_liftK.mpr P6_mem134), KB_mem012,
      by rw [← Finset.map_map, e134_map], fun m hm hm0 => by
        obtain ⟨h3, hP⟩ := e134_KB' m hm hm0
        rw [Function.Embedding.trans_apply]
        exact fresh_csum (hFf _ h3) hP⟩
  have E1 := goodPiece_T9.add (goodPiece_P6.homog hM₀ hs hF) hM₁ ht hT2
  have e1 : csum (csum M₀ s P6 {0, 1, 2} F) (({1, 3, 4} : Finset ℕ).map F) T9 {0, 1, 2}
      (eDyck.trans F) = M₀.erase s ∪ liftK F ((P6.erase {0, 1, 2}).erase {1, 3, 4} ∪
        liftK eDyck (T9.erase {0, 1, 2})) := csum_csum hnot
  have e2 : csum (csum M₀ s P6 {0, 1, 2} F) (({1, 3, 4} : Finset ℕ).map F) KB {0, 1, 2}
      (e134.trans F) = M₀.erase s ∪ liftK F ((P6.erase {0, 1, 2}).erase {1, 3, 4} ∪
        liftK e134 (KB.erase {0, 1, 2})) := csum_csum hnot
  have hC : Ctx (M₀.erase s) F {0, 1, 2} [] :=
    ⟨fun n hn hv => hFf n (by simp only [mem_insert, mem_singleton, not_or] at hn; omega)
      (verts2_mono (erase_subset _ _) hv), by simp⟩
  have hD : Disj (M₀.erase s) F
      ((P6.erase {0, 1, 2}).erase {1, 3, 4} ∪ liftK eDyck (T9.erase {0, 1, 2})) := fun t ht => by
    obtain ⟨m, hm, h3⟩ := X_inner t ht
    exact hC.map_notMem_of_fresh hm (by simp only [mem_insert, mem_singleton]; omega)
  have E2 := checkChain_sound hC _ hD chain_dyck
  have hK := twist_of_KB hKB
  refine ⟨F, hF, hK.1, hK.2.1, ?_⟩
  rw [← hK.2.2, e2]
  rw [e1] at E1
  exact EqvGen.trans _ _ _ E1 E2

/-- **A torus summand on a non-orientable model is two crosscaps.** If `M` is related by moves to
a placed `model P6 (n + 1)`, then `M # T9` is related by moves to the placed `model P6 (n + 3)`. -/
theorem t9_on_p6 [Infinite V] {M : Finset (Finset V)} {σ : Finset V} {f h : ℕ ↪ V} {n : ℕ}
    (hM : IsSurface M) (he : EqvGen Move2 M (liftK f (model P6 (n + 1))))
    (hg : IsGlue M σ T9 {0, 1, 2} h) :
    EqvGen Move2 (csum M σ T9 {0, 1, 2} h) (liftK f (model P6 (n + 3))) := by
  have hN : liftK f (model P6 (n + 1)) = csum (liftK f (model P6 n)) ((triOf (site n)).map f)
      P6 {0, 1, 2} ((gl n).trans f) := by rw [model, csum_map]
  have htri : (triOf (site (n + 1))).map f = ({1, 3, 4} : Finset ℕ).map ((gl n).trans f) := by
    rw [← triOf_site_succ, Finset.map_map]
  have hT := (isGlue_model' isPiece_P6 T9_mem012 (n + 1)).relabel f
  rw [hN, htri] at hT
  rw [hN] at he
  have hM₀ := isSurface_liftK_model goodPiece_P6 isPiece_P6 f n
  have hs := (isGlue_model isPiece_P6 n).relabel f
  obtain ⟨F, hF₁, hF₂, hF₃, hD⟩ := dyck_step hM₀ hs hT
  have hQ₁ := goodPiece_P6.isSurface_csum hM₀ hF₁
  have hQ₂ := goodPiece_P6.isSurface_csum hQ₁ hF₂
  have e₁ := add_model goodPiece_P6 isPiece_P6 hM₀ (EqvGen.refl _) hF₁
  have e₂ := add_model goodPiece_P6 isPiece_P6 hQ₁ e₁ hF₂
  have e₃ := add_model goodPiece_P6 isPiece_P6 hQ₂ e₂ hF₃
  exact EqvGen.trans _ _ _ (goodPiece_T9.add he hM hg hT) (EqvGen.trans _ _ _ hD e₃)

/-- Two independent erase-and-add steps commute. -/
lemma erase_union_comm {W : Type*} [DecidableEq W] {M T P : Finset W} {s t : W} (ht : t ∉ T)
    (hs : s ∉ P) : (M.erase s ∪ T).erase t ∪ P = (M.erase t ∪ P).erase s ∪ T := by
  rw [erase_union_distrib, erase_union_distrib, erase_eq_of_notMem ht, erase_eq_of_notMem hs,
    erase_right_comm, union_right_comm]

lemma T9_verts_lt : ∀ m ∈ verts2 T9, m ∉ ({0, 1, 2} : Finset ℕ) → 3 ≤ m := by decide +kernel

/-- **A crosscap on an orientable model.** If `M` is related by moves to a placed `model T9 n`
(the sphere with `n` handles), then `M # P6` is related by moves to the placed
`model P6 (2 n + 1)`. -/
theorem p6_on_t9 [Infinite V] : ∀ (n : ℕ) {M : Finset (Finset V)} {σ : Finset V} {f h : ℕ ↪ V},
    IsSurface M → EqvGen Move2 M (liftK f (model T9 n)) → IsGlue M σ P6 {0, 1, 2} h →
    EqvGen Move2 (csum M σ P6 {0, 1, 2} h) (liftK f (model P6 (2 * n + 1)))
  | 0, _, _, _, _, hM, he, hg => add_model goodPiece_P6 isPiece_P6 hM he hg
  | n + 1, M, σ, f, h, hM, he, hg => by
    have hNeq : liftK f (model T9 (n + 1)) = csum (liftK f (model T9 n))
        ((triOf (site n)).map f) T9 {0, 1, 2} ((gl n).trans f) := by rw [model, csum_map]
    rw [hNeq] at he
    have hM₀ := isSurface_liftK_model goodPiece_T9 isPiece_T9 f n
    have hs₁ := (isGlue_model isPiece_T9 n).relabel f
    have hNc := goodPiece_T9.isSurface_csum hM₀ hs₁
    -- a second triangle `t` of the placed `model T9 n`
    obtain ⟨x, y, z, hxy, -, -, hs3⟩ := card_eq_three.mp (hM₀.card _ hs₁.mem)
    obtain ⟨t, htM, hts, -⟩ := exists_other_tri hM₀.closed hs₁.mem (e := {x, y})
      (fun a ha => by rw [hs3]; simp only [mem_insert, mem_singleton] at ha ⊢; tauto)
      (card_pair hxy)
    have htN : t ∈ csum (liftK f (model T9 n)) ((triOf (site n)).map f) T9 {0, 1, 2}
        ((gl n).trans f) := mem_union_left _ (mem_erase.mpr ⟨hts, htM⟩)
    obtain ⟨h₂, hh₂, hh₂F⟩ := exists_glue goodPiece_P6 hNc.card htN
      (verts2 (liftK f (model T9 n)) ∪ (verts2 T9).map ((gl n).trans f))
    -- move the crosscap from `σ` to `t`
    have A := goodPiece_P6.add he hM hg hh₂
    have ht' : t ∉ liftK ((gl n).trans f) (T9.erase {0, 1, 2}) := by
      intro H
      obtain ⟨u, hu, hut⟩ := mem_liftK.mp H
      obtain ⟨m, hmu, h3⟩ := goodPiece_T9.inner u hu
      refine hs₁.fresh m (mem_verts2.mpr ⟨u, mem_of_mem_erase hu, hmu⟩)
        (by simp only [mem_insert, mem_singleton]; omega) (mem_verts2.mpr ⟨t, htM, ?_⟩)
      rw [← hut]
      exact mem_map_of_mem _ hmu
    have hs' : (triOf (site n)).map f ∉ liftK h₂ (P6.erase {0, 1, 2}) := by
      intro H
      obtain ⟨u, hu, hut⟩ := mem_liftK.mp H
      obtain ⟨m, hmu, h3⟩ := goodPiece_P6.inner u hu
      refine hh₂F m h3 (mem_union_left _ (mem_verts2.mpr ⟨_, hs₁.mem, ?_⟩))
      rw [← hut]
      exact mem_map_of_mem _ hmu
    have hcomm : csum (csum (liftK f (model T9 n)) ((triOf (site n)).map f) T9 {0, 1, 2}
        ((gl n).trans f)) t P6 {0, 1, 2} h₂ = csum (csum (liftK f (model T9 n)) t P6 {0, 1, 2} h₂)
        ((triOf (site n)).map f) T9 {0, 1, 2} ((gl n).trans f) := by
      simp only [csum]
      exact erase_union_comm ht' hs'
    rw [hcomm] at A
    have hg₀ : IsGlue (liftK f (model T9 n)) t P6 {0, 1, 2} h₂ :=
      ⟨htM, P6_mem012, hh₂.map, fun m _ hm0 H => hh₂F m
        (by simp only [mem_insert, mem_singleton, not_or] at hm0; omega) (mem_union_left _ H)⟩
    have hg₁ : IsGlue (csum (liftK f (model T9 n)) t P6 {0, 1, 2} h₂) ((triOf (site n)).map f)
        T9 {0, 1, 2} ((gl n).trans f) := by
      refine ⟨mem_union_left _ (mem_erase.mpr ⟨Ne.symm hts, hs₁.mem⟩), T9_mem012, hs₁.map,
        fun m hm hm0 H => ?_⟩
      rw [csum, verts2_union, mem_union, verts2_liftK] at H
      rcases H with H | H
      · exact hs₁.fresh m hm hm0 (verts2_mono (erase_subset _ _) H)
      · obtain ⟨m', -, hm'⟩ := mem_map.mp H
        by_cases h3 : 3 ≤ m'
        · exact hh₂F m' h3 (mem_union_right _ (hm' ▸ mem_map_of_mem _ hm))
        · refine hs₁.fresh m hm hm0 (mem_verts2.mpr ⟨t, htM, ?_⟩)
          rw [← hm', ← hh₂.map]
          exact mem_map_of_mem _ (by simp only [mem_insert, mem_singleton]; omega)
    have hQ := goodPiece_P6.isSurface_csum hM₀ hg₀
    have IH := p6_on_t9 n hM₀ (EqvGen.refl _) hg₀
    have B := t9_on_p6 hQ IH hg₁
    rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    exact EqvGen.trans _ _ _ A B

/-! ## The main theorem -/

/-- `L` is **related by moves to a standard model**, placed in `V` by some embedding. -/
def HasModel (L : Finset (Finset V)) : Prop :=
  ∃ (b : Bool) (n : ℕ) (f : ℕ ↪ V), EqvGen Move2 L (liftK f (stdModel b n))

/-- Having a model is invariant under moves. -/
lemma HasModel.of_eqvGen {L L' : Finset (Finset V)} (h : EqvGen Move2 L L')
    (hM : HasModel L') : HasModel L := by
  obtain ⟨b, n, f, e⟩ := hM
  exact ⟨b, n, f, EqvGen.trans _ _ _ h e⟩

/-- A torus summand keeps a surface related to a model. -/
theorem sum_T9 [Infinite V] {M : Finset (Finset V)} {σ : Finset V} {h : ℕ ↪ V}
    (hM : IsSurface M) (hstd : HasModel M) (hg : IsGlue M σ T9 {0, 1, 2} h) :
    HasModel (csum M σ T9 {0, 1, 2} h) := by
  obtain ⟨b, n, f, he⟩ := hstd
  cases b with
  | false => exact ⟨false, n + 2, f, t9_on_p6 (n := n) hM he hg⟩
  | true => exact ⟨true, n + 1, f, add_model goodPiece_T9 isPiece_T9 hM he hg⟩

/-- A projective-plane summand keeps a surface related to a model. -/
theorem sum_P6 [Infinite V] {M : Finset (Finset V)} {σ : Finset V} {h : ℕ ↪ V}
    (hM : IsSurface M) (hstd : HasModel M) (hg : IsGlue M σ P6 {0, 1, 2} h) :
    HasModel (csum M σ P6 {0, 1, 2} h) := by
  obtain ⟨b, n, f, he⟩ := hstd
  cases b with
  | false => exact ⟨false, n + 1, f, add_model (j := n + 1) goodPiece_P6 isPiece_P6 hM he hg⟩
  | true => exact ⟨false, 2 * n, f, p6_on_t9 n hM he hg⟩

/-- **The classification of closed surfaces.** Every closed triangulated surface (triangles,
every edge in two triangles, connected vertex links, connected) is related by 2D bistellar moves
to a standard model `stdModel b n`, placed in `V` by an embedding: the sphere with `n` handles
(`b = true`) or the connected sum of `n + 1` projective planes (`b = false`). -/
theorem classify [Infinite V] {L : Finset (Finset V)} (hS : IsSurface L) :
    ∃ (b : Bool) (n : ℕ) (f : ℕ ↪ V), EqvGen Move2 L (liftK f (stdModel b n)) := by
  suffices key : ∀ m : ℕ, ∀ L : Finset (Finset V), IsSurface L → 2 - euler2 L ≤ (m : ℤ) →
      HasModel L from key _ L hS (Int.self_le_toNat _)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  -- removing a handle or a crosscap raises `χ`
  have hH : ∀ {L₁ : Finset (Finset V)}, 2 - euler2 L₁ ≤ (m : ℤ) → HandleOf L₁ → HasModel L₁ := by
    rintro L₁ hm ⟨L', σ, h, hS', hχ, ⟨hg, hE⟩ | ⟨hg, hE⟩⟩
    · have hle := hS'.euler_le
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact (sum_T9 hS' (ihm m' (by omega) L' hS' (by omega)) hg).of_eqvGen hE
    · have hle := hS'.euler_le
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hK := twist_of_KB hg
      have h₁ := sum_P6 hS' (ihm m' (by omega) L' hS' (by omega)) hK.1
      have h₂ := sum_P6 (goodPiece_P6.isSurface_csum hS' hK.1) h₁ hK.2.1
      rw [hK.2.2] at hE
      exact h₂.of_eqvGen hE
  have hX : ∀ {L₁ : Finset (Finset V)}, 2 - euler2 L₁ ≤ (m : ℤ) → CrosscapOf L₁ →
      HasModel L₁ := by
    rintro L₁ hm ⟨L', σ, h, hS', hχ, hg, hE⟩
    have hle := hS'.euler_le
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact (sum_P6 hS' (ihm m' (by omega) L' hS' (by omega)) hg).of_eqvGen hE
  intro L₁ hS₁ hm₁
  -- induction on the number of triangles
  suffices mid : ∀ c, ∀ L : Finset (Finset V), #L = c → IsSurface L → 2 - euler2 L ≤ (m : ℤ) →
      HasModel L from mid _ L₁ rfl hS₁ hm₁
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihn =>
  intro L hc hS hm
  obtain ⟨v, hv⟩ := hS.verts_nonempty
  -- induction on the degree of `v`
  suffices inner : ∀ d, ∀ L' : Finset (Finset V), #L' = c → IsSurface L' →
      2 - euler2 L' ≤ (m : ℤ) → v ∈ verts2 L' → deg2 L' v = d → HasModel L' from
    inner _ L hc hS hm hv rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro L' hc' hS' hm' hv' hd
  obtain ⟨v₁, v₂, v₃, v₄, h12, h23, h34, h13, h42⟩ := hS'.local_structure hv'
  by_cases h14 : v₁ = v₄
  · -- degree 3: the link of `v` is the triangle `v₁ v₂ v₃`
    rw [← h14] at h34
    obtain ⟨hva, hvb, hab⟩ := tri_ne (hS'.card _ h12)
    obtain ⟨-, hvc, hbc⟩ := tri_ne (hS'.card _ h23)
    by_cases habc : ({v₁, v₂, v₃} : Finset V) ∈ L'
    · rw [hS'.eq_bdry h12 h23 h34 habc]
      obtain ⟨f, hf, -⟩ := exists_emb [v, v₁, v₂, v₃]
        (by simp [hva, hvb, hvc, hab, h13, hbc]) ∅
      have f0 : f 0 = v := hf 0 (by simp)
      have f1 : f 1 = v₁ := hf 1 (by simp)
      have f2 : f 2 = v₂ := hf 2 (by simp)
      have f3 : f 3 = v₃ := hf 3 (by simp)
      refine ⟨true, 0, f, ?_⟩
      rw [show stdModel true 0 = bdry 0 1 2 3 from rfl, liftK_bdry, f0, f1, f2, f3]
      exact EqvGen.refl _
    · obtain ⟨L₀, hmv, hlt⟩ := hS'.remove_deg3 h12 h23 h34 habc
      have hχ := euler2_eq_of_eqvGen (EqvGen.rel _ _ hmv)
      exact (ihn #L₀ (by omega) L₀ rfl ((Move2.isSurface_iff hmv).mpr hS') (by rw [hχ]; exact hm')).of_eqvGen
        (EqvGen.symm _ _ (EqvGen.rel _ _ hmv))
  · -- degree at least 4: flip an edge at `v`, or cut along a curve through `v`
    have hflip : ∀ {x y z : V}, ({v, x, y} : Finset V) ∈ L' → ({v, x, z} : Finset V) ∈ L' →
        y ≠ z → ({y, z} : Finset V) ∉ edges2 L' → HasModel L' := by
      intro x y z h₁ h₂ hyz hne
      obtain ⟨L'', hmv, hcard, hdeg, hv''⟩ := hS'.flip_lowers h₁ h₂ hyz
        (fun τ hτ hsub => hne (mem_edges2.mpr ⟨τ, hτ, hsub, card_pair hyz⟩))
      have hχ := euler2_eq_of_eqvGen (EqvGen.rel _ _ hmv)
      exact (ihd (deg2 L'' v) (by omega) L'' (hcard.trans hc') ((Move2.isSurface_iff hmv).mp hS')
        (by rw [← hχ]; exact hm') hv'' rfl).of_eqvGen (EqvGen.rel _ _ hmv)
    by_cases e13 : ({v₁, v₃} : Finset V) ∈ edges2 L'
    · by_cases e24 : ({v₂, v₄} : Finset V) ∈ edges2 L'
      · obtain ⟨τ₁, hτ₁, hs₁, -⟩ := mem_edges2.mp e13
        obtain ⟨τ₂, hτ₂, hs₂, -⟩ := mem_edges2.mp e24
        rcases hS'.cut h12 h23 h34 h13 (Ne.symm h42) h14
            ⟨τ₁, hτ₁, hs₁ (by simp), hs₁ (by simp)⟩ ⟨τ₂, hτ₂, hs₂ (by simp), hs₂ (by simp)⟩ with
          ⟨A, g, hc⟩ | ⟨A, g, hc⟩
        · exact hH hm' (handle_of_cut hS' hc)
        · exact hX hm' (crosscap_of_cut hS' hc)
      · exact hflip (by rw [tri_swap]; exact h23) h34 (Ne.symm h42) e24
    · exact hflip (by rw [tri_swap]; exact h12) h23 h13 e13

/-- **Closed surfaces are exactly what is related by moves to a standard model.** -/
theorem isSurface_iff_classify [Infinite V] {L : Finset (Finset V)} :
    IsSurface L ↔ ∃ (b : Bool) (n : ℕ) (f : ℕ ↪ V), EqvGen Move2 L (liftK f (stdModel b n)) :=
  ⟨classify, fun ⟨_, _, f, h⟩ => (isSurface_iff_of_eqvGen h).mpr (isSurface_liftK_stdModel f _ _)⟩

/-! ## Uniqueness of the model -/

/-- An orientation survives placing a complex. -/
theorem isOrientation_liftK {K : Finset (Finset ℕ)} {o : ℕ → ℕ → ℕ → ℤ}
    (ho : IsOrientation K o) (f : ℕ ↪ V) : IsOrientation (liftK f K) (pushO f o) where
  rot := pushO_rot ho.rot
  swap := pushO_swap ho.swap
  supp x y z h := by
    by_cases hr : x ∈ Set.range f ∧ y ∈ Set.range f ∧ z ∈ Set.range f
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := hr
      rw [pushO_apply] at h
      rw [← tri_map]
      exact map_mem_liftK.mpr (ho.supp a b c h)
    · exact absurd (pushO_eq_zero hr) h
  unit x y z h := by
    obtain ⟨t, ht, he⟩ := mem_liftK.mp h
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
    rw [pushO_apply]
    exact ho.unit a b c ht
  cycle u v := by
    rw [verts2_liftK]
    by_cases huv : u ∈ Set.range f ∧ v ∈ Set.range f
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := huv
      rw [sum_map]
      simp only [pushO_apply]
      exact ho.cycle a b
    · exact sum_eq_zero fun w _ => pushO_eq_zero (by tauto)

/-- **A placed standard model is orientable exactly when it is a sphere with handles.** -/
theorem isOrientable_liftK_stdModel (f : ℕ ↪ V) (b : Bool) (n : ℕ) :
    IsOrientable (liftK f (stdModel b n)) ↔ b = true := by
  cases b with
  | false =>
    refine iff_of_false ?_ (by decide)
    show ¬ IsOrientable (liftK f (model P6 (n + 1)))
    rw [model, csum_map]
    exact not_isOrientable_csum_P6 ((isGlue_model isPiece_P6 n).relabel f)
  | true =>
    obtain ⟨o, ho⟩ := isOrientable_model_T9 n
    exact iff_of_true ⟨_, isOrientation_liftK ho f⟩ rfl

/-- **Orientability and the Euler characteristic determine the standard model.** -/
theorem stdModel_eq_of_inv {b b' : Bool} {n n' : ℕ} (ho : b = true ↔ b' = true)
    (he : euler2 (stdModel b n) = euler2 (stdModel b' n')) : b = b' ∧ n = n' := by
  cases b <;> cases b'
  · rw [euler2_stdModel_false, euler2_stdModel_false] at he
    exact ⟨rfl, by omega⟩
  · exact absurd (ho.mpr rfl) (by decide)
  · exact absurd (ho.mp rfl) (by decide)
  · rw [euler2_stdModel_true, euler2_stdModel_true] at he
    exact ⟨rfl, by omega⟩

/-- **The standard model is unique**: a complex related by moves to two placed standard models
has the same model twice (moves preserve orientability and the Euler characteristic). -/
theorem classify_unique {L : Finset (Finset V)} {b b' : Bool} {n n' : ℕ} {f f' : ℕ ↪ V}
    (h : EqvGen Move2 L (liftK f (stdModel b n)))
    (h' : EqvGen Move2 L (liftK f' (stdModel b' n'))) : b = b' ∧ n = n' := by
  have hE := EqvGen.trans _ _ _ (EqvGen.symm _ _ h) h'
  refine stdModel_eq_of_inv ?_ ?_
  · rw [← isOrientable_liftK_stdModel f, ← isOrientable_liftK_stdModel f']
    exact isOrientable_iff_of_eqvGen hE
  · have := euler2_eq_of_eqvGen hE
    rwa [euler2_liftK, euler2_liftK] at this

/-- **The model of a surface is read off from its invariants**: a closed surface `L` is related
by moves to a placed `stdModel b n` exactly when `L` is orientable iff `b = true`, and `L` has the
Euler characteristic of the model. -/
theorem exists_eqvGen_stdModel_iff [Infinite V] {L : Finset (Finset V)} (hS : IsSurface L)
    (b : Bool) (n : ℕ) : (∃ f : ℕ ↪ V, EqvGen Move2 L (liftK f (stdModel b n))) ↔
      ((IsOrientable L ↔ b = true) ∧ euler2 L = euler2 (stdModel b n)) := by
  constructor
  · rintro ⟨f, h⟩
    refine ⟨(isOrientable_iff_of_eqvGen h).trans (isOrientable_liftK_stdModel f b n), ?_⟩
    rw [euler2_eq_of_eqvGen h, euler2_liftK]
  · rintro ⟨ho, he⟩
    obtain ⟨b', n', f, h⟩ := classify hS
    have ho' := (isOrientable_iff_of_eqvGen h).trans (isOrientable_liftK_stdModel f b' n')
    have he' : euler2 L = euler2 (stdModel b' n') := by rw [euler2_eq_of_eqvGen h, euler2_liftK]
    obtain ⟨rfl, rfl⟩ := stdModel_eq_of_inv (ho'.symm.trans ho) (he'.symm.trans he)
    exact ⟨f, h⟩

end Lightlike.Surfaces
