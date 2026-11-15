import Lightlike.PL.CutSpheres
import Lightlike.PL.StellarImage

/-!
# Slicing by finitely many functionals preserves stellar equivalence

If subdivisions of the dimension below are stellar equivalent, then for a geometric complex `K`
and any finite family `H` of affine functionals, `K` is stellar equivalent to its slicing by `H`.
The functionals are adjoined one at a time (`sliceEq_ext`, from `cutSpheres` and the walk through
the mixed poset), and the induction on the index type is closed by renaming the cell indices
along equivalences of the index type.

## Main results

* `SComplex.SliceEq`: `K` and its slicing by `H` are stellar equivalent, the slicing living on
  the cell indices.
* `SComplex.sliceEq_ext`: one more functional preserves this.
* `SComplex.stellarEquiv_slice`: `K` is stellar equivalent to its slicing by any finite family.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

universe u

section Reindex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι ι' : Type*}

/-- Renaming the cell indices along an equivalence of the index type of the functionals. -/
def cellReindex (e : ι ≃ ι') : CellIdx E ι ↪ CellIdx E ι' where
  toFun c := (c.1, c.2 ∘ e.symm)
  inj' a b h := by
    have h' : (a.1, a.2 ∘ e.symm) = (b.1, b.2 ∘ e.symm) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    refine Prod.ext h1 (funext fun i => ?_)
    simpa using congrFun h2 (e i)

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
/-- Reindexing does not change the face. -/
lemma cellReindex_fst (e : ι ≃ ι') (c : CellIdx E ι) : (cellReindex e c).1 = c.1 := rfl

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
/-- Reindexing precomposes the sign pattern with the inverse equivalence. -/
lemma cellReindex_snd (e : ι ≃ ι') (c : CellIdx E ι) (i : ι') :
    (cellReindex e c).2 i = c.2 (e.symm i) := rfl

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
/-- Reindexing along `e.symm` and then `e` is the identity. -/
lemma cellReindex_cancel (e : ι ≃ ι') (c : CellIdx E ι') :
    cellReindex e (cellReindex e.symm c) = c :=
  Prod.ext rfl (funext fun i => by rw [cellReindex_snd, cellReindex_snd]; simp)

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
/-- Reindexing preserves and reflects the closure order. -/
lemma cellReindex_le (e : ι ≃ ι') (a b : CellIdx E ι) :
    cellReindex e a ≤ cellReindex e b ↔ a ≤ b := by
  rw [cellIdx_le, cellIdx_le, cellReindex_fst, cellReindex_fst]
  refine and_congr_right fun _ => ⟨fun h i => ?_, fun h i => ?_⟩
  · have := h (e i)
    rwa [cellReindex_snd, cellReindex_snd, e.symm_apply_apply] at this
  · rw [cellReindex_snd, cellReindex_snd]; exact h _

omit [DecidableEq E] in
/-- The set of a reindexed cell is the set of the cell for the reindexed functionals. -/
lemma cellSet_reindex (e : ι ≃ ι') (H : ι' → E → ℝ) (c : CellIdx E ι) :
    cellSet H (cellReindex e c) = cellSet (fun i => H (e i)) c := by
  ext x
  simp only [cellSet, Set.mem_inter_iff, Set.mem_ofPred_eq, cellReindex_fst, cellReindex_snd]
  refine and_congr_right fun _ => ⟨fun h i => ?_, fun h i => ?_⟩
  · have := h (e i)
    rwa [e.symm_apply_apply] at this
  · have := h (e.symm i)
    rwa [e.apply_symm_apply] at this

/-- The cells for renamed functionals are the renamed cells. -/
lemma cells_reindex [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (K : SComplex E) (H : ι' → E → ℝ) :
    cells K H = (cells K (fun i => H (e i))).map (cellReindex e) := by
  ext c
  rw [Finset.mem_map]
  constructor
  · intro hc
    obtain ⟨hσ, hne⟩ := mem_cells.1 hc
    refine ⟨cellReindex e.symm c, mem_cells.2 ⟨hσ, ?_⟩, cellReindex_cancel e c⟩
    rw [← cellSet_reindex e H, cellReindex_cancel]; exact hne
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨hσ, hne⟩ := mem_cells.1 hc'
    exact mem_cells.2 ⟨hσ, by rw [cellSet_reindex]; exact hne⟩

/-- The slicing complex for renamed functionals is the renamed slicing complex. -/
lemma sliceComplex_reindex [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') (K : SComplex E) (H : ι' → E → ℝ) :
    sliceComplex K H = (sliceComplex K (fun i => H (e i))).map (cellReindex e) := by
  unfold sliceComplex
  rw [cells_reindex e K H, orderComplex_map _ (cellReindex_le e)]

end Reindex

section Step

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*}

/-- Mapping a complex along two embeddings that agree gives the same complex. -/
lemma map_congr' {V W : Type*} [DecidableEq V] [DecidableEq W] (K : SComplex V) {f g : V ↪ W}
    (h : ∀ x, f x = g x) : K.map f = K.map g := by
  have : f = g := DFunLike.ext _ _ h
  rw [this]

/-- **`K` is stellar equivalent to its slicing by `H`**, the slicing living on the cell indices
beside the vertices of `K`. -/
def SliceEq [Fintype ι] [DecidableEq ι] (K : SComplex E) (H : ι → E → ℝ) : Prop :=
  StellarEquiv (K.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι))
    ((sliceComplex K H).map (Function.Embedding.inr : CellIdx E ι ↪ E ⊕ CellIdx E ι))

/-- **Slicing is invariant under renaming the functionals.** -/
lemma SliceEq.of_reindex [Fintype ι] [DecidableEq ι] {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (e : ι ≃ ι') {K : SComplex E} {H : ι' → E → ℝ} (h : SliceEq K (fun i => H (e i))) :
    SliceEq K H := by
  unfold SliceEq at h ⊢
  rw [sliceComplex_reindex e K H]
  have := (StellarEquiv.map_iff (Function.Embedding.sumMap (Function.Embedding.refl E)
    (cellReindex e))).2 h
  have e1 : (K.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι)).map
      (Function.Embedding.sumMap (Function.Embedding.refl E) (cellReindex e)) =
      K.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι') := by
    rw [map_map]; exact map_congr' _ fun _ => rfl
  have e2 : ((sliceComplex K fun i => H (e i)).map
      (Function.Embedding.inr : CellIdx E ι ↪ E ⊕ CellIdx E ι)).map
      (Function.Embedding.sumMap (Function.Embedding.refl E) (cellReindex e)) =
      ((sliceComplex K fun i => H (e i)).map (cellReindex e)).map
        (Function.Embedding.inr : CellIdx E ι' ↪ E ⊕ CellIdx E ι') := by
    rw [map_map, map_map]; exact map_congr' _ fun _ => rfl
  rwa [e1, e2] at this

/-- With one more functional adjoined, the slicing is again stellar equivalent to `K`, provided
the cut cells have boundary spheres. -/
lemma sliceEq_ext [Infinite E] [Fintype ι] [DecidableEq ι] {K : SComplex E}
    {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} (hs : CutSpheres K H h)
    (ih : SliceEq K (fun i => ⇑(H i))) : SliceEq K (extH H h) := by
  classical
  have : Infinite (CellIdx E ι) :=
    Infinite.of_injective (fun x : E => ((({x} : Finset E), fun _ => (0 : SignType)) :
      CellIdx E ι)) (fun a b h => by simpa using congrArg (fun c => c.1) h)
  have : Infinite (CellIdx E (ι ⊕ Unit)) :=
    Infinite.of_injective (fun x : E => ((({x} : Finset E), fun _ => (0 : SignType)) :
      CellIdx E (ι ⊕ Unit))) (fun a b h => by simpa using congrArg (fun c => c.1) h)
  have : Infinite (Mixed E ι) := Infinite.of_injective (Mixed.newEmb (E := E) (ι := ι))
    Mixed.newEmb.injective
  unfold SliceEq at ih ⊢
  have h1 := (StellarEquiv.map_iff (Function.Embedding.sumMap (Function.Embedding.refl E)
    (Mixed.oldEmb : CellIdx E ι ↪ Mixed E ι))).2 ih
  have h2 := StellarEquiv.of_in ((stellarEquivIn_slice_ext hs).map
    (Function.Embedding.inr : Mixed E ι ↪ E ⊕ Mixed E ι))
  have e1 : (K.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E ι)).map
      (Function.Embedding.sumMap (Function.Embedding.refl E) Mixed.oldEmb) =
      K.map (Function.Embedding.inl : E ↪ E ⊕ Mixed E ι) := by
    rw [map_map]; exact map_congr' _ fun _ => rfl
  have e2 : ((sliceComplex K (fun i => ⇑(H i))).map
      (Function.Embedding.inr : CellIdx E ι ↪ E ⊕ CellIdx E ι)).map
      (Function.Embedding.sumMap (Function.Embedding.refl E) Mixed.oldEmb) =
      ((sliceComplex K (fun i => ⇑(H i))).map Mixed.oldEmb).map
        (Function.Embedding.inr : Mixed E ι ↪ E ⊕ Mixed E ι) := by
    rw [map_map, map_map]; exact map_congr' _ fun _ => rfl
  rw [e1, e2] at h1
  have h3 := h1.trans h2
  rw [← StellarEquiv.map_iff (Function.Embedding.sumMap (Function.Embedding.refl E)
    (Mixed.newEmb : CellIdx E (ι ⊕ Unit) ↪ Mixed E ι))]
  have e3 : (K.map (Function.Embedding.inl : E ↪ E ⊕ CellIdx E (ι ⊕ Unit))).map
      (Function.Embedding.sumMap (Function.Embedding.refl E) Mixed.newEmb) =
      K.map (Function.Embedding.inl : E ↪ E ⊕ Mixed E ι) := by
    rw [map_map]; exact map_congr' _ fun _ => rfl
  have e4 : ((sliceComplex K (extH H h)).map
      (Function.Embedding.inr : CellIdx E (ι ⊕ Unit) ↪ E ⊕ CellIdx E (ι ⊕ Unit))).map
      (Function.Embedding.sumMap (Function.Embedding.refl E) Mixed.newEmb) =
      ((sliceComplex K (extH H h)).map Mixed.newEmb).map
        (Function.Embedding.inr : Mixed E ι ↪ E ⊕ Mixed E ι) := by
    rw [map_map, map_map]; exact map_congr' _ fun _ => rfl
  rw [e3, e4]
  exact h3


/-- Slicing by `k` functionals, by induction on `k`. -/
lemma sliceEq_fin [Infinite E] {n : ℕ} (hT : SubdivStellar E (n - 1)) {K : SComplex E}
    (hK : IsGeom K) (h0 : ∅ ∈ K) (hKn : ∀ s ∈ K, #s ≤ n + 1) :
    ∀ (k : ℕ) (H : Fin k → E →ᵃ[ℝ] ℝ), SliceEq K (fun i => ⇑(H i)) := by
  intro k
  induction k with
  | zero =>
    intro H
    exact StellarEquiv.of_in (stellarEquivIn_slice_isEmpty K h0 _)
  | succ k ih =>
    intro H
    let e : Fin (k + 1) ≃ Fin k ⊕ Unit :=
      finSuccEquivLast.trans (Equiv.optionEquivSumPUnit (Fin k))
    refine SliceEq.of_reindex e.symm ?_
    have hF : (fun j => (fun i => ⇑(H i)) (e.symm j)) =
        extH (fun i => H (Fin.castSucc i)) (H (Fin.last k)) := by
      funext j
      rcases j with i | ⟨⟩
      · simp [e, extH]
      · simp [e, extH]
    rw [hF]
    exact sliceEq_ext (cutSpheres hT hK hKn _ _) (ih _)

/-- **Slicing a geometric complex by finitely many affine functionals gives a stellar equivalent
complex**, given stellar equivalence of subdivisions of dimension one lower. -/
theorem stellarEquiv_slice [Infinite E] {n : ℕ} (hT : SubdivStellar E (n - 1)) {K : SComplex E}
    (hK : IsGeom K) (h0 : ∅ ∈ K) (hKn : ∀ s ∈ K, #s ≤ n + 1) [Fintype ι] [DecidableEq ι]
    (H : ι → E →ᵃ[ℝ] ℝ) : SliceEq K (fun i => ⇑(H i)) := by
  have := sliceEq_fin hT hK h0 hKn (Fintype.card ι)
    (fun i => H ((Fintype.equivFin ι).symm i))
  exact SliceEq.of_reindex (Fintype.equivFin ι).symm this

end Step

end SComplex
end Lightlike.PL
