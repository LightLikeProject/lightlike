import Lightlike.Surfaces.Relabel
import Lightlike.PL.PachnerPL

/-!
# Classification of closed combinatorial surfaces up to PL homeomorphism

Two closed combinatorial surfaces are PL homeomorphic exactly when they have the same
orientability and Euler characteristic, and every closed surface is PL homeomorphic to exactly one
standard model, a sphere with handles or a connected sum of projective planes.

The statement composes `pachner_plHomeomorphic` (Pachner's theorem in PL form, for closed
combinatorial manifolds in every dimension) with the classification up to 2D bistellar moves of
`Lightlike/Surfaces/Classify.lean`. The infinite vertex type provides the new vertices that the
moves need.

## Main results

* `plHomeomorphic_iff`: PL homeomorphic closed surfaces have the same orientability and Euler
  characteristic, and conversely.
* `exists_plHomeomorphic_stdModel`: a closed surface is PL homeomorphic to a standard model.
* `stdModel_eq_of_plHomeomorphic`: PL homeomorphic standard models are equal.
-/

open Finset Lightlike.PR Lightlike.PL Lightlike.PL.SComplex

namespace Lightlike.Surfaces

variable {V : Type*} [DecidableEq V]

lemma IsSurface.nonempty_vertices {L : Finset (Finset V)} (hS : IsSurface L) : Nonempty V := by
  obtain ⟨t, ht⟩ := hS.nonempty
  obtain ⟨x, hx⟩ : t.Nonempty := card_pos.1 (by rw [hS.card t ht]; norm_num)
  exact ⟨x⟩

/-- **PL homeomorphic closed surfaces have the same orientability and Euler characteristic.** -/
theorem invariants_of_plHomeomorphic [Infinite V] {L L' : Finset (Finset V)} (hS : IsSurface L)
    (hS' : IsSurface L') (h : PLHomeomorphic (closure L) (closure L')) :
    (IsOrientable L ↔ IsOrientable L') ∧ euler2 L = euler2 L' := by
  have := hS.nonempty_vertices
  have h0 : (∅ : Finset V) ∈ closure L := by
    obtain ⟨t, ht⟩ := hS.nonempty
    exact mem_closure.2 ⟨t, ht, empty_subset _⟩
  have h0' : (∅ : Finset V) ∈ closure L' := by
    obtain ⟨t, ht⟩ := hS'.nonempty
    exact mem_closure.2 ⟨t, ht, empty_subset _⟩
  have hb := (pachner_plHomeomorphic hS.isClosedCombManifold h0 h0').1 h
  have hst := hb.stellarEquiv
  have hchain := eqvGen_move2_of_stellarEquiv hS hst hS'.card
  refine ⟨?_, ?_⟩
  · rw [← isOrientable_mapTri_iff (Function.Embedding.inl : V ↪ V ⊕ ℕ),
      ← isOrientable_mapTri_iff (Function.Embedding.inl : V ↪ V ⊕ ℕ)]
    exact isOrientable_iff_of_eqvGen hchain
  · have := euler2_eq_of_eqvGen hchain
    rwa [euler2_mapTri, euler2_mapTri] at this

/-- A standard model placed in `V` is PL homeomorphic to the model. -/
lemma plHomeomorphic_liftK {K : Finset (Finset ℕ)} (f : ℕ ↪ V) :
    PLHomeomorphic (closure K) (closure (liftK f K)) := by
  have : closure (liftK f K) = (closure K).map f := (map_closure K f).symm
  rw [this]
  exact PLHomeomorphic.map _ f

/-- **Closed surfaces with the same orientability and Euler characteristic are PL homeomorphic.** -/
theorem plHomeomorphic_of_invariants [Infinite V] {L L' : Finset (Finset V)} (hS : IsSurface L)
    (hS' : IsSurface L') (ho : IsOrientable L ↔ IsOrientable L') (he : euler2 L = euler2 L') :
    PLHomeomorphic (closure L) (closure L') := by
  obtain ⟨b, n, f, h⟩ := classify hS
  have hoL : IsOrientable L ↔ b = true :=
    (isOrientable_iff_of_eqvGen h).trans (isOrientable_liftK_stdModel f b n)
  have heL : euler2 L = euler2 (stdModel b n) := by rw [euler2_eq_of_eqvGen h, euler2_liftK]
  obtain ⟨f', h'⟩ := (exists_eqvGen_stdModel_iff hS' b n).2 ⟨ho.symm.trans hoL, he ▸ heL⟩
  have e₁ : PLHomeomorphic (closure L) (closure (liftK f (stdModel b n))) :=
    PLHomeomorphic.of_stellarEquiv ((stellarEquiv_of_eqvGen_move2 h).2 hS.card)
  have e₂ : PLHomeomorphic (closure L') (closure (liftK f' (stdModel b n))) :=
    PLHomeomorphic.of_stellarEquiv ((stellarEquiv_of_eqvGen_move2 h').2 hS'.card)
  exact e₁.trans ((plHomeomorphic_liftK f).symm.trans ((plHomeomorphic_liftK f').trans e₂.symm))

/-- **Classification of closed combinatorial surfaces up to PL homeomorphism.** Two closed
surfaces on an infinite vertex type are PL homeomorphic exactly when they have the same
orientability and the same Euler characteristic. -/
theorem plHomeomorphic_iff [Infinite V] {L L' : Finset (Finset V)} (hS : IsSurface L)
    (hS' : IsSurface L') :
    PLHomeomorphic (closure L) (closure L') ↔
      (IsOrientable L ↔ IsOrientable L') ∧ euler2 L = euler2 L' :=
  ⟨invariants_of_plHomeomorphic hS hS', fun ⟨ho, he⟩ => plHomeomorphic_of_invariants hS hS' ho he⟩

/-- **A closed surface is PL homeomorphic to a standard model.** -/
theorem exists_plHomeomorphic_stdModel [Infinite V] {L : Finset (Finset V)} (hS : IsSurface L) :
    ∃ (b : Bool) (n : ℕ), PLHomeomorphic (closure L) (closure (stdModel b n)) := by
  obtain ⟨b, n, f, h⟩ := classify hS
  exact ⟨b, n, (PLHomeomorphic.of_stellarEquiv ((stellarEquiv_of_eqvGen_move2 h).2 hS.card)).trans
    (plHomeomorphic_liftK f).symm⟩

/-- **PL homeomorphic standard models are equal.** -/
theorem stdModel_eq_of_plHomeomorphic {b b' : Bool} {n n' : ℕ}
    (h : PLHomeomorphic (closure (stdModel b n)) (closure (stdModel b' n'))) :
    b = b' ∧ n = n' := by
  have hS : IsSurface (stdModel b n) := by
    simpa [liftK_refl] using isSurface_liftK_stdModel (Function.Embedding.refl ℕ) b n
  have hS' : IsSurface (stdModel b' n') := by
    simpa [liftK_refl] using isSurface_liftK_stdModel (Function.Embedding.refl ℕ) b' n'
  obtain ⟨ho, he⟩ := invariants_of_plHomeomorphic hS hS' h
  have o₁ := isOrientable_liftK_stdModel (Function.Embedding.refl ℕ) b n
  have o₂ := isOrientable_liftK_stdModel (Function.Embedding.refl ℕ) b' n'
  simp only [liftK_refl] at o₁ o₂
  exact stdModel_eq_of_inv ((o₁.symm.trans ho).trans o₂) he

/-- **Every closed surface is PL homeomorphic to exactly one standard model.** -/
theorem existsUnique_plHomeomorphic_stdModel [Infinite V] {L : Finset (Finset V)}
    (hS : IsSurface L) :
    ∃! p : Bool × ℕ, PLHomeomorphic (closure L) (closure (stdModel p.1 p.2)) := by
  obtain ⟨b, n, h⟩ := exists_plHomeomorphic_stdModel hS
  refine ⟨(b, n), h, fun q hq => ?_⟩
  obtain ⟨hb, hn⟩ := stdModel_eq_of_plHomeomorphic (h.symm.trans hq)
  exact Prod.ext hb.symm hn.symm

end Lightlike.Surfaces
