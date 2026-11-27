import Lightlike.SpinFoam.EPRLStateSum.ComplexNetwork

/-!
# Relabelling the vertices of a 4-complex

`relabelComplex K σ` has the 4-simplices `σ s`, `relabelCol σ col` is the colouring `f ↦ col (σ⁻¹ f)`. A permutation `σ` of the vertices changes the
sorted order of the vertices of a 4-simplex `s` by the permutation `posPerm σ s` of the five positions.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The complex with the 4-simplices `σ s`, `s` a 4-simplex of `K`. -/
def relabelComplex (K : Complex4 V) (σ : V ≃ V) : Complex4 V where
  simps := K.simps.image (fun s => s.map σ.toEmbedding)
  card_eq := by
    intro s hs
    obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.1 hs
    rw [Finset.card_map]
    exact K.card_eq s0 hs0

/-- The colouring of the faces of the relabelled complex: `f ↦ col (σ⁻¹ f)`. -/
def relabelCol (σ : V ≃ V) (col : Finset V → ℕ) : Finset V → ℕ := fun f => col (f.map σ.symm.toEmbedding)

lemma map_map_symm (σ : V ≃ V) (f : Finset V) : (f.map σ.toEmbedding).map σ.symm.toEmbedding = f := by
  ext v; simp

lemma map_symm_map (σ : V ≃ V) (f : Finset V) : (f.map σ.symm.toEmbedding).map σ.toEmbedding = f := by
  ext v; simp

lemma mem_relabel_simps (K : Complex4 V) (σ : V ≃ V) (s' : Finset V) :
    s' ∈ (relabelComplex K σ).simps ↔ s'.map σ.symm.toEmbedding ∈ K.simps := by
  unfold relabelComplex
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rwa [map_map_symm]
  · intro h
    exact ⟨_, h, map_symm_map σ s'⟩

lemma mem_relabel_faces (K : Complex4 V) (σ : V ≃ V) (k : ℕ) (f' : Finset V) :
    f' ∈ (relabelComplex K σ).faces k ↔ f'.map σ.symm.toEmbedding ∈ K.faces k := by
  rw [Complex4.mem_faces, Complex4.mem_faces]
  constructor
  · rintro ⟨s', hs', hf, hc⟩
    refine ⟨s'.map σ.symm.toEmbedding, (mem_relabel_simps K σ s').1 hs', Finset.map_subset_map.2 hf, ?_⟩
    rwa [Finset.card_map]
  · rintro ⟨s, hs, hf, hc⟩
    refine ⟨s.map σ.toEmbedding, ?_, ?_, ?_⟩
    · rw [mem_relabel_simps, map_map_symm]; exact hs
    · have := Finset.map_subset_map (f := σ.toEmbedding).2 hf
      rwa [map_symm_map] at this
    · rwa [Finset.card_map] at hc

/-- The permutation of the `n` sorted positions of an `n`-element set `s` that `σ` induces: the new position `a'` of a vertex of `σ s`
goes to the old position of `σ⁻¹` of it in `s`. -/
noncomputable def ordPerm (σ : V ≃ V) (s : Finset V) (n : ℕ) (hs : #s = n) : Equiv.Perm (Fin n) :=
  have hs' : #(s.map σ.toEmbedding) = n := by rw [Finset.card_map]; exact hs
  ((s.map σ.toEmbedding).orderIsoOfFin hs').toEquiv.trans
    ((σ.symm.subtypeEquiv (p := fun v => v ∈ s.map σ.toEmbedding) (q := fun v => v ∈ s)
      (fun a => by simp)).trans (s.orderIsoOfFin hs).toEquiv.symm)

lemma orderEmb_ordPerm (σ : V ≃ V) (s : Finset V) (n : ℕ) (hs : #s = n) (a' : Fin n) :
    s.orderEmbOfFin hs (ordPerm σ s n hs a') =
      σ.symm ((s.map σ.toEmbedding).orderEmbOfFin (by rw [Finset.card_map]; exact hs) a') := by
  unfold ordPerm
  simp only [Equiv.trans_apply]
  rw [← Finset.coe_orderIsoOfFin_apply s hs]
  simp

/-- The position permutation of a 4-simplex. -/
noncomputable def posPerm (σ : V ≃ V) (s : Finset V) (hs : #s = 5) : Equiv.Perm (Fin 5) := ordPerm σ s 5 hs

lemma orderEmb_posPerm (σ : V ≃ V) (s : Finset V) (hs : #s = 5) (a' : Fin 5) :
    s.orderEmbOfFin hs (posPerm σ s hs a') =
      σ.symm ((s.map σ.toEmbedding).orderEmbOfFin (by rw [Finset.card_map]; exact hs) a') :=
  orderEmb_ordPerm σ s 5 hs a'

lemma orderEmb_relabel_ord (σ : V ≃ V) (s : Finset V) (n : ℕ) (hs : #s = n) (a' : Fin n) :
    (s.map σ.toEmbedding).orderEmbOfFin (by rw [Finset.card_map]; exact hs) a' =
      σ (s.orderEmbOfFin hs (ordPerm σ s n hs a')) := by
  rw [orderEmb_ordPerm]
  simp

lemma orderEmb_relabel (σ : V ≃ V) (s : Finset V) (hs : #s = 5) (a' : Fin 5) :
    (s.map σ.toEmbedding).orderEmbOfFin (by rw [Finset.card_map]; exact hs) a' =
      σ (s.orderEmbOfFin hs (posPerm σ s hs a')) := by
  rw [orderEmb_posPerm]
  simp

lemma map_erase_erase_symm (σ : V ≃ V) (s : Finset V) (u v : V) :
    (((s.map σ.toEmbedding).erase (σ u)).erase (σ v)).map σ.symm.toEmbedding = (s.erase u).erase v := by
  rw [show (s.map σ.toEmbedding).erase (σ u) = (s.erase u).map σ.toEmbedding from
      (Finset.map_erase σ.toEmbedding s u).symm,
    show ((s.erase u).map σ.toEmbedding).erase (σ v) = ((s.erase u).erase v).map σ.toEmbedding from
      (Finset.map_erase σ.toEmbedding (s.erase u) v).symm, map_map_symm]

/-- **The spins of a relabelled simplex** are the old spins at the permuted positions. -/
theorem complexJ_relabel (K : Complex4 V) (σ : V ≃ V) (col : Finset V → ℕ) (s : K.simps)
    (s' : (relabelComplex K σ).simps) (hs' : s'.1 = s.1.map σ.toEmbedding) (a' b' : Fin 5) :
    complexJ (relabelComplex K σ) (relabelCol σ col) s' a' b' =
      complexJ K col s (posPerm σ s.1 (K.card_eq _ s.2) a') (posPerm σ s.1 (K.card_eq _ s.2) b') := by
  obtain ⟨sv, hsv⟩ := s'
  simp only at hs'
  subst hs'
  unfold complexJ simplexJ relabelCol
  rw [orderEmb_relabel σ s.1 (K.card_eq _ s.2) a', orderEmb_relabel σ s.1 (K.card_eq _ s.2) b',
    map_erase_erase_symm]

end Lightlike.SpinFoam.EPRLStateSum
