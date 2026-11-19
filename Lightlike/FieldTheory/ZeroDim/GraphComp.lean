import Lightlike.FieldTheory.ZeroDim.GraphAlgebra

/-!
# The connected components of a labelled graph

The components of `Γ : LGraph n k` are the closed connected vertex sets (`comps`); every vertex lies in exactly one
(`existsUnique_comp`, from `HalfEdge.existsUnique_componentOn`), and a relabelling `(σ, τ)` maps the components of `Γ`
to those of `(σ, τ) • Γ` by `τ` (`comps_smul`), so the number of components is an invariant of the isomorphism class
(`ncomp_smul`). A step toward Borinsky's Theorem 2.4.1 in the algebra of graphs.
-/

open Finset MulAction

namespace Lightlike.FieldTheory.GraphAlg

variable {n k : ℕ}

open Classical in
/-- The **connected components** of a labelled graph: its closed connected vertex sets. -/
noncomputable def comps (Γ : LGraph n k) : Finset (Finset (Fin k)) :=
  univ.filter fun S => HalfEdge.Closed Γ.att Γ.inv S ∧ HalfEdge.ConnOn Γ.att Γ.inv S

/-- The **number of connected components**. -/
noncomputable def ncomp (Γ : LGraph n k) : ℕ := (comps Γ).card

lemma inv_mem_invOn_univ (Γ : LGraph n k) : Γ.inv ∈ HalfEdge.invOn Γ.att (univ : Finset (Fin k)) :=
  HalfEdge.mem_invOn.2 ⟨Γ.invol, fun h hh => absurd (mem_univ _) hh⟩

/-- Every vertex lies in exactly one component. -/
theorem existsUnique_comp (Γ : LGraph n k) (v : Fin k) : ∃! S, S ∈ comps Γ ∧ v ∈ S := by
  classical
  obtain ⟨S, ⟨⟨-, hv⟩, hc, hconn⟩, huniq⟩ :=
    HalfEdge.existsUnique_componentOn (inv_mem_invOn_univ Γ) (mem_univ v)
  refine ⟨S, ⟨mem_filter.2 ⟨mem_univ _, hc, hconn⟩, hv⟩, fun T ⟨hT, hvT⟩ => ?_⟩
  rw [comps, mem_filter] at hT
  exact huniq T ⟨⟨subset_univ _, hvT⟩, hT.2.1, hT.2.2⟩

/-- Closedness is carried by a relabelling. -/
lemma closed_smul (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (Γ : LGraph n k) (S : Finset (Fin k)) :
    HalfEdge.Closed (g • Γ).att (g • Γ).inv (S.map g.2.toEmbedding) ↔ HalfEdge.Closed Γ.att Γ.inv S := by
  simp only [HalfEdge.Closed, smul_att, smul_inv, Function.comp_apply, mem_map_equiv, Equiv.symm_apply_apply]
  constructor
  · intro h x hx
    have := h (g.1 x) (by simpa using hx)
    simpa using this
  · intro h x hx
    exact h (g.1.symm x) hx

/-- Connectedness is carried by a relabelling. -/
lemma connOn_smul (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (Γ : LGraph n k) (S : Finset (Fin k)) :
    HalfEdge.ConnOn (g • Γ).att (g • Γ).inv (S.map g.2.toEmbedding) ↔ HalfEdge.ConnOn Γ.att Γ.inv S := by
  have hmap : ∀ T : Finset (Fin k), (T.map g.2.toEmbedding).map g.2.symm.toEmbedding = T := fun T => by
    ext x; simp [mem_map_equiv]
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨map_nonempty.1 hn, fun T hTS hT => ?_⟩
    rcases hc (T.map g.2.toEmbedding) (map_subset_map.2 hTS) ((closed_smul g Γ T).2 hT) with h | h
    · exact Or.inl (map_eq_empty.1 h)
    · exact Or.inr (map_injective _ h)
  · rintro ⟨hn, hc⟩
    refine ⟨map_nonempty.2 hn, fun U hUS hU => ?_⟩
    have hU' : U = (U.map g.2.symm.toEmbedding).map g.2.toEmbedding := by ext x; simp [mem_map_equiv]
    rw [hU'] at hU hUS ⊢
    rw [closed_smul] at hU
    rcases hc _ (map_subset_map.1 hUS) hU with h | h
    · left; rw [h, map_empty]
    · right; rw [h]

/-- **A relabelling maps components to components.** -/
theorem comps_smul (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (Γ : LGraph n k) :
    comps (g • Γ) = (comps Γ).map ⟨fun S => S.map g.2.toEmbedding, map_injective _⟩ := by
  classical
  ext U
  simp only [comps, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hc, hconn⟩
    refine ⟨U.map g.2.symm.toEmbedding, ?_, by ext x; simp [mem_map_equiv]⟩
    have hU : U = (U.map g.2.symm.toEmbedding).map g.2.toEmbedding := by ext x; simp [mem_map_equiv]
    rw [hU] at hc hconn
    exact ⟨(closed_smul g Γ _).1 hc, (connOn_smul g Γ _).1 hconn⟩
  · rintro ⟨S, ⟨hc, hconn⟩, rfl⟩
    exact ⟨(closed_smul g Γ S).2 hc, (connOn_smul g Γ S).2 hconn⟩

/-- **The number of components is an isomorphism invariant.** -/
theorem ncomp_smul (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin k)) (Γ : LGraph n k) : ncomp (g • Γ) = ncomp Γ := by
  rw [ncomp, ncomp, comps_smul, card_map]

end Lightlike.FieldTheory.GraphAlg
