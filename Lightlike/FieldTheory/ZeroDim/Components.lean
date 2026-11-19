import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Pi

/-!
# Graphs with legs on a half-edge type, and their connected components

Borinsky, *Graphs in perturbation theory*, arXiv:1807.02046v1, §2.1, Definitions 2.1.1-2.1.2, p. 10: a graph is a set
of half-edges `H` with an attachment map `ν : H → V` to the vertices and an involution `ι` of `H`, whose 2-cycles are
the edges and whose fixed points are the legs. Here `π : H → V` is fixed and a graph structure on the vertices `S` is an
involution of `H` that fixes the half-edges at the other vertices (`invOn π S`); its fixed points at `S` are legs.

This is the first milestone toward Theorem 2.4.1 (p. 18) in the algebra of all graphs:
* `existsUnique_componentOn`: every vertex lies in exactly one closed connected vertex set (its component);
* `card_invOn_eq_sum`: splitting off the component of a vertex,
  `#graphs(R) = Σ_{v₀ ∈ S ⊆ R} #connected(S) · #graphs(R \ S)`.
The four-valent vacuum graphs are the case `H = V × Fin 4` with no legs.
-/

open Finset Function

namespace Lightlike.FieldTheory.HalfEdge

variable {V H : Type*} [Fintype V] [Fintype H] [DecidableEq V] [DecidableEq H] (π : H → V)

/-- A vertex set `S` is **closed** under `f` if `f` sends the half-edges at `S` to half-edges at `S`. -/
def Closed (f : H → H) (S : Finset V) : Prop := ∀ h, π h ∈ S → π (f h) ∈ S

/-- `f` is **connected on** `S`: `S` is nonempty and its only closed subsets are `∅` and `S`. -/
def ConnOn (f : H → H) (S : Finset V) : Prop := S.Nonempty ∧ ∀ T ⊆ S, Closed π f T → T = ∅ ∨ T = S

open Classical in
/-- The **graph structures on `S`**: involutions of the half-edges fixing the half-edges at the vertices off `S`
(their fixed points at `S` are the legs). -/
noncomputable def invOn (S : Finset V) : Finset (H → H) :=
  univ.filter fun f => Involutive f ∧ ∀ h, π h ∉ S → f h = h

open Classical in
/-- The **connected graph structures** on `S`. -/
noncomputable def connInvOn (S : Finset V) : Finset (H → H) := (invOn π S).filter fun f => ConnOn π f S

variable {π}

lemma mem_invOn {S : Finset V} {f : H → H} : f ∈ invOn π S ↔ Involutive f ∧ ∀ h, π h ∉ S → f h = h := by
  classical
  simp [invOn]

lemma closed_of_mem_invOn {S : Finset V} {f : H → H} (hf : f ∈ invOn π S) : Closed π f S := by
  intro h hh
  rw [mem_invOn] at hf
  by_contra hc
  have h1 : f (f h) = f h := hf.2 (f h) hc
  rw [hf.1 h] at h1
  rw [← h1] at hc
  exact hc hh

lemma Closed.inter {f : H → H} {S T : Finset V} (hS : Closed π f S) (hT : Closed π f T) :
    Closed π f (S ∩ T) :=
  fun h hh => mem_inter.2 ⟨hS h (mem_inter.1 hh).1, hT h (mem_inter.1 hh).2⟩

lemma Closed.sdiff {f : H → H} (hf : Involutive f) {S T : Finset V} (hS : Closed π f S) (hT : Closed π f T) :
    Closed π f (S \ T) := by
  intro h hh
  rw [mem_sdiff] at hh ⊢
  refine ⟨hS h hh.1, fun hc => hh.2 ?_⟩
  have := hT (f h) hc
  rwa [hf h] at this

/-- **The component of a vertex**: for a graph structure on `R` and `v₀ ∈ R`, exactly one `S ⊆ R` containing `v₀`
is closed and connected. -/
theorem existsUnique_componentOn {R : Finset V} {f : H → H} (hf : f ∈ invOn π R) {v₀ : V} (hv : v₀ ∈ R) :
    ∃! S : Finset V, (S ⊆ R ∧ v₀ ∈ S) ∧ Closed π f S ∧ ConnOn π f S := by
  classical
  have hinv := (mem_invOn.1 hf).1
  have hR : R ∈ R.powerset.filter fun T => v₀ ∈ T ∧ Closed π f T :=
    mem_filter.2 ⟨mem_powerset_self R, hv, closed_of_mem_invOn hf⟩
  obtain ⟨S, hS𝒞, hmin⟩ := (R.powerset.filter fun T => v₀ ∈ T ∧ Closed π f T).exists_min_image card ⟨R, hR⟩
  simp only [mem_filter, mem_powerset] at hS𝒞 hmin
  obtain ⟨hSR, hvS, hSc⟩ := hS𝒞
  have hconn : ConnOn π f S := by
    refine ⟨⟨v₀, hvS⟩, fun T hTS hTc => ?_⟩
    by_cases hvT : v₀ ∈ T
    · exact Or.inr (eq_of_subset_of_card_le hTS (hmin T ⟨hTS.trans hSR, hvT, hTc⟩))
    · left
      have hd : S \ T = S := eq_of_subset_of_card_le sdiff_subset
        (hmin (S \ T) ⟨sdiff_subset.trans hSR, mem_sdiff.2 ⟨hvS, hvT⟩, hSc.sdiff hinv hTc⟩)
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have hx' : x ∈ S \ T := by rw [hd]; exact hTS hx
      exact (mem_sdiff.1 hx').2 hx
  refine ⟨S, ⟨⟨hSR, hvS⟩, hSc, hconn⟩, fun S' hS' => ?_⟩
  obtain ⟨⟨-, hvS'⟩, hS'c, hS'conn⟩ := hS'
  have hv' : v₀ ∈ S' ∩ S := mem_inter.2 ⟨hvS', hvS⟩
  have h1 : S' ∩ S = S' := by
    rcases hS'conn.2 (S' ∩ S) inter_subset_left (hS'c.inter hSc) with h | h
    · rw [h] at hv'; exact absurd hv' (notMem_empty _)
    · exact h
  have h2 : S ∩ S' = S := by
    rcases hconn.2 (S ∩ S') inter_subset_left (hSc.inter hS'c) with h | h
    · rw [inter_comm, h] at hv'; exact absurd hv' (notMem_empty _)
    · exact h
  refine Subset.antisymm ?_ ?_
  · rw [← h1]; exact inter_subset_right
  · rw [← h2]; exact inter_subset_right

variable (π) in
/-- `f` on the half-edges at `S`, the identity elsewhere. -/
def restrictTo (f : H → H) (S : Finset V) : H → H := fun h => if π h ∈ S then f h else h

variable (π) in
/-- `g` on the half-edges at `S`, `k` elsewhere. -/
def glue (S : Finset V) (g k : H → H) : H → H := fun h => if π h ∈ S then g h else k h

lemma restrictTo_mem {R T : Finset V} {f : H → H} (hf : f ∈ invOn π R) (hT : Closed π f T) :
    restrictTo π f T ∈ invOn π T := by
  rw [mem_invOn] at hf ⊢
  refine ⟨fun h => ?_, fun h hh => by simp [restrictTo, hh]⟩
  by_cases hh : π h ∈ T
  · simp [restrictTo, hh, hT h hh, hf.1 h]
  · simp [restrictTo, hh]

lemma glue_mem {R S : Finset V} (hSR : S ⊆ R) {g k : H → H} (hg : g ∈ invOn π S)
    (hk : k ∈ invOn π (R \ S)) : glue π S g k ∈ invOn π R := by
  have hgS := closed_of_mem_invOn hg
  have hkS := closed_of_mem_invOn hk
  rw [mem_invOn] at hg hk ⊢
  have hk1 : ∀ h : H, π h ∉ S → π (k h) ∉ S := by
    intro h hh
    by_cases hR : π h ∈ R
    · exact (mem_sdiff.1 (hkS h (mem_sdiff.2 ⟨hR, hh⟩))).2
    · rw [hk.2 h (fun hm => hR (mem_sdiff.1 hm).1)]; exact hh
  refine ⟨fun h => ?_, fun h hh => ?_⟩
  · by_cases hh : π h ∈ S
    · simp [glue, hh, hgS h hh, hg.1 h]
    · simp [glue, hh, hk1 h hh, hk.1 h]
  · have hS : π h ∉ S := fun h' => hh (hSR h')
    simp only [glue, hS, if_false]
    exact hk.2 h (fun hm => hh (mem_sdiff.1 hm).1)

lemma closed_glue {S : Finset V} {g k : H → H} (hg : g ∈ invOn π S) : Closed π (glue π S g k) S := by
  intro h hh
  rw [show glue π S g k h = g h from if_pos hh]
  exact closed_of_mem_invOn hg h hh

lemma connOn_congr {S : Finset V} {f g : H → H} (hfg : ∀ h, π h ∈ S → f h = g h) :
    ConnOn π f S ↔ ConnOn π g S := by
  have hc : ∀ T ⊆ S, Closed π f T ↔ Closed π g T := fun T hTS =>
    ⟨fun hT h hh => by rw [← hfg h (hTS hh)]; exact hT h hh,
      fun hT h hh => by rw [hfg h (hTS hh)]; exact hT h hh⟩
  exact ⟨fun hf => ⟨hf.1, fun T hTS hT => hf.2 T hTS ((hc T hTS).2 hT)⟩,
    fun hg => ⟨hg.1, fun T hTS hT => hg.2 T hTS ((hc T hTS).1 hT)⟩⟩

open Classical in
/-- The graph structures on `R` in which `S` is closed and connected are the pairs (connected structure on `S`,
structure on `R \ S`). -/
theorem card_fiberOn {R S : Finset V} (hSR : S ⊆ R) :
    ((invOn π R).filter fun f => Closed π f S ∧ ConnOn π f S).card =
      (connInvOn π S).card * (invOn π (R \ S)).card := by
  rw [← card_product]
  refine card_nbij' (fun f => (restrictTo π f S, restrictTo π f (R \ S))) (fun p => glue π S p.1 p.2)
    ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    obtain ⟨hf, hSc, hSconn⟩ := hf
    have hRc := closed_of_mem_invOn hf
    rw [mem_coe, mem_product]
    dsimp only
    rw [connInvOn, mem_filter]
    exact ⟨⟨restrictTo_mem hf hSc, (connOn_congr fun h hh => (if_pos hh).symm).1 hSconn⟩,
      restrictTo_mem hf (hRc.sdiff (mem_invOn.1 hf).1 hSc)⟩
  · rintro ⟨g, k⟩ hp
    rw [mem_coe, mem_product, connInvOn, mem_filter] at hp
    obtain ⟨⟨hg, hgconn⟩, hk⟩ := hp
    rw [mem_coe, mem_filter]
    exact ⟨glue_mem hSR hg hk, closed_glue hg, (connOn_congr fun h hh => if_pos hh).2 hgconn⟩
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    have hf' := mem_invOn.1 hf.1
    funext h
    simp only [glue, restrictTo]
    by_cases hh : π h ∈ S
    · simp [hh]
    · by_cases hR : π h ∈ R
      · simp [hh, hR]
      · simp [hh, hR, hf'.2 h hR]
  · rintro ⟨g, k⟩ hp
    rw [mem_coe, mem_product, connInvOn, mem_filter] at hp
    obtain ⟨⟨hg, -⟩, hk⟩ := hp
    dsimp only at hg hk
    have hg' := mem_invOn.1 hg
    have hk' := mem_invOn.1 hk
    simp only [Prod.mk.injEq]
    constructor
    · funext h
      simp only [glue, restrictTo]
      by_cases hh : π h ∈ S
      · simp [hh]
      · simp [hh, hg'.2 h hh]
    · funext h
      simp only [glue, restrictTo]
      by_cases hh : π h ∈ R \ S
      · simp [hh, (mem_sdiff.1 hh).2]
      · simp [hh, hk'.2 h hh]

/-- **Splitting off the component of a vertex**: for `v₀ ∈ R`,
`#graphs(R) = Σ_{v₀ ∈ S ⊆ R} #connected(S) · #graphs(R \ S)`. -/
theorem card_invOn_eq_sum {R : Finset V} {v₀ : V} (hv : v₀ ∈ R) :
    (invOn π R).card = ∑ S ∈ R.powerset.filter (v₀ ∈ ·), (connInvOn π S).card * (invOn π (R \ S)).card := by
  classical
  have key : ∀ f ∈ invOn π R,
      ((R.powerset.filter (v₀ ∈ ·)).filter fun S => Closed π f S ∧ ConnOn π f S).card = 1 := by
    intro f hf
    obtain ⟨S, hS, huniq⟩ := existsUnique_componentOn hf hv
    rw [card_eq_one]
    refine ⟨S, ext fun T => ?_⟩
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨⟨hTR, hvT⟩, hT⟩; exact huniq T ⟨⟨hTR, hvT⟩, hT⟩
    · rintro rfl; exact ⟨hS.1, hS.2⟩
  calc (invOn π R).card = ∑ f ∈ invOn π R,
        ((R.powerset.filter (v₀ ∈ ·)).filter fun S => Closed π f S ∧ ConnOn π f S).card := by
        rw [sum_congr rfl key]; simp
    _ = ∑ S ∈ R.powerset.filter (v₀ ∈ ·), ((invOn π R).filter fun f => Closed π f S ∧ ConnOn π f S).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun f S => Closed π f S ∧ ConnOn π f S)
    _ = _ := sum_congr rfl fun S hS => card_fiberOn (mem_powerset.1 (mem_filter.1 hS).1)

end Lightlike.FieldTheory.HalfEdge
