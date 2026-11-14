module

public import Lightlike.PonzanoRegge.GaugeChange

/-!
# Forced edges, and when the cutoff does not matter

If two edges of a triangle are gauge edges (spin `0`), the triangle inequality forces spin `0` on
the third. Such a **forced edge** can be added to the gauge set without changing the gauge-fixed
amplitude (`amplitudeGF_force`).

When repeated forcing reaches every edge (`ForcesAll`), only the colouring with all spins `0`
contributes, so the amplitude is `1` **for every cutoff** (`amplitudeGF_of_forcesAll`): removing
the cutoff is then trivial. This happens, for example, for the boundary of the 4-simplex with a
star tree (`Lightlike/Tests/Forcing.lean`). It does not happen in general: on complexes with
non-contractible loops some spins remain free, and the amplitude depends on the cutoff and on the
tree (`Lightlike/Tests/TreeDependence.lean`, `scripts/pr_tree_check.py`).
-/

@[expose] public section

open Finset Lightlike.Pentagon PhyslibAlpha.Sl2

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- The weight of the colouring with all spins `0` is `1`: every edge, triangle and tetrahedron
contributes `1` (the 6j symbol with all spins `0` is `1`). -/
theorem weight_zero (K : Complex3 V) : weight K (fun _ => 0) = 1 := by
  have h6 : sixJSym 0 0 0 0 0 0 = 1 := by
    rw [sixJSym_zero_left]
    simp [Tri]
  rw [weight, prod_eq_one (fun e _ => by simp [edgeW]), prod_eq_one (fun f _ => by simp [triW]),
    prod_eq_one (fun t ht => ?_), one_mul, one_mul]
  rw [tetW, dite_eq_left_of_eq_true (eq_true (K.card_eq t ht)), tetAmp_eq]
  exact h6

/-- **The weight vanishes when a triangle is not admissible**: if a triangle `pqr` of `K` has spins
that fail the triangle conditions (`Tri`: even perimeter and triangle inequalities). -/
lemma weight_eq_zero_of_not_Tri {K : Complex3 V} {col : Colouring V} {p q r : V} (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hτ : {p, q, r} ∈ K.tris)
    (h : ¬ Tri (col {p, r}) (col {q, r}) (col {q, p})) : weight K col = 0 := by
  obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_tris.mp hτ
  have hcard : #t = 4 := K.card_eq t ht
  obtain ⟨z, hz, hzn⟩ : ∃ z ∈ t, z ∉ ({p, q, r} : Finset V) :=
    exists_mem_notMem_of_card_lt_card (by rw [hcard, card_three hpq hpr hqr]; norm_num)
  simp only [mem_insert, mem_singleton, not_or] at hzn
  obtain ⟨hzp, hzq, hzr⟩ := hzn
  have hp : p ∈ t := hsub (by simp)
  have hq : q ∈ t := hsub (by simp)
  have hr : r ∈ t := hsub (by simp)
  rw [weight, prod_eq_zero ht, mul_zero]
  rw [tetW_eq_tetAmp col hcard (p := ![z, q, p, r])
    (injective_vec4 hzq hzp hzr hpq.symm hqr hpr) (by intro i; fin_cases i <;> simp [hz, hp, hq, hr])]
  exact tetAmp_eq_zero_of_not_tri col _ h

/-- **Forcing a gauge edge.** If `pqr` is a triangle of `K` whose edges `pr`, `qr` are gauge
edges and `pq` is not, adding `pq` to the gauge set does not change the amplitude, for every
cutoff. -/
theorem amplitudeGF_force (K : Complex3 V) {T : Finset (Finset V)}
    {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hτ : {p, q, r} ∈ K.tris)
    (hpr' : {p, r} ∈ T) (hqr' : {q, r} ∈ T) (hpq' : {p, q} ∉ T) (cut : Finset V → ℕ) :
    amplitudeGF K (insert {p, q} T) cut = amplitudeGF K T cut := by
  obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_tris.mp hτ
  have hpqK : ({p, q} : Finset V) ∈ K.edges :=
    Complex3.mem_edges.mpr ⟨t, ht, (by small_subset : ({p, q} : Finset V) ⊆ {p, q, r}).trans hsub,
      card_pair hpq⟩
  have hne1 : ({p, r} : Finset V) ≠ {p, q} := fun h => hqr (by
    have : r ∈ ({p, q} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact absurd h'.symm hpr
    · exact h'.symm)
  have hne2 : ({q, r} : Finset V) ≠ {p, q} := fun h => hpr (by
    have : r ∈ ({p, q} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h'.symm
    · exact absurd h'.symm hqr)
  set S := K.edges \ insert {p, q} T with hS
  have hpqS : ({p, q} : Finset V) ∉ S := by simp [hS]
  have hprS : ({p, r} : Finset V) ∉ S := by simp [hS, hpr']
  have hqrS : ({q, r} : Finset V) ∉ S := by simp [hS, hqr']
  have h1 : K.edges \ T = insert {p, q} S := by
    ext x
    simp only [hS, mem_sdiff, mem_insert]
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hxf : x = {p, q}
      · exact Or.inl hxf
      · exact Or.inr ⟨hx, fun h => h.elim hxf hxT⟩
    · rintro (rfl | ⟨hx, hxT⟩)
      · exact ⟨hpqK, hpq'⟩
      · exact ⟨hx, fun h => hxT (Or.inr h)⟩
  simp only [amplitudeGF]
  rw [h1, sum_pi_insert_collapse hpqS]
  intro σ _ x hx
  refine weight_eq_zero_of_tri hpq hpr hqr hτ ?_ ?_ ?_
  · rw [Function.update_of_ne hne1, extS_of_not_mem hprS]
  · rw [Function.update_of_ne hne2, extS_of_not_mem hqrS]
  · rwa [pair_comm q p, Function.update_self]

/-- **The gauge set forces every edge**: either it already contains all edges, or a triangle with
two gauge edges forces a third, and the enlarged gauge set forces every edge. -/
inductive ForcesAll (K : Complex3 V) : Finset (Finset V) → Prop
  | done {T : Finset (Finset V)} (h : K.edges ⊆ T) : ForcesAll K T
  | step {T : Finset (Finset V)} {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
      (hτ : {p, q, r} ∈ K.tris) (hpr' : {p, r} ∈ T) (hqr' : {q, r} ∈ T) (hpq' : {p, q} ∉ T)
      (h : ForcesAll K (insert {p, q} T)) : ForcesAll K T

/-- **When the gauge set forces every edge, the gauge-fixed amplitude is `1` for every cutoff**:
only the colouring with all spins `0` contributes, so the cutoff can be removed. -/
theorem amplitudeGF_of_forcesAll (K : Complex3 V) {T : Finset (Finset V)} (hT : T ⊆ K.edges)
    (h : ForcesAll K T) (cut : Finset V → ℕ) : amplitudeGF K T cut = 1 := by
  induction h with
  | @done T hall =>
    have hS : K.edges \ T = ∅ := sdiff_eq_empty_iff_subset.mpr hall
    simp only [amplitudeGF]
    rw [hS, pi_empty, sum_singleton]
    have : extS (∅ : Finset (Finset V)) (Pi.empty _) = fun _ => 0 := by
      funext e
      exact extS_of_not_mem (notMem_empty e)
    rw [this, weight_zero]
  | @step T p q r hpq hpr hqr hτ hpr' hqr' hpq' _ ih =>
    obtain ⟨t, ht, hsub, -⟩ := Complex3.mem_tris.mp hτ
    have hpqK : ({p, q} : Finset V) ∈ K.edges :=
      Complex3.mem_edges.mpr ⟨t, ht,
        (by small_subset : ({p, q} : Finset V) ⊆ {p, q, r}).trans hsub, card_pair hpq⟩
    rw [← amplitudeGF_force K hpq hpr hqr hτ hpr' hqr' hpq' cut]
    exact ih (insert_subset hpqK hT)

end Lightlike.PR
