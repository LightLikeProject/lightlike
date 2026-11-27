import Lightlike.SpinFoam.EPRLStateSum.NetworkCovariance
import Lightlike.SpinFoam.EPRLStateSum.LinkParity

/-!
# The number of reversed links of a relabelling is even

For a closed 4-complex `K`, a colouring `col` whose four colours around every tetrahedron have an even sum, and a relabelling `σ` of the vertices, the
exponent `Σ_s invSum (complexJ K col s) (phi K σ s)` of the sign carried by the network of `relabelComplex K σ` is even: it counts, for every pair of
vertices `x < y` with `σ y < σ x`, the colours of the triangles of the link of the edge `{x, y}`, whose sum is even (`link_sum_even`).
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- A sum over the ten edges is the sum over the ordered pairs of positions. -/
lemma sum_epr {M : Type*} [AddCommMonoid M] (G : Fin 5 → Fin 5 → M) :
    ∑ e : Fin 10, G (epr e).1 (epr e).2 = ∑ p : Fin 5, ∑ q : Fin 5, if p < q then G p q else 0 := by
  simp [Fin.sum_univ_succ, epr]
  abel

/-- A sum over a finite set `s` of five elements is the sum over its sorted positions. -/
lemma sum_orderEmb {M : Type*} [AddCommMonoid M] (s : Finset V) (hs : #s = 5) (f : V → M) :
    ∑ x ∈ s, f x = ∑ p : Fin 5, f (s.orderEmbOfFin hs p) := by
  symm
  refine Finset.sum_bij (fun p _ => s.orderEmbOfFin hs p) (fun p _ => Finset.orderEmbOfFin_mem s hs p)
    (fun p _ q _ h => (s.orderEmbOfFin hs).injective h) (fun x hx => ?_) (fun p _ => rfl)
  have : x ∈ Set.range (s.orderEmbOfFin hs) := by
    rw [Finset.range_orderEmbOfFin]; exact hx
  obtain ⟨p, hp⟩ := this
  exact ⟨p, Finset.mem_univ _, hp⟩

/-- A relabelling reverses two sorted positions exactly when it reverses the vertices there. -/
lemma lt_posPerm_symm (σ : V ≃ V) (s : Finset V) (hs : #s = 5) (p q : Fin 5) :
    (posPerm σ s hs).symm q < (posPerm σ s hs).symm p ↔
      σ (s.orderEmbOfFin hs q) < σ (s.orderEmbOfFin hs p) := by
  have hw := fun a' => orderEmb_relabel σ s hs a'
  have h1 := hw ((posPerm σ s hs).symm q)
  have h2 := hw ((posPerm σ s hs).symm p)
  simp only [Equiv.apply_symm_apply] at h1 h2
  rw [← h1, ← h2]
  have hc : #(s.map σ.toEmbedding) = 5 := by rw [Finset.card_map]; exact hs
  exact ((s.map σ.toEmbedding).orderEmbOfFin hc).lt_iff_lt.symm

/-- **The exponent of one simplex in terms of its vertices**: the sum of the colours `col (s ∖ {x, y})` over the pairs `x < y` of vertices of `s`
that `σ` reverses. -/
lemma invSum_simplex (σ : V ≃ V) (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) :
    invSum (simplexJ s hs col) (posPerm σ s hs) =
      ∑ x ∈ s, ∑ y ∈ s, if x < y ∧ σ y < σ x then col ((s.erase x).erase y) else 0 := by
  have hsymm := simplexJ_symm s hs col
  rw [invSum_eq _ hsymm]
  refine Eq.trans (sum_epr (fun p q : Fin 5 =>
        if (posPerm σ s hs).symm q < (posPerm σ s hs).symm p then simplexJ s hs col p q else 0)) ?_
  rw [sum_orderEmb s hs]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_orderEmb s hs]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [lt_posPerm_symm]
  have hlt : s.orderEmbOfFin hs p < s.orderEmbOfFin hs q ↔ p < q := (s.orderEmbOfFin hs).lt_iff_lt
  by_cases h1 : p < q <;> by_cases h2 : σ (s.orderEmbOfFin hs q) < σ (s.orderEmbOfFin hs p) <;>
    simp [h1, h2, hlt, simplexJ]

/-- A sum over a subset is the sum over the larger set with the indicator. -/
lemma sum_subset_ite {M : Type*} [AddCommMonoid M] (U s : Finset V) (hsub : s ⊆ U) (g : V → M) :
    ∑ x ∈ s, g x = ∑ x ∈ U, if x ∈ s then g x else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]

/-- **The total exponent is even**: on a closed complex and a colouring with even tetrahedra, the number of reversed links of a relabelling, counted with the colours
of the triangles, is even. -/
theorem invSum_total_even (K : Complex4 V) (σ : V ≃ V) (hK : K.IsClosed4) (col : Finset V → ℕ) (hp : TetPar K col) :
    Even (∑ s : K.simps, invSum (complexJ K col s) (phi K σ s)) := by
  classical
  set U : Finset V := K.simps.biUnion id with hU
  have hsU : ∀ s ∈ K.simps, s ⊆ U := fun s hs x hx => Finset.mem_biUnion.2 ⟨s, hs, hx⟩
  have h1 : ∑ s : K.simps, invSum (complexJ K col s) (phi K σ s) =
      ∑ s ∈ K.simps, ∑ x ∈ s, ∑ y ∈ s, if x < y ∧ σ y < σ x then col ((s.erase x).erase y) else 0 := by
    rw [← Finset.sum_coe_sort K.simps (fun s => ∑ x ∈ s, ∑ y ∈ s,
      if x < y ∧ σ y < σ x then col ((s.erase x).erase y) else 0)]
    exact Finset.sum_congr rfl fun s _ => invSum_simplex σ s.1 (K.card_eq _ s.2) col
  have h2 : ∀ s ∈ K.simps, ∑ x ∈ s, ∑ y ∈ s, (if x < y ∧ σ y < σ x then col ((s.erase x).erase y) else 0) =
      ∑ x ∈ U, ∑ y ∈ U, if x ∈ s ∧ y ∈ s then
        (if x < y ∧ σ y < σ x then col ((s.erase x).erase y) else 0) else 0 := by
    intro s hs
    have hsub := hsU s hs
    rw [sum_subset_ite U s hsub]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ s
    · rw [if_pos hx, sum_subset_ite U s hsub]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y ∈ s <;> simp [hx, hy]
    · simp [hx]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.even_sum _ fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.even_sum _ fun y _ => ?_
  rw [← Finset.sum_filter]
  by_cases hc : x < y ∧ σ y < σ x
  · have := link_sum_even K hK col hp x y (ne_of_lt hc.1)
    simpa [hc] using this
  · simp [hc]

end Lightlike.SpinFoam.EPRLStateSum
