import Lightlike.SpinFoam.ForcingMoves
import Lightlike.SpinFoam.ForcingMove33
import Lightlike.SpinFoam.ForcingMove24

/-!
# Robust forcing sets and the 1-5 move

A set `T` of triangles is *robust* for a complex `K` if it forces every triangle of `K` even when any
one tetrahedron of `K` is removed. Numerical evidence (`scripts/spinfoam/robust_check.py`): the set carried
along from the boundary of the 5-simplex by random 3-3, 2-4 and 1-5 moves is robust at every
tetrahedron sampled (1,104,480 of 1,104,480 tetrahedra), at every 3-3 location (38,176 of 38,176), and
after each of 822 consecutive moves. It is a conjecture that the three moves preserve robustness.

This file proves the 1-5 case: if `T` is robust for `K`, then `T` together with the four gauge
triangles of the move is robust for the complex after the move. The 3-3 and 2-4 moves are not
covered.

## Main results

* `Robust`: the definition; `robustBy`, `robust_of_robustBy`: a kernel checker from explicit forcing
  steps.
* `Move15.robust_move15`: robust sets stay robust under the 1-5 move.
* `forces_move24_of_robust`: a robust set keeps forcing under every 2-4 move, with the triangle
  `{a, p, q}` added. No conjecture is involved: the closure condition of `forces_move24_iff` is the
  robustness condition at the removed tetrahedron.

## References

* `freidel-louapre-2003`, Section IV: the motivation (gauge fixing); the forcing rule itself is this
  library's.
-/

open Finset Lightlike.FourD Complex4

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- **Robust forcing.** `T` forces every triangle of `K` using the tetrahedra of `K` with any one of
them removed. -/
def Robust (K : Complex4 V) (T : Finset (Finset V)) : Prop :=
  ∀ t ∈ K.tets, ForcesIn (K.tets.erase t) K.tris T

/-- A checker for `Robust`: for every tetrahedron `t` of `K`, `L.lookup t` is a list of forcing steps,
checked by `forcesInBy`, that forces every triangle of `K` from `T` with `t` removed. -/
def robustBy (K : Complex4 V) (T : Finset (Finset V))
    (L : List (Finset V × List (Finset V × Finset V))) : Bool :=
  decide (∀ t ∈ K.tets, forcesInBy (K.tets.erase t) K.tris ((L.lookup t).getD []) T = true)

/-- A successful `robustBy` check proves `Robust`. -/
theorem robust_of_robustBy {K : Complex4 V} {T : Finset (Finset V)}
    {L : List (Finset V × List (Finset V × Finset V))} (h : robustBy K T L = true) : Robust K T :=
  fun t ht => forcesIn_of_forcesInBy (of_decide_eq_true h t ht)

namespace Move15

variable {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) {v : V} (hτ : τ = {v})
include h hτ

/-- **Robust forcing sets stay robust under the 1-5 move.** If `T` is robust for `K`, then `T` together
with the four gauge triangles `{v, a_0, a_j}` is robust for the complex after the move. This is the
1-5 case of a conjecture; the 3-3 and 2-4 moves are not covered. -/
theorem robust_move15 (hσ : #σ = 5) {a : Fin 5 → V} (hsurj : ∀ x, x ∈ σ ↔ ∃ j, a j = x)
    {T : Finset (Finset V)} (hR : Robust K T) :
    Robust (Complex4.move K h) (gaugeTri a v ∪ T) := by
  intro t' ht'
  set P' := (Complex4.move K h).tets.erase t' with hP'
  set Z : Finset (Finset V) := (gaugeTri a v ∪ T) ∪ K.tris with hZ
  have hv : v ∉ σ := hvσ h hτ
  have hmemσ : ∀ j, a j ∈ σ := fun j => (hsurj _).mpr ⟨j, rfl⟩
  have hsub := tets_subset_move15 h hσ
  have h1 : ForcesIn P' K.tris (gaugeTri a v ∪ T) := by
    by_cases ht'K : t' ∈ K.tets
    · exact (hR t' ht'K).mono (erase_subset_erase _ hsub) subset_union_right
    · obtain ⟨t0, ht0σ, ht0c⟩ := exists_subset_card_eq (show 4 ≤ #σ by omega)
      have ht0 : t0 ∈ K.tets := Complex4.mem_faces.mpr ⟨σ, mem_simps_of_move15 h hτ, ht0σ, ht0c⟩
      refine (hR t0 ht0).mono (fun x hx => ?_) subset_union_right
      obtain ⟨-, hxK⟩ := mem_erase.mp hx
      exact mem_erase.mpr ⟨fun e => ht'K (e ▸ hxK), hsub hxK⟩
  have hnew : ∀ f ∈ (Complex4.move K h).tris \ Z, ForcesIn P' {f} Z := by
    intro f hfm
    obtain ⟨hf, hfZ⟩ := mem_sdiff.mp hfm
    obtain hfK | ⟨x, hx, y, hy, hxy, rfl⟩ := tris_move15 h hτ hf
    · exact absurd (mem_union_right _ hfK) hfZ
    · have hgt : ∀ z ∈ σ, z ≠ a 0 → insert v (insert (a 0) {z}) ∈ gaugeTri a v := by
        intro z hz hne
        obtain ⟨j, rfl⟩ := (hsurj z).mp hz
        exact mem_image.mpr ⟨j, mem_erase.mpr ⟨fun e => hne (e ▸ rfl), mem_univ _⟩, rfl⟩
      have hxa : x ≠ a 0 := fun e => hfZ (mem_union_left _ (mem_union_left _ (by
        have := hgt y hy (fun e' => hxy (e.trans e'.symm)); rw [e]; simpa using this)))
      have hya : y ≠ a 0 := fun e => hfZ (mem_union_left _ (mem_union_left _ (by
        have := hgt x hx (fun e' => hxy (e'.trans e.symm)); rw [e, pair_comm]; simpa using this)))
      by_cases hT0 : t' = insert v (insert (a 0) {x, y})
      · -- the tetrahedron `{v, a_0, x, y}` is removed: go through a fifth vertex `z`
        obtain ⟨z, hz, hzx, hzy, hza⟩ : ∃ z ∈ σ, z ≠ x ∧ z ≠ y ∧ z ≠ a 0 := by
          by_contra hcon
          have hsub' : σ ⊆ insert (a 0) {x, y} := fun u hu => by
            by_contra hn
            exact hcon ⟨u, hu, fun e => hn (by simp [e]), fun e => hn (by simp [e]),
              fun e => hn (by simp [e])⟩
          have := card_le_card hsub'
          have := card_le_three (a 0) x y
          omega
        have hzt' : z ∉ t' := by
          rw [hT0]
          simp only [mem_insert, mem_singleton, not_or]
          exact ⟨fun e => hv (e ▸ hz), hza, hzx, hzy⟩
        have hKZ : K.tris ⊆ Z := subset_union_right
        have hZ1 : ∀ w ∈ σ, w ≠ a 0 → w ≠ z → z ≠ a 0 →
            ForcesIn P' {insert v {w, z}} Z := by
          intro w hw hwa hwz hza'
          obtain ⟨h1', h2', h3'⟩ := tet15 h hτ hσ (c := a 0) (hmemσ 0) hw hz hwz hwa hza hKZ
            (mem_union_left _ (mem_union_left _ (hgt w hw hwa)))
            (mem_union_left _ (mem_union_left _ (hgt z hz hza)))
          have hne : (insert v (insert (a 0) {w, z}) : Finset V) ≠ t' := fun e => hzt' (by
            rw [← e]; simp)
          exact ForcesIn.single (mem_erase.mpr ⟨hne, h1'⟩) h2' h3'
        have hA := hZ1 x hx hxa hzx.symm hza
        have hB := hZ1 y hy hya hzy.symm hza
        have hAB := hA.union hB
        set Z' : Finset (Finset V) := Z ∪ ({insert v {x, z}} ∪ {insert v {y, z}}) with hZ'
        have hKZ' : K.tris ⊆ Z' := hKZ.trans subset_union_left
        obtain ⟨h1', h2', h3'⟩ := tet15 h hτ hσ (c := z) hz hx hy hxy hzx.symm hzy.symm hKZ'
          (mem_union_right _ (mem_union_left _ (by
            have : (insert v (insert z {x}) : Finset V) = insert v {x, z} := by
              ext w; simp; tauto
            rw [this]; exact mem_singleton_self _)))
          (mem_union_right _ (mem_union_right _ (by
            have : (insert v (insert z {y}) : Finset V) = insert v {y, z} := by
              ext w; simp; tauto
            rw [this]; exact mem_singleton_self _)))
        have hne : (insert v (insert z {x, y}) : Finset V) ≠ t' := fun e => hzt' (by
          rw [← e]; simp)
        exact hAB.of_union (ForcesIn.single (mem_erase.mpr ⟨hne, h1'⟩) h2' h3')
      · obtain ⟨h1', h2', h3'⟩ := direct15 h hτ hσ hsurj (T := T) hx hy hxy hxa hya
        exact ForcesIn.single (mem_erase.mpr ⟨fun e => hT0 e.symm, h1'⟩) h2' h3'
  have h2 : ForcesIn P' (Complex4.move K h).tris Z :=
    (ForcesIn.of_singles hnew).mono_target (fun x hx => by
      by_cases hxZ : x ∈ Z
      · exact mem_union_right _ hxZ
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hxZ⟩))
  exact h1.of_union h2

end Move15


/-- **A robust set keeps forcing under every 2-4 move.** If `T` is robust for `K` and `σ` is the
tetrahedron removed by a 2-4 move to the edge `τ = {p, q}`, then `T` together with the triangle
`{a, p, q}`, `a ∈ σ`, forces every triangle of the complex after the move. The condition of
`Forcing24.forces_move24_iff` (the closure of `T` under the tetrahedra other than `σ` is complete) is
the robustness condition at `σ`, because the only tetrahedron of `K` that contains `σ` is `σ`. -/
theorem forces_move24_of_robust {K : Complex4 V} {σ τ : Finset V} (h : K.IsMove σ τ) (hσ : #σ = 4)
    {a : V} (ha : a ∈ σ) {T : Finset (Finset V)} (hT : T ⊆ K.tris) (hR : Robust K T) :
    Forces (K.move h) (K.move h).tris (insert (insert a τ) T) := by
  have hτ : #τ = 2 := by have := h.card; omega
  obtain ⟨v, hv⟩ : τ.Nonempty := card_pos.mp (by omega)
  have hσtet : σ ∈ K.tets := by
    refine Complex4.mem_faces.mpr ⟨(σ ∪ τ).erase v, h.mem v hv, ?_, hσ⟩
    intro x hx
    exact mem_erase.mpr ⟨fun hxv => disjoint_left.mp h.disj hx (hxv ▸ hv), mem_union_left _ hx⟩
  have hRσ := hR σ hσtet
  have heq : K.tets.erase σ = K.tets.filter fun t => ¬ σ ⊆ t := by
    ext t
    simp only [mem_erase, mem_filter]
    constructor
    · rintro ⟨hne, ht⟩
      refine ⟨ht, fun hs => hne ?_⟩
      obtain ⟨S, -, -, hc⟩ := Complex4.mem_faces.mp ht
      exact (eq_of_subset_of_card_le hs (by rw [hc, hσ])).symm
    · rintro ⟨ht, hs⟩
      exact ⟨fun e => hs (e ▸ subset_rfl), ht⟩
  have hF : Forces K K.tris T :=
    (Forcing33.forces_iff_forcesIn K _ _).mpr (hRσ.mono (erase_subset _ _) subset_rfl)
  exact (Forcing24.forces_move24_iff h hσ ha hT hF).mpr (heq ▸ hRσ)

end Lightlike.SpinFoam
