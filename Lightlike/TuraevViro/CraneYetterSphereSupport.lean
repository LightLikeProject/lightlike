import Lightlike.TuraevViro.CraneYetterSphere

/-!
# The support of the Crane–Yetter weight on the boundary of the 5-simplex at `r = 3`

The weight of a colouring with colours `0, 1` of `∂Δ⁵` vanishes unless the colouring is a cone cocycle: the triangles
not through the vertex `0` are determined by the cone formula from the ten triangles through `0`, and the tetrahedra by
the parity of their legs. This file derives these relations from the nonvanishing of the tetrahedron weights.
-/

open Finset Lightlike.Pentagon Lightlike.FourD Lightlike.FourD.Tests

namespace Lightlike.TV

/-- The tetrahedron `univ \ {p, p.succAbove a}`. -/
def tetset (p : Fin 6) (a : Fin 5) : Finset (Fin 6) := univ \ {p, p.succAbove a}

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Every triangle not through `0` spans, with `0`, a tetrahedron of the list `tetIdx`. -/
lemma exists_tet_of_tri : ∀ f : Finset (Fin 6), 0 ∉ f → #f = 3 → ∃ x ∈ tetIdx, tetset x.1 x.2 = insert 0 f := by
  unfold tetset tetIdx; decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Every tetrahedron is in the list `tetIdx`. -/
lemma exists_tet_of_card : ∀ f : Finset (Fin 6), #f = 4 → ∃ x ∈ tetIdx, tetset x.1 x.2 = f := by
  unfold tetset tetIdx; decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The leg `0` of a tetrahedron through `0` is the triangle opposite `0`. -/
lemma tetLeg_zero : ∀ x ∈ tetIdx, 0 ∈ tetset x.1 x.2 → tetLeg x.1 x.2 0 = (tetset x.1 x.2).erase 0 := by
  unfold tetset tetLeg tetIdx; decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The legs `1, 2, 3` of a tetrahedron through `0` are the triangles through `0` and two of the other three vertices. -/
lemma legs_cone : ∀ x ∈ tetIdx, 0 ∈ tetset x.1 x.2 →
    (((tetset x.1 x.2).erase 0).powersetCard 2).image (insert 0) =
      {tetLeg x.1 x.2 1, tetLeg x.1 x.2 2, tetLeg x.1 x.2 3} := by
  unfold tetset tetLeg tetIdx; decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
lemma legs_distinct : ∀ x ∈ tetIdx, tetLeg x.1 x.2 1 ∉ ({tetLeg x.1 x.2 2, tetLeg x.1 x.2 3} : Finset (Finset (Fin 6))) ∧
    tetLeg x.1 x.2 2 ∉ ({tetLeg x.1 x.2 3} : Finset (Finset (Fin 6))) := by
  unfold tetLeg tetIdx; decide +kernel

/-- `insert 0` is injective on the sets not containing `0`. -/
lemma insert_zero_inj : ∀ e₁ e₂ : Finset (Fin 6), 0 ∉ e₁ → 0 ∉ e₂ → insert 0 e₁ = insert 0 e₂ → e₁ = e₂ := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The vertices of even rank of a tetrahedron are the legs `0` and `2`. -/
lemma rank_even_tet : ∀ x ∈ tetIdx,
    (tetset x.1 x.2).filter (fun y => ((tetset x.1 x.2).filter (· < y)).card % 2 = 0) =
      {x.1.succAbove (x.2.succAbove 0), x.1.succAbove (x.2.succAbove 2)} := by
  unfold tetset tetIdx; decide +kernel


lemma card_tetLeg : ∀ (p : Fin 6) (a : Fin 5) (i : Fin 4), #(tetLeg p a i) = 3 := by
  unfold tetLeg; decide +kernel

lemma succAbove_succAbove_ne : ∀ (p : Fin 6) (a : Fin 5), p.succAbove (a.succAbove 0) ≠ p.succAbove (a.succAbove 2) := by
  decide +kernel

lemma theta3Z_ne_zero_iff {a b c : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    theta3Z a b c ≠ 0 ↔ (a + b + c) % 2 = 0 := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp [theta3Z]

/-- A nonzero tetrahedron weight forces the parity of its legs. -/
lemma tetModel_parity (col : Finset (Fin 6) → ℕ) (hc : ∀ f, col f ≤ 1) (p : Fin 6) (a : Fin 5)
    (h : tetModel col p a ≠ 0) :
    (col (tetset p a) + col (tetLeg p a 0) + col (tetLeg p a 2)) % 2 = 0 ∧
      (col (tetset p a) + col (tetLeg p a 1) + col (tetLeg p a 3)) % 2 = 0 := by
  unfold tetModel at h
  rcases mul_ne_zero_iff.1 h with ⟨h12, h2⟩
  rcases mul_ne_zero_iff.1 h12 with ⟨-, h1⟩
  exact ⟨(theta3Z_ne_zero_iff (hc _) (hc _) (hc _)).1 h1, (theta3Z_ne_zero_iff (hc _) (hc _) (hc _)).1 h2⟩

/-- **A colouring of `∂Δ⁵` with nonvanishing tetrahedron weights is a cone colouring**: it is the cone colouring of its
own values on the triangles through the vertex `0`. -/
theorem cone_of_ne_zero (col : Finset (Fin 6) → ℕ) (hc : ∀ f, col f ≤ 1)
    (hz : ∀ f, #f ≠ 3 → #f ≠ 4 → col f = 0) (hM : ∀ x ∈ tetIdx, tetModel col x.1 x.2 ≠ 0) :
    ∀ f, col f = coneCol col f := by
  have htri : ∀ f, #f = 3 → triCol col f = col f := by
    intro f hf
    unfold triCol
    by_cases h0 : 0 ∈ f
    · rw [if_pos h0]
    rw [if_neg h0]
    obtain ⟨x, hx, hT⟩ := exists_tet_of_tri f h0 hf
    have h0T : 0 ∈ tetset x.1 x.2 := by rw [hT]; exact mem_insert_self _ _
    have hl0 : tetLeg x.1 x.2 0 = f := by rw [tetLeg_zero x hx h0T, hT, erase_insert h0]
    have hpow : (f.powersetCard 2).image (insert 0) = {tetLeg x.1 x.2 1, tetLeg x.1 x.2 2, tetLeg x.1 x.2 3} := by
      have := legs_cone x hx h0T
      rwa [hT, erase_insert h0] at this
    have hsum : ∑ e ∈ f.powersetCard 2, col (insert 0 e) =
        col (tetLeg x.1 x.2 1) + col (tetLeg x.1 x.2 2) + col (tetLeg x.1 x.2 3) := by
      rw [← Finset.sum_image (f := col) (s := f.powersetCard 2) (g := insert 0) ?_, hpow]
      · obtain ⟨hd1, hd2⟩ := legs_distinct x hx
        rw [Finset.sum_insert hd1, Finset.sum_insert hd2, Finset.sum_singleton]
        ring
      · intro e1 h1 e2 h2 h
        have n1 : 0 ∉ e1 := fun h' => h0 ((mem_powersetCard.1 h1).1 h')
        have n2 : 0 ∉ e2 := fun h' => h0 ((mem_powersetCard.1 h2).1 h')
        exact insert_zero_inj e1 e2 n1 n2 h
    obtain ⟨hp1, hp2⟩ := tetModel_parity col hc x.1 x.2 (hM x hx)
    rw [hT, hl0] at hp1
    rw [hsum]
    have := hc f
    have := hc (insert 0 f)
    have := hc (tetLeg x.1 x.2 1)
    have := hc (tetLeg x.1 x.2 2)
    have := hc (tetLeg x.1 x.2 3)
    have hp2' : (col (insert 0 f) + col (tetLeg x.1 x.2 1) + col (tetLeg x.1 x.2 3)) % 2 = 0 := by
      have h := hp2; rwa [hT] at h
    omega
  intro f
  unfold coneCol
  by_cases h3 : #f = 3
  · rw [if_pos h3, htri f h3]
  rw [if_neg h3]
  by_cases h4 : #f = 4
  · rw [if_pos h4]
    obtain ⟨x, hx, hT⟩ := exists_tet_of_card f h4
    unfold tetCol
    rw [← hT, rank_even_tet x hx, Finset.sum_pair (succAbove_succAbove_ne x.1 x.2)]
    unfold tetset
    have e0 := erase_tet x.1 x.2 0
    have e2 := erase_tet x.1 x.2 2
    rw [e0, e2, htri _ (card_tetLeg _ _ _), htri _ (card_tetLeg _ _ _)]
    obtain ⟨hp1, -⟩ := tetModel_parity col hc x.1 x.2 (hM x hx)
    have b0 := hc (univ \ {x.1, x.1.succAbove x.2})
    have b1 := hc (tetLeg x.1 x.2 0)
    have b2 := hc (tetLeg x.1 x.2 2)
    simp only [tetset] at hp1
    omega
  · rw [if_neg h4]
    exact hz f h3 h4

end Lightlike.TV
