import Lightlike.SpinFoam.ForcingMoves
import Lightlike.SpinFoam.ForcingMove33
import Lightlike.SpinFoam.ForcingMove24

/-!
# Robust forcing sets and the 1-5 move

A set `T` of triangles is *robust* for a complex `K` if it forces every triangle of `K` even when any
one tetrahedron of `K` is removed. A robust set keeps forcing under every 2-4 move and under every 3-3
move that does not remove one of its triangles (`forces_move24_of_robust`, `forces_move33_of_robust`; the
3-3 case rests on `forcesIn_common_of_robust_33`, "Lemma X", proved with blocking sets), and it stays
robust under the 1-5 move (`robust_move15`). It is a conjecture that robust sets also stay robust under
the 3-3 and 2-4 moves. Numerical evidence (`scripts/spinfoam/robust_check.py`): the set carried along from
the boundary of the 5-simplex by random 3-3, 2-4 and 1-5 moves is robust at every tetrahedron sampled
(1,104,480 of 1,104,480 tetrahedra), at every 3-3 location (38,176 of 38,176), and after each of 822
consecutive moves.

## Main results

* `Robust`: the definition; `robustBy`, `robust_of_robustBy`: a kernel checker from explicit forcing
  steps.
* `Move15.robust_move15`: robust sets stay robust under the 1-5 move.
* `Forcing33.lemmaX_abstract`, `Forcing33.forcesIn_common_of_robust_33`: **Lemma X.** A robust set that
  does not contain the moved triangle forces by the tetrahedra without that triangle alone.
* `Forcing33.forces_move33_of_robust`: a robust set keeps forcing under a 3-3 move that does not remove
  one of its triangles.
* `forces_move24_of_robust`: a robust set keeps forcing under every 2-4 move, with the triangle
  `{a, p, q}` added: the closure condition of `forces_move24_iff` is the robustness condition at the
  removed tetrahedron.

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


namespace Forcing33

variable {V : Type*} [DecidableEq V]

lemma exists_k0 (X Y : Fin 3 → Bool) (h : ∀ k, ¬ (X k = true ∧ Y k = true)) :
    ∃ k0 : Fin 3, (∀ k, k ≠ k0 → X k = false) ∨ (∀ k, k ≠ k0 → Y k = false) := by
  revert X Y; decide

open Classical in
/-- **Lemma X, abstract form.** Let `P0` be the tetrahedra common to the complexes before and after a
3-3 move, `C` the common triangles, `T ⊆ C` a set that does not contain `σ`. If `T` forces every
triangle (those of `C` and `σ`) with any one of the tetrahedra `P0 ∪ {σ ∪ {c_k}}` removed, then `T`
forces `C` by the common tetrahedra alone.

Proof: if not, the common closure `A` of `T` misses some triangle, so `C ∖ A` is a nonempty blocking set
for `P0` that avoids `T`. In the tetrahedron `σ ∪ {c_k}` it meets the three triangles `m k p`, say in `n k`
of them. Both `A ∪ {σ}` and `A` are closed under `P0`; `A ∪ {σ}` is closed under `σ ∪ {c_k}` when
`n k ≠ 1`, and `A` when `n k ≠ 0`. Of the three values `n k`, at most one is `1` or at most one is `0`,
so one of the two sets is closed under all tetrahedra but one; the robustness hypothesis for that
tetrahedron, with soundness, puts `σ` or all of `C` in it, a contradiction. -/
theorem lemmaX_abstract (e : Fin 6 ↪ V) (P0 C T : Finset (Finset V))
    (hCt : ∀ t ∈ P0, ∀ g ∈ t.powersetCard 3, g ∈ C)
    (hσC : tx e sigX ∉ C) (hT : T ⊆ C)
    (hR : ∀ t ∈ P0 ∪ univ.image (fun k => tx e (tetS k)),
      ForcesIn ((P0 ∪ univ.image fun k => tx e (tetS k)).erase t) (insert (tx e sigX) C) T) :
    ForcesIn P0 C T := by
  by_contra hnot
  set A : Finset (Finset V) := C.filter (fun f => ForcesIn P0 {f} T) with hA
  have hAC : A ⊆ C := filter_subset _ _
  have hTA : T ⊆ A := fun f hf => mem_filter.mpr ⟨hT hf, .done (by simpa using hf)⟩
  have hAforced : ForcesIn P0 A T := ForcesIn.of_singles fun g hg => (mem_filter.mp hg).2
  have hAcl : ClosedUnder P0 A := fun t ht f hf hothers =>
    mem_filter.mpr ⟨hCt t ht f hf, ForcesIn.of_forced_others ht hf
      fun g hg hne => (mem_filter.mp (hothers g hg hne)).2⟩
  have hCA : ¬ C ⊆ A := fun h => hnot (hAforced.mono_target (fun x hx => mem_union_left _ (h hx)))
  have hσA : tx e sigX ∉ A := fun h => hσC (hAC h)
  set Q : Finset (Finset V) := univ.image (fun k => tx e (tetS k)) with hQ
  -- the number of triangles `m k p` of the tetrahedron `σ ∪ {c_k}` missing from `A`
  set n : Fin 3 → ℕ := fun k => #(univ.filter fun p => tx e (mX k p) ∉ A) with hn
  -- closedness under the common tetrahedra of `A` and `insert σ A`
  have hcl0 : ClosedUnder P0 (insert (tx e sigX) A) := by
    intro t ht f hf hothers
    refine mem_insert_of_mem (hAcl t ht f hf fun g hg hne => ?_)
    rcases mem_insert.mp (hothers g hg hne) with h | h
    · exact absurd (h ▸ hCt t ht g hg) hσC
    · exact h
  -- the two candidate sets
  have hW1 : ∀ k, n k ≠ 1 → ∀ f ∈ (tx e (tetS k)).powersetCard 3,
      (∀ g ∈ (tx e (tetS k)).powersetCard 3, g ≠ f → g ∈ insert (tx e sigX) A) →
        f ∈ insert (tx e sigX) A := by
    intro k hk f hf hothers
    rcases (mem_tris_tetS e k).mp hf with rfl | ⟨p, rfl⟩
    · exact mem_insert_self _ _
    · refine mem_insert_of_mem (by_contra fun hfA => hk ?_)
      have : (univ.filter fun p' => tx e (mX k p') ∉ A) = {p} := by
        ext p'
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hp'
          by_contra hne
          have := hothers (tx e (mX k p')) ((mem_tris_tetS e k).mpr (Or.inr ⟨p', rfl⟩))
            (fun h => hne (mX_inj k p' p ((tx_inj e).mp h)))
          rcases mem_insert.mp this with h | h
          · exact absurd ((tx_inj e).mp h) (mX_ne_sigX k p')
          · exact hp' h
        · rintro rfl; exact hfA
      simp only [hn, this, card_singleton]
  have hW2 : ∀ k, n k ≠ 0 → ∀ f ∈ (tx e (tetS k)).powersetCard 3,
      (∀ g ∈ (tx e (tetS k)).powersetCard 3, g ≠ f → g ∈ A) → f ∈ A := by
    intro k hk f hf hothers
    rcases (mem_tris_tetS e k).mp hf with rfl | ⟨p, rfl⟩
    · exfalso
      refine hk ?_
      simp only [hn, card_eq_zero, filter_eq_empty_iff, mem_univ, true_implies, not_not]
      intro p
      exact hothers _ ((mem_tris_tetS e k).mpr (Or.inr ⟨p, rfl⟩))
        (fun h => mX_ne_sigX k p ((tx_inj e).mp h))
    · exact absurd (hothers _ ((mem_tris_tetS e k).mpr (Or.inl rfl))
        (fun h => mX_ne_sigX k p ((tx_inj e).mp h.symm))) hσA
  -- choose the tetrahedron to remove
  obtain ⟨k0, hk0⟩ := exists_k0 (fun k => decide (n k = 1)) (fun k => decide (n k = 0))
    (fun k ⟨h1, h2⟩ => by simp only [decide_eq_true_eq] at h1 h2; omega)
  have ht0 : tx e (tetS k0) ∈ P0 ∪ Q := mem_union_right _ (mem_image_of_mem _ (mem_univ _))
  have hRk := hR _ ht0
  have hmemQ : ∀ t ∈ (P0 ∪ Q).erase (tx e (tetS k0)), t ∈ P0 ∨ ∃ k, k ≠ k0 ∧ t = tx e (tetS k) := by
    intro t ht
    obtain ⟨hne, htm⟩ := mem_erase.mp ht
    rcases mem_union.mp htm with h | h
    · exact Or.inl h
    · obtain ⟨k, -, rfl⟩ := mem_image.mp h
      exact Or.inr ⟨k, fun hk => hne (by rw [hk]), rfl⟩
  rcases hk0 with hk0 | hk0
  · -- every other `n k` differs from 1: `insert σ A` is closed
    have hcl : ClosedUnder ((P0 ∪ Q).erase (tx e (tetS k0))) (insert (tx e sigX) A) := by
      intro t ht f hf hothers
      rcases hmemQ t ht with h | ⟨k, hk, rfl⟩
      · exact hcl0 t h f hf hothers
      · exact hW1 k (by simpa using hk0 k hk) f hf hothers
    have := hRk.sound hcl (hTA.trans (subset_insert _ _))
    refine hCA fun f hf => ?_
    rcases mem_insert.mp (this (mem_insert_of_mem hf)) with h | h
    · exact absurd (h ▸ hf) hσC
    · exact h
  · -- every other `n k` differs from 0: `A` is closed, and does not contain `σ`
    have hcl : ClosedUnder ((P0 ∪ Q).erase (tx e (tetS k0))) A := by
      intro t ht f hf hothers
      rcases hmemQ t ht with h | ⟨k, hk, rfl⟩
      · exact hAcl t h f hf hothers
      · exact hW2 k (by simpa using hk0 k hk) f hf hothers
    have := hRk.sound hcl hTA
    exact hσA (this (mem_insert_self _ _))

end Forcing33


namespace Forcing33

section ComplexX

open Lightlike.FourD Complex4

variable {V : Type*} [LinearOrder V] {K : Complex4 V} {σ τ : Finset V}

/-- **Lemma X (3-3 case).** If `T` is robust for `K` and does not contain the triangle `σ` that a 3-3
move removes, then the closure of `T` under the tetrahedra of `K` that do not contain `σ` already
reaches every triangle of `K` other than `σ`. A nonempty blocking set for the tetrahedra without `σ`
that avoids `T` would be blocking for all of `K` (with or without `σ`) except possibly in the one
tetrahedron `σ ∪ {c}` where it meets exactly one more triangle, and robustness removes that tetrahedron
(`lemmaX_abstract`). Together with `forces_move33_iff` it gives `forces_move33_of_robust`. -/
theorem forcesIn_common_of_robust_33 (h : K.IsMove σ τ) (hσ : #σ = 3) {T : Finset (Finset V)}
    (hT : T ⊆ K.tris) (hσT : σ ∉ T) (hR : Robust K T) :
    ForcesIn (K.tets.filter fun t => ¬ σ ⊆ t) (K.tris.erase σ) T := by
  obtain ⟨e, hσe, hτe⟩ := exists_embedding h hσ
  subst hσe hτe
  have hSj : ∀ j : Fin 3, tx e (univ.erase (Fin.natAdd 3 j)) ∈ K.simps := fun j => by
    rw [← tx_univ_erase]; exact h.mem _ (mem_map_of_mem _ (natAdd_mem_tauX j))
  have hcσ : #(tx e sigX) = 3 := hσ
  have hσtri : tx e sigX ∈ K.tris :=
    mem_faces.mpr ⟨_, hSj 0, map_subset_map.mpr sigX_sub, hcσ⟩
  set P0 := K.tets.filter fun t => ¬ tx e sigX ⊆ t with hP0
  set C := K.tris.erase (tx e sigX) with hC
  have hKtris : K.tris = insert (tx e sigX) C := (insert_erase hσtri).symm
  have hKt : K.tets = P0 ∪ univ.image fun k => tx e (tetS k) := tets_before e h
  have hCt : ∀ t ∈ P0, ∀ g ∈ t.powersetCard 3, g ∈ C := by
    intro t ht g hg
    obtain ⟨htK, hσt⟩ := mem_filter.mp ht
    obtain ⟨hgt, hgc⟩ := mem_powersetCard.mp hg
    obtain ⟨S, hS, htS, -⟩ := mem_faces.mp htK
    exact mem_erase.mpr ⟨fun hgs => hσt (hgs ▸ hgt),
      mem_faces.mpr ⟨S, hS, hgt.trans htS, hgc⟩⟩
  have hσC : tx e sigX ∉ C := fun hh => (mem_erase.mp hh).1 rfl
  have hTC : T ⊆ C := fun f hf => mem_erase.mpr ⟨fun hh => hσT (hh ▸ hf), hT hf⟩
  have hR' : ∀ t ∈ P0 ∪ univ.image (fun k => tx e (tetS k)),
      ForcesIn ((P0 ∪ univ.image fun k => tx e (tetS k)).erase t) (insert (tx e sigX) C) T := by
    intro t ht
    rw [← hKt, ← hKtris]
    rw [← hKt] at ht
    exact hR t ht
  exact lemmaX_abstract e P0 C T hCt hσC hTC hR'

/-- **A robust set keeps forcing under a 3-3 move** that does not remove one of its triangles. -/
theorem forces_move33_of_robust (h : K.IsMove σ τ) (hσ : #σ = 3) {T : Finset (Finset V)}
    (hT : T ⊆ K.tris) (hσT : σ ∉ T) (hR : Robust K T) :
    Forces (K.move h) (K.move h).tris T := by
  obtain ⟨t0, ht0⟩ : K.tets.Nonempty := by
    obtain ⟨e, hσe, hτe⟩ := exists_embedding h hσ
    subst hσe hτe
    exact ⟨tx e (tetS 0), by
      rw [tets_before e h]; exact mem_union_right _ (mem_image_of_mem _ (mem_univ _))⟩
  have hF : Forces K K.tris T :=
    (forces_iff_forcesIn K _ _).mpr ((hR t0 ht0).mono (erase_subset _ _) subset_rfl)
  exact (forces_move33_iff h hσ hT hσT hF).mpr (forcesIn_common_of_robust_33 h hσ hT hσT hR)

end ComplexX

end Forcing33

end Lightlike.SpinFoam
