import Lightlike.PL.CutStepMixed

/-!
# Slicing by one more functional preserves stellar equivalence

The slicing `sliceComplex K H` is compared with the slicing by `H` and one more functional `h` by
walking through the mixed poset: the cells are split one at a time, in an order in which every cell
comes after its faces. An uncut cell is only renamed (`orderComplex_mixedCells_insert_of_const`);
a cut cell is exchanged for its three new cells (`stellarEquivIn_mixed_cut`), which needs the
boundary spheres of the positive and negative new cells. These are the hypothesis `hsph` below.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {K : SComplex E} {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ}

open Classical in
/-- The boundary-sphere hypothesis of a slicing walk: whenever a cell `A` is cut by `h`, all its
faces are split and nothing else is, the boundaries of the positive and negative new cells over
`A` are PL spheres of some dimension. -/
def CutSpheres (K : SComplex E) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) : Prop :=
  ∀ (D : Finset (CellIdx E ι)) (A : CellIdx E ι), A ∈ cells K (fun i => ⇑(H i)) → A ∉ D →
    (∀ x ∈ cells K (fun i => ⇑(H i)), ∀ y ∈ D, x ≤ y → x ∈ D) →
    (∀ x ∈ cells K (fun i => ⇑(H i)), x < A → x ∈ D) →
    (∃ x ∈ cellSet (fun i => ⇑(H i)) A, 0 < h x) →
    (∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x = 0) →
    (∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x < 0) →
    ∃ n : ℕ,
      IsSB false (n + 1)
        (orderComplex ((mixedCells K H h (insert A D)).filter (· < newOver A 1))) ∧
      IsSB false (n + 1)
        (orderComplex ((mixedCells K H h (insert A D)).filter (· < newOver A (-1))))

/-- **Walking through the splitting.** If the boundary spheres of the cut cells are stellar
spheres, the mixed poset after splitting any downward closed set `D` of cells has an order complex
stellar equivalent to the one before any splitting. -/
theorem stellarEquivIn_mixed_stage [Infinite (Mixed E ι)] (hs : CutSpheres K H h) :
    ∀ (n : ℕ) (D : Finset (CellIdx E ι)), D.card = n → D ⊆ cells K (fun i => ⇑(H i)) →
      (∀ x ∈ cells K (fun i => ⇑(H i)), ∀ y ∈ D, x ≤ y → x ∈ D) →
      StellarEquivIn (orderComplex (mixedCells K H h ∅)) (orderComplex (mixedCells K H h D)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro D hc _ _
    rw [Finset.card_eq_zero.1 hc]
  | succ n ih =>
    intro D hc hDs hDd
    have hne : D.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨A, hAD, hmax⟩ := Finset.exists_maximal hne
    have hAc : A ∈ cells K (fun i => ⇑(H i)) := hDs hAD
    set D' := D.erase A with hD'
    have hDeq : insert A D' = D := Finset.insert_erase hAD
    have hAn : A ∉ D' := Finset.notMem_erase A D
    have hcard : D'.card = n := by rw [Finset.card_erase_of_mem hAD]; omega
    have hD's : D' ⊆ cells K (fun i => ⇑(H i)) := fun x hx => hDs (Finset.mem_of_mem_erase hx)
    have hD'd : ∀ x ∈ cells K (fun i => ⇑(H i)), ∀ y ∈ D', x ≤ y → x ∈ D' := by
      intro x hx y hy hxy
      have hyD := Finset.mem_of_mem_erase hy
      have hxD := hDd x hx y hyD hxy
      refine Finset.mem_erase.2 ⟨?_, hxD⟩
      rintro rfl
      exact (Finset.ne_of_mem_erase hy) (le_antisymm (hmax hyD hxy) hxy)
    have hmin : ∀ x ∈ cells K (fun i => ⇑(H i)), x < A → x ∈ D' := by
      intro x hx hxA
      exact Finset.mem_erase.2 ⟨hxA.ne, hDd x hx A hAD hxA.le⟩
    refine (ih D' hcard hD's hD'd).trans ?_
    rw [← hDeq]
    rcases cell_sign_dichotomy H A h with ⟨e, he⟩ | ⟨hp, hz, hn⟩
    · rw [orderComplex_mixedCells_insert_of_const hAc hAn hD'd hmin he]
      exact StellarEquivIn.map_perm _ _
    · obtain ⟨m, hSp, hSm⟩ := hs D' A hAc hAn hD'd hmin hp hz hn
      exact stellarEquivIn_mixed_cut hAc hAn hD'd hmin hp hz hn hSp hSm

/-- **One more slicing functional preserves stellar equivalence.** If the boundary spheres of the
cut cells are stellar spheres, the slicing by `H` and the slicing by `H` and `h` are stellar
equivalent, both viewed in the mixed poset (the old cells and the new cells being kept apart). -/
theorem stellarEquivIn_slice_ext [Infinite (Mixed E ι)] (hs : CutSpheres K H h) :
    StellarEquivIn ((sliceComplex K (fun i => ⇑(H i))).map Mixed.oldEmb)
      ((sliceComplex K (extH H h)).map Mixed.newEmb) := by
  rw [← orderComplex_mixedCells_empty, ← orderComplex_mixedCells_univ]
  exact stellarEquivIn_mixed_stage hs _ _ rfl (fun _ hx => hx) (fun x hx _ _ _ => hx)

end SComplex
end Lightlike.PL
