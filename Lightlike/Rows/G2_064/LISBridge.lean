import Lightlike.CausalSets.LongestChain

/-!
# The longest chain of sprinkled points is the longest increasing subsequence

Row G2-064 (target `T-CS3-P1`). The asymptotics `2 √n` of the longest chain of `n` uniform points
of the `1 + 1` diamond reduces, by the theorem of Vershik–Kerov and Logan–Shepp, to the longest
increasing subsequence of a random permutation. This file proves the reduction step that is
deterministic:

* `isDomChain_iff_strictMonoOn`: a chain of the dominance order of `σ` is a set of positions on
  which `σ` is strictly increasing (an increasing subsequence);
* `longestChain_eq_lis`: `longestChain σ` is the largest size of such a set (`lis σ`);
* `coneLongestChain_sprinklePt`: the longest chain of the point set
  `{sprinklePt σ i}` of Minkowski space `ℝ^{1+1}`, for the geometric causal order `coneLE`, equals
  `longestChain σ`.

**Scope.** Only the deterministic bridge is proved. That `n` independent uniform points of the
diamond give a uniform permutation, and the limit `2`, are not proved here.

## References

* D. Romik, *The Surprising Mathematics of Longest Increasing Subsequences*, Cambridge University
  Press (2015) (`romik-2015` in `docs/tasks/sources.yaml`).
* A. M. Vershik and S. V. Kerov, Soviet Math. Dokl. 18 (1977); B. F. Logan and L. A. Shepp,
  Adv. Math. 26 (1977).

The comparison of the statements with these sources at a location is pending.
-/

open Finset

namespace Lightlike.CausalSets

variable {n : ℕ}

/-- A set of positions `S` is an **increasing subsequence** of `σ`: `σ` is strictly increasing on
`S`. -/
def IsIncSubseq (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
  StrictMonoOn σ (S : Set (Fin n))

/-- The **length of a longest increasing subsequence** of the permutation `σ`. -/
noncomputable def lis (σ : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Fin n))).filter (IsIncSubseq σ)).sup Finset.card

/-- A chain of the dominance order of `σ` is exactly an increasing subsequence of `σ`. -/
theorem isDomChain_iff_strictMonoOn (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    IsDomChain σ S ↔ IsIncSubseq σ S := by
  constructor
  · intro h i hi j hj hij
    rcases h i hi j hj with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact lt_of_le_of_ne h2 (fun e => hij.ne (σ.injective e))
    · exact absurd hij (not_lt.mpr h1)
  · intro h i hi j hj
    rcases le_total i j with hij | hij
    · rcases hij.eq_or_lt with e | hlt
      · subst e; exact Or.inl ⟨le_rfl, le_rfl⟩
      · exact Or.inl ⟨hij, (h hi hj hlt).le⟩
    · rcases hij.eq_or_lt with e | hlt
      · subst e; exact Or.inl ⟨le_rfl, le_rfl⟩
      · exact Or.inr ⟨hij, (h hj hi hlt).le⟩

/-- The longest chain of the dominance order of `σ` is the longest increasing subsequence. -/
theorem longestChain_eq_lis (σ : Equiv.Perm (Fin n)) : longestChain σ = lis σ := by
  classical
  unfold longestChain lis
  have : (Finset.univ.filter (IsDomChain σ)) = Finset.univ.filter (IsIncSubseq σ) := by
    ext S; simp [isDomChain_iff_strictMonoOn]
  convert congrArg (fun F => F.sup Finset.card) this

/-- Every increasing subsequence has at most `lis σ` elements. -/
theorem card_le_lis {σ : Equiv.Perm (Fin n)} {S : Finset (Fin n)} (h : IsIncSubseq σ S) :
    S.card ≤ lis σ := by
  classical
  unfold lis
  exact Finset.le_sup (f := Finset.card) (by simpa using h)

/-- Some increasing subsequence has exactly `lis σ` elements. -/
theorem exists_incSubseq_card_eq_lis (σ : Equiv.Perm (Fin n)) :
    ∃ S : Finset (Fin n), IsIncSubseq σ S ∧ S.card = lis σ := by
  classical
  unfold lis
  obtain ⟨S, hS, e⟩ := Finset.exists_mem_eq_sup
    ((Finset.univ : Finset (Finset (Fin n))).filter (IsIncSubseq σ))
    ⟨∅, by simp [IsIncSubseq, StrictMonoOn]⟩ Finset.card
  exact ⟨S, (Finset.mem_filter.mp hS).2, e.symm⟩

/-- The sprinkled points `sprinklePt σ i` are pairwise distinct. -/
theorem sprinklePt_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (sprinklePt σ) := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [sprinklePt, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have : ((i : ℕ) : ℝ) = (j : ℕ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-- The **length of a longest chain** of a finite set of points of `ℝ^{1+1}` for the geometric
causal order `coneLE`. -/
noncomputable def coneLongestChain (P : Finset (Fin 2 → ℝ)) : ℕ := by
  classical
  exact (P.powerset.filter (fun Q : Finset (Fin 2 → ℝ) =>
    IsChain coneLE (Q : Set (Fin 2 → ℝ)))).sup Finset.card

/-- A subset of the sprinkled points is a `coneLE`-chain iff its positions form a chain of the
dominance order. -/
theorem isChain_coneLE_image_iff (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    IsChain coneLE ((S.image (sprinklePt σ) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)) ↔
      IsDomChain σ S := by
  rw [Finset.coe_image]
  constructor
  · intro h i hi j hj
    by_cases e : i = j
    · subst e; exact Or.inl ⟨le_rfl, le_rfl⟩
    · have := h (Set.mem_image_of_mem _ hi) (Set.mem_image_of_mem _ hj)
        (fun e' => e ((sprinklePt_injective σ) e'))
      rcases this with h1 | h1
      · exact Or.inl ((coneLE_sprinklePt σ i j).1 h1)
      · exact Or.inr ((coneLE_sprinklePt σ j i).1 h1)
  · rintro h _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ _
    rcases h i hi j hj with h1 | h1
    · exact Or.inl ((coneLE_sprinklePt σ i j).2 h1)
    · exact Or.inr ((coneLE_sprinklePt σ j i).2 h1)

/-- **The longest chain of the sprinkled points of `σ` in `ℝ^{1+1}` is the longest increasing
subsequence of `σ`.** -/
theorem coneLongestChain_sprinklePt (σ : Equiv.Perm (Fin n)) :
    coneLongestChain (Finset.univ.image (sprinklePt σ)) = lis σ := by
  classical
  rw [← longestChain_eq_lis]
  unfold coneLongestChain longestChain
  apply le_antisymm
  · apply Finset.sup_le
    intro Q hQ
    rw [Finset.mem_filter, Finset.mem_powerset] at hQ
    obtain ⟨S, -, rfl⟩ := Finset.subset_image_iff.mp hQ.1
    rw [Finset.card_image_of_injective _ (sprinklePt_injective σ)]
    exact Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (isChain_coneLE_image_iff σ S).1 hQ.2⟩)
  · apply Finset.sup_le
    intro S hS
    have hS' := (Finset.mem_filter.mp hS).2
    have := Finset.le_sup (f := Finset.card)
      (s := (Finset.univ.image (sprinklePt σ)).powerset.filter
        (fun Q : Finset (Fin 2 → ℝ) => IsChain coneLE (Q : Set (Fin 2 → ℝ))))
      (b := S.image (sprinklePt σ))
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.image_subset_image (Finset.subset_univ _)),
        (isChain_coneLE_image_iff σ S).2 hS'⟩)
    rwa [Finset.card_image_of_injective _ (sprinklePt_injective σ)] at this

end Lightlike.CausalSets
