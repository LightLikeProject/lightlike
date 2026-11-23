import Lightlike.Rows.G2_008.Limit

/-!
# Surjectivity of the projections of a projective limit (row G2-008)

If the bonding maps of an inverse system of compact Hausdorff spaces over a directed set are
surjective, then so is every projection `lim X → X i`. The proof is a finite-intersection argument
in the compact product `∀ i, X i`.  This is what makes `φ ∘ proj i ↦ φ` well defined, i.e. what
lets cylindrical functions be identified with functions on `X i`.
-/

noncomputable section

open Set

namespace Lightlike.Rows.G2_008

namespace InvSystem

variable {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
variable (S : InvSystem ι X)

/-- **The projections of a limit of compact Hausdorff spaces with surjective bonding maps over
a directed set are surjective.** -/
theorem proj_surjective [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)] [IsDirectedOrder ι]
    (hS : ∀ {i j : ι} (h : i ≤ j), Function.Surjective (S.f h)) (i : ι) :
    Function.Surjective (S.proj i) := by
  classical
  have : Nonempty ι := ⟨i⟩
  intro a
  let t : Option (ι × ι) → Set (∀ i, X i) := fun o =>
    match o with
    | none => {x | x i = a}
    | some p => {x | ∀ h : p.1 ≤ p.2, S.f h (x p.2) = x p.1}
  have hclosed : ∀ o, IsClosed (t o) := by
    rintro (_ | ⟨j, k⟩)
    · exact isClosed_eq (continuous_apply i) continuous_const
    · by_cases h : j ≤ k
      · have : t (some (j, k)) = {x | S.f h (x k) = x j} := by
          ext x
          exact ⟨fun hx => hx h, fun hx _ => hx⟩
        rw [this]
        exact isClosed_eq ((S.continuous_f h).comp (continuous_apply k)) (continuous_apply j)
      · have : t (some (j, k)) = univ := by
          ext x
          exact ⟨fun _ => trivial, fun _ h' => absurd h' h⟩
        rw [this]
        exact isClosed_univ
  have hfin : ∀ u : Finset (Option (ι × ι)), (univ ∩ ⋂ o ∈ u, t o).Nonempty := by
    intro u
    obtain ⟨M, hM⟩ := Finset.exists_le
      (insert i (u.biUnion fun o => match o with
        | none => (∅ : Finset ι)
        | some p => {p.1, p.2}))
    have hiM : i ≤ M := hM i (Finset.mem_insert_self _ _)
    obtain ⟨y, hy⟩ := hS hiM a
    have hne : ∀ l, Nonempty (X l) := by
      intro l
      obtain ⟨n, hln, hMn⟩ := exists_ge_ge l M
      obtain ⟨z, _⟩ := hS hMn y
      exact ⟨S.f hln z⟩
    let x : ∀ l, X l := fun l => if h : l ≤ M then S.f h y else (hne l).some
    refine ⟨x, trivial, ?_⟩
    simp only [mem_iInter]
    intro o ho
    rcases o with _ | ⟨j, k⟩
    · show x i = a
      simp only [x, hiM, ↓reduceDIte]
      exact hy
    · intro h
      have hj : j ≤ M := hM j (Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨some (j, k), ho, by simp⟩))
      have hk : k ≤ M := hM k (Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨some (j, k), ho, by simp⟩))
      show S.f h (x k) = x j
      simp only [x, hj, hk, ↓reduceDIte]
      exact S.f_comp h hk y
  obtain ⟨x, -, hx⟩ := isCompact_univ.inter_iInter_nonempty t hclosed hfin
  exact ⟨⟨x, fun j k h => (mem_iInter.mp hx (some (j, k))) h⟩, mem_iInter.mp hx none⟩

end InvSystem

end Lightlike.Rows.G2_008
