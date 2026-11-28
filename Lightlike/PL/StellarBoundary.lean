import Lightlike.PL.Links
import Lightlike.PL.Euler

/-!
# Balls, spheres and the boundary of a stellar manifold

Following Lickorish (*Simplicial moves on complexes and manifolds*, 1999, Definition 3.1), a
**stellar ball** is a complex stellar equivalent to a simplex `Δᵐ` (`m ≥ 0`) and a **stellar sphere**
is a complex stellar equivalent to the boundary `∂Δᵐ⁺¹` of a simplex (`m ≥ −1`; the `(−1)`-sphere
`∂Δ⁰ = {∅}` is the link of a top face, as in Lickorish's Definition 2.3). Stellar equivalence is
measured after lifting to `V ⊕ ℕ`, as for `StellarEquiv`.

* `not_isStellarBall_and_isStellarSphere`: **no complex is both a stellar ball and a stellar sphere**,
  in any dimensions: the signed face count (an Euler characteristic, `signedCount`) is a stellar
  invariant, `0` for a simplex and `−(−1)^{#A} ≠ 0` for the boundary of the simplex on `A`.
* `stellarBoundary K`: the nonempty faces of `K` whose link is a stellar ball (Lickorish, p. 305);
  `stellarBoundary' K`: the nonempty faces whose link is not a stellar sphere.
* `IsCombManifold.stellarBoundary_eq_empty_iff`, `IsCombManifold.stellarBoundary'_eq_empty_iff`: for
  a stellar `n`-manifold `K` (`IsCombManifold n K`, Definition 3.1), each boundary is empty exactly
  when `K` is a closed combinatorial `n`-manifold.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- `K` is a **stellar ball**: stellar equivalent (after lifting to `V ⊕ ℕ`) to a simplex on a
nonempty vertex set. -/
def IsStellarBall (K : SComplex V) : Prop :=
  ∃ A : Finset (V ⊕ ℕ), A.Nonempty ∧ StellarEquivIn K.lift (simplex A)

/-- `K` is a **stellar sphere**: stellar equivalent (after lifting to `V ⊕ ℕ`) to the boundary of a
simplex on a nonempty vertex set (the boundary of a single vertex is the `(−1)`-sphere `{∅}`). -/
def IsStellarSphere (K : SComplex V) : Prop :=
  ∃ A : Finset (V ⊕ ℕ), A.Nonempty ∧ StellarEquivIn K.lift (boundary A)

/-- **No complex is both a stellar ball and a stellar sphere**, in any dimensions: a stellar
equivalence preserves the signed face count, which is `0` on a simplex and `−(−1)^{#A} ≠ 0` on the
boundary of the simplex on `A`. -/
theorem not_isStellarBall_and_isStellarSphere (K : SComplex V) :
    ¬ (IsStellarBall K ∧ IsStellarSphere K) := by
  rintro ⟨⟨A, hA, hKA⟩, ⟨B, hB, hKB⟩⟩
  have h := StellarEquivIn.signedCount_eq (StellarEquivIn.trans (StellarEquivIn.symm hKA) hKB)
  rw [signedCount_simplex hA, signedCount_boundary hB] at h
  rcases neg_one_pow_eq_or ℤ #B with h' | h' <;> rw [h'] at h <;> norm_num at h

/-- A stellar `m`-ball in the sense of `IsPLBall` is a stellar ball. -/
lemma IsPLBall.isStellarBall {m : ℕ} {K : SComplex V} (h : IsPLBall m K) : K.IsStellarBall := by
  obtain ⟨A, hA, hKA⟩ := h
  exact ⟨A, card_pos.1 (by omega), hKA⟩

/-- A stellar `m`-sphere in the sense of `IsPLSphere` is a stellar sphere. -/
lemma IsPLSphere.isStellarSphere {m : ℕ} {K : SComplex V} (h : IsPLSphere m K) : K.IsStellarSphere := by
  obtain ⟨A, hA, hKA⟩ := h
  exact ⟨A, card_pos.1 (by omega), hKA⟩

open Classical in
/-- The **boundary** of `K` (Lickorish, p. 305): the nonempty faces of `K` whose link is a stellar
ball. -/
noncomputable def stellarBoundary (K : SComplex V) : Finset (Finset V) :=
  K.faces.filter fun σ => σ.Nonempty ∧ (K.link σ).IsStellarBall

open Classical in
/-- The nonempty faces of `K` whose link is **not a stellar sphere**. -/
noncomputable def stellarBoundary' (K : SComplex V) : Finset (Finset V) :=
  K.faces.filter fun σ => σ.Nonempty ∧ ¬ (K.link σ).IsStellarSphere

open Classical in
lemma mem_stellarBoundary {K : SComplex V} {σ : Finset V} :
    σ ∈ K.stellarBoundary ↔ σ ∈ K ∧ σ.Nonempty ∧ (K.link σ).IsStellarBall := by
  simp [stellarBoundary]

open Classical in
lemma mem_stellarBoundary' {K : SComplex V} {σ : Finset V} :
    σ ∈ K.stellarBoundary' ↔ σ ∈ K ∧ σ.Nonempty ∧ ¬ (K.link σ).IsStellarSphere := by
  simp [stellarBoundary']

/-- On a closed combinatorial manifold every nonempty face has a stellar sphere as link. -/
lemma IsClosedCombManifold.isStellarSphere_link {n : ℕ} {K : SComplex V} (h : IsClosedCombManifold n K)
    {σ : Finset V} (hσ : σ ∈ K) (hne : σ.Nonempty) : (K.link σ).IsStellarSphere := by
  obtain ⟨A, hA, hLA⟩ := h.link_face hσ hne
  have := h.card_le hσ
  exact ⟨A, card_pos.1 (by omega), hLA⟩

/-- The first boundary lies in the second: a ball is not a sphere. -/
lemma stellarBoundary_subset (K : SComplex V) : K.stellarBoundary ⊆ K.stellarBoundary' := by
  intro σ hσ
  rw [mem_stellarBoundary] at hσ
  rw [mem_stellarBoundary']
  exact ⟨hσ.1, hσ.2.1, fun hs => not_isStellarBall_and_isStellarSphere _ ⟨hσ.2.2, hs⟩⟩

/-- **The boundary of a stellar manifold is empty exactly when the manifold is closed** (balls as
links): for `IsCombManifold n K`, `stellarBoundary K = ∅ ↔ IsClosedCombManifold n K`. -/
theorem IsCombManifold.stellarBoundary_eq_empty_iff {n : ℕ} {K : SComplex V} (hK : IsCombManifold n K) :
    K.stellarBoundary = ∅ ↔ IsClosedCombManifold n K := by
  constructor
  · intro h0
    rw [isClosedCombManifold_iff]
    intro v hv
    rcases isCombManifold_iff.1 hK v hv with hs | ⟨A, hA, hLA⟩
    · exact hs
    · rcases A.eq_empty_or_nonempty with rfl | hne
      · refine ⟨{Sum.inr 0}, by simp [hA.symm], ?_⟩
        rwa [boundary_singleton]
      · exfalso
        have hm : {v} ∈ K.stellarBoundary :=
          mem_stellarBoundary.2 ⟨mem_verts.1 hv, singleton_nonempty v, ⟨A, hne, hLA⟩⟩
        rw [h0] at hm
        exact notMem_empty _ hm
  · intro hc
    refine eq_empty_of_forall_notMem fun σ hσ => ?_
    have := stellarBoundary_subset K hσ
    rw [mem_stellarBoundary'] at this
    exact this.2.2 (hc.isStellarSphere_link this.1 this.2.1)

/-- **The faces with a non-sphere link**: for a stellar `n`-manifold `K`,
`IsClosedCombManifold n K ↔ stellarBoundary' K = ∅`. -/
theorem IsCombManifold.stellarBoundary'_eq_empty_iff {n : ℕ} {K : SComplex V} (hK : IsCombManifold n K) :
    IsClosedCombManifold n K ↔ K.stellarBoundary' = ∅ := by
  constructor
  · intro hc
    refine eq_empty_of_forall_notMem fun σ hσ => ?_
    rw [mem_stellarBoundary'] at hσ
    exact hσ.2.2 (hc.isStellarSphere_link hσ.1 hσ.2.1)
  · intro h0
    rw [← hK.stellarBoundary_eq_empty_iff]
    exact subset_empty.1 (h0 ▸ stellarBoundary_subset K)

end SComplex

end Lightlike.PL
