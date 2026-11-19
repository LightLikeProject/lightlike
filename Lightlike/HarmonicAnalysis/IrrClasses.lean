import Lightlike.HarmonicAnalysis.IrrDecomposition

/-!
# Equivalence classes of irreducible representations

Equivalence of unitary matrix representations is an equivalence relation, the conjugate of an irreducible
representation is irreducible, and the matrix coefficients of equivalent representations span the same space.

Supporting lemmas for the Peter–Weyl theorem; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace UnitaryMatrixRep

variable {ι κ ν : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]

lemma conj_mat (ρ : UnitaryMatrixRep G ι) (g : G) : ρ.conj.mat g = (ρ.mat g).map (starRingEnd ℂ) := rfl

lemma Equivalent.refl (ρ : UnitaryMatrixRep G ι) : Equivalent ρ ρ :=
  ⟨LinearEquiv.refl ℂ _, fun _ _ => rfl⟩

lemma Equivalent.symm {ρ : UnitaryMatrixRep G ι} {σ : UnitaryMatrixRep G κ} (h : Equivalent ρ σ) :
    Equivalent σ ρ := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun g w => ?_⟩
  apply e.injective
  rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

lemma Equivalent.trans {ρ : UnitaryMatrixRep G ι} {σ : UnitaryMatrixRep G κ} {τ : UnitaryMatrixRep G ν}
    (h1 : Equivalent ρ σ) (h2 : Equivalent σ τ) : Equivalent ρ τ := by
  obtain ⟨e, he⟩ := h1
  obtain ⟨f, hf⟩ := h2
  exact ⟨f.trans e, fun g w => by simp [hf, he]⟩

/-- The conjugate of an irreducible representation is irreducible. -/
lemma IsIrreducible.conj {ρ : UnitaryMatrixRep G ι} (h : ρ.IsIrreducible) : ρ.conj.IsIrreducible := by
  refine ⟨h.1, fun X hX => ?_⟩
  let Xc : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | (fun i => starRingEnd ℂ (w i)) ∈ X}
      add_mem' := fun {a b} ha hb => by
        show (fun i => starRingEnd ℂ ((a + b) i)) ∈ X
        have h := X.add_mem ha hb
        have e : (fun i => starRingEnd ℂ ((a + b) i)) =
            (fun i => starRingEnd ℂ (a i)) + fun i => starRingEnd ℂ (b i) := by
          funext i; simp
        rw [e]; exact h
      zero_mem' := by
        show (fun i => starRingEnd ℂ ((0 : ι → ℂ) i)) ∈ X
        have e : (fun i => starRingEnd ℂ ((0 : ι → ℂ) i)) = 0 := by funext i; simp
        rw [e]; exact X.zero_mem
      smul_mem' := fun c w hw => by
        show (fun i => starRingEnd ℂ ((c • w) i)) ∈ X
        have h := X.smul_mem (starRingEnd ℂ c) hw
        have e : (fun i => starRingEnd ℂ ((c • w) i)) =
            starRingEnd ℂ c • fun i => starRingEnd ℂ (w i) := by
          funext i; simp
        rw [e]; exact h }
  have hXc : ∀ g, ∀ w ∈ Xc, (ρ.mat g).mulVec w ∈ Xc := by
    intro g w hw
    have h1 := hX g _ hw
    show (fun i => starRingEnd ℂ (((ρ.mat g).mulVec w) i)) ∈ X
    convert h1 using 1
    ext i
    simp [Matrix.mulVec, dotProduct, conj_mat, map_sum]
  rcases h.2 Xc hXc with h0 | h0
  · left
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have : (fun i => starRingEnd ℂ (x i)) ∈ Xc := by
      show (fun i => starRingEnd ℂ (starRingEnd ℂ (x i))) ∈ X
      simpa using hx
    rw [h0] at this
    ext i
    have := congrFun (show (fun i => starRingEnd ℂ (x i)) = 0 by simpa using this) i
    simpa using this
  · right
    refine (Submodule.eq_top_iff').2 fun x => ?_
    have : (fun i => starRingEnd ℂ (x i)) ∈ Xc := by rw [h0]; trivial
    have h2 : (fun i => starRingEnd ℂ (starRingEnd ℂ (x i))) ∈ X := this
    have e : (fun i => starRingEnd ℂ (starRingEnd ℂ (x i))) = x := by funext i; simp
    rwa [e] at h2

/-- The entries of an equivalent representation are linear combinations of the entries of the other. -/
lemma entry_eq_sum_of_equivalent {ρ : UnitaryMatrixRep G ι} {σ : UnitaryMatrixRep G κ}
    (h : Equivalent ρ σ) (k l : κ) :
    ∃ c : ι → ι → ℂ, ∀ g, σ.mat g k l = ∑ a, ∑ b, c a b * ρ.mat g a b := by
  obtain ⟨e, he⟩ := h
  let E : Matrix ι κ ℂ := LinearMap.toMatrix' (e : (κ → ℂ) →ₗ[ℂ] (ι → ℂ))
  let F : Matrix κ ι ℂ := LinearMap.toMatrix' (e.symm : (ι → ℂ) →ₗ[ℂ] (κ → ℂ))
  have hE : ∀ w, e w = E.mulVec w := fun w => by
    simp [E, LinearMap.toMatrix'_mulVec]
  have hF : ∀ w, e.symm w = F.mulVec w := fun w => by
    simp [F, LinearMap.toMatrix'_mulVec]
  refine ⟨fun a b => F k a * E b l, fun g => ?_⟩
  have h1 : (σ.mat g).mulVec (Pi.single l 1) = e.symm ((ρ.mat g).mulVec (e (Pi.single l 1))) := by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply]
  have h2 := congrFun h1 k
  rw [Matrix.mulVec_single_one] at h2
  have h2' : σ.mat g k l = e.symm ((ρ.mat g).mulVec (e (Pi.single l 1))) k := h2
  rw [h2', hF, hE]
  simp only [Matrix.mulVec, dotProduct, Matrix.mulVec_single_one, Pi.single_apply]
  simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

end UnitaryMatrixRep

end

end Lightlike.HarmonicAnalysis
