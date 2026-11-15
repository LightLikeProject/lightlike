import Lightlike.PL.RadialPolytope
import Lightlike.PL.RadialGauge

/-!
# A reference simplex around a point of an affine subspace

For a finite-dimensional affine subspace `A` of dimension `d` and a point `v` of `A`, there is an
affinely independent set of `d + 1` points of `A` whose affine span is `A` and whose open simplex
contains `v`. It is the translate, by `v` minus its centroid, of any simplex spanning `A`.

## Main results

* `SComplex.exists_refSimplex`: the reference simplex.
* `SComplex.isSB_of_polytope_boundary`: a complex whose underlying set is the boundary of a bounded
  polytope is a stellar sphere, given the stellar statement in lower dimension.
-/

open Finset Module

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {κ : Type*} [Fintype κ]
  [Nonempty κ]

/-- **A simplex spanning `A` with `v` in its open simplex.** -/
theorem exists_refSimplex (A : AffineSubspace ℝ E) [FiniteDimensional ℝ A.direction] {v : E}
    (hv : v ∈ A) :
    ∃ σ : Finset E, (↑σ : Set E) ⊆ (A : Set E) ∧ AffineIndependent ℝ ((↑) : σ → E) ∧
      σ.card = finrank ℝ A.direction + 1 ∧ affineSpan ℝ (σ : Set E) = A ∧ v ∈ openHull σ := by
  have hF : FiniteDimensional ℝ (vectorSpan ℝ (A : Set E)) := by
    rw [← direction_affineSpan, AffineSubspace.affineSpan_coe]; infer_instance
  obtain ⟨t, htA, hspan, hind, hnc⟩ :=
    exists_affineIndependent_of_finiteDimensional ℝ E (A : Set E)
  rw [AffineSubspace.affineSpan_coe] at hspan
  have htf : t.Finite := by
    refine (finiteDimensional_iff_setFinite ℝ hind).mp ?_
    rw [Subtype.range_coe, ← direction_affineSpan, hspan]; infer_instance
  obtain ⟨T, rfl⟩ : ∃ T : Finset E, ↑T = t := ⟨htf.toFinset, htf.coe_toFinset⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.1 h] at hspan
    have : v ∈ affineSpan ℝ (↑(∅ : Finset E) : Set E) := hspan ▸ hv
    exact AffineSubspace.notMem_bot ℝ E v (by simpa using this)
  have : Nonempty (↥(↑T : Set E)) := ⟨⟨hTne.choose, hTne.choose_spec⟩⟩
  have hcard : T.card = finrank ℝ A.direction + 1 := by
    have h := hind.finrank_vectorSpan_add_one
    rw [Subtype.range_coe, ← direction_affineSpan, hspan] at h
    simpa using h.symm
  set n : ℝ := (T.card : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hTne.card_pos
  set c : E := ∑ x ∈ T, n⁻¹ • x with hc
  have hcA : c ∈ A := by
    refine A.convex.sum_mem (fun _ _ => inv_nonneg.2 hn0.le) ?_ fun x hx => htA hx
    rw [Finset.sum_const, nsmul_eq_mul]; exact mul_inv_cancel₀ hn0.ne'
  have hδ : v - c ∈ A.direction := A.vsub_mem_direction hv hcA
  have hinj : Function.Injective fun x : E => x + (v - c) := add_left_injective _
  have hsubA : ∀ x ∈ T, x + (v - c) ∈ A := fun x hx => by
    have := A.vadd_mem_of_mem_direction hδ (htA hx)
    simpa [add_comm] using this
  have hp : AffineIndependent ℝ (fun x : (↑T : Set E) => (x : E) + (v - c)) := by
    have := hind.map' (AffineEquiv.constVAdd ℝ E (v - c)).toAffineMap (AffineEquiv.injective _)
    simpa [Function.comp_def, add_comm] using this
  have e : (↑(T.image fun x => x + (v - c)) : Set E) =
      Set.range (fun x : (↑T : Set E) => (x : E) + (v - c)) := by
    ext y
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  refine ⟨T.image fun x => x + (v - c), ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact hsubA x hx
  · have h := hp.range
    rw [← e] at h
    exact h
  · rw [Finset.card_image_of_injective _ hinj, hcard]
  · rw [e]
    refine hp.affineSpan_eq_of_le_of_card_eq_finrank_add_one (sp := A) ?_ ?_
    · refine affineSpan_le.2 ?_
      rintro _ ⟨x, rfl⟩
      exact hsubA x x.2
    · simpa using hcard
  · refine ⟨fun _ => n⁻¹, fun _ _ => inv_pos.2 hn0, ?_, ?_⟩
    · rw [Finset.sum_const, Finset.card_image_of_injective _ hinj, nsmul_eq_mul]
      exact mul_inv_cancel₀ hn0.ne'
    · rw [Finset.sum_image (fun x _ y _ h => hinj h)]
      simp only [smul_add, Finset.sum_add_distrib, ← hc, ← Finset.smul_sum, Finset.sum_const, nsmul_eq_mul]
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn0.ne', one_smul]
      abel

/-- **A bounded polytope boundary is a stellar sphere**, given the stellar statement in lower
dimension. In an affine subspace `A` of dimension `d`, let `P` be the polytope of the affine
functions `g k` that are negative at a point `v` of `A`, bounded in the sense that no ray from `v`
in `A` keeps all of them non-increasing. A geometric complex `γ` of simplices with at most `d`
vertices whose underlying set is the boundary of `P` in `A` is a stellar sphere of dimension `d`. -/
theorem isSB_of_polytope_boundary [Infinite E] {d : ℕ} (hT : SubdivStellar E (d - 1))
    (A : AffineSubspace ℝ E) [FiniteDimensional ℝ A.direction] (hd : finrank ℝ A.direction = d)
    {v : E} (hvA : v ∈ A) (g : κ → E →ᵃ[ℝ] ℝ) (hneg : ∀ k, g k v < 0)
    (hbdd : ∀ y ∈ A, y ≠ v → ∃ k, g k v < g k y) {γ : SComplex E} (hγ : IsGeom γ)
    (h₀γ : ∅ ∈ γ) (hγn : ∀ s ∈ γ, #s ≤ d)
    (hspace : γ.space = {x | x ∈ A ∧ (∀ k, g k x ≤ 0) ∧ ∃ k, g k x = 0}) :
    IsSB false d γ := by
  obtain ⟨σ, -, hσ, hcard, hspan, hvo⟩ := exists_refSimplex A hvA
  rw [hd] at hcard
  have hne : σ.Nonempty := Finset.card_pos.1 (by omega)
  set f : κ → E →ᵃ[ℝ] ℝ := fun k => AffineMap.const ℝ E 1 - (g k v)⁻¹ • g k with hf
  obtain ⟨β, hβ, h₀β, hdom⟩ := exists_gauge_subdivision hσ hne f
  have hpos : ∀ y ∈ (boundary σ).space, 0 < polyScale g v y := by
    intro y hy
    obtain ⟨hyc, hyn⟩ := (mem_space_boundary hσ).1 hy
    have hyA : y ∈ A := hspan ▸ convexHull_subset_affineSpan _ hyc
    have hyv : y ≠ v := fun h => hyn (h ▸ hvo)
    obtain ⟨k, hk⟩ := hbdd y hyA hyv
    have h1 : g k y / g k v < 1 := (div_lt_one_of_neg (hneg k)).2 hk
    have := polyScale_apply_le g v k y
    linarith
  have hr : IsRadialOn β v (polyScale g v) := by
    refine isRadialOn_gaugeMax (g := f) hdom ?_ ?_
    · intro s hs y hy
      have : y ∈ (boundary σ).space := by
        rw [← hβ.space_eq]
        exact mem_space.2 ⟨s, hs, subset_convexHull ℝ _ hy⟩
      exact hpos y this
    · intro s hs
      obtain ⟨t, ht, hst⟩ := hβ.le s hs
      have ht' := mem_boundary.1 ht
      intro hv
      refine notMem_affineSpan_of_mem_openHull hσ ht'.subset ht'.ne hvo ?_
      refine affineSpan_le.2 (fun y hy => ?_) hv
      exact convexHull_subset_affineSpan _ (hst (subset_convexHull ℝ _ hy))
  have hinj := injOn_projMap_boundary hσ hvo hpos
  have hβs : β.space = (boundary σ).space := hβ.space_eq
  refine isSB_of_radial hT hσ hcard hβ h₀β hr (hβs ▸ hinj) hγ h₀γ hγn ?_
  rw [hβs, projMap_image_boundary hσ hvo g hneg hpos, hspan, hspace]

end SComplex
end Lightlike.PL
