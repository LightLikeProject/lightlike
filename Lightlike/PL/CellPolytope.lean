import Lightlike.PL.SliceGeom
import Lightlike.PL.Barycentric
import Lightlike.PL.Carrier
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# A cell of a slicing as a polytope

A cell `(s, sg)` of the slicing of a geometric complex by affine functionals `H` is a polytope in
the affine subspace `cellA` cut out of the affine span of `s` by the functionals `H i` whose sign
on the cell is zero. Its closed part is described by finitely many affine functions `g k` on the
whole space, namely the barycentric coordinates of `s` and the functionals `H i` with a nonzero
sign, and its open part is the set where all of them are negative.

## Main results

* `SComplex.cellA`: the affine subspace of a cell.
* `SComplex.cellG`: the facet functions.
* `SComplex.sliceHull_iff`, `SComplex.cellSet_iff`: the closed and the open part of a cell.
-/

open Finset Module

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*}

/-- **The affine subspace of a cell**: the affine span of its simplex, cut by the functionals
that vanish on the cell. -/
def cellA (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) : AffineSubspace ℝ E where
  carrier := {x | x ∈ affineSpan ℝ ((c.1 : Finset E) : Set E) ∧ ∀ i, c.2 i = 0 → H i x = 0}
  smul_vsub_vadd_mem' t p₁ p₂ p₃ h₁ h₂ h₃ := by
    refine ⟨AffineSubspace.smul_vsub_vadd_mem _ t h₁.1 h₂.1 h₃.1, fun i hi => ?_⟩
    rw [AffineMap.map_vadd, map_smul, AffineMap.linear_apply_vsub, h₁.2 i hi, h₂.2 i hi, h₃.2 i hi]
    simp

lemma mem_cellA {H : ι → E →ᵃ[ℝ] ℝ} {c : CellIdx E ι} {x : E} :
    x ∈ cellA H c ↔ x ∈ affineSpan ℝ ((c.1 : Finset E) : Set E) ∧ ∀ i, c.2 i = 0 → H i x = 0 :=
  Iff.rfl

/-- **The facet functions of a cell**: minus the barycentric coordinates `w`, and for each `i`
either a constant `-1` (when the sign is zero) or `-sign` times `H i`. -/
noncomputable def cellG (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) (w : E → (E →ᵃ[ℝ] ℝ)) :
    ((c.1 : Finset E) ⊕ ι) → (E →ᵃ[ℝ] ℝ)
  | .inl y => -(w y)
  | .inr i => if c.2 i = 0 then AffineMap.const ℝ E (-1) else -((c.2 i : ℝ)) • H i

lemma sign_weak_iff (a : ℝ) (sg : SignType) :
    (SignType.sign a = 0 ∨ SignType.sign a = sg) ↔
      ((sg = 0 → a = 0) ∧ (if sg = 0 then (-1 : ℝ) else -(sg : ℝ) * a) ≤ 0) := by
  rcases lt_trichotomy a 0 with h | h | h
  · rw [sign_neg h]; rcases sg with _ | _ | _ <;> simp [h.le, h.ne] <;> linarith
  · subst h; rcases sg with _ | _ | _ <;> simp
  · rw [sign_pos h]; rcases sg with _ | _ | _ <;> simp [h.le, h.ne'] <;> linarith

lemma sign_strict_iff (a : ℝ) (sg : SignType) :
    SignType.sign a = sg ↔
      ((sg = 0 → a = 0) ∧ (if sg = 0 then (-1 : ℝ) else -(sg : ℝ) * a) < 0) := by
  rcases lt_trichotomy a 0 with h | h | h
  · rw [sign_neg h]; rcases sg with _ | _ | _ <;> simp [h, h.ne] <;> linarith
  · subst h; rcases sg with _ | _ | _ <;> simp
  · rw [sign_pos h]; rcases sg with _ | _ | _ <;> simp [h, h.ne'] <;> linarith

variable [DecidableEq E]

@[simp] lemma cellG_inl (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) (w : E → (E →ᵃ[ℝ] ℝ))
    (y : (c.1 : Finset E)) (x : E) : cellG H c w (.inl y) x = -(w y x) := rfl

lemma cellG_inr (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) (w : E → (E →ᵃ[ℝ] ℝ)) (i : ι) (x : E) :
    cellG H c w (.inr i) x = if c.2 i = 0 then (-1 : ℝ) else -((c.2 i : ℝ)) * H i x := by
  by_cases h : c.2 i = 0 <;> simp [cellG, h]

/-- **The closed part of a cell** in terms of the facet functions. -/
theorem sliceHull_eq (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι)
    (w : E → (E →ᵃ[ℝ] ℝ))
    (hw : ∀ u : E → ℝ, ∑ y ∈ c.1, u y = 1 → ∀ y ∈ c.1, w y (∑ z ∈ c.1, u z • z) = u y) :
    sliceHull H c = {x | x ∈ cellA H c ∧ ∀ k, cellG H c w k x ≤ 0} := by
  ext x
  simp only [sliceHull, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_cellA]
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨u, hu0, hu1, hux⟩ := Finset.mem_convexHull'.1 hx
    have hs' : ∀ i, _ := fun i => (sign_weak_iff _ _).1 (hs i)
    refine ⟨⟨convexHull_subset_affineSpan _ hx, fun i hi => (hs' i).1 hi⟩, ?_⟩
    rintro (y | i)
    · have := hw u hu1 y y.2
      rw [hux] at this
      simp only [cellG_inl, this]
      linarith [hu0 y y.2]
    · rw [cellG_inr]; exact (hs' i).2
  · rintro ⟨⟨hA, hz⟩, hk⟩
    obtain ⟨u, hu1, hux⟩ := exists_weights_of_mem_affineSpan hA
    refine ⟨Finset.mem_convexHull'.2 ⟨u, fun y hy => ?_, hu1, hux⟩, fun i =>
      (sign_weak_iff _ _).2 ⟨hz i, ?_⟩⟩
    · have := hw u hu1 y hy
      rw [hux] at this
      have := hk (.inl ⟨y, hy⟩)
      simp only [cellG_inl] at this
      linarith
    · have := hk (.inr i)
      rwa [cellG_inr] at this

/-- **The cell** in terms of the facet functions: the points of the subspace where every facet
function is negative. -/
theorem cellSet_eq (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι)
    (w : E → (E →ᵃ[ℝ] ℝ))
    (hw : ∀ u : E → ℝ, ∑ y ∈ c.1, u y = 1 → ∀ y ∈ c.1, w y (∑ z ∈ c.1, u z • z) = u y) :
    cellSet (fun i => ⇑(H i)) c = {x | x ∈ cellA H c ∧ ∀ k, cellG H c w k x < 0} := by
  ext x
  simp only [cellSet, openHull, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_cellA]
  constructor
  · rintro ⟨⟨u, hu0, hu1, hux⟩, hs⟩
    have hs' : ∀ i, _ := fun i => (sign_strict_iff _ _).1 (hs i)
    have hA : x ∈ affineSpan ℝ ((c.1 : Finset E) : Set E) :=
      convexHull_subset_affineSpan _ (openHull_subset_convexHull c.1 ⟨u, hu0, hu1, hux⟩)
    refine ⟨⟨hA, fun i hi => (hs' i).1 hi⟩, ?_⟩
    rintro (y | i)
    · have := hw u hu1 y y.2
      rw [hux] at this
      simp only [cellG_inl, this]
      linarith [hu0 y y.2]
    · rw [cellG_inr]; exact (hs' i).2
  · rintro ⟨⟨hA, hz⟩, hk⟩
    obtain ⟨u, hu1, hux⟩ := exists_weights_of_mem_affineSpan hA
    refine ⟨⟨u, fun y hy => ?_, hu1, hux⟩, fun i => (sign_strict_iff _ _).2 ⟨hz i, ?_⟩⟩
    · have := hw u hu1 y hy
      rw [hux] at this
      have := hk (.inl ⟨y, hy⟩)
      simp only [cellG_inl] at this
      linarith
    · have := hk (.inr i)
      rwa [cellG_inr] at this

/-- A face of a cell, other than the cell, lies in a facet hyperplane: some facet function vanishes
on its whole closed part. -/
theorem exists_facet (H : ι → E →ᵃ[ℝ] ℝ) {C D : CellIdx E ι} (hDC : D < C)
    (w : E → (E →ᵃ[ℝ] ℝ))
    (hw : ∀ u : E → ℝ, ∑ y ∈ C.1, u y = 1 → ∀ y ∈ C.1, w y (∑ z ∈ C.1, u z • z) = u y) :
    ∃ k, ∀ x ∈ sliceHull H D, cellG H C w k x = 0 := by
  by_cases h1 : D.1 = C.1
  · have hne : ∃ i, D.2 i ≠ C.2 i := by
      by_contra hcon
      exact hDC.ne (Prod.ext h1 (funext fun i => not_not.1 (not_exists.1 hcon i)))
    obtain ⟨i, hi⟩ := hne
    have hD0 : D.2 i = 0 := (hDC.le.2 i).resolve_right hi
    have hC0 : C.2 i ≠ 0 := fun h => hi (hD0.trans h.symm)
    refine ⟨.inr i, fun x hx => ?_⟩
    have := hx.2 i
    have hx0 : H i x = 0 := by
      rcases this with h | h
      · exact sign_eq_zero_iff.1 h
      · exact sign_eq_zero_iff.1 (h.trans hD0)
    simp [cellG_inr, hC0, hx0]
  · have hsub : D.1 ⊂ C.1 := Finset.ssubset_iff_subset_ne.2 ⟨hDC.le.1, h1⟩
    obtain ⟨y, hyC, hyD⟩ := Finset.exists_of_ssubset hsub
    refine ⟨.inl ⟨y, hyC⟩, fun x hx => ?_⟩
    obtain ⟨u, hu0, hu1, hux⟩ := Finset.mem_convexHull'.1 hx.1
    obtain ⟨he1, hex⟩ := sum_extend_zero hsub.subset u
    have := hw _ (he1.trans hu1) y hyC
    rw [hex, hux] at this
    simp [this, hyD]

/-- An affinely independent finite set in the part of a hyperplane inside an affine subspace `A`
has at most `dim A` points, provided the hyperplane does not contain `A`. -/
theorem card_le_finrank_of_hyperplane (A : AffineSubspace ℝ E) [FiniteDimensional ℝ A.direction]
    (g : E →ᵃ[ℝ] ℝ) {q : E} (hqA : q ∈ A) (hq : g q ≠ 0) (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hsA : ∀ z ∈ s, z ∈ A) (hsg : ∀ z ∈ s, g z = 0) :
    s.card ≤ finrank ℝ A.direction := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨z0, hz0⟩
  · simp
  haveI : Nonempty s := ⟨⟨z0, hz0⟩⟩
  set W : Submodule ℝ E := A.direction ⊓ LinearMap.ker g.linear with hW
  have hvs : vectorSpan ℝ (s : Set E) ≤ W := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨p, hp, r, hr, rfl⟩
    simp only [SetLike.mem_coe, hW, Submodule.mem_inf, LinearMap.mem_ker]
    refine ⟨AffineSubspace.vsub_mem_direction (hsA p hp) (hsA r hr), ?_⟩
    rw [AffineMap.linear_apply_vsub, hsg p hp, hsg r hr]
    simp
  have hWlt : W < A.direction := by
    refine lt_of_le_of_ne inf_le_left fun h => hq ?_
    have hmem : q -ᵥ z0 ∈ A.direction := AffineSubspace.vsub_mem_direction hqA (hsA z0 hz0)
    have : q -ᵥ z0 ∈ W := h ▸ hmem
    have h2 : g.linear (q -ᵥ z0) = 0 := (Submodule.mem_inf.1 this).2
    rw [AffineMap.linear_apply_vsub, hsg z0 hz0] at h2
    simpa using h2
  have h1 : finrank ℝ (vectorSpan ℝ (s : Set E)) + 1 = s.card := by
    have h := hs.finrank_vectorSpan_add_one
    rw [Fintype.card_coe] at h
    have hv : vectorSpan ℝ (Set.range ((↑) : s → E)) = vectorSpan ℝ (s : Set E) := by
      rw [Subtype.range_coe]
    have : finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) =
        finrank ℝ (vectorSpan ℝ (s : Set E)) := by rw [hv]
    omega
  have h2 := Submodule.finrank_mono hvs
  have h3 := Submodule.finrank_lt_finrank_of_lt hWlt
  omega

end SComplex
end Lightlike.PL
