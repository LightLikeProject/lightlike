import Lightlike.PL.Projective

/-!
# The gauge of a polytope as a radial scale

For a convex polytope `P = {p | ∀ k, a k p ≤ 0}` with a point `v` where every `a k` is negative,
the scale `m x = max_k (1 - a k x / a k v)` is the gauge of `P` seen from `v`: the radial map
`x ↦ v + (x - v) / m x` sends a point with positive scale into `P`, onto a face of `P`.
The scale is a maximum of finitely many affine functions, so it is affine on every closed
simplex on which one of them dominates the others, and then it is radial on a complex whose
simplices have that property.

## Main results

* `gaugeMax`: the maximum of finitely many affine functions.
* `gaugeMax_eq_of_dominates`: it agrees with a dominating function.
* `isRadialOn_gaugeMax`: it is a radial scale on a complex whose simplices each have a dominating
  function and avoid the centre.
* `affine_projMap`, `projMap_mem_polytope`, `exists_projMap_face`: the radial image of a point
  with positive scale lies in the polytope, on one of its facets.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {κ : Type*} [Fintype κ] [Nonempty κ]

/-- The **maximum** of a finite family of affine functions. -/
noncomputable def gaugeMax (g : κ → E →ᵃ[ℝ] ℝ) (x : E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k => g k x

lemma le_gaugeMax (g : κ → E →ᵃ[ℝ] ℝ) (k : κ) (x : E) : g k x ≤ gaugeMax g x :=
  Finset.le_sup' (fun k => g k x) (Finset.mem_univ k)

lemma exists_gaugeMax_eq (g : κ → E →ᵃ[ℝ] ℝ) (x : E) : ∃ k, gaugeMax g x = g k x := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := κ)) fun k => g k x
  exact ⟨k, hk⟩

/-- On a set where `g k` dominates every `g j`, the maximum equals `g k`. -/
lemma gaugeMax_eq_of_dominates (g : κ → E →ᵃ[ℝ] ℝ) {S : Set E} {k : κ}
    (h : ∀ y ∈ S, ∀ j, g j y ≤ g k y) {y : E} (hy : y ∈ S) : gaugeMax g y = g k y :=
  le_antisymm (Finset.sup'_le _ _ fun j _ => h y hy j) (le_gaugeMax g k y)

/-- **The maximum of affine functions is a radial scale** on a complex each of whose simplices has
a dominating function, positive vertices and an affine span missing the centre. -/
theorem isRadialOn_gaugeMax {K : SComplex E} {v : E} (g : κ → E →ᵃ[ℝ] ℝ)
    (hdom : ∀ s ∈ K, ∃ k, ∀ y ∈ convexHull ℝ (s : Set E), ∀ j, g j y ≤ g k y)
    (hpos : ∀ s ∈ K, ∀ y ∈ s, 0 < gaugeMax g y)
    (hv : ∀ s ∈ K, v ∉ affineSpan ℝ (s : Set E)) : IsRadialOn K v (gaugeMax g) := by
  intro s hs
  obtain ⟨k, hk⟩ := hdom s hs
  exact ⟨hpos s hs, ⟨g k, fun y hy => gaugeMax_eq_of_dominates g hk hy⟩, hv s hs⟩

/-- An affine function of a radial image. -/
lemma affine_projMap (a : E →ᵃ[ℝ] ℝ) (v x : E) (c : ℝ) :
    a (v + c⁻¹ • (x - v)) = a v + c⁻¹ * (a x - a v) := by
  have h : v + c⁻¹ • (x - v) = AffineMap.lineMap v x c⁻¹ := by
    rw [AffineMap.lineMap_apply_module']
    simp [add_comm]
  rw [h, AffineMap.apply_lineMap, AffineMap.lineMap_apply_module']
  simp [add_comm, smul_eq_mul]

/-- The polytope's scale: `max_k (1 - a k x / a k v)`. -/
noncomputable def polyScale (a : κ → E →ᵃ[ℝ] ℝ) (v : E) : E → ℝ :=
  gaugeMax fun k => AffineMap.const ℝ E 1 - (a k v)⁻¹ • a k

lemma polyScale_apply_le (a : κ → E →ᵃ[ℝ] ℝ) (v : E) (k : κ) (x : E) :
    1 - a k x / a k v ≤ polyScale a v x := by
  have := le_gaugeMax (fun k => AffineMap.const ℝ E 1 - (a k v)⁻¹ • a k) k x
  simpa [polyScale, div_eq_inv_mul] using this

lemma exists_polyScale_eq (a : κ → E →ᵃ[ℝ] ℝ) (v x : E) :
    ∃ k, polyScale a v x = 1 - a k x / a k v := by
  obtain ⟨k, hk⟩ := exists_gaugeMax_eq (fun k => AffineMap.const ℝ E 1 - (a k v)⁻¹ • a k) x
  exact ⟨k, by simpa [polyScale, div_eq_inv_mul] using hk⟩

/-- **The radial image of a point with positive scale lies in the polytope.** -/
theorem projMap_mem_polytope (a : κ → E →ᵃ[ℝ] ℝ) {v : E} (hv : ∀ k, a k v < 0) {x : E}
    (hx : 0 < polyScale a v x) (k : κ) : a k (projMap v (polyScale a v) x) ≤ 0 := by
  unfold projMap
  rw [affine_projMap]
  have h1 := polyScale_apply_le a v k x
  have hk := hv k
  set c := polyScale a v x
  have h2 : (a k x - a k v) ≤ -(a k v) * c := by
    have : -(a k x / a k v) ≤ c - 1 := by linarith
    have h3 : a k x / a k v * a k v = a k x := div_mul_cancel₀ _ hk.ne
    nlinarith [mul_le_mul_of_nonpos_right this hk.le]
  have h4 : c⁻¹ * (a k x - a k v) ≤ -(a k v) := by
    calc c⁻¹ * (a k x - a k v) ≤ c⁻¹ * (-(a k v) * c) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hx.le)
      _ = -(a k v) := by field_simp
  linarith

/-- **The radial image of a point with positive scale lies on a facet of the polytope.** -/
theorem exists_projMap_face (a : κ → E →ᵃ[ℝ] ℝ) {v : E} (hv : ∀ k, a k v < 0) {x : E}
    (hx : 0 < polyScale a v x) : ∃ k, a k (projMap v (polyScale a v) x) = 0 := by
  obtain ⟨k, hk⟩ := exists_polyScale_eq a v x
  refine ⟨k, ?_⟩
  unfold projMap
  rw [affine_projMap]
  have hk0 := hv k
  have hne : a k v - a k x ≠ 0 := by
    intro h0
    have h1 : a k x = a k v := by linarith
    have : polyScale a v x = 0 := by rw [hk, h1, div_self hk0.ne]; simp
    exact hx.ne' this
  have e : 1 - a k x / a k v = (a k v - a k x) / a k v := by
    rw [sub_div, div_self hk0.ne]
  rw [hk, e, inv_div]
  have e2 : a k x - a k v = -(a k v - a k x) := by ring
  rw [e2]
  field_simp
  ring

end SComplex
end Lightlike.PL
