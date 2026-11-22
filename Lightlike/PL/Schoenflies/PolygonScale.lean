import Lightlike.PL.Polygon

/-!
# Rescaling a polygon by a positive factor

Row G3-188, milestone PL5 (third pass), item 5b, route A.  The lattice polygons live in units of `δ / 4`;
to compare them with a compact set in the plane they are rescaled by `h = δ / 4`.

* `xAt_smul`, `crossesRay_smul`: the half-open crossing rule is invariant under `x ↦ h • x`, `h > 0`.
* `parity_smul`: the crossing parity of `h • p` at `h • x` equals that of `p` at `x`.
* `carrier_smul`: the carrier of `h • p` is the image of `carrier p` under `z ↦ h • z`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

lemma xAt_smul {h : ℝ} (hh : h ≠ 0) (u v : ℝ × ℝ) (y : ℝ) :
    xAt (h • u) (h • v) (h * y) = h * xAt u v y := by
  unfold xAt
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  by_cases hd : v.2 - u.2 = 0
  · have : h * v.2 - h * u.2 = 0 := by rw [← mul_sub, hd, mul_zero]
    rw [hd, this]; simp
  · have h2 : h * v.2 - h * u.2 ≠ 0 := by rw [← mul_sub]; exact mul_ne_zero hh hd
    field_simp

lemma crossesRay_smul {h : ℝ} (hh : 0 < h) (u v x : ℝ × ℝ) :
    CrossesRay (h • u) (h • v) (h • x) ↔ CrossesRay u v x := by
  unfold CrossesRay
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [xAt_smul hh.ne']
  simp only [mul_le_mul_iff_right₀ hh, mul_lt_mul_iff_right₀ hh]

lemma parity_smul {n : ℕ} (p : Polygon n) {h : ℝ} (hh : 0 < h) (x : ℝ × ℝ) :
    Polygon.parity (n := n) (fun i => h • p i) (h • x) = p.parity x := by
  unfold Polygon.parity
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Lightlike.PL.Polygon.ind_congr (crossesRay_smul hh _ _ _)]

lemma carrier_smul {n : ℕ} (p : Polygon n) (h : ℝ) :
    Polygon.carrier (n := n) (fun i => h • p i) = (fun z => h • z) '' p.carrier := by
  set f : ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ := (LinearMap.lsmul ℝ (ℝ × ℝ) h).toAffineMap with hf
  have fapp : ∀ a, f a = h • a := fun a => rfl
  have edge_eq : ∀ i, Polygon.edge (n := n) (fun i => h • p i) i = f '' p.edge i := by
    intro i
    simp only [Polygon.edge]
    rw [image_segment, fapp, fapp]
  unfold Polygon.carrier
  simp only [edge_eq]
  rw [Set.image_iUnion]
  rfl

end Lightlike.PL.Schoenflies
