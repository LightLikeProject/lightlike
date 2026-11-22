import Mathlib
import Lightlike.PL.Schoenflies.TriMap

/-!
# Adding one vertex to a convex set

Piece 6 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  If `X` is a convex set
containing `a` and `b`, lying in the closed wedge cut out by the three lines `ab`, `bv`, `va` on the
side opposite to `v`, then `convexHull (insert v X) = X ∪ triangle a b v`.  This is the step that
builds a strictly convex polygon vertex by vertex from fan triangles.
-/

namespace Lightlike.PL.Schoenflies

/-- Componentwise identity behind `hull_insert_cut`. -/
lemma comp_eq (α D G P Q s ui vi ai bi : ℝ) (hG : G ≠ 0) (hs : s ≠ 0) (hs' : s = D - G)
    (h : D * ui = Q * ai + P * bi + G * vi) :
    α * vi + (1 - α) * ui =
      (α * s / (-G)) * ((P / s) * bi + (Q / s) * ai) + (1 - α * s / (-G)) * ui := by
  have hPb : P * bi + Q * ai = D * ui - G * vi := by linarith
  have : (P / s) * bi + (Q / s) * ai = (D * ui - G * vi) / s := by
    rw [← hPb]; field_simp
  rw [this]
  field_simp
  rw [hs']
  ring

/-- **Adding a vertex to a convex set.**  Let `X` be convex with `a, b ∈ X`, and let `v` lie on the
positive side of `ab` (`0 < det3 a b v`).  If every point `u` of `X` lies on the other side of `ab`
(`det3 a b u ≤ 0`) and on the inner sides of `bv` and `va`, then
`convexHull (insert v X) = X ∪ convexHull {a, b, v}`. -/
theorem hull_insert_cut {X : Set (ℝ × ℝ)} (hX : Convex ℝ X) {a b v : ℝ × ℝ}
    (ha : a ∈ X) (hb : b ∈ X) (hD : 0 < det3 a b v)
    (h1 : ∀ u ∈ X, det3 a b u ≤ 0) (h2 : ∀ u ∈ X, 0 ≤ det3 b v u)
    (h3 : ∀ u ∈ X, 0 ≤ det3 v a u) :
    convexHull ℝ (insert v X) = X ∪ convexHull ℝ {a, b, v} := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [convexHull_insert ⟨a, ha⟩, hX.convexHull_eq, convexJoin_singleton_left] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨u, hu, α, β, hα, hβ, hαβ, rfl⟩ := hx
    have hβ' : β = 1 - α := by linarith
    have hG := h1 u hu
    have hQ := h2 u hu
    have hP := h3 u hu
    have e1 : cross (α • v + β • u - a) (v - a) = β * det3 v a u := by
      subst hβ'; simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    have e2 : det3 a b (α • v + β • u) = α * det3 a b v + β * det3 a b u := by
      subst hβ'; simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    have e3 : det3 b v (α • v + β • u) = β * det3 b v u := by
      subst hβ'; simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
    have I1 : ∀ y : ℝ × ℝ, det3 b v y + det3 v a y + det3 a b y = det3 a b v := by
      intro y
      simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring
    rcases le_total 0 (det3 a b (α • v + β • u)) with hx | hx
    · right
      have hne : det3 a b v ≠ 0 := hD.ne'
      rw [mem_hull_iff hne]
      have hcr : cross (α • v + β • u - a) (v - a) = det3 v a (α • v + β • u) := by
        simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring
      have hI := I1 (α • v + β • u)
      have hB : tmB a b v (α • v + β • u) = det3 v a (α • v + β • u) / det3 a b v := by
        unfold tmB; rw [hcr]
      have hC : tmC a b v (α • v + β • u) = det3 a b (α • v + β • u) / det3 a b v := rfl
      have hvau : det3 v a (α • v + β • u) = β * det3 v a u := by rw [← hcr, e1]
      rw [hB, hC]
      refine ⟨div_nonneg (by rw [hvau]; positivity) hD.le, div_nonneg hx hD.le, ?_⟩
      rw [← add_div, div_le_one hD]
      rw [e3] at hI
      have : 0 ≤ β * det3 b v u := by positivity
      linarith
    · left
      rcases hα.eq_or_lt with h0 | hpos
      · have : β = 1 := by linarith
        subst this; rw [← h0]; simpa using hu
      · have hGneg : det3 a b u < 0 := by
          rw [e2] at hx
          by_contra hc
          have hc' : 0 ≤ det3 a b u := not_lt.1 hc
          have : 0 < α * det3 a b v := mul_pos hpos hD
          have : 0 ≤ β * det3 a b u := by positivity
          linarith
        set D := det3 a b v with hDdef
        set G := det3 a b u with hGdef
        set P := det3 v a u with hPdef
        set Q := det3 b v u with hQdef
        have hs : 0 < D - G := by linarith
        have hI := I1 u
        -- the point where the segment `v u` meets the line `ab`
        have hzmem : (P / (D - G)) • b + (Q / (D - G)) • a ∈ X :=
          hX hb ha (div_nonneg hP hs.le) (div_nonneg hQ hs.le)
            (by rw [← add_div, div_eq_one_iff_eq hs.ne']; linarith)
        have hl0 : 0 ≤ α * (D - G) / (-G) :=
          div_nonneg (mul_nonneg hα hs.le) (neg_nonneg.2 hGneg.le)
        have hbG : β * G = G - α * G := by rw [hβ']; ring
        have hl1 : α * (D - G) / (-G) ≤ 1 := by
          rw [div_le_one (neg_pos.2 hGneg)]
          have : α * (D - G) = α * D - α * G := by ring
          rw [e2] at hx
          linarith
        have I2a : D * u.1 = Q * a.1 + P * b.1 + G * v.1 := by
          rw [hDdef, hGdef, hPdef, hQdef]
          simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring
        have I2b : D * u.2 = Q * a.2 + P * b.2 + G * v.2 := by
          rw [hDdef, hGdef, hPdef, hQdef]
          simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring
        have hmem := hX hzmem hu hl0 (by linarith : 0 ≤ 1 - α * (D - G) / (-G))
          (add_sub_cancel _ _)
        convert hmem using 1
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          rw [hβ']
          exact comp_eq α D G P Q (D - G) u.1 v.1 a.1 b.1 hGneg.ne hs.ne' rfl I2a
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          rw [hβ']
          exact comp_eq α D G P Q (D - G) u.2 v.2 a.2 b.2 hGneg.ne hs.ne' rfl I2b
  · intro x hx
    rcases hx with hx | hx
    · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hx)
    · refine convexHull_mono ?_ hx
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact Set.mem_insert_of_mem _ ha
      · exact Set.mem_insert_of_mem _ hb
      · exact Set.mem_insert _ _

end Lightlike.PL.Schoenflies
