import Mathlib
import Lightlike.PL.Schoenflies.HomeoForm

/-!
# Polygonal Schoenflies: the closed disc form

Row G3-188, milestone PL5 (third pass).  The closed region of a simple polygon with `n ≥ 3` vertices is
homeomorphic to the closed Euclidean unit disc, by a homeomorphism that sends the carrier of the polygon
onto the unit circle (and only the carrier).  This is the form in which the topological Schoenflies
theorem will be approximated: `polygonal_schoenflies_disc`.

* `disc`, `circ`: the closed unit disc and the unit circle in `ℝ × ℝ` (Euclidean, not the sup norm);
* `convex_disc`, `isBounded_disc`, `interior_disc`, `frontier_disc`: the facts needed to apply Mathlib's
  `exists_homeomorph_image_eq`;
* `interior_hull_nonempty`: a strictly convex polygon with `≥ 3` vertices has a hull with interior.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL Filter Topology

/-- The closed Euclidean unit disc in `ℝ × ℝ`. -/
def disc : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 ≤ 1}

/-- The Euclidean unit circle in `ℝ × ℝ`. -/
def circ : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 = 1}

lemma convex_disc : Convex ℝ disc := by
  intro x hx y hy a b ha hb hab
  simp only [disc, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at *
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg (x.1 - y.1)) (sq_nonneg (x.2 - y.2))),
    mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]

lemma isBounded_disc : Bornology.IsBounded disc := by
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).subset ?_
  intro z hz
  simp only [disc, Set.mem_ofPred_eq] at hz
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  constructor <;> rw [Real.norm_eq_abs] <;> apply abs_le.2 <;> constructor <;>
    nlinarith [sq_nonneg z.1, sq_nonneg z.2]

lemma isClosed_disc : IsClosed disc :=
  isClosed_le (by fun_prop) continuous_const

lemma interior_disc : interior disc = {z | z.1 ^ 2 + z.2 ^ 2 < 1} := by
  refine Subset.antisymm ?_ (interior_maximal (fun z hz => (le_of_lt hz : z.1 ^ 2 + z.2 ^ 2 ≤ 1))
    (isOpen_lt (by fun_prop) continuous_const))
  intro z hz
  by_contra hlt
  have hz' : z ∈ disc := interior_subset hz
  have heq : z.1 ^ 2 + z.2 ^ 2 = 1 := le_antisymm hz' (not_lt.1 hlt)
  have hcont : Continuous fun t : ℝ => t • z := continuous_id.smul continuous_const
  have hev : ∀ᶠ t in 𝓝 (1 : ℝ), t • z ∈ interior disc :=
    hcont.continuousAt.eventually (isOpen_interior.mem_nhds (by simpa using hz))
  obtain ⟨t, ht, hmem⟩ := hev.exists_gt
  have := interior_subset hmem
  simp only [disc, Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at this
  have e : (t * z.1) ^ 2 + (t * z.2) ^ 2 = t ^ 2 * (z.1 ^ 2 + z.2 ^ 2) := by ring
  rw [e, heq] at this
  nlinarith

lemma frontier_disc : frontier disc = circ := by
  rw [frontier, isClosed_disc.closure_eq, interior_disc]
  ext z
  simp only [disc, circ, Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h1 h2
  · intro h; exact ⟨h.le, h.ge⟩

lemma interior_hull_nonempty {n : ℕ} (h3 : 3 ≤ n) {c : Polygon n} (hc : StrictConvexPos c) :
    (interior (convexHull ℝ (range c))).Nonempty := by
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have hdet := hc i0 i1 i2 (Fin.mk_lt_mk.2 (by omega)) (Fin.mk_lt_mk.2 (by omega))
  have hind : AffineIndependent ℝ ![c i0, c i1, c i2] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro hcol
    rw [collinear_iff_of_mem (p₀ := c i0) (by simp)] at hcol
    obtain ⟨v, hv⟩ := hcol
    obtain ⟨r1, h1⟩ := hv (c i1) (by simp)
    obtain ⟨r2, h2⟩ := hv (c i2) (by simp)
    have e1 : c i1 - c i0 = r1 • v := by rw [h1]; simp
    have e2 : c i2 - c i0 = r2 • v := by rw [h2]; simp
    have : det3 (c i0) (c i1) (c i2) = 0 := by
      simp only [det3, cross, e1, e2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    linarith
  have htop := (hind.affineSpan_eq_top_iff_card_eq_finrank_add_one).2 (by simp)
  refine eq_top_iff.2 ?_
  rw [← htop]
  refine affineSpan_mono ℝ ?_
  rintro _ ⟨j, rfl⟩
  fin_cases j <;> simp

/-- **Polygonal Schoenflies theorem, disc form.**  The closed region of a simple polygon with `n ≥ 3`
vertices is homeomorphic to the closed unit disc, and a point of the region lies on the carrier of the
polygon exactly when its image lies on the unit circle. -/
theorem polygonal_schoenflies_disc {n : ℕ} [NeZero n] {p : Polygon n} (h3 : 3 ≤ n)
    (hs : p.IsSimple) :
    ∃ e : region p ≃ₜ disc, ∀ x : region p, (x : ℝ × ℝ) ∈ p.carrier ↔ ((e x : disc) : ℝ × ℝ) ∈ circ := by
  obtain ⟨c, e1, f, hc, hpw, hef, -, hcar⟩ := polygonal_schoenflies_homeo h3 hs
  have hKb : Bornology.IsBounded (convexHull ℝ (range c)) :=
    ((Set.finite_range c).isCompact_convexHull ℝ).isBounded
  have hD0 : (interior disc).Nonempty := ⟨0, by rw [interior_disc]; simp⟩
  obtain ⟨h, -, hcl, hfr⟩ := exists_homeomorph_image_eq (convex_convexHull ℝ (range c))
    (interior_hull_nonempty h3 hc) (NormedSpace.isVonNBounded_of_isBounded _ hKb)
    convex_disc hD0 (NormedSpace.isVonNBounded_of_isBounded _ isBounded_disc)
  rw [(isClosed_hull c).closure_eq, isClosed_disc.closure_eq] at hcl
  rw [frontier_disc] at hfr
  have hK : h '' convexHull ℝ (range c) = disc := hcl
  let e2 : convexHull ℝ (range c) ≃ₜ disc :=
    (h.image (convexHull ℝ (range c))).trans (Homeomorph.setCongr hK)
  have he2 : ∀ y : convexHull ℝ (range c), ((e2 y : disc) : ℝ × ℝ) = h y := fun y => rfl
  refine ⟨e1.trans e2, fun x => ?_⟩
  have hcr : p.carrier ⊆ region p := subset_union_right
  have hx : ((e1.trans e2) x : ℝ × ℝ) = h (f x) := by
    show ((e2 (e1 x) : disc) : ℝ × ℝ) = h (f x)
    rw [he2, hef]
  rw [hx]
  have hcircle : h (f x) ∈ circ ↔ f x ∈ frontier (convexHull ℝ (range c)) := by
    rw [← hfr]
    exact h.injective.mem_set_image
  rw [hcircle]
  constructor
  · intro hxc
    rw [← hcar]
    exact ⟨x, hxc, rfl⟩
  · intro hfx
    rw [← hcar] at hfx
    obtain ⟨y, hy, hyx⟩ := hfx
    have : (⟨y, hcr hy⟩ : region p) = x := by
      apply e1.injective
      apply Subtype.ext
      rw [hef, hef]
      exact hyx
    rw [← this]
    exact hy

end Lightlike.PL.Schoenflies
