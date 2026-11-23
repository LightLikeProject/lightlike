import Mathlib
import Lightlike.PL.Schoenflies.TriMap
import Lightlike.PL.Schoenflies.ConvexCut

/-!
# Clipping an ear off a convex hull

Piece 8 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  Index-free geometry of the
convex side of the ear induction: if `p0 p1 p2` is a positively oriented triangle and every point of
a set `S ∋ p0, p2` lies on the inner side of the three lines `p0p2`, `p0p1`, `p1p2`, then adding `p1`
to `S` adds exactly the triangle `p0 p1 p2` to the hull, and the new triangle meets the old hull in the
segment `[p0, p2]`.
-/

namespace Lightlike.PL.Schoenflies

/-- `det3` changes sign when its first two arguments are swapped. -/
lemma det3_swap (a b c : ℝ × ℝ) : det3 b a c = - det3 a b c := by
  simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- `det3` is invariant under cyclic rotation of its arguments. -/
lemma det3_cyc (a b c : ℝ × ℝ) : det3 b c a = det3 a b c := by
  simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- A closed half-plane `0 ≤ det3 a b u` is convex. -/
lemma convex_det3_nonneg (a b : ℝ × ℝ) : Convex ℝ {u : ℝ × ℝ | 0 ≤ det3 a b u} := by
  intro u hu w hw s t hs ht hst
  have ht' : t = 1 - s := by linarith
  have e : det3 a b (s • u + t • w) = s * det3 a b u + t * det3 a b w := by
    subst ht'
    simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  show 0 ≤ det3 a b (s • u + t • w)
  rw [e]
  have h1 : 0 ≤ det3 a b u := hu
  have h2 : 0 ≤ det3 a b w := hw
  positivity

/-- A half-plane inequality true on `S` holds on `convexHull S`. -/
lemma det3_nonneg_hull {S : Set (ℝ × ℝ)} {a b : ℝ × ℝ} (hS : ∀ u ∈ S, 0 ≤ det3 a b u) :
    ∀ u ∈ convexHull ℝ S, 0 ≤ det3 a b u :=
  fun _ hu => convexHull_min (fun u hu => hS u hu) (convex_det3_nonneg a b) hu

/-- **Clipping an ear (convex side).**  Let `p0 p1 p2` be positively oriented and `S` a set with
`p0, p2 ∈ S`, all of whose points `u` satisfy `0 ≤ det3 p0 p2 u`, `0 ≤ det3 p0 p1 u`,
`0 ≤ det3 p1 p2 u`.  Then `convexHull (insert p1 S) = convexHull S ∪ triangle p0 p1 p2`, and the
triangle meets `convexHull S` exactly in the segment `[p0, p2]`. -/
theorem hull_ear_geom {S : Set (ℝ × ℝ)} {p0 p1 p2 : ℝ × ℝ} (h0 : p0 ∈ S) (h2 : p2 ∈ S)
    (hD : 0 < det3 p0 p1 p2) (c1 : ∀ u ∈ S, 0 ≤ det3 p0 p2 u)
    (c2 : ∀ u ∈ S, 0 ≤ det3 p0 p1 u) (c3 : ∀ u ∈ S, 0 ≤ det3 p1 p2 u) :
    convexHull ℝ (insert p1 S) = convexHull ℝ S ∪ convexHull ℝ {p0, p1, p2} ∧
      convexHull ℝ S ∩ convexHull ℝ {p0, p1, p2} = segment ℝ p0 p2 := by
  have hX := convex_convexHull ℝ S
  have hSX : S ⊆ convexHull ℝ S := subset_convexHull ℝ S
  have k1 := det3_nonneg_hull c1
  have k2 := det3_nonneg_hull c2
  have k3 := det3_nonneg_hull c3
  have hD' : 0 < det3 p2 p0 p1 := by rw [det3_cyc, det3_cyc]; exact hD
  have hcut := hull_insert_cut hX (a := p2) (b := p0) (v := p1) (hSX h2) (hSX h0) hD'
    (fun u hu => by rw [det3_swap]; linarith [k1 u hu]) (fun u hu => k2 u hu) (fun u hu => k3 u hu)
  have hset : ({p2, p0, p1} : Set (ℝ × ℝ)) = {p0, p1, p2} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [hset] at hcut
  constructor
  · rw [← hcut]
    apply Set.Subset.antisymm
    · exact convexHull_mono (Set.insert_subset_insert hSX)
    · apply convexHull_min _ (convex_convexHull ℝ _)
      intro x hx
      rcases hx with rfl | hx
      · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      · exact convexHull_mono (Set.subset_insert _ _) hx
  · have hne : det3 p0 p1 p2 ≠ 0 := hD.ne'
    apply Set.Subset.antisymm
    · rintro x ⟨hxS, hxT⟩
      rw [mem_hull_iff hne] at hxT
      obtain ⟨hB, hC, hBC⟩ := hxT
      have hk := k1 x hxS
      have hBe : tmB p0 p1 p2 x * det3 p0 p1 p2 = - det3 p0 p2 x := by
        rw [tmB_mul hne]
        simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring
      have hB0 : tmB p0 p1 p2 x = 0 := by
        have : 0 ≤ tmB p0 p1 p2 x * det3 p0 p1 p2 := mul_nonneg hB hD.le
        have h' : tmB p0 p1 p2 x * det3 p0 p1 p2 = 0 := by linarith
        rcases mul_eq_zero.1 h' with h | h
        · exact h
        · exact absurd h hne
      have hrec := recon hne x
      rw [hB0, zero_smul, add_zero] at hrec
      rw [segment_eq_image']
      exact ⟨tmC p0 p1 p2 x, ⟨hC, by linarith⟩, hrec⟩
    · intro x hx
      refine ⟨(convex_convexHull ℝ S).segment_subset (hSX h0) (hSX h2) hx, ?_⟩
      have hT : segment ℝ p0 p2 ⊆ convexHull ℝ {p0, p1, p2} :=
        (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ (by simp))
          (subset_convexHull ℝ _ (by simp))
      exact hT hx

/-- Non-vacuity: the hypotheses hold for `S = {(1,0),(0,0)}` and `p1 = (0,1)`, so the unit right
triangle is clipped off the segment. -/
example : convexHull ℝ (insert ((0, 1) : ℝ × ℝ) {(1, 0), (0, 0)}) =
    convexHull ℝ {((1, 0) : ℝ × ℝ), (0, 0)} ∪ convexHull ℝ {(1, 0), (0, 1), (0, 0)} :=
  (hull_ear_geom (S := {((1, 0) : ℝ × ℝ), (0, 0)}) (p0 := (1, 0)) (p1 := (0, 1)) (p2 := (0, 0))
    (by simp) (by simp) (by norm_num [det3, cross])
    (by intro u hu; rcases hu with rfl | rfl <;> norm_num [det3, cross])
    (by intro u hu; rcases hu with rfl | rfl <;> norm_num [det3, cross])
    (by intro u hu; rcases hu with rfl | rfl <;> norm_num [det3, cross])).1

/-- Wrong input gives a different answer: if `p1` is on the wrong side (`det3 p0 p1 p2 < 0`), the
orientation hypothesis of `hull_ear_geom` fails. -/
example : ¬ (0 < det3 ((0, 0) : ℝ × ℝ) (0, 1) (1, 0)) := by norm_num [det3, cross]

end Lightlike.PL.Schoenflies
