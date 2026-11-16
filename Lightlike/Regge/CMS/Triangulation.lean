import Mathlib
import Lightlike.Regge.CMS.Final
import Lightlike.Regge.CMS.TriArea
import Lightlike.Regge.CMS.StarCover

/-!
# The deficit convergence theorem for an explicit triangulation (RC6b)

A triangulation of a planar region is given by positions `P : ι → ℝ²` of the vertices and a finite
family of triangles `t`, with corners `c t : Fin 3 → ι`. The triangle `cell t` is the convex hull
of its corners (`tri`). Triangles overlap only in null sets. The star of a vertex `v` lists the
triangles `(v, nb v j, nb v (j+1))`, `j ∈ ℤ/n`, that contain it (the corners of `c t` may be listed in
any order, so a triangle can belong to the stars of its three corners).

From these data the cells of `cms_convergence` are built, not assumed: the star cell is the union
of the triangles around `v`, its area is `½ ∑ⱼ det2` (`volume_tri`), the cover three times
(`star_cover`) holds outside the triangles with a corner outside `V`, and the area of that layer
is bounded through the number of such triangles.

## Main results

`cms_convergence_triangulation`.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- The triangle of the triangulation `(P, c)` with index `t`. -/
def cell {ι τ : Type} (P : ι → Fin 2 → ℝ) (c : τ → Fin 3 → ι) (t : τ) : Set (Fin 2 → ℝ) :=
  tri (P (c t 0)) (P (c t 1)) (P (c t 2))

theorem tri_subset_closedBall {a b c q : Fin 2 → ℝ} {h : ℝ} (ha : dist a q ≤ h) (hb : dist b q ≤ h)
    (hc : dist c q ≤ h) : tri a b c ⊆ Metric.closedBall q h := by
  rw [tri_eq_convexHull]
  apply convexHull_min _ (convex_closedBall q h)
  intro p hp
  simp only [mem_insert_iff, mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl <;> assumption

theorem volume_real_tri_le {a b c q : Fin 2 → ℝ} {h : ℝ} (hh : 0 ≤ h) (ha : dist a q ≤ h)
    (hb : dist b q ≤ h) (hc : dist c q ≤ h) : volume.real (tri a b c) ≤ 4 * h ^ 2 := by
  have := measureReal_mono (μ := volume) (tri_subset_closedBall ha hb hc)
    (by rw [Real.volume_pi_closedBall _ hh]; exact ENNReal.ofReal_ne_top)
  refine this.trans ?_
  rw [Measure.real, Real.volume_pi_closedBall _ hh, ENNReal.toReal_ofReal (by positivity)]
  simp [Fintype.card_fin]; nlinarith

/-- **Convergence of weighted deficit angles for an explicit triangulation.** The triangulation is
`(P, c)`; `V` is a finite set of vertices with stars `(nb v, tt v)`; the region is the union `Ω` of
the triangles all of whose corners are in `V`. The remaining hypotheses are that the triangles
overlap only in null sets, lie in `K`, have, at the first corner of each triangle, edges of length at most `h` and that the triangles
with a corner outside `V` number at most `m / h`; and, at each vertex of `V`, the star has valence
at most `N`, is `ρ`-fat and winds once (angle sum `2π`).

As in `cms_convergence`, the threshold on `h` keeps every edge in a ball contained in `U`, so
the geodesic distances are genuine lengths and not the value `0` of `dist g U` without an
admissible curve. -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.cms_convergence_triangulation
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ N M m : ℝ} (hm : 0 ≤ m) (hρ : 0 < ρ)
    {f : (Fin 2 → ℝ) → ℝ} {Lf : NNReal} (hf : LipschitzOnWith Lf f K) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ (ι τ : Type) [DecidableEq ι] [Fintype τ] (V : Finset ι) (n : ι → ℕ)
      [∀ v, NeZero (n v)] (P : ι → Fin 2 → ℝ) (c : τ → Fin 3 → ι) (nb : (v : ι) → ZMod (n v) → ι)
      (tt : (v : ι) → ZMod (n v) → τ) (h : ℝ),
      0 < h → h ≤ h₀ → (V.card : ℝ) * h ^ 2 ≤ M →
      (∀ t, Function.Injective (c t)) →
      (∀ t t', t ≠ t' → AEDisjoint volume (cell P c t) (cell P c t')) →
      (∀ t, cell P c t ⊆ K) → (∀ t k, dist (P (c t k)) (P (c t 0)) ≤ h) →
      (∀ v ∈ V, Function.Injective (tt v) ∧ ∀ t, (∃ k, c t k = v) ↔ ∃ j, tt v j = t) →
      (∀ v ∈ V, ∀ j, ∃ σ : Equiv.Perm (Fin 3), c (tt v j) ∘ σ = ![v, nb v j, nb v (j + 1)]) →
      (∀ v ∈ V, P v ∈ K) → (∀ v ∈ V, (n v : ℝ) ≤ N) →
      (∀ v ∈ V, ∀ j, ‖P (nb v j) - P v‖ ≤ h) →
      (∀ v ∈ V, ∀ j, ρ * h ^ 2 ≤ det2 (P (nb v j) - P v) (P (nb v (j + 1)) - P v)) →
      (∀ v ∈ V, ∑ j, InnerProductGeometry.angle (toC (P (nb v j) - P v))
        (toC (P (nb v (j + 1)) - P v)) = 2 * π) →
      ((Finset.univ.filter fun t => cornersIn c V t ≠ 3).card : ℝ) * h ≤ m →
      |∑ v ∈ V, f (P v) * (2 * π - ∑ j, triAngle (dist g U (P v) (P (nb v j)) ^ 2)
            (dist g U (P v) (P (nb v (j + 1))) ^ 2)
            (dist g U (P (nb v j)) (P (nb v (j + 1))) ^ 2)) -
        ∫ x in ⋃ t ∈ Finset.univ.filter (fun t => cornersIn c V t = 3), cell P c t,
          f x * (scalarCurvature g x / 2 * √((g x).det))| ≤ C * h := by
  obtain ⟨C, h₀, hh₀, hmain⟩ := hg.cms_convergence hK hKU (ρ := ρ) (N := N) (M := M) (b := 4 * m)
    (by positivity) hρ hf
  refine ⟨C, h₀, hh₀, ?_⟩
  intro ι τ _ _ V n _ P c nb tt h hh hh0 hcard hinj hdisj hK' hedge hstar hcorn hp hn hw hd h2π hbd
  have hcell : ∀ v ∈ V, ∀ j, cell P c (tt v j) = tri (P v) (P (nb v j)) (P (nb v (j + 1))) := by
    intro v hv j
    obtain ⟨σ, hσ⟩ := hcorn v hv j
    have hr : Set.range (fun k => P (c (tt v j) k)) = {P v, P (nb v j), P (nb v (j + 1))} := by
      have h1 : Set.range (fun k => P ((c (tt v j) ∘ σ) k)) = Set.range (fun k => P (c (tt v j) k)) :=
        Function.Surjective.range_comp σ.surjective (fun k => P (c (tt v j) k))
      rw [← h1, hσ]
      ext x; simp [Fin.exists_fin_succ, eq_comm]
    rw [cell, tri_eq_convexHull, tri_eq_convexHull]
    congr 1
    rw [← hr]
    ext x; simp [Fin.exists_fin_succ, eq_comm]
  have hcov := star_cover (fun t => cell P c t) hdisj hinj tt hstar
  have e := hmain ι V n P (fun v j => P (nb v j) - P v) (fun v => ⋃ j, cell P c (tt v j))
    (⋃ t ∈ Finset.univ.filter (fun t => cornersIn c V t = 3), cell P c t)
    (⋃ t ∈ Finset.univ.filter (fun t => cornersIn c V t ≠ 3), cell P c t) h hh hh0 hcard hp hn hw
    hd h2π ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcov.1 hcov.2
  · simpa only [add_sub_cancel] using e
  · intro v _; exact MeasurableSet.iUnion fun j => measurableSet_tri _ _ _
  · intro v _; exact iUnion_subset fun j => hK' _
  · intro v hv x hx
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    rw [hcell v hv j] at hj
    have := tri_subset_closedBall (q := P v) (h := h) (by simp [hh.le]) (by simpa [dist_eq_norm] using hw v hv j)
      (by simpa [dist_eq_norm] using hw v hv (j + 1)) hj
    exact this
  · intro v hv
    have hvol : ∀ j, volume.real (cell P c (tt v j)) =
        det2 (P (nb v j) - P v) (P (nb v (j + 1)) - P v) / 2 := by
      intro j
      rw [hcell v hv j, Measure.real, volume_tri, ENNReal.toReal_ofReal (by positivity),
        abs_of_pos (lt_of_lt_of_le (by positivity) (hd v hv j))]
    have hU : (⋃ j, cell P c (tt v j)) = ⋃ j ∈ (Finset.univ : Finset (ZMod (n v))), cell P c (tt v j) := by
      simp
    rw [hU, measureReal_biUnion_finset₀
      (fun j _ j' _ hne => hdisj _ _ (fun h => hne ((hstar v hv).1 h)))
      (fun j _ => by rw [hcell v hv j]; exact (measurableSet_tri _ _ _).nullMeasurableSet)
      (fun j _ => by rw [hcell v hv j, volume_tri]; exact ENNReal.ofReal_ne_top)]
    simp_rw [hvol]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  · exact MeasurableSet.biUnion (Finset.countable_toSet _) fun t _ => measurableSet_tri _ _ _
  · exact iUnion₂_subset fun t _ => hK' t
  · exact MeasurableSet.biUnion (Finset.countable_toSet _) fun t _ => measurableSet_tri _ _ _
  · exact iUnion₂_subset fun t _ => hK' t
  · have hcellle : ∀ t, volume.real (cell P c t) ≤ 4 * h ^ 2 := fun t =>
      volume_real_tri_le hh.le (by simp [hh.le]) (hedge t 1) (hedge t 2)
    calc volume.real (⋃ t ∈ Finset.univ.filter (fun t => cornersIn c V t ≠ 3), cell P c t)
        ≤ ∑ t ∈ Finset.univ.filter (fun t => cornersIn c V t ≠ 3), volume.real (cell P c t) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ (Finset.univ.filter fun t => cornersIn c V t ≠ 3).card • (4 * h ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ fun t _ => hcellle t
      _ = 4 * h * (((Finset.univ.filter fun t => cornersIn c V t ≠ 3).card : ℝ) * h) := by
          rw [nsmul_eq_mul]; ring
      _ ≤ 4 * h * m := by gcongr
      _ = 4 * m * h := by ring

end Lightlike.CMS
