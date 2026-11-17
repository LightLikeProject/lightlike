import Mathlib
import Lightlike.Regge.CMS.VertexSum
import Lightlike.Regge.CMS.CellSum
import Lightlike.Regge.CMS.Density
import Lightlike.Regge.CMS.Fatness

/-!
# Convergence of weighted Regge deficit angles to curvature (RC6b)

The sum of the deficit angles of the vertices of a fat triangulation of a region of a Riemannian
surface, weighted by a Lipschitz function `f`, differs from the integral of `f` against the Gauss
curvature (with respect to the Riemannian area) by at most a constant times the mesh size `h`.

The triangulation enters through the stars of its vertices: the displacements `w i j` from vertex
`i` to its neighbours, and the cells `S i`, the Euclidean unions of the triangles around vertex
`i`, whose area is `½ ∑ⱼ det2 (w i j) (w i (j+1))`. Every triangle lies in three stars, so the
cells cover the region three times, except in a thin boundary layer `B` (the triangles with only
some of their vertices among the chosen ones), where they cover it at most three times; the layer
has area at most `b h`.

## Main results

* `lipschitzOn_mul`: a product of Lipschitz functions on a compact set is Lipschitz there.
* `IsRiemMetric.cms_convergence`: `|∑ᵢ f(pᵢ) δᵢ - ∫_Ω f K dA| ≤ C h`.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- A product of functions that are Lipschitz on a compact set is Lipschitz there. -/
theorem lipschitzOn_mul {α : Type*} [PseudoMetricSpace α] {K : Set α} (hK : IsCompact K)
    {f ψ : α → ℝ} {Lf Lψ : NNReal} (hf : LipschitzOnWith Lf f K) (hψ : LipschitzOnWith Lψ ψ K) :
    ∃ L : NNReal, LipschitzOnWith L (fun x => f x * ψ x) K := by
  obtain ⟨Fm, hF⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Pm, hP⟩ := hK.exists_bound_of_continuousOn hψ.continuousOn
  have hF0 : 0 ≤ max Fm 0 := le_max_right _ _
  have hP0 : 0 ≤ max Pm 0 := le_max_right _ _
  refine ⟨(max Fm 0).toNNReal * Lψ + (max Pm 0).toNNReal * Lf, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have h1 := hf.dist_le_mul x hx y hy
  have h2 := hψ.dist_le_mul x hx y hy
  have hx1 : |f x| ≤ max Fm 0 := by
    have := hF x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hy2 : |ψ y| ≤ max Pm 0 := by
    have := hP y hy; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  rw [Real.dist_eq] at h1 h2 ⊢
  have e : f x * ψ x - f y * ψ y = f x * (ψ x - ψ y) + ψ y * (f x - f y) := by ring
  rw [e]
  push_cast
  calc |f x * (ψ x - ψ y) + ψ y * (f x - f y)|
      ≤ |f x * (ψ x - ψ y)| + |ψ y * (f x - f y)| := abs_add_le _ _
    _ = |f x| * |ψ x - ψ y| + |ψ y| * |f x - f y| := by rw [abs_mul, abs_mul]
    _ ≤ max Fm 0 * (Lψ * dist x y) + max Pm 0 * (Lf * dist x y) := by gcongr
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ hF0,
      Real.coe_toNNReal _ hP0]; ring

/-- **Convergence of weighted deficit angles to the Gauss curvature** (dimension two, geodesic
edge lengths, fat triangulations).

For a Riemannian metric `g` on `U`, a compact `K ⊆ U` and a Lipschitz `f`, there are `C` and `h₀`
such that, whenever the stars of the vertices `p i ∈ K` have edges of length at most `h ≤ h₀`,
are `ρ`-fat (`ρ h² ≤ det2` of consecutive edges), have at most `N` edges, wind once around the
vertex (their angles are then at most `π - arcsin (ρ/2)` by fatness), and the number of vertices satisfies `#V h² ≤ M`, and the
cells `S i` (area `½ ∑ⱼ det2 (w i j) (w i (j+1))`, diameter at most `h` around `p i`) cover at
most three times everywhere and exactly three times in the region `Ω` outside a layer `B` of area
at most `b h`, then
`|∑ᵢ f(pᵢ) δᵢ - ∫_Ω f (R/2) √det| ≤ C h`,
where `δᵢ = 2π - ∑ⱼ (triangle angle at pᵢ computed from geodesic edge lengths)` is the deficit
angle, `R / 2` the Gauss curvature and `√det g dx` the Riemannian area element.

The threshold `h₀` is smaller than the radius of a neighbourhood of `K` inside `U`, so every edge
of a star lies in a ball contained in `U` and is joined by an admissible curve there: the
distances `dist g U` in the deficit are genuine lengths, never the value `0` that `dist g U`
takes when no admissible curve exists.

**Differences from the source.** The comparison with the cited source (Christiansen 2011, Section 1) is pending: it
was not read at that location. This is not the theorem of Cheeger, Müller and Schrader (1984), which holds in every
dimension and for arbitrary fine triangulations of a manifold: here the region is planar (one chart), the vertex stars
are `ρ`-fat of bounded valence, the edge lengths are geodesic, the weight `f` is Lipschitz, the rate is `O(h)`, and the
vertex cells `S i` are hypotheses (building them from a triangulation is not proved). -/
theorem _root_.Lightlike.Geodesic.IsRiemMetric.cms_convergence
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} {U : Set (Fin 2 → ℝ)}
    (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {ρ N M b : ℝ} (hb : 0 ≤ b) (hρ : 0 < ρ)
    {f : (Fin 2 → ℝ) → ℝ} {Lf : NNReal} (hf : LipschitzOnWith Lf f K) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ (ι : Type) (V : Finset ι) (n : ι → ℕ) [∀ i, NeZero (n i)]
      (p : ι → Fin 2 → ℝ) (w : (i : ι) → ZMod (n i) → Fin 2 → ℝ) (S : ι → Set (Fin 2 → ℝ))
      (Ω B : Set (Fin 2 → ℝ)) (h : ℝ),
      0 < h → h ≤ h₀ → (V.card : ℝ) * h ^ 2 ≤ M → (∀ i ∈ V, p i ∈ K) → (∀ i ∈ V, (n i : ℝ) ≤ N) →
      (∀ i ∈ V, ∀ j, ‖w i j‖ ≤ h) → (∀ i ∈ V, ∀ j, ρ * h ^ 2 ≤ det2 (w i j) (w i (j + 1))) →
      (∀ i ∈ V, ∑ j, InnerProductGeometry.angle (toC (w i j)) (toC (w i (j + 1))) = 2 * π) →
      (∀ i ∈ V, MeasurableSet (S i)) → (∀ i ∈ V, S i ⊆ K) →
      (∀ i ∈ V, ∀ x ∈ S i, dist x (p i) ≤ h) →
      (∀ i ∈ V, volume.real (S i) = 1 / 2 * ∑ j, det2 (w i j) (w i (j + 1))) →
      MeasurableSet Ω → Ω ⊆ K → MeasurableSet B → B ⊆ K → volume.real B ≤ b * h →
      (∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), ∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x ≤ 3) →
      (∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), x ∉ B →
        ∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x = 3 * Ω.indicator (fun _ => (1 : ℝ)) x) →
      |∑ i ∈ V, f (p i) * (2 * π - ∑ j, triAngle (dist g U (p i) (p i + w i j) ^ 2)
            (dist g U (p i) (p i + w i (j + 1)) ^ 2)
            (dist g U (p i + w i j) (p i + w i (j + 1)) ^ 2)) -
        ∫ x in Ω, f x * (scalarCurvature g x / 2 * √((g x).det))| ≤ C * h := by
  have hθ : 0 < arcsin (min (ρ / 2) 1) := Real.arcsin_pos.2 (lt_min (by linarith) one_pos)
  have hθπ : arcsin (min (ρ / 2) 1) ≤ π := (Real.arcsin_le_pi_div_two _).trans (by linarith [pi_pos])
  obtain ⟨Lψ, hLψ⟩ := hg.lipschitz_density hK hKU
  obtain ⟨L, hL⟩ := lipschitzOn_mul hK hf hLψ
  obtain ⟨Fm, hF⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨C, h₀, hh₀, hv⟩ := hg.vertex_deficit_expansion hK hKU (N := N) hρ hθ hθπ
  obtain ⟨Φ, hΦ⟩ := hK.exists_bound_of_continuousOn hL.continuousOn
  refine ⟨max C 0 * max Fm 0 * max M 0 + 2 * L * volume.real K + max Φ 0 * b, h₀, hh₀, ?_⟩
  intro ι V n _ p w S Ω B h hh hh0 hcard hp hn hw hd h2π hSm hSK hSb hSvol hΩm hΩ hBm hBK hBv hle hout
  set φ : (Fin 2 → ℝ) → ℝ := fun x => f x * (scalarCurvature g x / 2 * √((g x).det)) with hφ
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hF0 : 0 ≤ max Fm 0 := le_max_right _ _
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hper : ∀ i ∈ V, |f (p i) * (2 * π - ∑ j, triAngle (dist g U (p i) (p i + w i j) ^ 2)
            (dist g U (p i) (p i + w i (j + 1)) ^ 2)
            (dist g U (p i + w i j) (p i + w i (j + 1)) ^ 2)) -
        (1 / 3) * (φ (p i) * volume.real (S i))| ≤ max Fm 0 * (max C 0 * h ^ 3) := by
    intro i hi
    have e := hv (p i) (hp i hi) (n i) (w i) h hh hh0 (hn i hi) (hw i hi) (hd i hi) (h2π i hi)
      (fun j => angle_le_of_fat hh hρ (hw i hi j) (hw i hi (j + 1)) (hd i hi j))
    rw [jetScalar_eq_scalarCurvature hg.coord (hKU (hp i hi))] at e
    have hfx : |f (p i)| ≤ max Fm 0 := by
      have := hF (p i) (hp i hi); rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    have e2 : f (p i) * (2 * π - ∑ j, triAngle (dist g U (p i) (p i + w i j) ^ 2)
            (dist g U (p i) (p i + w i (j + 1)) ^ 2)
            (dist g U (p i + w i j) (p i + w i (j + 1)) ^ 2)) -
        (1 / 3) * (φ (p i) * volume.real (S i)) =
        f (p i) * ((2 * π - ∑ j, triAngle (dist g U (p i) (p i + w i j) ^ 2)
            (dist g U (p i) (p i + w i (j + 1)) ^ 2)
            (dist g U (p i + w i j) (p i + w i (j + 1)) ^ 2)) -
          scalarCurvature g (p i) / 12 * √((g (p i)).det) *
            ∑ j, det2 (w i j) (w i (j + 1))) := by
      simp only [hφ, hSvol i hi]; ring
    rw [e2, abs_mul]
    have hCh : C * h ^ 3 ≤ max C 0 * h ^ 3 := by gcongr; exact le_max_left _ _
    calc |f (p i)| * _ ≤ max Fm 0 * (C * h ^ 3) := by gcongr
      _ ≤ _ := by gcongr
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hper)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hΦ' : ∀ x ∈ K, |φ x| ≤ max Φ 0 := fun x hx => by
    have := hΦ x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hcs := cell_sum_approx (μ := (volume : Measure (Fin 2 → ℝ))) hh.le (le_max_right _ _) hΦ'
    hK hL hSm hSK hp hSb hΩm hΩ hBm hBK hle hout
  have e : ∑ i ∈ V, f (p i) * (2 * π - ∑ j, triAngle (dist g U (p i) (p i + w i j) ^ 2)
            (dist g U (p i) (p i + w i (j + 1)) ^ 2)
            (dist g U (p i + w i j) (p i + w i (j + 1)) ^ 2)) - ∫ x in Ω, φ x =
      ∑ i ∈ V, (f (p i) * (2 * π - ∑ j, triAngle (dist g U (p i) (p i + w i j) ^ 2)
            (dist g U (p i) (p i + w i (j + 1)) ^ 2)
            (dist g U (p i + w i j) (p i + w i (j + 1)) ^ 2)) -
        (1 / 3) * (φ (p i) * volume.real (S i))) +
      ((1 / 3) * ∑ i ∈ V, φ (p i) * volume.real (S i) - ∫ x in Ω, φ x) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  show |∑ i ∈ V, f (p i) * _ - ∫ x in Ω, φ x| ≤ _
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have hb : (V.card : ℝ) * (max Fm 0 * (max C 0 * h ^ 3)) ≤ max C 0 * max Fm 0 * max M 0 * h := by
    have : (V.card : ℝ) * (max Fm 0 * (max C 0 * h ^ 3)) =
        ((V.card : ℝ) * h ^ 2) * (max Fm 0 * max C 0 * h) := by ring
    rw [this]
    calc ((V.card : ℝ) * h ^ 2) * (max Fm 0 * max C 0 * h) ≤ max M 0 * (max Fm 0 * max C 0 * h) := by
          gcongr; exact hcard.trans (le_max_left _ _)
      _ = _ := by ring
  have hL' : 2 * (L : ℝ) * h * volume.real K = 2 * L * volume.real K * h := by ring
  have hΦb : max Φ 0 * volume.real B ≤ max Φ 0 * (b * h) := by gcongr
  nlinarith [hsum, hcs, hb, hL', hΦb]

end Lightlike.CMS
