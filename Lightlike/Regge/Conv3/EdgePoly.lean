import Lightlike.Regge.CMS.Reexpand

/-!
# The squared geodesic edge length as a jet polynomial, in any dimension

For two points `v + w`, `v + w'` near a point `v` of a compact set `K ⊆ U`, the squared geodesic
distance equals, up to a uniform `O(h⁵)` error, a polynomial in the displacements whose
coefficients are the metric and its first two derivatives at `v`. This is the dimension-general
part of the two-dimensional normal-coordinate expansion (midpoint expansion followed by the
re-expansion of the midpoint jet about the vertex).

## Main results

* `IsRiemMetric.edge_sq_poly`: with `s = (w + w')/2` and `Δ = w' - w`,
  `|d(v + w, v + w')² - P_v(s, Δ)| ≤ C h⁵` for `‖w‖, ‖w'‖ ≤ h ≤ r`, where
  `P_v(s, Δ) = g_v(Δ,Δ) + ∂_s g_v(Δ,Δ) + ½ ∂_s ∂_s g_v(Δ,Δ) + (1/24) ∂_Δ ∂_Δ g_v(Δ,Δ)
  - (1/12) |Γ_v(Δ,Δ)|²_{g_v}` (`edgePoly`).
-/

open Set Lightlike
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The jet polynomial of the squared edge length: the metric and its first two derivatives at the
vertex `v`, evaluated on the midpoint offset `s` and the edge vector `Δ`. -/
noncomputable def edgePoly (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v s Δ : Fin n → ℝ) : ℝ :=
  Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ) + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ))
    + (1 / 24) * (Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ))
    - (1 / 12) * (chr g v Δ Δ ⬝ᵥ (g v *ᵥ chr g v Δ Δ))

/-- **The squared geodesic edge length as a jet polynomial.** For a Riemannian coordinate metric
on `U` and a compact `K ⊆ U` there are `C` and `r > 0` such that for `v ∈ K` and
`‖w‖, ‖w'‖ ≤ h ≤ r`, `|d(v + w, v + w')² - edgePoly g v ((w + w')/2) (w' - w)| ≤ C h⁵`. -/
theorem IsRiemMetric.edge_sq_poly (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ w w' : Fin n → ℝ, ∀ h : ℝ, ‖w‖ ≤ h → ‖w'‖ ≤ h → h ≤ r →
      |dist g U (v + w) (v + w') ^ 2 - edgePoly g v (fun i => (w i + w' i) / 2) (w' - w)| ≤
        C * h ^ 5 := by
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hK' : IsCompact (Metric.cthickening ρ K) := hK.cthickening
  obtain ⟨C1, r1, hr1, h1⟩ := hg.dist_sq_expansion_midpoint hK' hρU
  obtain ⟨C2, r2, hr2, h2⟩ := hg.exists_midJet_reexpand hK hKU
  refine ⟨|C1| * 32 + |C2| * 32, min (min (r1 / 2) (r2 / 2)) ρ,
    lt_min (lt_min (by linarith) (by linarith)) hρ, ?_⟩
  intro v hv w w' h hw hw' hh
  have hh0 : 0 ≤ h := (norm_nonneg w).trans hw
  have hhr1 : h ≤ r1 / 2 := hh.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhr2 : h ≤ r2 / 2 := hh.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhρ : h ≤ ρ := hh.trans (min_le_right _ _)
  set s : Fin n → ℝ := fun i => (w i + w' i) / 2 with hs
  set Δ : Fin n → ℝ := w' - w with hΔ
  have hΔn : ‖Δ‖ ≤ 2 * h := (norm_sub_le w' w).trans (by linarith)
  have hsn : ‖s‖ ≤ h := by
    refine (pi_norm_le_iff_of_nonneg hh0).2 fun i => ?_
    rw [Real.norm_eq_abs, hs]
    have a1 := abs_le_norm_apply w i
    have a2 := abs_le_norm_apply w' i
    simp only [abs_le] at a1 a2 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, (norm_nonneg w), (norm_nonneg w')]
  have hvm : v + s ∈ Metric.cthickening ρ K :=
    Metric.closedBall_subset_cthickening hv ρ (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hsn.trans hhρ)
  have e1 : v + s - (1 / 2 : ℝ) • Δ = v + w := by
    ext i; simp [hs, hΔ]; ring
  have e2 : v + s + (1 / 2 : ℝ) • Δ = v + w' := by
    ext i; simp [hs, hΔ]; ring
  have A1 := h1 (v + s) hvm Δ (by linarith)
  rw [e1, e2] at A1
  have A1' : |dist g U (v + w) (v + w') ^ 2 - midJet g (v + s) Δ| ≤ |C1| * 32 * h ^ 5 := by
    refine A1.trans ?_
    calc C1 * ‖Δ‖ ^ 5 ≤ |C1| * ‖Δ‖ ^ 5 :=
          mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)
      _ ≤ |C1| * (2 * h) ^ 5 := by gcongr
      _ = |C1| * 32 * h ^ 5 := by ring
  have B1 := h2 v hv s Δ (2 * h) (by linarith) hΔn (by linarith)
  have B1' : |midJet g (v + s) Δ - edgePoly g v s Δ| ≤ |C2| * 32 * h ^ 5 := by
    refine (le_of_eq (by simp only [edgePoly])).trans (B1.trans ?_)
    calc C2 * (2 * h) ^ 5 ≤ |C2| * (2 * h) ^ 5 :=
          mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)
      _ = |C2| * 32 * h ^ 5 := by ring
  have := abs_sub_le (dist g U (v + w) (v + w') ^ 2) (midJet g (v + s) Δ) (edgePoly g v s Δ)
  nlinarith [A1', B1']

end Lightlike.Geodesic
