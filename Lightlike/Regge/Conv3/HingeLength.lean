import Lightlike.Regge.Conv3.HingeExpansion

/-!
# The length of a hinge

For a Riemannian metric `g` on `U`, a compact `K ⊆ U` and a nonzero vector `w` of sup norm at most `1`,
the geodesic length of the segment of vector `ε w` centred at `v ∈ K` is `ε √(g(v)(w, w))` up to
`C ε³`, uniformly in `v ∈ K` (`hinge_length`). The squared length is the edge polynomial of the jet at the
midpoint, which has no cubic term at the midpoint, so the error of the square is `O(ε⁴)` and the error of
the length `O(ε³)`.

## Main results

* `hinge_length`: `|d(v - (ε/2) w, v + (ε/2) w) - ε √(g(v)(w, w))| ≤ C ε³`.
* `abs_sub_le_of_sq`: `|d - m| ≤ |d² - m²| / m` for `d ≥ 0`, `m > 0`.

**Limits.** The constant is not explicit and the statement is for one fixed direction `w`.
-/

open Real Matrix Lightlike Filter Topology Metric Set
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)}

/-- For `d, m ≥ 0` with `m > 0`: `|d - m| ≤ |d² - m²| / m`. -/
theorem abs_sub_le_of_sq {d m : ℝ} (hd : 0 ≤ d) (hm : 0 < m) : |d - m| ≤ |d ^ 2 - m ^ 2| / m := by
  rw [le_div_iff₀ hm]
  have : |d ^ 2 - m ^ 2| = |d - m| * (d + m) := by
    rw [show d ^ 2 - m ^ 2 = (d - m) * (d + m) by ring, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ d + m by linarith)]
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

/-- **The length of a hinge.** For a Riemannian metric `g` on `U`, a compact `K ⊆ U` and a vector `w`
with sup norm at most `1` and `w ≠ 0`, the geodesic length of the segment of vector `ε w` centred at
`v ∈ K` is `ε √(g(v)(w, w))` up to `C ε³`, uniformly in `v ∈ K`. -/
theorem hinge_length (hg : IsRiemMetric g U) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) {w : Fin 3 → ℝ} (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1) :
    ∃ C r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |Geodesic.dist g U (v - (ε / 2) • w) (v + (ε / 2) • w) - ε * √(edgeQ g v w)| ≤ C * ε ^ 3 := by
  classical
  by_cases hne : K.Nonempty
  swap
  · exact ⟨0, 1, one_pos, fun v hv => absurd ⟨v, hv⟩ hne⟩
  obtain ⟨C1, r1, hr1, h1⟩ := hg.edge_sq_poly hK hKU
  -- lower bound of `edgeQ` and bound of `edgeR` on `K`
  have hQc : ContinuousOn (fun v => edgeQ g v w) K := (continuousOn_edgeQ hg.coord w).mono hKU
  have hRc : ContinuousOn (fun v => |edgeR g v 0 w|) K := (continuousOn_edgeR hg.coord 0 w).mono hKU |>.abs
  obtain ⟨v0, hv0, hmin⟩ := hK.exists_isMinOn hne hQc
  obtain ⟨v1, hv1, hmax⟩ := hK.exists_isMaxOn hne hRc
  set a : ℝ := edgeQ g v0 w with ha
  have hpos : ∀ v ∈ K, 0 < edgeQ g v w := fun v hv => by
    have := posDef_dpos (hg.posDef v (hKU hv)) hw
    simpa [edgeQ] using this
  have ha0 : 0 < a := hpos v0 hv0
  set B : ℝ := |edgeR g v1 0 w| with hB
  have hB0 : 0 ≤ B := abs_nonneg _
  refine ⟨(|C1| / 32 + B) / √a, min r1 1, lt_min hr1 one_pos, fun v hv ε hε hεr => ?_⟩
  have hεr1 : ε ≤ r1 := hεr.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := hεr.trans (min_le_right _ _)
  set Q : ℝ := edgeQ g v w with hQ
  have hQa : a ≤ Q := hmin hv
  have hQ0 : 0 < Q := hpos v hv
  set d : ℝ := Geodesic.dist g U (v - (ε / 2) • w) (v + (ε / 2) • w) with hd
  have hd0 : 0 ≤ d := Geodesic.dist_nonneg
  have hw1' : ‖-((ε / 2) • w)‖ ≤ ε / 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [norm_nonneg w]
  have hw2' : ‖(ε / 2) • w‖ ≤ ε / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [norm_nonneg w]
  have hh := h1 v hv (-((ε / 2) • w)) ((ε / 2) • w) (ε / 2) hw1' hw2' (by linarith)
  have e1 : v + -((ε / 2) • w) = v - (ε / 2) • w := by abel
  have e2 : (fun i => ((-((ε / 2) • w)) i + ((ε / 2) • w) i) / 2) = ε • (0 : Fin 3 → ℝ) := by
    ext i; simp
  have e3 : (ε / 2) • w - -((ε / 2) • w) = ε • w := by
    ext i; simp; ring
  rw [e1, e2, e3, edgePoly_smul] at hh
  have hC0 : edgeC g v 0 w = 0 := by simp [edgeC, dmat_zero]
  rw [hC0] at hh
  have hR : |edgeR g v 0 w| ≤ B := hmax hv
  have hsq : |d ^ 2 - (ε * √Q) ^ 2| ≤ (|C1| / 32 + B) * ε ^ 4 := by
    have hQs : (ε * √Q) ^ 2 = ε ^ 2 * Q := by rw [mul_pow, Real.sq_sqrt hQ0.le]
    rw [hQs]
    have : d ^ 2 - ε ^ 2 * Q = (d ^ 2 - (ε ^ 2 * Q + ε ^ 3 * 0 + ε ^ 4 * edgeR g v 0 w))
        + ε ^ 4 * edgeR g v 0 w := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    have h5 : |C1| * (ε / 2) ^ 5 ≤ |C1| / 32 * ε ^ 4 := by
      have : (ε / 2) ^ 5 = ε ^ 4 * (ε / 32) := by ring
      rw [this]
      have : ε / 32 ≤ 1 / 32 := by linarith
      nlinarith [abs_nonneg C1, pow_pos hε 4, mul_nonneg (abs_nonneg C1) (pow_pos hε 4).le]
    have h6 : |ε ^ 4 * edgeR g v 0 w| ≤ B * ε ^ 4 := by
      rw [abs_mul, abs_of_pos (pow_pos hε 4)]; nlinarith [pow_pos hε 4]
    have h7 : |d ^ 2 - (ε ^ 2 * Q + ε ^ 3 * 0 + ε ^ 4 * edgeR g v 0 w)| ≤ |C1| / 32 * ε ^ 4 :=
      hh.trans ((mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)).trans h5)
    nlinarith
  have hm : 0 < ε * √Q := mul_pos hε (Real.sqrt_pos.2 hQ0)
  have hfin := (abs_sub_le_of_sq hd0 hm).trans (div_le_div_of_nonneg_right hsq hm.le)
  have hsa : √a ≤ √Q := Real.sqrt_le_sqrt hQa
  have hsa0 : 0 < √a := Real.sqrt_pos.2 ha0
  calc |d - ε * √Q| ≤ (|C1| / 32 + B) * ε ^ 4 / (ε * √Q) := hfin
    _ ≤ (|C1| / 32 + B) * ε ^ 4 / (ε * √a) := by
        gcongr
    _ = (|C1| / 32 + B) / √a * ε ^ 3 := by field_simp

end Lightlike.Regge.Conv3
