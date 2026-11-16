import Lightlike.Regge.Conv3.ChartChangeClasses
import Lightlike.Regge.Conv3.JetSlice

/-!
# Coefficients of the angle sum of a displaced flat star

For the lengths `q + ε c + ε² r'` of the star with displaced vertices (`dispLen`), the first-order
coefficient `Σ Dh(q, c)` and the second-order coefficient `Σ (Dh(q, r') + ½ D²Dsq(q)(c, c))` of the
dihedral angle sum of each edge class vanish (`disp_coeffs`): the angle sum is `2π` for small `ε`
(`cls0_disp`, …) and `Σ Dsq q = 2π` (`jet_angle_sum`), and the uniform expansion
`dihSq_curve_expansion` makes `Σ Dsq (q + ε c + ε² r') - 2π` equal to `a ε + b ε²` up to `O(ε³)`.

**Limits.** Same as `ChartChangeClasses.lean`: the metric `g` is Riemannian on `U`, `m ∈ U`.
-/

open Real Matrix Lightlike Filter Topology
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {m : Fin 3 → ℝ} {U : Set (Fin 3 → ℝ)}

/-- `clsSum` is linear. -/
theorem clsSum_lin (w : Fin 3 → ℝ) (ε : ℝ) (A B C D : Fin 6 → Fin 6 → ℝ) :
    clsSum w (fun σ h => A σ h - B σ h - ε * C σ h - ε ^ 2 * D σ h) =
      clsSum w A - clsSum w B - ε * clsSum w C - ε ^ 2 * clsSum w D := by
  classical
  simp only [clsSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

/-- A bound on the summands bounds `clsSum` by `36` times it. -/
theorem abs_clsSum_le (w : Fin 3 → ℝ) (f : Fin 6 → Fin 6 → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ σ h, |f σ h| ≤ M) : |clsSum w f| ≤ 36 * M := by
  classical
  unfold clsSum
  calc |∑ σ, ∑ h, if InClass w σ h then f σ h else 0|
      ≤ ∑ σ, |∑ h, if InClass w σ h then f σ h else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Fin 6, ∑ h : Fin 6, M := by
        refine Finset.sum_le_sum fun σ _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun h _ => ?_)
        split_ifs
        · exact hf σ h
        · simpa using hM
    _ = 36 * M := by simp; ring

/-- The second-order coefficient of the angle of the displaced flat tetrahedron:
`Dh(q, r') + ½ D²Dsq(q)(c, c)`. -/
noncomputable def angC2d (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (σ h : Fin 6) : ℝ :=
  Dh (incQ g m σ h, incRd g m σ h)
    + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) (incQ g m σ h) (incC g m σ h) (incC g m σ h)

/-- **The coefficients of the angle sum of a displaced flat star vanish.** -/
theorem disp_coeffs (hg : IsRiemMetric g U) (hm : m ∈ U) (k : Fin 7) :
    clsSum (dirs k) (angC1 g m) = 0 ∧ clsSum (dirs k) (angC2d g m) = 0 := by
  have hG := hg.posDef m hm
  -- the finite set of base lengths
  set K : Set (Fin 6 → ℝ) := Set.range (fun p : Fin 6 × Fin 6 => incQ g m p.1 p.2) with hK
  have hKc : IsCompact K := (Set.finite_range _).isCompact
  have hKV : ∀ L ∈ K, Valid L := by
    rintro L ⟨p, rfl⟩; exact valid_incQ hG p.1 p.2
  set B : ℝ := ∑ p : Fin 6 × Fin 6, (‖incC g m p.1 p.2‖ + ‖incRd g m p.1 p.2‖) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun p _ => by positivity
  have hBc : ∀ p : Fin 6 × Fin 6, ‖incC g m p.1 p.2‖ ≤ B := fun p => by
    refine le_trans ?_ (Finset.single_le_sum (f := fun p : Fin 6 × Fin 6 =>
      ‖incC g m p.1 p.2‖ + ‖incRd g m p.1 p.2‖) (fun q _ => by positivity) (Finset.mem_univ p))
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hBr : ∀ p : Fin 6 × Fin 6, ‖incRd g m p.1 p.2‖ ≤ B := fun p => by
    refine le_trans ?_ (Finset.single_le_sum (f := fun p : Fin 6 × Fin 6 =>
      ‖incC g m p.1 p.2‖ + ‖incRd g m p.1 p.2‖) (fun q _ => by positivity) (Finset.mem_univ p))
    exact le_add_of_nonneg_left (norm_nonneg _)
  obtain ⟨M, r, hr, hexp⟩ := dihSq_curve_expansion hKc hKV hB0
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), clsSum (dirs k) (fun σ h => Dsq (dispLen g m ε σ h)) = 2 * π := by
    fin_cases k
    · exact cls0_disp hg hm
    · exact cls1_disp hg hm
    · exact cls2_disp hg hm
    · exact cls3_disp hg hm
    · exact cls4_disp hg hm
    · exact cls5_disp hg hm
    · exact cls6_disp hg hm
  -- the uniform expansion termwise
  have hterm : ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ σ h : Fin 6,
      |Dsq (dispLen g m ε σ h) - Dsq (incQ g m σ h) - ε * Dh (incQ g m σ h, incC g m σ h)
        - ε ^ 2 * angC2d g m σ h| ≤ M * ε ^ 3 := fun ε hε hεr σ h => by
    have := hexp (incQ g m σ h) ⟨(σ, h), rfl⟩ (incC g m σ h) (incRd g m σ h) (hBc (σ, h))
      (hBr (σ, h)) ε hε hεr
    simpa [dispLen, angC2d] using this
  have hM : 0 ≤ |M| := abs_nonneg M
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.1 hev
  have hr1 : 0 < min r (δ / 2) := lt_min hr (half_pos hδ)
  have hS0 : clsSum (dirs k) (fun σ h => Dsq (incQ g m σ h)) = 2 * π := jet_angle_sum hG k
  have key := coeffs_zero_of_expansion (F := fun ε => clsSum (dirs k) (fun σ h => Dsq (dispLen g m ε σ h)))
    (a := clsSum (dirs k) (angC1 g m)) (b := clsSum (dirs k) (angC2d g m)) (M := 36 * |M|)
    (r := min r (δ / 2)) hr1
    (fun ε hε hεr => hδev (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      have := hεr.trans (min_le_right _ _); linarith))
    (fun ε hε hεr => by
      have hεr' : ε ≤ r := hεr.trans (min_le_left _ _)
      have := abs_clsSum_le (dirs k) (fun σ h => Dsq (dispLen g m ε σ h) - Dsq (incQ g m σ h)
        - ε * Dh (incQ g m σ h, incC g m σ h) - ε ^ 2 * angC2d g m σ h)
        (M := |M| * ε ^ 3) (by positivity) (fun σ h => (hterm ε hε hεr' σ h).trans
          (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)))
      rw [clsSum_lin] at this
      have e : clsSum (dirs k) (fun σ h => Dsq (incQ g m σ h)) = 2 * π := hS0
      have e2 : (fun σ h => Dh (incQ g m σ h, incC g m σ h)) = angC1 g m := rfl
      rw [e, e2] at this
      refine le_trans (le_of_eq ?_) (this.trans (le_of_eq (by ring : 36 * (|M| * ε ^ 3) = 36 * |M| * ε ^ 3)))
      congr 1
      ring)
  exact key

end Lightlike.Regge.Conv3
