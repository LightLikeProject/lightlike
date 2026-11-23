import Mathlib
import Lightlike.Regge.CMS4.Dihedral4Smooth

/-!
# Expansion of the dihedral angle of a 4-simplex along a quadratic curve

On a compact set of admissible matrices of squared lengths, the dihedral angle at a hinge of a
4-simplex, evaluated along `s + ε c + ε² ρ`, is `dihS s + ε D c + ε² (D ρ + ½ D²(c, c))` up to
`M ε³`, uniformly in `s`. It is the dimension-4 counterpart of `Conv3.dihSq_curve_expansion`.

## Main results

* `dihF`: the dihedral angle as a function of the matrix of squared lengths.
* `fderiv2_dihS_bound`: uniform bound of the second derivative on a compact admissible set.
* `dihS_curve_expansion`: the uniform expansion along `s + ε c + ε² ρ`.
-/

open Real Set Metric

namespace Lightlike.Regge4

variable {V : Type*} [Fintype V]

/-- The dihedral angle at the hinge `pqr` of `pqrtu`, as a function of the matrix `s` of squared
lengths. -/
noncomputable def dihF (p q r t u : V) (s : V → V → ℝ) : ℝ := dihS s p q r t u

/-- The second derivative of the dihedral angle is uniformly bounded, as a bilinear form, on a
compact admissible set. -/
theorem fderiv2_dihS_bound {p q r t u : V} {K : Set (V → V → ℝ)} (hK : IsCompact K)
    (hKV : ∀ s ∈ K, Valid4 p q r t u s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ c ρ : V → V → ℝ,
      |fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c ρ| ≤ C * ‖c‖ * ‖ρ‖ := by
  have hF : ContDiffOn ℝ 3 (dihF p q r t u) {s | Valid4 p q r t u s} := fun s hs =>
    (contDiffAt_dihS hs).contDiffWithinAt
  have h3 : ContinuousOn (fun x => ‖iteratedFDeriv ℝ 2 (dihF p q r t u) x‖)
      {s | Valid4 p q r t u s} := by
    have := hF.continuousOn_iteratedFDerivWithin (m := 2) (by norm_num)
      (isOpen_valid4 p q r t u).uniqueDiffOn
    exact (this.congr (iteratedFDerivWithin_of_isOpen 2 (isOpen_valid4 p q r t u)).symm).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image (h3.mono (fun s hs => hKV s hs))
  refine ⟨max B 0, le_max_right _ _, fun s hs c ρ => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ 2 (dihF p q r t u) s‖ ≤ max B 0 :=
    (hB ⟨s, hs, rfl⟩).trans (le_max_left _ _)
  have h2 := (iteratedFDeriv ℝ 2 (dihF p q r t u) s).le_opNorm ![c, ρ]
  rw [iteratedFDeriv_two_apply] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.prod_univ_two] at h2
  calc |fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c ρ|
      = ‖fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c ρ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ 2 (dihF p q r t u) s‖ * (‖c‖ * ‖ρ‖) := by simpa using h2
    _ ≤ max B 0 * (‖c‖ * ‖ρ‖) := by gcongr
    _ = max B 0 * ‖c‖ * ‖ρ‖ := by ring

set_option maxHeartbeats 800000 in
/-- **Uniform expansion of the dihedral angle of a 4-simplex along a quadratic curve.** On a
compact admissible set `K`, for `‖c‖, ‖ρ‖ ≤ B` and `0 < ε ≤ r`,
`dihF (s + ε c + ε² ρ)` equals `dihF s + ε D(s) c + ε² (D(s) ρ + ½ D²(s)(c, c))` up to `M ε³`. -/
theorem dihS_curve_expansion {p q r t u : V} {K : Set (V → V → ℝ)} (hK : IsCompact K)
    (hKV : ∀ s ∈ K, Valid4 p q r t u s) {B : ℝ} (hB : 0 ≤ B) :
    ∃ M r0 : ℝ, 0 < r0 ∧ ∀ s ∈ K, ∀ c ρ : V → V → ℝ, ‖c‖ ≤ B → ‖ρ‖ ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ r0 →
        |dihF p q r t u (s + ε • c + ε ^ 2 • ρ) - dihF p q r t u s
          - ε * fderiv ℝ (dihF p q r t u) s c
          - ε ^ 2 * (fderiv ℝ (dihF p q r t u) s ρ
            + (1 / 2) * fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c c)| ≤ M * ε ^ 3 := by
  obtain ⟨M0, r1, hr0, hT⟩ := dihS_taylor3 hK hKV
  obtain ⟨C, hC0, hC⟩ := fderiv2_dihS_bound hK hKV
  refine ⟨|M0| * (2 * B) ^ 3 + 2 * C * B ^ 2, min 1 (r1 / (2 * B + 1)), lt_min one_pos
    (div_pos hr0 (by linarith)), fun s hs c ρ hc hρ ε hε hεr => ?_⟩
  have hε1 : ε ≤ 1 := hεr.trans (min_le_left _ _)
  have hε2 : ε ≤ r1 / (2 * B + 1) := hεr.trans (min_le_right _ _)
  set δ : V → V → ℝ := ε • c + ε ^ 2 • ρ with hδ
  have hδn : ‖δ‖ ≤ 2 * B * ε := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε,
      abs_of_pos (pow_pos hε 2)]
    have a1 : ε * ‖c‖ ≤ ε * B := mul_le_mul_of_nonneg_left hc hε.le
    have a2 : ε ^ 2 * ‖ρ‖ ≤ ε * B :=
      calc ε ^ 2 * ‖ρ‖ ≤ ε ^ 2 * B := mul_le_mul_of_nonneg_left hρ (by positivity)
        _ ≤ ε * B := by nlinarith [mul_nonneg (mul_nonneg hε.le hB) (sub_nonneg.2 hε1)]
    linarith
  have hδr : ‖δ‖ ≤ r1 := by
    have : 2 * B * ε ≤ r1 := by
      rw [le_div_iff₀ (by linarith)] at hε2
      nlinarith
    linarith
  have hTay := hT s hs δ hδr
  change |dihF p q r t u (s + δ) - dihF p q r t u s
    - fderiv ℝ (dihF p q r t u) s δ
    - (1 / 2) * fderiv ℝ (fderiv ℝ (dihF p q r t u)) s δ δ| ≤ M0 * ‖δ‖ ^ 3 at hTay
  have lin : fderiv ℝ (dihF p q r t u) s δ
      = ε * fderiv ℝ (dihF p q r t u) s c + ε ^ 2 * fderiv ℝ (dihF p q r t u) s ρ := by
    rw [hδ]
    simp
  have hess : fderiv ℝ (fderiv ℝ (dihF p q r t u)) s δ δ
      = ε ^ 2 * fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c c
      + (ε ^ 3 * (fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c ρ
        + fderiv ℝ (fderiv ℝ (dihF p q r t u)) s ρ c)
      + ε ^ 4 * fderiv ℝ (fderiv ℝ (dihF p q r t u)) s ρ ρ) := by
    rw [hδ]
    simp
    ring
  rw [lin, hess] at hTay
  have hcn := norm_nonneg c
  have hρn := norm_nonneg ρ
  have hcB : ‖c‖ * ‖ρ‖ ≤ B ^ 2 := by
    rw [pow_two]; exact mul_le_mul hc hρ hρn hB
  have hρB : ‖ρ‖ * ‖ρ‖ ≤ B ^ 2 := by
    rw [pow_two]; exact mul_le_mul hρ hρ hρn hB
  have b1 : |fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c ρ| ≤ C * B ^ 2 :=
    (hC s hs c ρ).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hcB hC0)
  have b2 : |fderiv ℝ (fderiv ℝ (dihF p q r t u)) s ρ c| ≤ C * B ^ 2 :=
    (hC s hs ρ c).trans (by rw [mul_assoc, mul_comm ‖ρ‖ ‖c‖]; exact
      mul_le_mul_of_nonneg_left hcB hC0)
  have b3 : |fderiv ℝ (fderiv ℝ (dihF p q r t u)) s ρ ρ| ≤ C * B ^ 2 :=
    (hC s hs ρ ρ).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hρB hC0)
  have hε3 : ε ^ 4 ≤ ε ^ 3 := by
    have := mul_le_mul_of_nonneg_left hε1 (pow_pos hε 3).le
    calc ε ^ 4 = ε ^ 3 * ε := by ring
      _ ≤ ε ^ 3 * 1 := this
      _ = ε ^ 3 := mul_one _
  have hCB : 0 ≤ C * B ^ 2 := by positivity
  have hT1 : |ε ^ 3 * (fderiv ℝ (fderiv ℝ (dihF p q r t u)) s c ρ
      + fderiv ℝ (fderiv ℝ (dihF p q r t u)) s ρ c)| ≤ ε ^ 3 * (2 * (C * B ^ 2)) := by
    rw [abs_mul, abs_of_pos (pow_pos hε 3)]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) (by positivity)
  have hT2 : |ε ^ 4 * fderiv ℝ (fderiv ℝ (dihF p q r t u)) s ρ ρ| ≤ ε ^ 3 * (C * B ^ 2) := by
    rw [abs_mul, abs_of_pos (pow_pos hε 4)]
    calc ε ^ 4 * |fderiv ℝ (fderiv ℝ (dihF p q r t u)) s ρ ρ| ≤ ε ^ 4 * (C * B ^ 2) :=
          mul_le_mul_of_nonneg_left b3 (by positivity)
      _ ≤ ε ^ 3 * (C * B ^ 2) := mul_le_mul_of_nonneg_right hε3 hCB
  have hTT := abs_le.1 ((abs_add_le _ _).trans (add_le_add hT1 hT2))
  have e3 : ‖δ‖ ^ 3 ≤ (2 * B * ε) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hδn 3
  have hM0 : M0 * ‖δ‖ ^ 3 ≤ |M0| * ((2 * B) ^ 3 * ε ^ 3) :=
    (mul_le_mul_of_nonneg_right (le_abs_self M0) (by positivity)).trans
      (by rw [← mul_pow]; exact mul_le_mul_of_nonneg_left e3 (abs_nonneg _))
  have hq := abs_le.1 hTay
  have key : dihF p q r t u (s + ε • c + ε ^ 2 • ρ) = dihF p q r t u (s + δ) := by
    rw [hδ, add_assoc]
  rw [key, abs_le]
  constructor <;> nlinarith [hq.1, hq.2, hM0, hTT.1, hTT.2]

end Lightlike.Regge4
