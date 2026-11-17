import Lightlike.Regge.Conv3.DihedralTaylor2

/-!
# The averaged second-order Taylor expansion of Christiansen's degrees of freedom

For a field `hf` of symmetric matrices on `ℝ³` with `C³` entries, the interpolated degree of freedom of an edge of
unit-scale direction `D` through the points `v + ε (s₀ + t D)` is
`∫₀¹ D ⬝ hf (v + ε (s₀ + t D)) D dt`. Up to `M ε³`, uniformly in the base point `v` of a compact set and in `s₀`, `D`
of sup norm at most `1`, it equals the polynomial `Σ_ij D_i D_j [h_ij + ε Σ (s₀ + D/2)_k ∂_k h_ij +
(ε²/2) Σ (s₀_k s₀_l + (s₀_k D_l + D_k s₀_l)/2 + D_k D_l/3) ∂_k ∂_l h_ij]` (`quad_taylor`). The proof applies the uniform
second-order Taylor bound `Conv3.taylor3_uniform` coordinatewise (`taylor_coord`) to the points of the edge and
integrates the polynomial (`int_quad`).

## Main results

* `pd1`, `pd2`: the first and second coordinate derivatives of a function on `ℝ³`.
* `taylor_coord`: the uniform Taylor bound in coordinates.
* `int_taylor`: the averaged expansion of one entry along an edge.
* `quad_taylor`: the expansion of the quadratic form `D ⬝ hf D`.

**Limits.** `C³` entries; the bound is uniform on compact sets, not on all of `ℝ³`.
-/

open Real Set
namespace Lightlike.Regge.Linear3
open Lightlike.Regge.Conv3

/-- The expansion of a `C³` function of `ℝ³` to second order in coordinates: the partial derivatives
`∂_k F` and `∂_l ∂_k F` at `v`. -/
noncomputable def pd1 (F : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  fderiv ℝ F v (Pi.single k 1)

/-- The second partial derivative `∂_l ∂_k F (v)` of a function on `ℝ³`, as the second Fréchet derivative on basis vectors. -/
noncomputable def pd2 (F : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) (k l : Fin 3) : ℝ :=
  fderiv ℝ (fderiv ℝ F) v (Pi.single l 1) (Pi.single k 1)

/-- A vector of `ℝ³` is the sum of its coordinates times the basis vectors. -/
theorem vec_expand (y : Fin 3 → ℝ) : y = ∑ k, y k • (Pi.single k (1 : ℝ) : Fin 3 → ℝ) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem fderiv_expand (F : (Fin 3 → ℝ) → ℝ) (v y : Fin 3 → ℝ) :
    fderiv ℝ F v y = ∑ k, y k * pd1 F v k := by
  conv_lhs => rw [vec_expand y]
  simp [map_sum, pd1, mul_comm]

theorem fderiv2_expand (F : (Fin 3 → ℝ) → ℝ) (v y : Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ F) v y y = ∑ k, ∑ l, y k * y l * pd2 F v k l := by
  conv_lhs => rw [vec_expand y]
  simp only [map_sum, sum_apply, map_smul, smul_apply, pd2,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Uniform second-order Taylor expansion in coordinates** of a `C³` function on a compact set. -/
theorem taylor_coord {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ y : Fin 3 → ℝ, ‖y‖ ≤ r →
      |F (v + y) - F v - ∑ k, y k * pd1 F v k - (1 / 2) * ∑ k, ∑ l, y k * y l * pd2 F v k l| ≤
        M * ‖y‖ ^ 3 := by
  obtain ⟨M, r, hr, h⟩ := taylor3_uniform (E := Fin 3 → ℝ) (F := F) (V := Set.univ) isOpen_univ
    hF.contDiffOn hK (Set.subset_univ _)
  refine ⟨M, r, hr, fun v hv y hy => ?_⟩
  have := h v hv y hy
  rwa [fderiv_expand, fderiv2_expand] at this


theorem int_quad (p q r : ℝ) : ∫ t in (0 : ℝ)..1, (p + q * t + r * t ^ 2) = p + q / 2 + r / 3 := by
  have i1 : IntervalIntegrable (fun t : ℝ => p + q * t) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => p + q * t).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t : ℝ => r * t ^ 2) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => r * t ^ 2).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun t : ℝ => p) MeasureTheory.volume 0 1 := intervalIntegrable_const
  have i4 : IntervalIntegrable (fun t : ℝ => q * t) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => q * t).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_add i3 i4,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp [integral_id, integral_pow]
  ring

/-- **The averaged second-order expansion of an entry along an edge.** For a `C³` function `G` and a compact
`K`, the integral `∫₀¹ G (v + ε (s₀ + t D)) dt` is `G v + ε Σ (s₀ + D/2)_k ∂_k G + (ε²/2) Σ
(s₀_k s₀_l + (s₀_k D_l + D_k s₀_l)/2 + D_k D_l/3) ∂_k ∂_l G` up to `M ε³`, uniformly in `v ∈ K` and in
`s₀`, `D` of sup norm at most `1`. -/
theorem int_taylor {G : (Fin 3 → ℝ) → ℝ} (hG : ContDiff ℝ 3 G) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ s0 D : Fin 3 → ℝ, ‖s0‖ ≤ 1 → ‖D‖ ≤ 1 →
      |(∫ t in (0 : ℝ)..1, G (v + ε • (s0 + t • D))) -
        (G v + ε * ∑ k, (s0 k + D k / 2) * pd1 G v k +
          ε ^ 2 / 2 * ∑ k, ∑ l, (s0 k * s0 l + (s0 k * D l + D k * s0 l) / 2 + D k * D l / 3) *
            pd2 G v k l)| ≤ M * ε ^ 3 := by
  obtain ⟨M, r, hr, h⟩ := taylor_coord hG hK
  refine ⟨8 * |M|, r / 2, by positivity, fun v hv ε hε hεr s0 D hs0 hD => ?_⟩
  set p : ℝ := G v + ε * ∑ k, s0 k * pd1 G v k + ε ^ 2 / 2 * ∑ k, ∑ l, s0 k * s0 l * pd2 G v k l with hp
  set q : ℝ := ε * ∑ k, D k * pd1 G v k + ε ^ 2 / 2 * ∑ k, ∑ l, (s0 k * D l + D k * s0 l) * pd2 G v k l with hq
  set r2 : ℝ := ε ^ 2 / 2 * ∑ k, ∑ l, D k * D l * pd2 G v k l with hr2
  have hP : ∀ t : ℝ, G v + ε * ∑ k, (s0 k + t * D k) * pd1 G v k +
      ε ^ 2 / 2 * ∑ k, ∑ l, ((s0 k + t * D k) * (s0 l + t * D l)) * pd2 G v k l = p + q * t + r2 * t ^ 2 := by
    intro t
    simp only [hp, hq, hr2, Fin.sum_univ_three]
    ring
  have htarget : G v + ε * ∑ k, (s0 k + D k / 2) * pd1 G v k +
      ε ^ 2 / 2 * ∑ k, ∑ l, (s0 k * s0 l + (s0 k * D l + D k * s0 l) / 2 + D k * D l / 3) * pd2 G v k l =
      p + q / 2 + r2 / 3 := by
    simp only [hp, hq, hr2, Fin.sum_univ_three]
    ring
  rw [htarget, ← int_quad]
  have hcont : Continuous fun t : ℝ => G (v + ε • (s0 + t • D)) := by
    have := hG.continuous
    fun_prop
  have hint1 : IntervalIntegrable (fun t : ℝ => G (v + ε • (s0 + t • D))) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t : ℝ => p + q * t + r2 * t ^ 2) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => p + q * t + r2 * t ^ 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hint1 hint2]
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖G (v + ε • (s0 + t • D)) - (p + q * t + r2 * t ^ 2)‖ ≤ 8 * |M| * ε ^ 3 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hst : ‖s0 + t • D‖ ≤ 2 := by
      calc ‖s0 + t • D‖ ≤ ‖s0‖ + ‖t • D‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le]
          nlinarith [ht.2, norm_nonneg D]
        _ = 2 := by norm_num
    have hy : ‖ε • (s0 + t • D)‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      nlinarith [norm_nonneg (s0 + t • D)]
    have h1 := h v hv (ε • (s0 + t • D)) hy
    have e1 : ∑ k, (ε • (s0 + t • D)) k * pd1 G v k = ε * ∑ k, (s0 k + t * D k) * pd1 G v k := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, ∑ l, (ε • (s0 + t • D)) k * (ε • (s0 + t • D)) l * pd2 G v k l =
        ε ^ 2 * ∑ k, ∑ l, ((s0 k + t * D k) * (s0 l + t * D l)) * pd2 G v k l := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2] at h1
    have : G (v + ε • (s0 + t • D)) - (p + q * t + r2 * t ^ 2) =
        G (v + ε • (s0 + t • D)) - G v - ε * ∑ k, (s0 k + t * D k) * pd1 G v k -
          1 / 2 * (ε ^ 2 * ∑ k, ∑ l, ((s0 k + t * D k) * (s0 l + t * D l)) * pd2 G v k l) := by
      rw [← hP t]; ring
    rw [Real.norm_eq_abs, this]
    refine h1.trans ?_
    have hn3 : ‖ε • (s0 + t • D)‖ ^ 3 ≤ 8 * ε ^ 3 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, mul_pow]
      have : ‖s0 + t • D‖ ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hst 3
      nlinarith [pow_pos hε 3]
    calc M * ‖ε • (s0 + t • D)‖ ^ 3 ≤ |M| * ‖ε • (s0 + t • D)‖ ^ 3 :=
          mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
      _ ≤ |M| * (8 * ε ^ 3) := mul_le_mul_of_nonneg_left hn3 (abs_nonneg M)
      _ = 8 * |M| * ε ^ 3 := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) hbd
  simpa [Real.norm_eq_abs] using this


open Matrix in
/-- **The averaged second-order expansion of the interpolated degree of freedom.** For a field `hf` of matrices with
`C³` entries, the integral `∫₀¹ D ⬝ hf (v + ε (s₀ + t D)) D dt` is, up to `M ε³`, uniformly in `v ∈ K` and in `s₀`, `D` of
sup norm at most `1`, the polynomial `Σ_ij D_i D_j [h_ij + ε Σ (s₀ + D/2)_k ∂_k h_ij + (ε²/2) Σ
(s₀_k s₀_l + (s₀_k D_l + D_k s₀_l)/2 + D_k D_l/3) ∂_k ∂_l h_ij](v)`. -/
theorem quad_taylor {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ s0 D : Fin 3 → ℝ, ‖s0‖ ≤ 1 → ‖D‖ ≤ 1 →
      |(∫ t in (0 : ℝ)..1, D ⬝ᵥ (hf (v + ε • (s0 + t • D)) *ᵥ D)) -
        ∑ i, ∑ j, D i * D j * (hf v i j + ε * ∑ k, (s0 k + D k / 2) * pd1 (fun y => hf y i j) v k +
          ε ^ 2 / 2 * ∑ k, ∑ l, (s0 k * s0 l + (s0 k * D l + D k * s0 l) / 2 + D k * D l / 3) *
            pd2 (fun y => hf y i j) v k l)| ≤ M * ε ^ 3 := by
  have h := fun i j => int_taylor (hsm i j) hK
  choose M r hr hb using h
  let rr : ℝ := Finset.univ.inf' (⟨(0, 0), Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin 3 × Fin 3)).Nonempty)
    (fun p => r p.1 p.2)
  have hrr : 0 < rr := (Finset.lt_inf'_iff _).2 fun p _ => hr p.1 p.2
  have hrle : ∀ i j, rr ≤ r i j := fun i j => Finset.inf'_le _ (Finset.mem_univ (i, j))
  refine ⟨∑ i, ∑ j, |M i j|, rr, hrr, fun v hv ε hε hεr s0 D hs0 hD => ?_⟩
  have hDi : ∀ i, |D i| ≤ 1 := fun i => (norm_le_pi_norm D i).trans hD
  have hcont : ∀ i j, Continuous fun t : ℝ => hf (v + ε • (s0 + t • D)) i j := fun i j => by
    have := (hsm i j).continuous
    fun_prop
  have hexp : ∀ t : ℝ, D ⬝ᵥ (hf (v + ε • (s0 + t • D)) *ᵥ D) =
      ∑ i, ∑ j, D i * D j * hf (v + ε • (s0 + t • D)) i j := fun t => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [hexp]
  have hI : (∫ t in (0 : ℝ)..1, ∑ i, ∑ j, D i * D j * hf (v + ε • (s0 + t • D)) i j) =
      ∑ i, ∑ j, D i * D j * ∫ t in (0 : ℝ)..1, hf (v + ε • (s0 + t • D)) i j := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        IntervalIntegrable (fun t : ℝ => ∑ j, D i * D j * hf (v + ε • (s0 + t • D)) i j)
          MeasureTheory.volume 0 1 := fun i _ =>
      (continuous_finsetSum _ fun j _ => continuous_const.mul (hcont i j)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hi]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
        IntervalIntegrable (fun t : ℝ => D i * D j * hf (v + ε • (s0 + t • D)) i j)
          MeasureTheory.volume 0 1 := fun j _ =>
      (continuous_const.mul (hcont i j)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hj]
    exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
  rw [hI, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |∑ j, D i * D j * (∫ t in (0 : ℝ)..1, hf (v + ε • (s0 + t • D)) i j) -
        ∑ j, D i * D j * (hf v i j + ε * ∑ k, (s0 k + D k / 2) * pd1 (fun y => hf y i j) v k +
          ε ^ 2 / 2 * ∑ k, ∑ l, (s0 k * s0 l + (s0 k * D l + D k * s0 l) / 2 + D k * D l / 3) *
            pd2 (fun y => hf y i j) v k l)|
      ≤ ∑ i, ∑ j, |M i j| * ε ^ 3 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [← mul_sub, abs_mul, abs_mul]
        have hb' := hb i j v hv ε hε (hεr.trans (hrle i j)) s0 D hs0 hD
        have h1 : |D i| * |D j| ≤ 1 := by
          have := hDi i; have := hDi j
          nlinarith [abs_nonneg (D i), abs_nonneg (D j)]
        calc |D i| * |D j| * |(∫ t in (0 : ℝ)..1, hf (v + ε • (s0 + t • D)) i j) -
            (hf v i j + ε * ∑ k, (s0 k + D k / 2) * pd1 (fun y => hf y i j) v k +
              ε ^ 2 / 2 * ∑ k, ∑ l, (s0 k * s0 l + (s0 k * D l + D k * s0 l) / 2 + D k * D l / 3) *
                pd2 (fun y => hf y i j) v k l)|
            ≤ 1 * (M i j * ε ^ 3) := by
              exact mul_le_mul h1 hb' (abs_nonneg _) zero_le_one
          _ ≤ |M i j| * ε ^ 3 := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ = (∑ i, ∑ j, |M i j|) * ε ^ 3 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]

end Lightlike.Regge.Linear3
