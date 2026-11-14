import Lightlike.Regge.Geodesic.Equation

/-!
# The exponential map near a point

Step 3 of RC6a. Near a point `x` of `U` every small vector `v` is the initial velocity of a
geodesic defined up to time `1`; its endpoint is `exp_x(v)`, and `exp_x(v) = x + v + O(|v|²)`.

Mathlib has no smooth dependence of ODE solutions on their initial data, so the estimate is
proven directly. On a closed ball around `x` the acceleration is bounded by `A |v|²`. A barrier
argument (`image_norm_le_of_norm_deriv_right_lt_deriv_boundary`) keeps every geodesic with
initial velocity of norm at most `M` in that ball for a uniform time (`geodesic_stays`), and the
mean value inequality then bounds `γ(τ) - x - τ γ'(0)` by `A (M + R)² τ²` (`geodesic_sub_le`).
The exponential map is defined through the geodesic with initial velocity of norm `r` in the
direction of `v`, at time `|v|/r`.

## Main results

* `exists_accel_bound`: `|Γ(z)(v, v)| ≤ A |v|²` on compact subsets of `U`.
* `geodesic_stays`, `geodesic_sub_le`: uniform containment and the quadratic estimate.
* `exists_expMap`: a map `E` near `0` with `E 0 = x`, such that `t ↦` (geodesic with initial
  velocity `v`) reaches `E v` at time `1`, and `|E v - x - v| ≤ C |v|²`.
-/

open Set Filter Topology Metric

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The acceleration is quadratically bounded** on a compact subset `K` of `U`:
`‖Γ(z)(v, v)‖ ≤ A ‖v‖²` for `z ∈ K` (sup norms). -/
theorem exists_accel_bound (hg : Lightlike.IsCoordMetric g U) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ A : ℝ, 0 ≤ A ∧ ∀ z ∈ K, ∀ v, ‖accel g z v‖ ≤ A * ‖v‖ ^ 2 := by
  have hb : ∀ i j k, ∃ G, ∀ z ∈ K, ‖Lightlike.christoffel g i j k z‖ ≤ G := fun i j k =>
    hK.exists_bound_of_continuousOn ((hg.contDiffOn_christoffel i j k).continuousOn.mono hKU)
  choose G hG using hb
  refine ⟨∑ i, ∑ j, ∑ k, |G i j k|, by positivity, fun z hz v => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have hv : ∀ j, |v j| ≤ ‖v‖ := fun j => by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j
  simp only [accel, Real.norm_eq_abs, abs_neg]
  calc |∑ j, ∑ k, Lightlike.christoffel g i j k z * v j * v k|
      ≤ ∑ j, ∑ k, |G i j k| * ‖v‖ ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_mul, sq]
        have h1 : |Lightlike.christoffel g i j k z| ≤ |G i j k| :=
          (by simpa [Real.norm_eq_abs] using hG i j k z hz : |Lightlike.christoffel g i j k z| ≤ G i j k).trans
            (le_abs_self _)
        exact (mul_le_mul (mul_le_mul h1 (hv j) (abs_nonneg _) (abs_nonneg _)) (hv k)
          (abs_nonneg _) (by positivity)).trans_eq (by ring)
    _ = (∑ j, ∑ k, |G i j k|) * ‖v‖ ^ 2 := by simp only [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ∑ k, |G i j k|) * ‖v‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact Finset.single_le_sum (f := fun i => ∑ j, ∑ k, |G i j k|)
          (fun i _ => by positivity) (Finset.mem_univ i)

/-- **Geodesics stay near their start for a uniform time.** If the acceleration is bounded by
`A ‖v‖²` on `closedBall x R`, a geodesic from `x` with `‖γ'(0)‖ ≤ M`, defined on `(-ε, ε)`, stays
in that ball, with `‖γ'(t) - γ'(0)‖ ≤ R`, for `0 ≤ t ≤ T` as long as `β T < R`, where
`β = M + R + A (M + R)² + 1`. -/
theorem geodesic_stays {x : Fin n → ℝ} {R A M : ℝ} (hR : 0 < R) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hB : ∀ z ∈ closedBall x R, ∀ v, ‖accel g z v‖ ≤ A * ‖v‖ ^ 2) {γ w : ℝ → Fin n → ℝ}
    {ε T : ℝ} (hT : 0 ≤ T) (hTε : T < ε) (hgeo : IsGeodesicOn g γ w (Ioo (-ε) ε)) (h0 : γ 0 = x)
    (hw0 : ‖w 0‖ ≤ M) (hTR : (M + R + A * (M + R) ^ 2 + 1) * T < R) :
    ∀ t ∈ Icc 0 T, ‖γ t - x‖ ≤ R ∧ ‖w t - w 0‖ ≤ R := by
  set β := M + R + A * (M + R) ^ 2 + 1
  set η := (R - β * T) / 2
  have hη : 0 < η := by simp only [η]; linarith
  have hβ : 0 ≤ β := by simp only [β]; positivity
  have hmem : ∀ t ∈ Icc 0 T, t ∈ Ioo (-ε) ε := fun t ht =>
    ⟨by linarith [ht.1, hT.trans_lt hTε], by linarith [ht.2]⟩
  let f : ℝ → (Fin n → ℝ) × (Fin n → ℝ) := fun t => (γ t - x, w t - w 0)
  have hf : ∀ t ∈ Icc 0 T, HasDerivAt f (w t, accel g (γ t) (w t)) t := fun t ht =>
    ((hgeo.pos t (hmem t ht)).sub_const x).prodMk ((hgeo.vel t (hmem t ht)).sub_const (w 0))
  have key := image_norm_le_of_norm_deriv_right_lt_deriv_boundary (f := f) (a := 0) (b := T)
    (f' := fun t => (w t, accel g (γ t) (w t))) (B := fun t => β * t + η) (B' := fun _ => β)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [f, h0, hη.le])
    (fun t => by simpa using ((hasDerivAt_id t).const_mul β).add_const η)
    (fun t ht hft => by
      have hft' : ‖f t‖ ≤ β * t + η := hft.le
      have h1 : ‖γ t - x‖ ≤ β * t + η := (norm_fst_le (f t)).trans hft'
      have h2 : ‖w t - w 0‖ ≤ β * t + η := (norm_snd_le (f t)).trans hft'
      have hlt : β * t + η < R := by
        have := mul_le_mul_of_nonneg_left ht.2.le hβ
        simp only [η]; linarith
      have hz : γ t ∈ closedBall x R := by
        rw [mem_closedBall, dist_eq_norm]; linarith
      have hw : ‖w t‖ ≤ M + R := by
        calc ‖w t‖ = ‖(w t - w 0) + w 0‖ := by rw [sub_add_cancel]
          _ ≤ ‖w t - w 0‖ + ‖w 0‖ := norm_add_le _ _
          _ ≤ M + R := by linarith
      have hacc : ‖accel g (γ t) (w t)‖ ≤ A * (M + R) ^ 2 :=
        (hB _ hz _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hw 2) hA)
      rw [Prod.norm_def]
      refine max_lt ?_ ?_
      · simp only [β]; nlinarith [sq_nonneg (M + R), mul_nonneg hA (sq_nonneg (M + R))]
      · simp only [β]; nlinarith [norm_nonneg (w t)])
  intro t ht
  have := key ht
  have hlt : β * t + η < R := by
    have := mul_le_mul_of_nonneg_left ht.2 hβ
    simp only [η]; linarith
  exact ⟨((norm_fst_le (f t)).trans this).trans hlt.le, ((norm_snd_le (f t)).trans this).trans hlt.le⟩

/-- **The quadratic estimate.** Under the hypotheses of `geodesic_stays`, for `0 ≤ τ ≤ T`,
`‖γ(τ) - x - τ γ'(0)‖ ≤ A (M + R)² τ²`. -/
theorem geodesic_sub_le {x : Fin n → ℝ} {R A M : ℝ} (hR : 0 < R) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hB : ∀ z ∈ closedBall x R, ∀ v, ‖accel g z v‖ ≤ A * ‖v‖ ^ 2) {γ w : ℝ → Fin n → ℝ}
    {ε T : ℝ} (hT : 0 ≤ T) (hTε : T < ε) (hgeo : IsGeodesicOn g γ w (Ioo (-ε) ε)) (h0 : γ 0 = x)
    (hw0 : ‖w 0‖ ≤ M) (hTR : (M + R + A * (M + R) ^ 2 + 1) * T < R) {τ : ℝ}
    (hτ : τ ∈ Icc 0 T) : ‖γ τ - x - τ • w 0‖ ≤ A * (M + R) ^ 2 * τ ^ 2 := by
  have hst := geodesic_stays hR hA hM hB hT hTε hgeo h0 hw0 hTR
  have hmem : ∀ t ∈ Icc 0 T, t ∈ Ioo (-ε) ε := fun t ht =>
    ⟨by linarith [ht.1, hT.trans_lt hTε], by linarith [ht.2]⟩
  -- the acceleration along the geodesic
  have hacc : ∀ t ∈ Icc 0 T, ‖accel g (γ t) (w t)‖ ≤ A * (M + R) ^ 2 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hst t ht
    have hz : γ t ∈ closedBall x R := by rw [mem_closedBall, dist_eq_norm]; exact h1
    have hw : ‖w t‖ ≤ M + R := by
      calc ‖w t‖ = ‖(w t - w 0) + w 0‖ := by rw [sub_add_cancel]
        _ ≤ ‖w t - w 0‖ + ‖w 0‖ := norm_add_le _ _
        _ ≤ M + R := by linarith
    exact (hB _ hz _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2) hA)
  -- the velocity changes by at most `A (M + R)² t`
  have hwv : ∀ t ∈ Icc 0 τ, ‖w t - w 0‖ ≤ A * (M + R) ^ 2 * t := by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := w) (a := 0) (b := τ)
      (f' := fun t => accel g (γ t) (w t)) (C := A * (M + R) ^ 2)
      (fun t ht => (hgeo.vel t (hmem t ⟨ht.1, ht.2.trans hτ.2⟩)).hasDerivWithinAt)
      (fun t ht => hacc t ⟨ht.1, ht.2.le.trans hτ.2⟩)
    intro t ht
    simpa using this t ht
  -- integrate once more
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t => γ t - t • w 0) (a := 0)
    (b := τ) (f' := fun t => w t - w 0) (C := A * (M + R) ^ 2 * τ)
    (fun t ht => by
      exact ((hgeo.pos t (hmem t ⟨ht.1, ht.2.trans hτ.2⟩)).sub
        ((hasDerivAt_id t).smul_const (w 0))).hasDerivWithinAt.congr_deriv (by rw [one_smul]))
    (fun t ht => (hwv t ⟨ht.1, ht.2.le⟩).trans (by
      have := mul_le_mul_of_nonneg_left ht.2.le (by positivity : 0 ≤ A * (M + R) ^ 2)
      linarith))
    τ ⟨hτ.1, le_rfl⟩
  simp only [zero_smul, sub_zero, h0] at this
  calc ‖γ τ - x - τ • w 0‖ = ‖γ τ - τ • w 0 - x‖ := by congr 1; abel
    _ ≤ A * (M + R) ^ 2 * τ * τ := this
    _ = A * (M + R) ^ 2 * τ ^ 2 := by ring

/-- **The exponential map near a point.** For `x ∈ U` there are `ρ > 0`, `C` and a map `E` with
`E 0 = x` such that every `v` with `‖v‖ ≤ ρ` is the initial velocity of a geodesic from `x`,
defined beyond `[0, 1]`, that reaches `E v` at time `1`, and `‖E v - x - v‖ ≤ C ‖v‖²`. -/
theorem exists_expMap (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ ρ > (0 : ℝ), ∃ C : ℝ, ∃ E : (Fin n → ℝ) → (Fin n → ℝ), E 0 = x ∧
      (∀ v, ‖v‖ ≤ ρ → ∃ δ > (0 : ℝ), ∃ γ w : ℝ → Fin n → ℝ, γ 0 = x ∧ w 0 = v ∧ γ 1 = E v ∧
        IsGeodesicOn g γ w (Ioo (-δ) (1 + δ))) ∧
      ∀ v, ‖v‖ ≤ ρ → ‖E v - x - v‖ ≤ C * ‖v‖ ^ 2 := by
  -- a closed ball in `U` and the bound on the acceleration there
  obtain ⟨R, hR, hRU⟩ : ∃ R > 0, closedBall x R ⊆ U := by
    obtain ⟨R, hR, hb⟩ := Metric.isOpen_iff.mp hg.isOpen x hx
    exact ⟨R / 2, half_pos hR, (closedBall_subset_ball (half_lt_self hR)).trans hb⟩
  obtain ⟨A, hA, hB⟩ := exists_accel_bound hg (isCompact_closedBall x R) hRU
  -- geodesics for all initial velocities of norm at most `r`
  obtain ⟨r, hr, ε, hε, H⟩ := exists_geodesic hg hx 0
  choose γ w hγ0 hw0 hgeo using fun v (hv : ‖v - 0‖ ≤ r) => H v hv
  set β := r + R + A * (r + R) ^ 2 + 1
  have hβ : 0 < β := by simp only [β]; positivity
  set T := min (ε / 2) (R / (2 * β))
  have hT : 0 < T := lt_min (half_pos hε) (div_pos hR (by positivity))
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hTR : β * T < R := by
    have : T ≤ R / (2 * β) := min_le_right _ _
    calc β * T ≤ β * (R / (2 * β)) := mul_le_mul_of_nonneg_left this hβ.le
      _ = R / 2 := by field_simp
      _ < R := half_lt_self hR
  -- the direction `u = (r/|v|) v` and the time `τ = |v|/r`
  have hu : ∀ v : Fin n → ℝ, v ≠ 0 → ‖(r / ‖v‖) • v - 0‖ ≤ r := fun v hv => by
    rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hr, abs_norm,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]
  classical
  let E : (Fin n → ℝ) → (Fin n → ℝ) := fun v =>
    if hv : v = 0 then x else γ ((r / ‖v‖) • v) (hu v hv) (‖v‖ / r)
  refine ⟨r * T, mul_pos hr hT, A * (r + R) ^ 2 / r ^ 2, E, by simp [E], ?_, ?_⟩
  · intro v hv
    by_cases h0 : v = 0
    · -- the constant geodesic
      refine ⟨1, one_pos, fun _ => x, fun _ => 0, rfl, h0.symm, by simp [E, h0], ?_⟩
      refine ⟨fun t _ => hasDerivAt_const t x, fun t _ => ?_⟩
      have : accel g x 0 = 0 := by funext i; simp [accel]
      rw [this]
      exact hasDerivAt_const t 0
    · set τ := ‖v‖ / r
      have hτ : 0 < τ := div_pos (norm_pos_iff.mpr h0) hr
      have hτT : τ ≤ T := by
        rw [div_le_iff₀ hr]; linarith [mul_comm r T]
      have hsc := (hgeo _ (hu v h0)).scale τ
      refine ⟨1 / 2, by norm_num, fun t => γ _ (hu v h0) (τ * t),
        fun t => τ • w _ (hu v h0) (τ * t), by simp [hγ0], ?_, by simp [E, h0, τ], ?_⟩
      · simp only [mul_zero, hw0, smul_smul]
        rw [div_mul_div_comm, mul_comm (‖v‖) r, div_self (by positivity), one_smul]
      · refine ⟨fun t ht => hsc.pos t ?_, fun t ht => hsc.vel t ?_⟩ <;>
        · simp only [mem_preimage, mem_Ioo] at ht ⊢
          constructor <;> nlinarith [ht.1, ht.2, hτT, min_le_left (ε / 2) (R / (2 * β))]
  · intro v hv
    by_cases h0 : v = 0
    · simp [E, h0]
    · set τ := ‖v‖ / r
      have hτ : 0 < τ := div_pos (norm_pos_iff.mpr h0) hr
      have hτT : τ ≤ T := by
        rw [div_le_iff₀ hr]; linarith [mul_comm r T]
      have hest := geodesic_sub_le hR hA hr.le hB hT.le hTε (hgeo _ (hu v h0)) (hγ0 _ _)
        (by rw [hw0, ← sub_zero ((r / ‖v‖) • v)]; exact hu v h0) hTR ⟨hτ.le, hτT⟩
      rw [hw0, smul_smul, div_mul_div_comm, mul_comm (‖v‖) r, div_self (by positivity),
        one_smul] at hest
      simp only [E, h0, dite_false]
      calc ‖γ _ (hu v h0) τ - x - v‖ ≤ A * (r + R) ^ 2 * τ ^ 2 := hest
        _ = A * (r + R) ^ 2 / r ^ 2 * ‖v‖ ^ 2 := by simp only [τ]; field_simp

end Lightlike.Geodesic
