import Lightlike.Spacetime.CausalLadder.ConeStability

/-!
# Lifting a causal chart curve to a timelike one by a small shift

Estimates in a chart, in the frame coordinates of `exists_chart_model`: let `A x` be the Gram matrix and
`B x` the pairing with the time orientation at the point with chart coordinates `x`, `A` Lipschitz
(the metric is smooth) and `B` continuous, and `e` a future timelike vector at `x₀`. If a vector `w`
is future causal at `x`, then `w + ν λ(w) e`, with `λ(w) = -B x₀ ⬝ w` and `ν ∈ (0, 1]`, is future
timelike with a margin at every point `x'` at distance at most `ν m₀` from `x`, with `m₀` independent
of `ν`. The margin `ε` depends on `ν`, and the neighbourhood does not. This is the estimate behind
lifting a causal curve to a timelike curve by the displacement `-ν (λ(u d) - λ(u t)) e`, which is
proportional to the increase of the time function `λ ∘ u` and ends at the end of the curve
(the push-up lemma of causality theory).

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Filter Topology

namespace Lightlike.Causal


/-- The bilinear form of a matrix. -/
def bilForm {n : ℕ} (a : Fin n → Fin n → ℝ) (w e : Fin n → ℝ) : ℝ := ∑ i, ∑ j, w i * e j * a i j

/-- Expansion of the quadratic form of a symmetric matrix along `τ w + s e`. -/
lemma quadForm_comb {n : ℕ} {a : Fin n → Fin n → ℝ} (hs : ∀ i j, a i j = a j i) (w e : Fin n → ℝ)
    (τ s : ℝ) :
    quadForm a (τ • w + s • e) =
      τ ^ 2 * quadForm a w + 2 * τ * s * bilForm a w e + s ^ 2 * quadForm a e := by
  have h1 : ∑ i, ∑ j, e i * w j * a i j = bilForm a w e := by
    unfold bilForm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hs j i]; ring
  unfold quadForm
  simp only [bilForm] at h1 ⊢
  have : ∀ i j, (τ • w + s • e) i * (τ • w + s • e) j * a i j =
      τ ^ 2 * (w i * w j * a i j) + τ * s * (w i * e j * a i j) + τ * s * (e i * w j * a i j)
        + s ^ 2 * (e i * e j * a i j) := by
    intro i j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1]; ring

/-- The linear form of the pairing with `e`. -/
lemma linForm_pair {n : ℕ} (a : Fin n → Fin n → ℝ) (e w : Fin n → ℝ) :
    linForm (fun i => ∑ j, a i j * e j) w = bilForm a w e := by
  unfold linForm bilForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form is Lipschitz in the matrix, with the scaling by the squared norm. -/
lemma abs_quadForm_sub_le_mul {n : ℕ} (a a' : Fin n → Fin n → ℝ) (w : Fin n → ℝ) {η : ℝ}
    (h : ∀ i j, |a' i j - a i j| ≤ η) : |quadForm a' w - quadForm a w| ≤ n ^ 2 * η * ‖w‖ ^ 2 := by
  by_cases hw : w = 0
  · subst hw; simp [quadForm]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 := abs_quadForm_sub_le a a' (w := (‖w‖⁻¹) • w) (η := η)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']) h
  have e1 : ∀ b : Fin n → Fin n → ℝ, quadForm b ((‖w‖⁻¹) • w) = (‖w‖⁻¹) ^ 2 * quadForm b w :=
    fun b => quadForm_smul b _ w
  rw [e1, e1, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)] at h1
  have : |quadForm a' w - quadForm a w| ≤ (n ^ 2 * η) * ‖w‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖w‖)
    calc |quadForm a' w - quadForm a w| = ‖w‖ ^ 2 * ((‖w‖⁻¹) ^ 2 * |quadForm a' w - quadForm a w|) := by
          field_simp
      _ ≤ _ := by rw [mul_comm] at this ⊢; linarith
  linarith



/-- The real inequality behind `cone_lift_estimate`. -/
lemma lift_arith {N K m₀ c c₃ q₀ ν ℓ τ nrm Qw Bil Qe Q Q' V : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hℓ : 0 < ℓ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hK : 0 ≤ K) (hm : 0 < m₀) (hN : 0 ≤ N) (hc : 0 < c)
    (hc₃ : 0 < c₃) (hq₀ : 0 < q₀) (hnrm : 0 ≤ nrm)
    (hm1 : 2 * N ^ 2 * K * m₀ * c ^ 2 ≤ c₃ / 2) (hm2 : 2 * N ^ 2 * K * m₀ * nrm ^ 2 ≤ q₀ / 2)
    (hQw : Qw ≤ 0) (hBil : Bil ≤ -(c₃ * ℓ)) (hQe : Qe ≤ -q₀)
    (hexp : Q = τ ^ 2 * Qw + 2 * τ * (ν * ℓ) * Bil + (ν * ℓ) ^ 2 * Qe)
    (hloss : |Q' - Q| ≤ N ^ 2 * (K * ν * m₀) * V ^ 2) (hV0 : 0 ≤ V) (hV : V ≤ ℓ * (τ * c + ν * nrm)) :
    Q' ≤ -(ν * ℓ ^ 2) * (τ * c₃ + ν * q₀ / 2) := by
  have h1 : Q ≤ -2 * τ * ν * ℓ ^ 2 * c₃ - ν ^ 2 * ℓ ^ 2 * q₀ := by
    have a1 : τ ^ 2 * Qw ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hQw
    have a2 : 2 * τ * (ν * ℓ) * Bil ≤ 2 * τ * (ν * ℓ) * (-(c₃ * ℓ)) :=
      mul_le_mul_of_nonneg_left hBil (by positivity)
    have a3 : (ν * ℓ) ^ 2 * Qe ≤ (ν * ℓ) ^ 2 * (-q₀) :=
      mul_le_mul_of_nonneg_left hQe (sq_nonneg _)
    rw [hexp]; linarith
  have h2 : V ^ 2 ≤ 2 * ℓ ^ 2 * (τ * c ^ 2 + ν * nrm ^ 2) := by
    have : V ^ 2 ≤ (ℓ * (τ * c + ν * nrm)) ^ 2 := pow_le_pow_left₀ hV0 hV 2
    have h3 : (τ * c + ν * nrm) ^ 2 ≤ 2 * (τ * c ^ 2 + ν * nrm ^ 2) := by
      have : τ ^ 2 ≤ τ := pow_le_of_le_one hτ hτ1 two_ne_zero
      have : ν ^ 2 ≤ ν := pow_le_of_le_one hν.le hν1 two_ne_zero
      nlinarith [sq_nonneg (τ * c - ν * nrm)]
    calc V ^ 2 ≤ (ℓ * (τ * c + ν * nrm)) ^ 2 := this
      _ = ℓ ^ 2 * (τ * c + ν * nrm) ^ 2 := by ring
      _ ≤ ℓ ^ 2 * (2 * (τ * c ^ 2 + ν * nrm ^ 2)) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = 2 * ℓ ^ 2 * (τ * c ^ 2 + ν * nrm ^ 2) := by ring
  have h3 : N ^ 2 * (K * ν * m₀) * V ^ 2 ≤
      τ * ν * ℓ ^ 2 * (c₃ / 2) + ν ^ 2 * ℓ ^ 2 * (q₀ / 2) := by
    have hpos : 0 ≤ N ^ 2 * (K * ν * m₀) := by positivity
    calc N ^ 2 * (K * ν * m₀) * V ^ 2 ≤ N ^ 2 * (K * ν * m₀) * (2 * ℓ ^ 2 * (τ * c ^ 2 + ν * nrm ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hpos
      _ = ν * ℓ ^ 2 * (τ * (2 * N ^ 2 * K * m₀ * c ^ 2) + ν * (2 * N ^ 2 * K * m₀ * nrm ^ 2)) := by
          ring
      _ ≤ ν * ℓ ^ 2 * (τ * (c₃ / 2) + ν * (q₀ / 2)) := by
          gcongr
      _ = _ := by ring
  have h4 := (abs_le.1 hloss).2
  nlinarith [mul_nonneg hτ (mul_nonneg hν.le (sq_nonneg ℓ)), mul_pos hc₃ hν]


/-- The linear form is Lipschitz in the vector, with the scaling by the norm. -/
lemma abs_linForm_sub_le_mul {n : ℕ} (b b' : Fin n → ℝ) (w : Fin n → ℝ) {η : ℝ}
    (h : ∀ i, |b' i - b i| ≤ η) : |linForm b' w - linForm b w| ≤ n * η * ‖w‖ := by
  by_cases hw : w = 0
  · subst hw; simp [linForm]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 := abs_linForm_sub_le b b' (w := (‖w‖⁻¹) • w) (η := η)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']) h
  rw [linForm_smul, linForm_smul, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)] at h1
  have := mul_le_mul_of_nonneg_left h1 hn.le
  calc |linForm b' w - linForm b w| = ‖w‖ * (‖w‖⁻¹ * |linForm b' w - linForm b w|) := by
        field_simp
    _ ≤ ‖w‖ * (n * η) := this
    _ = n * η * ‖w‖ := by ring

lemma continuousAt_quadForm_apply {P : Type*} [TopologicalSpace P] {n : ℕ} {x₀ : P}
    {A : P → Fin n → Fin n → ℝ} (hA : ContinuousAt A x₀) (w : Fin n → ℝ) :
    ContinuousAt (fun x => quadForm (A x) w) x₀ := by
  unfold quadForm
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    continuousAt_const.mul (continuousAt_pi.1 (continuousAt_pi.1 hA i) j)

lemma continuousAt_linForm_apply {P : Type*} [TopologicalSpace P] {n : ℕ} {x₀ : P}
    {B : P → Fin n → ℝ} (hB : ContinuousAt B x₀) (w : Fin n → ℝ) :
    ContinuousAt (fun x => linForm (B x) w) x₀ := by
  unfold linForm
  exact tendsto_finsetSum _ fun i _ => continuousAt_const.mul (continuousAt_pi.1 hB i)


set_option maxHeartbeats 2000000 in
/-- **A causal vector plus a small multiple of a timelike vector has a margin.** See the module
docstring. -/
theorem cone_lift_estimate {P : Type*} [MetricSpace P] {n : ℕ} {x₀ : P}
    {A : P → Fin n → Fin n → ℝ} {B : P → Fin n → ℝ} {e : Fin n → ℝ}
    (hAc : ContinuousAt A x₀) (hBc : ContinuousAt B x₀) (hsymm : ∀ x i j, A x i j = A x j i)
    {K r₀ : ℝ} (hK0 : 0 ≤ K) (hr₀ : 0 < r₀)
    (hK : ∀ x ∈ Metric.ball x₀ r₀, ∀ x' ∈ Metric.ball x₀ r₀, ∀ i j,
      |A x' i j - A x i j| ≤ K * dist x' x)
    (h0 : ∀ w : Fin n → ℝ, w ≠ 0 → quadForm (A x₀) w ≤ 0 → linForm (B x₀) w ≠ 0)
    (h0e : ∀ w : Fin n → ℝ, w ≠ 0 → quadForm (A x₀) w ≤ 0 → bilForm (A x₀) w e ≠ 0)
    (hbil : ∀ x ∈ Metric.ball x₀ r₀, ∀ w : Fin n → ℝ, quadForm (A x) w ≤ 0 → linForm (B x) w < 0 →
      bilForm (A x) w e < 0)
    (hsgn : ∀ x ∈ Metric.ball x₀ r₀, ∀ z : Fin n → ℝ, quadForm (A x) z < 0 → linForm (B x) z ≠ 0)
    (heq : quadForm (A x₀) e < 0) (hel : linForm (B x₀) e < 0) :
    ∃ m₀ > 0, ∃ r₁ > 0, r₁ ≤ r₀ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∃ ε > 0,
      ∀ x ∈ Metric.ball x₀ r₁, ∀ x' ∈ Metric.ball x₀ r₁, dist x' x ≤ ν * m₀ →
      ∀ w : Fin n → ℝ, quadForm (A x) w ≤ 0 → linForm (B x) w < 0 →
        0 < -(linForm (B x₀) w) ∧
        quadForm (A x') (w + (ν * (-(linForm (B x₀) w))) • e) ≤
            -ε * (linForm (B x') (w + (ν * (-(linForm (B x₀) w))) • e)) ^ 2 ∧
          linForm (B x') (w + (ν * (-(linForm (B x₀) w))) • e) < 0 := by
  classical
  obtain ⟨W₁, hW₁, c, hc, hcone⟩ := uniform_cone_bound hAc hBc h0
  obtain ⟨Be, hBe⟩ : ∃ Be : P → Fin n → ℝ, Be = fun x i => ∑ j, A x i j * e j := ⟨_, rfl⟩
  have hAij : ∀ i j, ContinuousAt (fun x => A x i j) x₀ := fun i j =>
    continuousAt_pi.1 (continuousAt_pi.1 hAc i) j
  have hBec : ContinuousAt Be x₀ :=
    by rw [hBe]; exact continuousAt_pi.2 fun i => tendsto_finsetSum _ fun j _ => (hAij i j).mul continuousAt_const
  have hlinBe : ∀ x w, linForm (Be x) w = bilForm (A x) w e := fun x w => by
    rw [hBe]; exact linForm_pair (A x) e w
  have h0' : ∀ w : Fin n → ℝ, w ≠ 0 → quadForm (A x₀) w ≤ 0 → linForm (Be x₀) w ≠ 0 :=
    fun w hw hq => by rw [hlinBe]; exact h0e w hw hq
  obtain ⟨W₂, hW₂, ce, hce, hcone2⟩ := uniform_cone_bound hAc hBec h0'
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) + 1 := ⟨_, rfl⟩
  have hN1 : (n : ℝ) ≤ N := by rw [hN]; linarith
  have hN0 : 0 < N := by rw [hN]; positivity
  obtain ⟨Bb, hBb⟩ : ∃ Bb : ℝ, Bb = ∑ i, |B x₀ i| + 1 := ⟨_, rfl⟩
  have hsumnn : 0 ≤ ∑ i, |B x₀ i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBb1 : 1 ≤ Bb := by rw [hBb]; linarith
  have hBb0 : 0 < Bb := by linarith
  have hBx0 : ∀ i, |B x₀ i| + 1 ≤ Bb := fun i => by
    have h : |B x₀ i| ≤ ∑ j, |B x₀ j| :=
      Finset.single_le_sum (f := fun i => |B x₀ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hBb]; linarith
  obtain ⟨q₀, hq₀def⟩ : ∃ q₀ : ℝ, q₀ = -quadForm (A x₀) e / 2 := ⟨_, rfl⟩
  have hq₀ : 0 < q₀ := by rw [hq₀def]; linarith
  have ev_q : ∀ᶠ x in 𝓝 x₀, quadForm (A x) e < -q₀ :=
    (continuousAt_quadForm_apply hAc e).eventually (gt_mem_nhds (by rw [hq₀def]; linarith))
  have ev_B : ∀ᶠ x in 𝓝 x₀, ∀ i, |B x i| ≤ Bb := by
    have : ∀ i, ∀ᶠ x in 𝓝 x₀, |B x i| < |B x₀ i| + 1 := fun i =>
      ((continuousAt_pi.1 hBc i).abs).eventually (gt_mem_nhds (by linarith))
    exact Filter.eventually_all.2 fun i => (this i).mono fun x hx => by linarith [hx, hBx0 i]
  have ev_L : ∀ᶠ x in 𝓝 x₀, linForm (B x) e < 0 :=
    (continuousAt_linForm_apply hBc e).eventually (gt_mem_nhds hel)
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : ℝ, η₁ = 1 / (2 * ce * N) := ⟨_, rfl⟩
  have hη₁pos : 0 < η₁ := by rw [hη₁]; positivity
  have ev_Be : ∀ᶠ x in 𝓝 x₀, ∀ i, |Be x i - Be x₀ i| ≤ η₁ := by
    have : ∀ i, ∀ᶠ x in 𝓝 x₀, |Be x i - Be x₀ i| < η₁ := fun i =>
      (((continuousAt_pi.1 hBec i).sub continuousAt_const).abs).eventually
        (gt_mem_nhds (by simpa using hη₁pos))
    exact Filter.eventually_all.2 fun i => (this i).mono fun x hx => hx.le
  have hnhds : {x | x ∈ W₁ ∧ x ∈ W₂ ∧ quadForm (A x) e < -q₀ ∧ (∀ i, |B x i| ≤ Bb) ∧
      linForm (B x) e < 0 ∧ (∀ i, |Be x i - Be x₀ i| ≤ η₁)} ∈ 𝓝 x₀ := by
    filter_upwards [hW₁, hW₂, ev_q, ev_B, ev_L, ev_Be] with x h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.1 hnhds
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ℝ, r₁ = min r' r₀ := ⟨_, rfl⟩
  have hr₁pos : 0 < r₁ := by rw [hr₁]; exact lt_min hr' hr₀
  have hr₁r' : Metric.ball x₀ r₁ ⊆ Metric.ball x₀ r' := by
    rw [hr₁]; exact Metric.ball_subset_ball (min_le_left _ _)
  have hr₁r₀ : Metric.ball x₀ r₁ ⊆ Metric.ball x₀ r₀ := by
    rw [hr₁]; exact Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : ℝ, c₃ = 1 / (2 * ce * N * Bb) := ⟨_, rfl⟩
  have hc₃pos : 0 < c₃ := by rw [hc₃]; positivity
  obtain ⟨en, hen⟩ : ∃ en : ℝ, en = ‖e‖ := ⟨_, rfl⟩
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = min (c₃ / (4 * N ^ 2 * (K + 1) * c ^ 2))
    (q₀ / (4 * N ^ 2 * (K + 1) * (en ^ 2 + 1))) := ⟨_, rfl⟩
  have hK1 : 0 < K + 1 := by linarith
  have hm₀pos : 0 < m₀ := by rw [hm₀]; exact lt_min (by positivity) (by positivity)
  have hm1 : 2 * N ^ 2 * K * m₀ * c ^ 2 ≤ c₃ / 2 := by
    have h := (le_div_iff₀ (by positivity)).1 (hm₀ ▸ min_le_left (c₃ / (4 * N ^ 2 * (K + 1) * c ^ 2))
      (q₀ / (4 * N ^ 2 * (K + 1) * (en ^ 2 + 1))))
    have hpos : 0 ≤ 2 * N ^ 2 * m₀ * c ^ 2 := by positivity
    linarith
  have hm2 : 2 * N ^ 2 * K * m₀ * en ^ 2 ≤ q₀ / 2 := by
    have h := (le_div_iff₀ (by positivity)).1 (hm₀ ▸ min_le_right (c₃ / (4 * N ^ 2 * (K + 1) * c ^ 2))
      (q₀ / (4 * N ^ 2 * (K + 1) * (en ^ 2 + 1))))
    have hpos : 0 ≤ 2 * N ^ 2 * m₀ * en ^ 2 := by positivity
    nlinarith [sq_nonneg en, mul_nonneg (mul_nonneg hN0.le hN0.le) (mul_nonneg hm₀pos.le (sq_nonneg en))]
  have hen0 : 0 ≤ en := by rw [hen]; exact norm_nonneg _
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = N * Bb * (c + en) := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; positivity
  refine ⟨m₀, hm₀pos, r₁, hr₁pos, by rw [hr₁]; exact min_le_right _ _, fun ν hν hν1 => ?_⟩
  refine ⟨ν * c₃ / M ^ 2, by positivity, fun x hx x' hx' hd w hq hl => ?_⟩
  obtain ⟨hxW1, hxW2, hxq, hxB, hxL, hxBe⟩ := hsub (hr₁r' hx)
  obtain ⟨-, -, -, hxB', hxL', -⟩ := hsub (hr₁r' hx')
  have hxr₀ := hr₁r₀ hx
  have hx'r₀ := hr₁r₀ hx'
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = -linForm (B x₀) w := ⟨_, rfl⟩
  have hwc : ‖w‖ ≤ c * ℓ := by rw [hℓdef]; exact hcone x hxW1 w hq hl
  have hw0 : w ≠ 0 := by rintro rfl; simp [linForm] at hl
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hℓ : 0 < ℓ := by
    by_contra h
    push Not at h
    nlinarith
  have hℓn : ℓ ≤ N * Bb * ‖w‖ := by
    have h1 := abs_linForm_le (B x₀) (B := Bb) (fun i => by linarith [hBx0 i, abs_nonneg (B x₀ i)]) w
    have h2 : -linForm (B x₀) w ≤ |linForm (B x₀) w| := neg_le_abs _
    have h3 : (n : ℝ) * Bb * ‖w‖ ≤ N * Bb * ‖w‖ := by gcongr
    rw [hℓdef]; linarith
  have hbilx : bilForm (A x) w e < 0 := hbil x hxr₀ w hq hl
  have hbil2 : ‖w‖ ≤ ce * (-(linForm (Be x₀) w)) :=
    hcone2 x hxW2 w hq (by rw [hlinBe]; exact hbilx)
  have hdiff : |linForm (Be x) w - linForm (Be x₀) w| ≤ ‖w‖ / (2 * ce) := by
    have h1 := abs_linForm_sub_le_mul (Be x₀) (Be x) w hxBe
    have h2 : (n : ℝ) * η₁ * ‖w‖ ≤ ‖w‖ / (2 * ce) := by
      have : (n : ℝ) * η₁ ≤ 1 / (2 * ce) := by
        have e1 : N * η₁ = 1 / (2 * ce) := by rw [hη₁]; field_simp
        calc (n : ℝ) * η₁ ≤ N * η₁ := by gcongr
          _ = 1 / (2 * ce) := e1
      calc (n : ℝ) * η₁ * ‖w‖ ≤ 1 / (2 * ce) * ‖w‖ := by gcongr
        _ = ‖w‖ / (2 * ce) := by ring
    linarith
  have hbilbound : bilForm (A x) w e ≤ -(c₃ * ℓ) := by
    have h1 : linForm (Be x₀) w ≤ -(‖w‖ / ce) := by
      have : ‖w‖ / ce ≤ -(linForm (Be x₀) w) := by
        rw [div_le_iff₀ hce]; linarith
      linarith
    have h2 : linForm (Be x) w ≤ linForm (Be x₀) w + ‖w‖ / (2 * ce) := by
      linarith [(abs_le.1 hdiff).2]
    have h3 : ℓ / (N * Bb) ≤ ‖w‖ := by
      rw [div_le_iff₀ (by positivity)]; linarith [hℓn, mul_comm ‖w‖ (N * Bb)]
    have h4 : c₃ * ℓ = ℓ / (N * Bb) / (2 * ce) := by rw [hc₃]; field_simp
    have h5 : ℓ / (N * Bb) / (2 * ce) ≤ ‖w‖ / (2 * ce) := by gcongr
    have h6 : ‖w‖ / ce = 2 * (‖w‖ / (2 * ce)) := by field_simp
    rw [← hlinBe]
    linarith
  have hnorm0 : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ‖τ • w + (ν * ℓ) • e‖ ≤ ℓ * (τ * c + ν * en) := by
    intro τ hτ hτ1
    calc ‖τ • w + (ν * ℓ) • e‖ ≤ ‖τ • w‖ + ‖(ν * ℓ) • e‖ := norm_add_le _ _
      _ = τ * ‖w‖ + ν * ℓ * en := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hτ, Real.norm_of_nonneg (by positivity), hen]
      _ ≤ τ * (c * ℓ) + ν * ℓ * en := by gcongr
      _ = ℓ * (τ * c + ν * en) := by ring
  have claim : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      quadForm (A x') (τ • w + (ν * ℓ) • e) ≤ -(ν * ℓ ^ 2) * (τ * c₃ + ν * q₀ / 2) := by
    intro τ hτ hτ1
    have hexp := quadForm_comb (hsymm x) w e τ (ν * ℓ)
    have hloss := abs_quadForm_sub_le_mul (A x) (A x') (τ • w + (ν * ℓ) • e) (η := K * (ν * m₀))
      (fun i j => (hK x hxr₀ x' hx'r₀ i j).trans (mul_le_mul_of_nonneg_left hd hK0))
    have hloss' : |quadForm (A x') (τ • w + (ν * ℓ) • e) - quadForm (A x) (τ • w + (ν * ℓ) • e)| ≤
        N ^ 2 * (K * ν * m₀) * ‖τ • w + (ν * ℓ) • e‖ ^ 2 := by
      refine hloss.trans ?_
      have : (n : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN1 2
      have h2 : 0 ≤ K * (ν * m₀) * ‖τ • w + (ν * ℓ) • e‖ ^ 2 := by positivity
      linarith [mul_le_mul_of_nonneg_right this h2]
    exact lift_arith (N := N) (K := K) (m₀ := m₀) (c := c) (c₃ := c₃) (q₀ := q₀) (ν := ν) (ℓ := ℓ)
      (τ := τ) (nrm := en) hν hν1 hℓ hτ hτ1 hK0 hm₀pos hN0.le hc hc₃pos hq₀ hen0 hm1 hm2
      hq hbilbound hxq.le hexp hloss' (norm_nonneg _) (hnorm0 τ hτ hτ1)
  have hneg : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → quadForm (A x') (τ • w + (ν * ℓ) • e) < 0 := fun τ h1 h2 =>
    lt_of_le_of_lt (claim τ h1 h2) (by
      have : 0 < ν * ℓ ^ 2 * (τ * c₃ + ν * q₀ / 2) := by positivity
      linarith)
  have hcont : ContinuousOn (fun τ : ℝ => linForm (B x') (τ • w + (ν * ℓ) • e)) (Set.Icc 0 1) :=
    ((continuous_linForm (B x')).comp
      ((continuous_id.smul continuous_const).add continuous_const)).continuousOn
  have hf0 : linForm (B x') ((0 : ℝ) • w + (ν * ℓ) • e) < 0 := by
    rw [zero_smul, zero_add, linForm_smul]
    exact mul_neg_of_pos_of_neg (by positivity) hxL'
  have hf1 : linForm (B x') ((1 : ℝ) • w + (ν * ℓ) • e) < 0 := by
    by_contra h
    push Not at h
    have hne : linForm (B x') ((1 : ℝ) • w + (ν * ℓ) • e) ≠ 0 :=
      hsgn x' hx'r₀ _ (hneg 1 zero_le_one le_rfl)
    have hpos : 0 < linForm (B x') ((1 : ℝ) • w + (ν * ℓ) • e) := lt_of_le_of_ne h (Ne.symm hne)
    obtain ⟨τ, hτ, hz⟩ := intermediate_value_Icc zero_le_one hcont
      (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨hf0.le, hpos.le⟩)
    exact hsgn x' hx'r₀ _ (hneg τ hτ.1 hτ.2) hz
  rw [one_smul] at hf1
  rw [← hℓdef]
  refine ⟨hℓ, ?_, hf1⟩
  have hQ1 := claim 1 zero_le_one le_rfl
  rw [one_smul] at hQ1
  have hlin : |linForm (B x') (w + (ν * ℓ) • e)| ≤ ℓ * M := by
    have h1 := abs_linForm_le (B x') (B := Bb) hxB' (w + (ν * ℓ) • e)
    have h2 := hnorm0 1 zero_le_one le_rfl
    rw [one_smul] at h2
    have h3 : (n : ℝ) * Bb * ‖w + (ν * ℓ) • e‖ ≤ N * Bb * (ℓ * (1 * c + ν * en)) := by
      calc (n : ℝ) * Bb * ‖w + (ν * ℓ) • e‖ ≤ N * Bb * ‖w + (ν * ℓ) • e‖ := by gcongr
        _ ≤ N * Bb * (ℓ * (1 * c + ν * en)) := by gcongr
    have h4 : N * Bb * (ℓ * (1 * c + ν * en)) ≤ ℓ * M := by
      rw [hM]
      have : ν * en ≤ en := mul_le_of_le_one_left hen0 hν1
      nlinarith [mul_pos hN0 hBb0, mul_pos (mul_pos hN0 hBb0) hℓ]
    linarith
  have hsq : linForm (B x') (w + (ν * ℓ) • e) ^ 2 ≤ (ℓ * M) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hlin 2
  have hε : 0 ≤ ν * c₃ / M ^ 2 := by positivity
  have hfin : -(ν * c₃ / M ^ 2) * (ℓ * M) ^ 2 = -(ν * c₃ * ℓ ^ 2) := by field_simp
  have hQ2 : quadForm (A x') (w + (ν * ℓ) • e) ≤ -(ν * c₃ * ℓ ^ 2) := by
    refine hQ1.trans ?_
    have : 0 ≤ ν * ℓ ^ 2 * (ν * q₀ / 2) := by positivity
    linarith
  calc quadForm (A x') (w + (ν * ℓ) • e) ≤ -(ν * c₃ * ℓ ^ 2) := hQ2
    _ = -(ν * c₃ / M ^ 2) * (ℓ * M) ^ 2 := hfin.symm
    _ ≤ -(ν * c₃ / M ^ 2) * linForm (B x') (w + (ν * ℓ) • e) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hsq hε
        linarith

end Lightlike.Causal
