import Lightlike.Spacetime.CausalLadder.UniformCone

/-!
# A cone with a margin at a nearby point lies in the strict cone at the base point

Let `a q` be a symmetric-matrix-valued and `b q` a vector-valued function, both continuous at `p`
(the Gram matrix of a Lorentzian metric in a frame, and its pairing with the time orientation), and
suppose that at `p` no nonzero `w` with `wᵀ a(p) w ≤ 0` has `b(p) ⬝ w = 0`. If `w` lies in the cone with
margin `ε` at a point `q` near `p` (`wᵀ a(q) w ≤ -ε (b(q) ⬝ w)²` and `b(q) ⬝ w < 0`), then `w` lies in
the strict future timelike cone at `p` (`wᵀ a(p) w < 0` and `b(p) ⬝ w < 0`). In a chart this says that
the velocity of a timelike curve with a margin, near a point `p`, is a timelike vector at `p`, which is
what is needed to average the velocity of a curve and to perturb the end of a timelike curve.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Filter Topology

namespace Lightlike.Causal

/-- **The cone with a margin near `p` is inside the strict cone at `p`.** -/
theorem cone_margin_transfer {Q : Type*} [TopologicalSpace Q] {n : ℕ} {p : Q}
    {a : Q → Fin n → Fin n → ℝ} {b : Q → Fin n → ℝ} (ha : ContinuousAt a p)
    (hb : ContinuousAt b p)
    (h0 : ∀ w : Fin n → ℝ, w ≠ 0 → quadForm (a p) w ≤ 0 → linForm (b p) w ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W ∈ 𝓝 p, ∀ q ∈ W, ∀ w : Fin n → ℝ,
      quadForm (a q) w ≤ -ε * (linForm (b q) w) ^ 2 → linForm (b q) w < 0 →
        quadForm (a p) w < 0 ∧ linForm (b p) w < 0 := by
  obtain ⟨W0, hW0, c, hc, hcone⟩ := uniform_cone_bound ha hb h0
  set η : ℝ := min (1 / (2 * c * (n + 1))) (ε / (8 * c ^ 2 * (n ^ 2 + 1))) with hη
  have hη0 : 0 < η := by
    have : 0 < (n : ℝ) + 1 := by positivity
    have : 0 < (n : ℝ) ^ 2 + 1 := by positivity
    exact lt_min (by positivity) (by positivity)
  have hevent : ∀ᶠ q in 𝓝 p, (∀ i j, |a q i j - a p i j| ≤ η) ∧ (∀ i, |b q i - b p i| ≤ η) := by
    refine (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_).and
      (Filter.eventually_all.2 fun i => ?_)
    · have h1 : ContinuousAt (fun q => a q i j) p :=
        (continuousAt_pi.1 (continuousAt_pi.1 ha i) j)
      filter_upwards [h1.eventually (Metric.closedBall_mem_nhds _ hη0)] with q hq
      simpa [Real.dist_eq, abs_sub_comm] using hq
    · have h1 : ContinuousAt (fun q => b q i) p := continuousAt_pi.1 hb i
      filter_upwards [h1.eventually (Metric.closedBall_mem_nhds _ hη0)] with q hq
      simpa [Real.dist_eq, abs_sub_comm] using hq
  refine ⟨_, (Filter.eventually_of_mem hW0 fun q hq => hq).and hevent, ?_⟩
  rintro q ⟨hq0, hqa, hqb⟩ w hmargin hL
  have hw0 : w ≠ 0 := fun h => by simp [h, linForm] at hL
  have hcausal : quadForm (a q) w ≤ 0 := by nlinarith [sq_nonneg (linForm (b q) w)]
  have h1 := hcone q hq0 w hcausal hL
  set r := ‖w‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 hw0
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- scaling to the unit sphere
  have hu : ‖r⁻¹ • w‖ ≤ 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hrpos.ne']
  have hwu : w = r • (r⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
  have hQ := abs_quadForm_sub_le (a p) (a q) hu hqa
  have hLb := abs_linForm_sub_le (b p) (b q) hu hqb
  have hQs : |quadForm (a q) w - quadForm (a p) w| ≤ n ^ 2 * η * r ^ 2 := by
    have e : ∀ x : Fin n → Fin n → ℝ, quadForm x w = r ^ 2 * quadForm x (r⁻¹ • w) := fun x => by
      conv_lhs => rw [hwu]
      rw [quadForm_smul]
    rw [e (a q), e (a p), ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
    calc r ^ 2 * |quadForm (a q) (r⁻¹ • w) - quadForm (a p) (r⁻¹ • w)| ≤ r ^ 2 * (n ^ 2 * η) :=
          mul_le_mul_of_nonneg_left hQ (sq_nonneg r)
      _ = n ^ 2 * η * r ^ 2 := by ring
  have hLs : |linForm (b q) w - linForm (b p) w| ≤ n * η * r := by
    have e : ∀ x : Fin n → ℝ, linForm x w = r * linForm x (r⁻¹ • w) := fun x => by
      conv_lhs => rw [hwu]
      rw [linForm_smul]
    rw [e (b q), e (b p), ← mul_sub, abs_mul, abs_of_nonneg hrpos.le]
    calc r * |linForm (b q) (r⁻¹ • w) - linForm (b p) (r⁻¹ • w)| ≤ r * (n * η) :=
          mul_le_mul_of_nonneg_left hLb hrpos.le
      _ = n * η * r := by ring
  have hη1 : η ≤ 1 / (2 * c * (n + 1)) := min_le_left _ _
  have hη2 : η ≤ ε / (8 * c ^ 2 * (n ^ 2 + 1)) := min_le_right _ _
  have hnη : (n : ℝ) * η ≤ 1 / (2 * c) := by
    have h3 : (n : ℝ) * η ≤ n * (1 / (2 * c * (n + 1))) := mul_le_mul_of_nonneg_left hη1 hn
    refine h3.trans ?_
    rw [show (n : ℝ) * (1 / (2 * c * (n + 1))) = (1 / (2 * c)) * (n / (n + 1)) by field_simp]
    have : (n : ℝ) / (n + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h2c : 0 ≤ 1 / (2 * c) := by positivity
    nlinarith
  have hn2η : (n : ℝ) ^ 2 * η ≤ ε / (8 * c ^ 2) := by
    have h3 : (n : ℝ) ^ 2 * η ≤ (n ^ 2 + 1) * (ε / (8 * c ^ 2 * (n ^ 2 + 1))) := by
      have : (n : ℝ) ^ 2 ≤ n ^ 2 + 1 := by linarith
      exact mul_le_mul this hη2 hη0.le (by positivity)
    refine h3.trans (le_of_eq ?_)
    field_simp
  -- the linear form at p
  have hLp : linForm (b p) w ≤ -(r / c) := by
    have : r / c ≤ -(linForm (b p) w) := by rw [div_le_iff₀ hc]; linarith
    linarith
  have hLpneg : linForm (b p) w < 0 := by
    have : 0 < r / c := by positivity
    linarith
  have hLq : r / (2 * c) ≤ -(linForm (b q) w) := by
    have h5 : n * η * r ≤ r / (2 * c) := by
      calc n * η * r ≤ (1 / (2 * c)) * r := mul_le_mul_of_nonneg_right hnη hrpos.le
        _ = r / (2 * c) := by ring
    have h6 := (abs_le.1 hLs).2
    have : r / c = r / (2 * c) + r / (2 * c) := by field_simp; ring
    linarith
  refine ⟨?_, hLpneg⟩
  have hLq2 : (r / (2 * c)) ^ 2 ≤ (linForm (b q) w) ^ 2 := by
    have h7 : 0 ≤ r / (2 * c) := by positivity
    nlinarith
  have h8 := (abs_le.1 hQs).1
  have h9 : -ε * (linForm (b q) w) ^ 2 ≤ -ε * (r / (2 * c)) ^ 2 := by nlinarith
  have h10 : ε * (r / (2 * c)) ^ 2 = ε / (4 * c ^ 2) * r ^ 2 := by field_simp; ring
  have h11 : (n : ℝ) ^ 2 * η * r ^ 2 ≤ ε / (8 * c ^ 2) * r ^ 2 :=
    mul_le_mul_of_nonneg_right hn2η (sq_nonneg r)
  have h12 : 0 < ε / (8 * c ^ 2) * r ^ 2 := by positivity
  have h13 : ε / (4 * c ^ 2) * r ^ 2 = 2 * (ε / (8 * c ^ 2) * r ^ 2) := by field_simp; ring
  linarith

end Lightlike.Causal
