import Lightlike.Spacetime.CausalLadder.ConeTransfer

/-!
# The cone with a margin is stable under small relative perturbations, at nearby points

Let `a q` be the Gram matrix and `b q` the pairing with the time orientation, continuous at `p` as in
`ConeTransfer`. If `w` lies in the cone with margin `ε` at a point `q` near `p` and `u` is a perturbation
with `‖u‖ ≤ θ ‖w‖` for a fixed small `θ`, then `w + u` lies in the cone with margin `ε / 2` at every
point `q'` near `p`. A timelike curve with a margin can thus be perturbed, in a chart, by a displacement
whose derivative is small relative to the velocity, and stays timelike.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Filter Topology

namespace Lightlike.Causal

/-- A bound on the entries bounds the change of the quadratic form under a perturbation. -/
lemma abs_quadForm_add_sub_le {n : ℕ} (a : Fin n → Fin n → ℝ) {A : ℝ} (hA : ∀ i j, |a i j| ≤ A)
    (w u : Fin n → ℝ) :
    |quadForm a (w + u) - quadForm a w| ≤ A * n ^ 2 * (2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2) := by
  unfold quadForm
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (∑ j, (w + u) i * (w + u) j * a i j - ∑ j, w i * w j * a i j)|
      ≤ ∑ i, |∑ j, (w + u) i * (w + u) j * a i j - ∑ j, w i * w j * a i j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (n : ℝ) * (A * (2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        calc |∑ j, ((w + u) i * (w + u) j * a i j - w i * w j * a i j)|
            ≤ ∑ j, |(w + u) i * (w + u) j * a i j - w i * w j * a i j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin n, A * (2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have e : (w + u) i * (w + u) j * a i j - w i * w j * a i j =
                  a i j * (w i * u j + u i * w j + u i * u j) := by
                simp only [Pi.add_apply]; ring
              rw [e, abs_mul]
              have hwi : |w i| ≤ ‖w‖ := by simpa using norm_le_pi_norm w i
              have hwj : |w j| ≤ ‖w‖ := by simpa using norm_le_pi_norm w j
              have hui : |u i| ≤ ‖u‖ := by simpa using norm_le_pi_norm u i
              have huj : |u j| ≤ ‖u‖ := by simpa using norm_le_pi_norm u j
              have h1 : |w i * u j + u i * w j + u i * u j| ≤ 2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2 := by
                calc |w i * u j + u i * w j + u i * u j|
                    ≤ |w i * u j| + |u i * w j| + |u i * u j| := abs_add_three _ _ _
                  _ = |w i| * |u j| + |u i| * |w j| + |u i| * |u j| := by simp only [abs_mul]
                  _ ≤ ‖w‖ * ‖u‖ + ‖u‖ * ‖w‖ + ‖u‖ * ‖u‖ := by
                        gcongr
                  _ = 2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2 := by ring
              exact mul_le_mul (hA i j) h1 (abs_nonneg _) ((abs_nonneg _).trans (hA i j))
          _ = n * (A * (2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2)) := by simp
    _ = A * n ^ 2 * (2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2) := by simp; ring

/-- A bound on the entries bounds the linear form. -/
lemma abs_linForm_le {n : ℕ} (b : Fin n → ℝ) {B : ℝ} (hB : ∀ i, |b i| ≤ B) (u : Fin n → ℝ) :
    |linForm b u| ≤ n * B * ‖u‖ := by
  unfold linForm
  calc |∑ i, u i * b i| ≤ ∑ i, |u i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, B * ‖u‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        have hui : |u i| ≤ ‖u‖ := by simpa using norm_le_pi_norm u i
        calc |u i| * |b i| ≤ ‖u‖ * B := mul_le_mul hui (hB i) (abs_nonneg _) (norm_nonneg _)
          _ = B * ‖u‖ := by ring
    _ = n * B * ‖u‖ := by simp; ring

/-- The real inequalities behind `cone_margin_stable`. -/
lemma stable_arith {c ε r L L' Q Q' δ1 δ2 : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 0 < r)
    (hL : L ≤ -(r / (2 * c))) (hQ : Q ≤ -ε * L ^ 2) (hL' : |L' - L| ≤ r * δ1)
    (hQ' : |Q' - Q| ≤ r ^ 2 * δ2) (hδ1 : δ1 ≤ 1 / (12 * c)) (hδ2 : δ2 ≤ ε / (16 * c ^ 2)) :
    Q' ≤ -(ε / 2) * L' ^ 2 ∧ L' < 0 := by
  have hrc : 0 < r / (2 * c) := by positivity
  have hLneg : L < 0 := by linarith
  have h1 : r * δ1 ≤ r / (12 * c) := by
    calc r * δ1 ≤ r * (1 / (12 * c)) := mul_le_mul_of_nonneg_left hδ1 hr.le
      _ = r / (12 * c) := by ring
  have h2 : r / (12 * c) = (r / (2 * c)) / 6 := by field_simp; ring
  have hLa : L' ≤ L + r * δ1 := by linarith [(abs_le.1 hL').2]
  have hLb : L - r * δ1 ≤ L' := by linarith [(abs_le.1 hL').1]
  have hL'neg : L' < 0 := by linarith
  refine ⟨?_, hL'neg⟩
  -- `|L'| ≤ (7/6) |L|`
  have hr2 : r / (2 * c) ≤ -L := by linarith
  have hLL' : -L' ≤ (7 / 6) * (-L) := by linarith
  have hsq : L' ^ 2 ≤ (49 / 36) * L ^ 2 := by
    have h3 : 0 ≤ -L' := by linarith
    nlinarith [mul_self_le_mul_self h3 hLL']
  have hrL : r ^ 2 ≤ 4 * c ^ 2 * L ^ 2 := by
    have : r ≤ 2 * c * (-L) := by
      rw [div_le_iff₀ (by positivity)] at hr2
      linarith
    nlinarith [this, hr.le]
  have hQd : Q' ≤ Q + r ^ 2 * δ2 := by linarith [(abs_le.1 hQ').2]
  have h4 : r ^ 2 * δ2 ≤ (4 * c ^ 2 * L ^ 2) * (ε / (16 * c ^ 2)) :=
    mul_le_mul hrL hδ2 (by
      have : 0 ≤ δ2 := by
        by_contra hneg; push_neg at hneg
        have := mul_neg_of_pos_of_neg (pow_pos hr 2) hneg
        linarith [abs_nonneg (Q' - Q)]
      exact this) (by positivity)
  have h5 : (4 * c ^ 2 * L ^ 2) * (ε / (16 * c ^ 2)) = ε / 4 * L ^ 2 := by field_simp; ring
  nlinarith [sq_nonneg L, mul_nonneg hε.le (sq_nonneg L)]

lemma quadForm_sub_matrix {n : ℕ} (a a' : Fin n → Fin n → ℝ) (w : Fin n → ℝ) :
    quadForm a' w - quadForm a w = quadForm (fun i j => a' i j - a i j) w := by
  unfold quadForm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma linForm_sub_vec {n : ℕ} (b b' w : Fin n → ℝ) :
    linForm b' w - linForm b w = linForm (fun i => b' i - b i) w := by
  unfold linForm
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma linForm_add_right {n : ℕ} (b w u : Fin n → ℝ) :
    linForm b (w + u) = linForm b w + linForm b u := by
  unfold linForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]; ring

lemma abs_quadForm_entries {n : ℕ} (d : Fin n → Fin n → ℝ) {η : ℝ} (hd : ∀ i j, |d i j| ≤ η)
    (x : Fin n → ℝ) : |quadForm d x| ≤ η * n ^ 2 * ‖x‖ ^ 2 := by
  have := abs_quadForm_add_sub_le d hd 0 x
  simp only [zero_add, norm_zero, mul_zero, zero_mul, zero_add] at this
  have h0 : quadForm d 0 = 0 := by simp [quadForm]
  rw [h0, sub_zero] at this
  exact this

set_option maxHeartbeats 1000000 in
/-- **Stability of the cone with a margin.** See the module docstring. -/
theorem cone_margin_stable {Q : Type*} [TopologicalSpace Q] {n : ℕ} {p : Q}
    {a : Q → Fin n → Fin n → ℝ} {b : Q → Fin n → ℝ} (ha : ContinuousAt a p)
    (hb : ContinuousAt b p)
    (h0 : ∀ w : Fin n → ℝ, w ≠ 0 → quadForm (a p) w ≤ 0 → linForm (b p) w ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W ∈ 𝓝 p, ∃ θ > 0, ∀ q ∈ W, ∀ q' ∈ W, ∀ w u : Fin n → ℝ,
      quadForm (a q) w ≤ -ε * (linForm (b q) w) ^ 2 → linForm (b q) w < 0 → ‖u‖ ≤ θ * ‖w‖ →
        quadForm (a q') (w + u) ≤ -(ε / 2) * (linForm (b q') (w + u)) ^ 2 ∧
          linForm (b q') (w + u) < 0 := by
  obtain ⟨W0, hW0, c, hc, hcone⟩ := uniform_cone_bound ha hb h0
  -- bounds on the entries at `p`
  obtain ⟨A0, hA0⟩ := (Set.finite_range (fun ij : Fin n × Fin n => |a p ij.1 ij.2|)).bddAbove
  obtain ⟨B0, hB0⟩ := (Set.finite_range (fun i : Fin n => |b p i|)).bddAbove
  set A : ℝ := max A0 0 + 1 with hA
  set Bb : ℝ := max B0 0 + 1 with hBb
  have hA1 : 1 ≤ A := by have := le_max_right A0 0; linarith
  have hBb1 : 1 ≤ Bb := by have := le_max_right B0 0; linarith
  have hAp : ∀ i j, |a p i j| ≤ A - 1 := fun i j => by
    have := hA0 ⟨(i, j), rfl⟩
    have h2 := le_max_left A0 0
    simp only at this; linarith
  have hBp : ∀ i, |b p i| ≤ Bb - 1 := fun i => by
    have := hB0 ⟨i, rfl⟩
    have h2 := le_max_left B0 0
    simp only at this; linarith
  set n' : ℝ := (n : ℝ) + 1 with hn'
  have hn'pos : 0 < n' := by positivity
  set η : ℝ := min 1 (min (1 / (96 * c * n')) (ε / (256 * c ^ 2 * n' ^ 2))) with hη
  have hη0 : 0 < η := lt_min one_pos (lt_min (by positivity) (by positivity))
  set θ : ℝ := min 1 (min (1 / (24 * c * n' * (Bb + 1))) (ε / (96 * c ^ 2 * n' ^ 2 * (A + 1)))) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (lt_min (by positivity) (by positivity))
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
  refine ⟨_, (Filter.eventually_of_mem hW0 fun q hq => hq).and hevent, θ, hθ0, ?_⟩
  rintro q ⟨hq0, hqa, hqb⟩ q' ⟨hq'0, hqa', hqb'⟩ w u hmargin hL hu
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η ≤ 1 / (96 * c * n') := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ ε / (256 * c ^ 2 * n' ^ 2) := (min_le_right _ _).trans (min_le_right _ _)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθ2 : θ ≤ 1 / (24 * c * n' * (Bb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hθ3 : θ ≤ ε / (96 * c ^ 2 * n' ^ 2 * (A + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hw0 : w ≠ 0 := fun h => by simp [h, linForm] at hL
  have hcausal : quadForm (a q) w ≤ 0 := by nlinarith [sq_nonneg (linForm (b q) w)]
  have h1 := hcone q hq0 w hcausal hL
  set r := ‖w‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 hw0
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnn' : (n : ℝ) ≤ n' := by rw [hn']; linarith
  have hur : ‖u‖ ≤ r := hu.trans (by nlinarith)
  have hv : ‖w + u‖ ≤ 2 * r := (norm_add_le _ _).trans (by linarith)
  -- the linear form at `q`
  have hLd : |linForm (b q) w - linForm (b p) w| ≤ n * η * r := by
    rw [linForm_sub_vec]
    exact abs_linForm_le _ (fun i => hqb i) w
  have hnη : (n : ℝ) * η ≤ 1 / (2 * c) := by
    have h3 : (n : ℝ) * η ≤ n' * (1 / (96 * c * n')) :=
      mul_le_mul hnn' hη2 hη0.le hn'pos.le
    refine h3.trans ?_
    rw [show n' * (1 / (96 * c * n')) = 1 / (96 * c) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hLq : linForm (b q) w ≤ -(r / (2 * c)) := by
    have hLp : r / c ≤ -(linForm (b p) w) := by rw [div_le_iff₀ hc]; linarith
    have h5 : (n : ℝ) * η * r ≤ r / (2 * c) := by
      calc (n : ℝ) * η * r ≤ (1 / (2 * c)) * r := mul_le_mul_of_nonneg_right hnη hrpos.le
        _ = r / (2 * c) := by ring
    have h6 := (abs_le.1 hLd).2
    have : r / c = r / (2 * c) + r / (2 * c) := by field_simp; ring
    linarith
  -- perturbation of the linear form, from `(q, w)` to `(q', w + u)`
  have hbq : ∀ i, |b q i| ≤ Bb := fun i => by
    have := abs_sub_abs_le_abs_sub (b q i) (b p i)
    have h2 := hqb i
    have h3 := hBp i
    linarith
  have haq : ∀ i j, |a q i j| ≤ A := fun i j => by
    have := abs_sub_abs_le_abs_sub (a q i j) (a p i j)
    have h2 := hqa i j
    have h3 := hAp i j
    linarith
  have hL1 : |linForm (b q') (w + u) - linForm (b q) (w + u)| ≤ n * (2 * η) * (2 * r) := by
    rw [linForm_sub_vec]
    have hd : ∀ i, |b q' i - b q i| ≤ 2 * η := fun i => by
      have h2 := hqb i; have h3 := hqb' i
      calc |b q' i - b q i| = |(b q' i - b p i) - (b q i - b p i)| := by ring_nf
        _ ≤ |b q' i - b p i| + |b q i - b p i| := abs_sub _ _
        _ ≤ 2 * η := by linarith
    calc |linForm (fun i => b q' i - b q i) (w + u)| ≤ n * (2 * η) * ‖w + u‖ := abs_linForm_le _ hd _
      _ ≤ n * (2 * η) * (2 * r) := by
          apply mul_le_mul_of_nonneg_left hv; positivity
  have hL2 : |linForm (b q) (w + u) - linForm (b q) w| ≤ n * Bb * (θ * r) := by
    rw [linForm_add_right, add_sub_cancel_left]
    exact (abs_linForm_le _ hbq u).trans (mul_le_mul_of_nonneg_left hu (by positivity))
  have hLtot : |linForm (b q') (w + u) - linForm (b q) w| ≤ r * (4 * n * η + n * Bb * θ) := by
    have := abs_add_le (linForm (b q') (w + u) - linForm (b q) (w + u))
      (linForm (b q) (w + u) - linForm (b q) w)
    rw [show linForm (b q') (w + u) - linForm (b q) (w + u) + (linForm (b q) (w + u) - linForm (b q) w)
      = linForm (b q') (w + u) - linForm (b q) w by ring] at this
    nlinarith [this, hL1, hL2]
  -- perturbation of the quadratic form
  have hQ1 : |quadForm (a q') (w + u) - quadForm (a q) (w + u)| ≤ (2 * η) * n ^ 2 * (2 * r) ^ 2 := by
    rw [quadForm_sub_matrix]
    have hd : ∀ i j, |a q' i j - a q i j| ≤ 2 * η := fun i j => by
      have h2 := hqa i j; have h3 := hqa' i j
      calc |a q' i j - a q i j| = |(a q' i j - a p i j) - (a q i j - a p i j)| := by ring_nf
        _ ≤ |a q' i j - a p i j| + |a q i j - a p i j| := abs_sub _ _
        _ ≤ 2 * η := by linarith
    refine (abs_quadForm_entries _ hd _).trans ?_
    have hv0 : 0 ≤ ‖w + u‖ := norm_nonneg _
    have : ‖w + u‖ ^ 2 ≤ (2 * r) ^ 2 := by nlinarith
    have h0' : 0 ≤ 2 * η * (n : ℝ) ^ 2 := by positivity
    nlinarith
  have hQ2 : |quadForm (a q) (w + u) - quadForm (a q) w| ≤ A * n ^ 2 * (3 * θ * r ^ 2) := by
    refine (abs_quadForm_add_sub_le (a q) haq w u).trans ?_
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have : 2 * ‖w‖ * ‖u‖ + ‖u‖ ^ 2 ≤ 3 * θ * r ^ 2 := by
      have h1' : ‖u‖ ≤ θ * r := hu
      have h2' : ‖u‖ ^ 2 ≤ θ * r * r := by nlinarith
      nlinarith
    have hA0' : 0 ≤ A * (n : ℝ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left this hA0'
  have hQtot : |quadForm (a q') (w + u) - quadForm (a q) w| ≤
      r ^ 2 * (8 * n ^ 2 * η + 3 * A * n ^ 2 * θ) := by
    have := abs_add_le (quadForm (a q') (w + u) - quadForm (a q) (w + u))
      (quadForm (a q) (w + u) - quadForm (a q) w)
    rw [show quadForm (a q') (w + u) - quadForm (a q) (w + u) + (quadForm (a q) (w + u) - quadForm (a q) w)
      = quadForm (a q') (w + u) - quadForm (a q) w by ring] at this
    nlinarith [this, hQ1, hQ2]
  -- the parameters
  have hδ1 : 4 * n * η + n * Bb * θ ≤ 1 / (12 * c) := by
    have e1 : 4 * (n : ℝ) * η ≤ 1 / (24 * c) := by
      have : (n : ℝ) * η ≤ n' * (1 / (96 * c * n')) := mul_le_mul hnn' hη2 hη0.le hn'pos.le
      rw [show n' * (1 / (96 * c * n')) = 1 / (96 * c) by field_simp] at this
      have h4 : 4 * (1 / (96 * c)) = 1 / (24 * c) := by field_simp; ring
      linarith
    have e2 : (n : ℝ) * Bb * θ ≤ 1 / (24 * c) := by
      have : (n : ℝ) * Bb * θ ≤ n' * (Bb + 1) * (1 / (24 * c * n' * (Bb + 1))) := by
        apply mul_le_mul _ hθ2 hθ0.le (by positivity)
        exact mul_le_mul hnn' (by linarith) (by positivity) hn'pos.le
      refine this.trans (le_of_eq ?_)
      field_simp
    have : 1 / (24 * c) + 1 / (24 * c) = 1 / (12 * c) := by field_simp; ring
    linarith
  have hδ2 : 8 * (n : ℝ) ^ 2 * η + 3 * A * n ^ 2 * θ ≤ ε / (16 * c ^ 2) := by
    have e1 : 8 * (n : ℝ) ^ 2 * η ≤ ε / (32 * c ^ 2) := by
      have h7 : (n : ℝ) ^ 2 * η ≤ n' ^ 2 * (ε / (256 * c ^ 2 * n' ^ 2)) :=
        mul_le_mul (by nlinarith) hη3 hη0.le (by positivity)
      rw [show n' ^ 2 * (ε / (256 * c ^ 2 * n' ^ 2)) = ε / (256 * c ^ 2) by field_simp] at h7
      have : 8 * (ε / (256 * c ^ 2)) = ε / (32 * c ^ 2) := by field_simp; ring
      linarith
    have e2 : 3 * A * (n : ℝ) ^ 2 * θ ≤ ε / (32 * c ^ 2) := by
      have h8 : 3 * A * (n : ℝ) ^ 2 * θ ≤ 3 * A * n' ^ 2 * (ε / (96 * c ^ 2 * n' ^ 2 * (A + 1))) := by
        apply mul_le_mul _ hθ3 hθ0.le (by positivity)
        exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      refine h8.trans ?_
      have : 3 * A * n' ^ 2 * (ε / (96 * c ^ 2 * n' ^ 2 * (A + 1))) = (A / (A + 1)) * (ε / (32 * c ^ 2)) := by
        field_simp; ring
      rw [this]
      have hA' : A / (A + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hε' : 0 ≤ ε / (32 * c ^ 2) := by positivity
      nlinarith
    have : ε / (32 * c ^ 2) + ε / (32 * c ^ 2) = ε / (16 * c ^ 2) := by field_simp; ring
    linarith
  exact stable_arith hc hε hrpos hLq hmargin hLtot hQtot hδ1 hδ2

end Lightlike.Causal
