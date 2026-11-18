import Mathlib

/-!
# A uniform bound for vectors of a slowly varying cone

Let `a q` be a symmetric-matrix-valued and `b q` a vector-valued function, both continuous at `p`.
Think of `a q` as the Gram matrix of a Lorentzian metric in a frame and of `b q` as the pairing of
the frame with the time orientation. If at `p` no nonzero vector `w` has both `wᵀ a w ≤ 0` and
`b ⬝ w = 0` (a causal vector is not orthogonal to the time orientation), then near `p` every `w`
with `wᵀ a(q) w ≤ 0` and `b(q) ⬝ w < 0` (future causal) is controlled by the fixed functional
`-(b(p) ⬝ w)`: `‖w‖ ≤ c · (-(b(p) ⬝ w))`.

The proof is a compactness argument on the unit sphere of `Fin n → ℝ`, without sequences.

Supporting lemma for the causal ladder; no catalogue entry.
-/

namespace Lightlike.Causal

open Filter Topology

/-- The quadratic form of a matrix. -/
def quadForm {n : ℕ} (a : Fin n → Fin n → ℝ) (w : Fin n → ℝ) : ℝ := ∑ i, ∑ j, w i * w j * a i j

/-- The linear form of a vector. -/
def linForm {n : ℕ} (b : Fin n → ℝ) (w : Fin n → ℝ) : ℝ := ∑ i, w i * b i

lemma continuous_quadForm {n : ℕ} (a : Fin n → Fin n → ℝ) : Continuous (quadForm a) := by
  unfold quadForm; fun_prop

lemma continuous_linForm {n : ℕ} (b : Fin n → ℝ) : Continuous (linForm b) := by
  unfold linForm; fun_prop

lemma quadForm_smul {n : ℕ} (a : Fin n → Fin n → ℝ) (r : ℝ) (w : Fin n → ℝ) :
    quadForm a (r • w) = r ^ 2 * quadForm a w := by
  unfold quadForm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma linForm_smul {n : ℕ} (b : Fin n → ℝ) (r : ℝ) (w : Fin n → ℝ) :
    linForm b (r • w) = r * linForm b w := by
  unfold linForm
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- On the unit sphere, nearby matrices give nearby quadratic forms. -/
lemma abs_quadForm_sub_le {n : ℕ} (a a' : Fin n → Fin n → ℝ) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1)
    {η : ℝ} (h : ∀ i j, |a' i j - a i j| ≤ η) : |quadForm a' w - quadForm a w| ≤ n ^ 2 * η := by
  have hw' : ∀ i, |w i| ≤ 1 := fun i => by simpa using (norm_le_pi_norm w i).trans hw
  unfold quadForm
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (∑ j, w i * w j * a' i j - ∑ j, w i * w j * a i j)|
      ≤ ∑ i, |∑ j, w i * w j * a' i j - ∑ j, w i * w j * a i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (n : ℝ) * η := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        calc |∑ j, (w i * w j * a' i j - w i * w j * a i j)|
            ≤ ∑ j, |w i * w j * a' i j - w i * w j * a i j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin n, η := by
              refine Finset.sum_le_sum fun j _ => ?_
              have : w i * w j * a' i j - w i * w j * a i j = (w i * w j) * (a' i j - a i j) := by ring
              rw [this, abs_mul, abs_mul]
              have h1 := hw' i
              have h2 := hw' j
              have h3 := h i j
              have : |w i| * |w j| ≤ 1 := by nlinarith [abs_nonneg (w i), abs_nonneg (w j)]
              calc |w i| * |w j| * |a' i j - a i j| ≤ 1 * |a' i j - a i j| :=
                    mul_le_mul_of_nonneg_right this (abs_nonneg _)
                _ ≤ η := by linarith
          _ = n * η := by simp
    _ = n ^ 2 * η := by simp; ring

/-- On the unit ball, nearby vectors give nearby linear forms. -/
lemma abs_linForm_sub_le {n : ℕ} (b b' : Fin n → ℝ) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1)
    {η : ℝ} (h : ∀ i, |b' i - b i| ≤ η) : |linForm b' w - linForm b w| ≤ n * η := by
  have hw' : ∀ i, |w i| ≤ 1 := fun i => by simpa using (norm_le_pi_norm w i).trans hw
  unfold linForm
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (w i * b' i - w i * b i)| ≤ ∑ i, |w i * b' i - w i * b i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, η := by
        refine Finset.sum_le_sum fun i _ => ?_
        have : w i * b' i - w i * b i = w i * (b' i - b i) := by ring
        rw [this, abs_mul]
        calc |w i| * |b' i - b i| ≤ 1 * |b' i - b i| :=
              mul_le_mul_of_nonneg_right (hw' i) (abs_nonneg _)
          _ ≤ η := by linarith [h i]
    _ = n * η := by simp

/-- A continuous positive function on a compact set is bounded below by a positive constant. -/
lemma exists_pos_le_of_isCompact {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {f : X → ℝ} (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ δ > 0, ∀ x ∈ K, δ ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩

/-- **Uniform bound for a slowly varying cone.** If `a` and `b` are continuous at `p` and at `p` no
nonzero `w` with `wᵀ a(p) w ≤ 0` has `b(p) ⬝ w = 0`, then near `p` every `w` with `wᵀ a(q) w ≤ 0`
and `b(q) ⬝ w < 0` satisfies `‖w‖ ≤ c · (-(b(p) ⬝ w))` for a fixed constant `c`. -/
theorem uniform_cone_bound {Q : Type*} [TopologicalSpace Q] {n : ℕ} {p : Q}
    {a : Q → Fin n → Fin n → ℝ} {b : Q → Fin n → ℝ} (ha : ContinuousAt a p)
    (hb : ContinuousAt b p)
    (h0 : ∀ w : Fin n → ℝ, w ≠ 0 → quadForm (a p) w ≤ 0 → linForm (b p) w ≠ 0) :
    ∃ W ∈ 𝓝 p, ∃ c > 0, ∀ q ∈ W, ∀ w : Fin n → ℝ, quadForm (a q) w ≤ 0 → linForm (b q) w < 0 →
      ‖w‖ ≤ c * (-(linForm (b p) w)) := by
  set S : Set (Fin n → ℝ) := Metric.sphere 0 1 with hS
  have hSc : IsCompact S := isCompact_sphere 0 1
  have hSne : ∀ w ∈ S, w ≠ 0 := fun w hw h0 => by simp [hS, h0] at hw
  have hK : IsCompact (S ∩ {w | quadForm (a p) w ≤ 0}) :=
    hSc.inter_right (isClosed_le (continuous_quadForm _) continuous_const)
  obtain ⟨δ0, hδ0, hδ0K⟩ := exists_pos_le_of_isCompact hK
    (f := fun w => |linForm (b p) w|) (continuous_linForm _ |>.abs |>.continuousOn)
    (fun w hw => abs_pos.2 (h0 w (hSne w hw.1) hw.2))
  have hS2 : IsCompact (S ∩ {w | |linForm (b p) w| ≤ δ0 / 2}) :=
    hSc.inter_right (isClosed_le (continuous_linForm _ |>.abs) continuous_const)
  obtain ⟨η0, hη0, hη0S⟩ := exists_pos_le_of_isCompact hS2
    (f := fun w => quadForm (a p) w) (continuous_quadForm _ |>.continuousOn)
    (fun w hw => by
      by_contra hneg
      push Not at hneg
      have := hδ0K w ⟨hw.1, hneg⟩
      have := hw.2
      simp only [Set.mem_ofPred_eq] at this
      linarith)
  set τ : ℝ := min (η0 / 2) (δ0 / 4) with hτ
  have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
  set e : ℝ := τ / (n ^ 2 + n + 1) with he
  have hden : 0 < (n : ℝ) ^ 2 + n + 1 := by positivity
  have hepos : 0 < e := div_pos hτpos hden
  have hn2 : (n : ℝ) ^ 2 * e ≤ τ := by
    rw [he, ← mul_div_assoc, div_le_iff₀ hden]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hn1 : (n : ℝ) * e ≤ τ := by
    rw [he, ← mul_div_assoc, div_le_iff₀ hden]
    nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
  have hWa : ∀ᶠ q in 𝓝 p, ∀ i j, |a q i j - a p i j| ≤ e := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have : ContinuousAt (fun q => a q i j) p := (continuousAt_pi.1 (continuousAt_pi.1 ha i) j)
    have := this.eventually (Metric.closedBall_mem_nhds (a p i j) hepos)
    filter_upwards [this] with q hq
    simpa [Real.dist_eq] using hq
  have hWb : ∀ᶠ q in 𝓝 p, ∀ i, |b q i - b p i| ≤ e := by
    refine Filter.eventually_all.2 fun i => ?_
    have : ContinuousAt (fun q => b q i) p := continuousAt_pi.1 hb i
    have := this.eventually (Metric.closedBall_mem_nhds (b p i) hepos)
    filter_upwards [this] with q hq
    simpa [Real.dist_eq] using hq
  refine ⟨_, hWa.and hWb, 2 / δ0, by positivity, ?_⟩
  rintro q ⟨hqa, hqb⟩ w hQ hL
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp [linForm] at hL
  have hnorm : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set r : ℝ := ‖w‖⁻¹ with hr
  have hrpos : 0 < r := inv_pos.2 hnorm
  set u : Fin n → ℝ := r • w with hu
  have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hr]; field_simp
  have huS : u ∈ S := by simp [hS, hu1]
  have hQu : quadForm (a q) u ≤ 0 := by
    rw [hu, quadForm_smul]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hQ
  have hLu : linForm (b q) u < 0 := by
    rw [hu, linForm_smul]; exact mul_neg_of_pos_of_neg hrpos hL
  have h1 := abs_quadForm_sub_le (a p) (a q) hu1.le hqa
  have h2 := abs_linForm_sub_le (b p) (b q) hu1.le hqb
  have hQp : quadForm (a p) u ≤ τ := by
    have := (abs_le.1 h1).1
    nlinarith
  have hnotS2 : u ∉ S ∩ {w | |linForm (b p) w| ≤ δ0 / 2} := by
    intro hmem
    have := hη0S u hmem
    have : τ ≤ η0 / 2 := min_le_left _ _
    linarith
  have habs : δ0 / 2 < |linForm (b p) u| := by
    by_contra hle
    push Not at hle
    exact hnotS2 ⟨huS, hle⟩
  have hLp : linForm (b p) u < δ0 / 4 := by
    have h3 := (abs_le.1 h2).1
    have : τ ≤ δ0 / 4 := min_le_right _ _
    linarith
  have hLneg : linForm (b p) u < -(δ0 / 2) := by
    rcases lt_abs.1 habs with h | h
    · linarith
    · exact by linarith
  rw [hu, linForm_smul] at hLneg
  have hlt : r * linForm (b p) w < -(δ0 / 2) := hLneg
  have hrn : r * ‖w‖ = 1 := by rw [hr]; field_simp
  -- `‖w‖ = ‖w‖ * (r * ‖w‖)`, and `r * (-L) > δ0 / 2`
  have hkey : δ0 / 2 * ‖w‖ ≤ -(linForm (b p) w) := by
    have h1 : δ0 / 2 < r * (-(linForm (b p) w)) := by linarith
    have h2 : (δ0 / 2) * ‖w‖ < r * (-(linForm (b p) w)) * ‖w‖ :=
      mul_lt_mul_of_pos_right h1 hnorm
    have h3 : r * (-(linForm (b p) w)) * ‖w‖ = -(linForm (b p) w) * (r * ‖w‖) := by ring
    rw [h3, hrn] at h2
    linarith
  have hd : 0 < δ0 := hδ0
  calc ‖w‖ = (2 / δ0) * (δ0 / 2 * ‖w‖) := by field_simp
    _ ≤ (2 / δ0) * (-(linForm (b p) w)) := mul_le_mul_of_nonneg_left hkey (by positivity)

end Lightlike.Causal
