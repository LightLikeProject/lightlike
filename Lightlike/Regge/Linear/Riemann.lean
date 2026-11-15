import Mathlib

/-!
# Riemann sums over the square lattice of mesh `1/n`

For a Lipschitz function `F` of the plane that vanishes outside the ball of radius `R`, the sum
`∑_v (1/n)² F(v/n)` over the lattice points of that ball differs from `∫ F` by at most
`Λ (2R+1)² / n`, where `Λ` is the Lipschitz constant. The proof tiles the plane by the half-open
squares of side `1/n` and bounds the integral over each square against the value at its corner.
-/

open Set MeasureTheory

namespace Lightlike.Regge.Linear

/-- The lattice point `v / n` of the grid of mesh `1/n`. -/
noncomputable def gpt (n : ℕ) (v : ℤ × ℤ) : Fin 2 → ℝ := ![(v.1 : ℝ) / n, (v.2 : ℝ) / n]

/-- The half-open square of side `1/n` with lower corner `gpt n v`. -/
noncomputable def cell (n : ℕ) (v : ℤ × ℤ) : Set (Fin 2 → ℝ) :=
  Set.pi univ fun k => Ico (gpt n v k) (gpt n v k + 1 / n)

/-- The lattice points with both coordinates in `[-R n, R n]`, i.e. in the square of radius `R`. -/
def gbox (R n : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-((R * n : ℕ) : ℤ)) ((R * n : ℕ) : ℤ) ×ˢ Finset.Icc (-((R * n : ℕ) : ℤ)) ((R * n : ℕ) : ℤ)

lemma measurableSet_cell (n : ℕ) (v : ℤ × ℤ) : MeasurableSet (cell n v) :=
  MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico

lemma volume_real_cell {n : ℕ} (hn : 0 < n) (v : ℤ × ℤ) :
    volume.real (cell n v) = (1 / (n : ℝ)) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cell Measure.real
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Ico, Fin.prod_univ_two, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by simp), ENNReal.toReal_ofReal (by simp)]
  simp; ring

lemma volume_cell_lt_top (n : ℕ) (v : ℤ × ℤ) : volume (cell n v) < ⊤ := by
  unfold cell
  rw [volume_pi, Measure.pi_pi]
  exact ENNReal.prod_lt_top fun _ _ => by simp [Real.volume_Ico]

lemma aux_iff {n : ℕ} (hn : 0 < n) (a x : ℝ) :
    (a / n ≤ x ∧ x < a / n + 1 / n) ↔ (a ≤ n * x ∧ n * x < a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← add_div, div_le_iff₀ hn', lt_div_iff₀ hn']
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith [mul_comm x (n : ℝ)], by linarith [mul_comm x (n : ℝ)]⟩

lemma mem_cell_iff {n : ℕ} (hn : 0 < n) {x : Fin 2 → ℝ} {v : ℤ × ℤ} :
    x ∈ cell n v ↔ ((v.1 : ℝ) ≤ n * x 0 ∧ n * x 0 < v.1 + 1) ∧
      ((v.2 : ℝ) ≤ n * x 1 ∧ n * x 1 < v.2 + 1) := by
  simp only [cell, mem_pi, mem_univ, true_implies, Fin.forall_fin_two, gpt, mem_Ico]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [aux_iff hn, aux_iff hn]

lemma cell_disjoint {n : ℕ} (hn : 0 < n) {v w : ℤ × ℤ} (hvw : v ≠ w) :
    Disjoint (cell n v) (cell n w) := by
  rw [Set.disjoint_left]
  intro x hv hw
  rw [mem_cell_iff hn] at hv hw
  apply hvw
  have h1 : v.1 = w.1 := by
    have a1 : (v.1 : ℝ) < w.1 + 1 := by linarith [hv.1.1, hw.1.2]
    have a2 : (w.1 : ℝ) < v.1 + 1 := by linarith [hw.1.1, hv.1.2]
    have b1 : v.1 < w.1 + 1 := by exact_mod_cast a1
    have b2 : w.1 < v.1 + 1 := by exact_mod_cast a2
    omega
  have h2 : v.2 = w.2 := by
    have a1 : (v.2 : ℝ) < w.2 + 1 := by linarith [hv.2.1, hw.2.2]
    have a2 : (w.2 : ℝ) < v.2 + 1 := by linarith [hw.2.1, hv.2.2]
    have b1 : v.2 < w.2 + 1 := by exact_mod_cast a1
    have b2 : w.2 < v.2 + 1 := by exact_mod_cast a2
    omega
  exact Prod.ext h1 h2

/-- Every point lies in the cell of the lattice point `(⌊n x₀⌋, ⌊n x₁⌋)`. -/
lemma mem_cell_floor {n : ℕ} (hn : 0 < n) (x : Fin 2 → ℝ) :
    x ∈ cell n (⌊n * x 0⌋, ⌊n * x 1⌋) := by
  rw [mem_cell_iff hn]
  exact ⟨⟨Int.floor_le _, Int.lt_floor_add_one _⟩, ⟨Int.floor_le _, Int.lt_floor_add_one _⟩⟩

lemma floor_mem_gbox {n R : ℕ} (hn : 0 < n) {x : Fin 2 → ℝ} (hx : ‖x‖ ≤ R) :
    ((⌊n * x 0⌋, ⌊n * x 1⌋) : ℤ × ℤ) ∈ gbox R n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : ∀ k, |(n : ℝ) * x k| ≤ (R * n : ℕ) := by
    intro k
    have := (norm_le_pi_norm x k).trans hx
    rw [abs_mul, abs_of_pos hn']
    push_cast
    rw [Real.norm_eq_abs] at this
    nlinarith
  have key : ∀ k, -((R * n : ℕ) : ℤ) ≤ ⌊(n : ℝ) * x k⌋ ∧ ⌊(n : ℝ) * x k⌋ ≤ ((R * n : ℕ) : ℤ) := by
    intro k
    have := abs_le.mp (hk k)
    constructor
    · rw [Int.le_floor]; push_cast at this ⊢; linarith [this.1]
    · have : ⌊(n : ℝ) * x k⌋ ≤ ⌊((R * n : ℕ) : ℝ)⌋ := Int.floor_le_floor (by linarith)
      rwa [Int.floor_natCast] at this
  simp only [gbox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨key 0, key 1⟩

lemma card_gbox (R n : ℕ) : ((gbox R n).card : ℝ) = (2 * (R * n : ℕ) + 1) ^ 2 := by
  simp only [gbox, Finset.card_product, Int.card_Icc]
  have : ((R * n : ℕ) : ℤ) + 1 - -((R * n : ℕ) : ℤ) = 2 * (R * n : ℕ) + 1 := by ring
  rw [this]
  have h0 : (0 : ℤ) ≤ 2 * (R * n : ℕ) + 1 := by positivity
  have e : (((2 * ((R * n : ℕ) : ℤ) + 1).toNat : ℕ) : ℝ) = 2 * ((R * n : ℕ) : ℝ) + 1 := by
    exact_mod_cast Int.toNat_of_nonneg h0
  rw [Nat.cast_mul, e]; ring

lemma coord_le {n : ℕ} (hn : 0 < n) {a x : ℝ} (h1 : a ≤ n * x) (h2 : n * x < a + 1) :
    |x - a / n| ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : x - a / n = (n * x - a) / n := by field_simp
  rw [e, abs_div, abs_of_pos hn']
  exact div_le_div_of_nonneg_right (by rw [abs_le]; constructor <;> linarith) hn'.le

/-- **Riemann sums on the lattice.** -/
theorem riemann_sum {F : (Fin 2 → ℝ) → ℝ} {Λ : NNReal} (hF : LipschitzWith Λ F) {R : ℕ}
    (hR : ∀ x, (R : ℝ) < ‖x‖ → F x = 0) {n : ℕ} (hn : 0 < n) :
    |∑ v ∈ gbox R n, (1 / (n : ℝ)) ^ 2 * F (gpt n v) - ∫ x, F x| ≤ Λ * (2 * R + 1) ^ 2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hFc : Continuous F := hF.continuous
  have hsupp : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 R)
      (isCompact_closedBall _ _) ?_
    intro x hx
    by_contra hxn
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hxn
    exact hx (hR x hxn)
  have hint : Integrable F := hFc.integrable_of_hasCompactSupport hsupp
  have hU : ∫ x in ⋃ v ∈ gbox R n, cell n v, F x = ∫ x, F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    by_contra hne
    have hxR : ‖x‖ ≤ R := by
      by_contra h; exact hne (hR x (not_le.mp h))
    exact hx (mem_biUnion (floor_mem_gbox hn hxR) (mem_cell_floor hn x))
  have hsum : ∫ x in ⋃ v ∈ gbox R n, cell n v, F x = ∑ v ∈ gbox R n, ∫ x in cell n v, F x :=
    integral_biUnion_finset _ (fun v _ => measurableSet_cell n v)
      (fun v _ w _ hvw => cell_disjoint hn hvw) (fun v _ => hint.integrableOn)
  rw [← hU, hsum, ← Finset.sum_sub_distrib]
  have hcell : ∀ v ∈ gbox R n,
      |(1 / (n : ℝ)) ^ 2 * F (gpt n v) - ∫ x in cell n v, F x| ≤ Λ / n * (1 / (n : ℝ)) ^ 2 := by
    intro v _
    have h1 : ∫ x in cell n v, F (gpt n v) = (1 / (n : ℝ)) ^ 2 * F (gpt n v) := by
      rw [setIntegral_const, smul_eq_mul, volume_real_cell hn]
    have h2 : (1 / (n : ℝ)) ^ 2 * F (gpt n v) - ∫ x in cell n v, F x =
        -∫ x in cell n v, (F x - F (gpt n v)) := by
      rw [integral_sub hint.integrableOn (integrableOn_const (volume_cell_lt_top n v).ne),
        setIntegral_const, smul_eq_mul, volume_real_cell hn]
      ring
    rw [h2, abs_neg, ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (volume_cell_lt_top n v) ?_).trans
      (le_of_eq (by rw [volume_real_cell hn]))
    intro x hx
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    have hd : dist x (gpt n v) ≤ 1 / n := by
      rw [dist_eq_norm, pi_norm_le_iff_of_nonneg (by positivity)]
      intro k
      have hx' := (mem_cell_iff hn).mp hx
      rw [Real.norm_eq_abs]
      fin_cases k
      · simpa [gpt] using coord_le hn hx'.1.1 hx'.1.2
      · simpa [gpt] using coord_le hn hx'.2.1 hx'.2.2
    calc _ ≤ Λ * (1 / (n : ℝ)) := (hF.dist_le_mul x (gpt n v)).trans
          (mul_le_mul_of_nonneg_left hd Λ.coe_nonneg)
      _ = Λ / n := by ring
  calc _ ≤ ∑ v ∈ gbox R n, |(1 / (n : ℝ)) ^ 2 * F (gpt n v) - ∫ x in cell n v, F x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ gbox R n, Λ / n * (1 / (n : ℝ)) ^ 2 := Finset.sum_le_sum hcell
    _ = (gbox R n).card * (Λ / n * (1 / (n : ℝ)) ^ 2) := by simp
    _ ≤ Λ * (2 * R + 1) ^ 2 / n := by
        rw [card_gbox]; push_cast
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have key : (2 * ((R : ℝ) * n) + 1) ^ 2 ≤ ((2 * R + 1) * n) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by nlinarith) 2
        calc (2 * ((R : ℝ) * n) + 1) ^ 2 * ((Λ : ℝ) / n * (1 / (n : ℝ)) ^ 2)
            ≤ ((2 * R + 1) * n) ^ 2 * ((Λ : ℝ) / n * (1 / (n : ℝ)) ^ 2) := by gcongr
          _ = (Λ : ℝ) * (2 * R + 1) ^ 2 / n := by field_simp

end Lightlike.Regge.Linear
