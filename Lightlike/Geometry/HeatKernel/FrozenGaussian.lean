import Mathlib
import Lightlike.Asymptotics.GaussianIntegralPi

/-!
# The frozen Gaussian is an approximate identity, uniformly in the base point

For positive definite matrices `G_p` (`p ∈ S`) with a uniform lower bound `λ₀ ‖z‖² ≤ z·G_p z` and a bounded, uniformly
continuous `F : ℝⁿ → ℝ`,

`(∫ (4πt)^{-n/2} e^{-(y − p)·G_p(y − p)/4t} F(y) dy) → F(p) / √det G_p`   as `t → 0⁺`, uniformly in `p ∈ S`
(`frozenGaussian_approx`).

The normalization is `integral_exp_neg_mul_quadForm`; the error is `∫ k_t(y) (F(y) − F(p)) dy` with `k_t ≥ 0` the
Gaussian, bounded by `ε ∫ k_t` near `p` (uniform continuity) and by `2B ‖y − p‖²/δ²` away from `p`, whose integral
against `k_t` is `O(t)` (`u e^{-u} ≤ 2 e^{-u/2}`).
-/

open MeasureTheory Real Matrix Set Filter Metric
open scoped Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- `u e^{-u} ≤ 2 e^{-u/2}` for `u ≥ 0`. -/
theorem mul_exp_neg_le (u : ℝ) (hu : 0 ≤ u) : u * Real.exp (-u) ≤ 2 * Real.exp (-u / 2) := by
  have h1 : u ≤ 2 * Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2); linarith
  have h2 : Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (u / 2) * Real.exp (-u / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  calc u * Real.exp (-u) = u * Real.exp (-u / 2) * Real.exp (-u / 2) := by rw [h2]; ring
    _ ≤ 2 * Real.exp (u / 2) * Real.exp (-u / 2) * Real.exp (-u / 2) := by gcongr
    _ = 2 * Real.exp (-u / 2) := by rw [mul_assoc 2, h3, mul_one]

/-- `‖z‖² ≤ Σ zᵢ²` for the sup norm (one coordinate realizes the norm). -/
theorem norm_sq_le_sum_sq (z : Fin n → ℝ) : ‖z‖ ^ 2 ≤ ∑ i, z i ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · simp [Subsingleton.elim z 0]
  · obtain ⟨i, hi⟩ := Finite.exists_max fun i => |z i|
    have hz : ‖z‖ = |z i| := by
      apply le_antisymm
      · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => by rw [Real.norm_eq_abs]; exact hi j
      · simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
    rw [hz, sq_abs]
    exact Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

/-- `Σ zᵢ² ≤ n ‖z‖²` for the sup norm. -/
theorem sum_sq_le_card_mul_norm_sq (z : Fin n → ℝ) : ∑ i, z i ^ 2 ≤ (n : ℝ) * ‖z‖ ^ 2 := by
  have h : ∀ i, z i ^ 2 ≤ ‖z‖ ^ 2 := fun i => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using norm_le_pi_norm z i) 2
  calc ∑ i, z i ^ 2 ≤ ∑ _i : Fin n, ‖z‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = (n : ℝ) * ‖z‖ ^ 2 := by simp

/-- The integral of the dominating Gaussian: `∫ (4πt)^{-n/2} e^{-a Σ (yᵢ − pᵢ)²/t} dy = (1/(4a))^{n/2}`. -/
theorem integral_heat_gauss_sum {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (p : Fin n → ℝ) :
    ∫ y : Fin n → ℝ, (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(a / t) * ∑ i, (y i - p i) ^ 2) =
      (1 / (4 * a)) ^ ((n : ℝ) / 2) := by
  rw [integral_const_mul, integral_exp_neg_mul_sum_sq_sub n (div_pos ha ht) p,
    show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg (by positivity), ← div_eq_inv_mul,
    ← Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **The normalization of the frozen Gaussian**: `∫ (4πt)^{-n/2} e^{-(y − p)·G(y − p)/4t} dy = 1/√det G`. -/
theorem integral_frozenGauss {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {t : ℝ} (ht : 0 < t) (p : Fin n → ℝ) :
    ∫ y : Fin n → ℝ, (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (G *ᵥ (y - p))) / (4 * t)) =
      1 / √G.det := by
  have he : ∀ y : Fin n → ℝ, Real.exp (-((y - p) ⬝ᵥ (G *ᵥ (y - p))) / (4 * t)) =
      Real.exp (-(1 / (4 * t)) * ((y - p) ⬝ᵥ (G *ᵥ (y - p)))) := fun y => by congr 1; ring
  simp only [he]
  rw [integral_const_mul, integral_exp_neg_mul_quadForm hG (by positivity) p,
    show π / (1 / (4 * t)) = 4 * π * t by field_simp, mul_div_assoc', ← Real.rpow_add (by positivity),
    show -(n : ℝ) / 2 + n / 2 = 0 by ring, Real.rpow_zero]

/-- The pointwise domination of the frozen Gaussian by a coordinate Gaussian. -/
theorem frozenGauss_le {G : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} (hlow : ∀ z, lam * ‖z‖ ^ 2 ≤ z ⬝ᵥ (G *ᵥ z))
    {t : ℝ} (ht : 0 < t) (p y : Fin n → ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ lam) :
    Real.exp (-((y - p) ⬝ᵥ (G *ᵥ (y - p))) / (4 * t)) ≤
      Real.exp (-(c / (4 * ((n : ℝ) + 1)) / t) * ∑ i, (y i - p i) ^ 2) := by
  apply Real.exp_le_exp.2
  have hq := hlow (y - p)
  have hs : ∑ i, (y i - p i) ^ 2 ≤ ((n : ℝ) + 1) * ‖y - p‖ ^ 2 := by
    have := sum_sq_le_card_mul_norm_sq (y - p)
    simp only [Pi.sub_apply] at this
    nlinarith [sq_nonneg ‖y - p‖]
  have h1 : c * ∑ i, (y i - p i) ^ 2 ≤ ((n : ℝ) + 1) * ((y - p) ⬝ᵥ (G *ᵥ (y - p))) := by
    have h2 : c * ‖y - p‖ ^ 2 ≤ lam * ‖y - p‖ ^ 2 := by gcongr
    nlinarith [sq_nonneg ‖y - p‖]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : (-(c / (4 * ((n : ℝ) + 1)) / t) * ∑ i, (y i - p i) ^ 2) * (4 * t) =
      -(c * ∑ i, (y i - p i) ^ 2) / ((n : ℝ) + 1) := by
    set S := ∑ i, (y i - p i) ^ 2
    field_simp
  rw [this, neg_div, neg_le_neg_iff, div_le_iff₀ hn]
  linarith

/-- The second moment against the frozen Gaussian, dominated: `kₜ(y) ‖y − p‖² ≤ (8t/λ₀) (4πt)^{-n/2} e^{-a₂ Σ(yᵢ−pᵢ)²/t}`. -/
theorem frozenGauss_mul_norm_sq_le {G : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hlow : ∀ z, lam * ‖z‖ ^ 2 ≤ z ⬝ᵥ (G *ᵥ z)) {t : ℝ} (ht : 0 < t) (p y : Fin n → ℝ) :
    (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (G *ᵥ (y - p))) / (4 * t)) * ‖y - p‖ ^ 2 ≤
      8 * t / lam * ((4 * π * t) ^ (-(n : ℝ) / 2) *
        Real.exp (-((lam / 2) / (4 * ((n : ℝ) + 1)) / t) * ∑ i, (y i - p i) ^ 2)) := by
  have hG0 : 0 < (4 * π * t) ^ (-(n : ℝ) / 2) := by positivity
  set u := lam * ‖y - p‖ ^ 2 / (4 * t) with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : Real.exp (-((y - p) ⬝ᵥ (G *ᵥ (y - p))) / (4 * t)) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.2
    rw [hu, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_right (hlow _) (by positivity)
  have h2 : ‖y - p‖ ^ 2 = 4 * t / lam * u := by rw [hu]; field_simp
  have h3 : Real.exp (-u / 2) ≤ Real.exp (-((lam / 2) / (4 * ((n : ℝ) + 1)) / t) * ∑ i, (y i - p i) ^ 2) := by
    apply Real.exp_le_exp.2
    have hs : ∑ i, (y i - p i) ^ 2 ≤ ((n : ℝ) + 1) * ‖y - p‖ ^ 2 := by
      have := sum_sq_le_card_mul_norm_sq (y - p)
      simp only [Pi.sub_apply] at this
      nlinarith [sq_nonneg ‖y - p‖]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hu]
    have : -((lam / 2) / (4 * ((n : ℝ) + 1)) / t) * ∑ i, (y i - p i) ^ 2 =
        -(lam * (∑ i, (y i - p i) ^ 2) / ((n : ℝ) + 1)) / (8 * t) := by
      set S := ∑ i, (y i - p i) ^ 2
      field_simp; ring
    rw [this, show -(lam * ‖y - p‖ ^ 2 / (4 * t)) / 2 = -(lam * ‖y - p‖ ^ 2) / (8 * t) by ring, neg_div, neg_div,
      neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [div_le_iff₀ hn]
    nlinarith
  calc (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (G *ᵥ (y - p))) / (4 * t)) * ‖y - p‖ ^ 2
      ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-u) * (4 * t / lam * u) := by
        rw [h2]; gcongr
    _ = 4 * t / lam * ((4 * π * t) ^ (-(n : ℝ) / 2) * (u * Real.exp (-u))) := by ring
    _ ≤ 4 * t / lam * ((4 * π * t) ^ (-(n : ℝ) / 2) * (2 * Real.exp (-u / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_exp_neg_le u hu0) hG0.le) (by positivity)
    _ ≤ 4 * t / lam * ((4 * π * t) ^ (-(n : ℝ) / 2) *
          (2 * Real.exp (-((lam / 2) / (4 * ((n : ℝ) + 1)) / t) * ∑ i, (y i - p i) ^ 2))) := by gcongr
    _ = _ := by ring

/-- **The frozen Gaussian is an approximate identity, uniformly in the base point.** -/
theorem frozenGaussian_approx {S : Set (Fin n → ℝ)} {G : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hG : ∀ p ∈ S, (G p).PosDef) {lam : ℝ} (hlam : 0 < lam)
    (hlow : ∀ p ∈ S, ∀ z, lam * ‖z‖ ^ 2 ≤ z ⬝ᵥ (G p *ᵥ z)) {F : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hB : ∀ y, |F y| ≤ B) (hF : UniformContinuous F) :
    ∀ ε > 0, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ p ∈ S,
      |(∫ y : Fin n → ℝ, (4 * π * t) ^ (-(n : ℝ) / 2) *
          Real.exp (-((y - p) ⬝ᵥ (G p *ᵥ (y - p))) / (4 * t)) * F y) - F p / √(G p).det| ≤ ε := by
  intro ε hε
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set a₁ := lam / (4 * ((n : ℝ) + 1)) with ha₁
  set a₂ := (lam / 2) / (4 * ((n : ℝ) + 1)) with ha₂
  have ha₁0 : 0 < a₁ := by positivity
  have ha₂0 : 0 < a₂ := by positivity
  set A := (1 / (4 * a₁)) ^ ((n : ℝ) / 2) with hA
  set A' := (1 / (4 * a₂)) ^ ((n : ℝ) / 2) with hA'
  have hA0 : 0 ≤ A := by positivity
  have hA'0 : 0 ≤ A' := by positivity
  set ε' := ε / (2 * (A + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuous_iff.1 hF ε' hε'0
  set t₀ := ε * δ ^ 2 * lam / (32 * (B + 1) * (A' + 1)) with ht₀
  refine ⟨t₀, by positivity, fun t ht p hp => ?_⟩
  have ht0 : 0 < t := ht.1
  set k : (Fin n → ℝ) → ℝ := fun y =>
    (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (G p *ᵥ (y - p))) / (4 * t)) with hk
  set D₁ : (Fin n → ℝ) → ℝ := fun y => (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(a₁ / t) * ∑ i, (y i - p i) ^ 2)
  set D₂ : (Fin n → ℝ) → ℝ := fun y => (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-(a₂ / t) * ∑ i, (y i - p i) ^ 2)
  have hD₁i : Integrable D₁ := (integrable_exp_neg_mul_sum_sq_sub n (div_pos ha₁0 ht0) p).const_mul _
  have hD₂i : Integrable D₂ := (integrable_exp_neg_mul_sum_sq_sub n (div_pos ha₂0 ht0) p).const_mul _
  have hk0 : ∀ y, 0 ≤ k y := fun y => by positivity
  have hkD : ∀ y, k y ≤ D₁ y := fun y =>
    mul_le_mul_of_nonneg_left (frozenGauss_le (hlow p hp) ht0 p y hlam.le le_rfl) (by positivity)
  have hkc : Continuous k := by
    simp only [hk]
    refine continuous_const.mul (Real.continuous_exp.comp ((((continuous_id.sub continuous_const).dotProduct
      (continuous_const.matrix_mulVec (continuous_id.sub continuous_const))).neg).div_const _))
  have hki : Integrable k :=
    hD₁i.mono' hkc.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hk0 y)]; exact hkD y)
  have hFc : Continuous F := hF.continuous
  have hkFi : Integrable fun y => k y * F y :=
    (hD₁i.const_mul B).mono' (hkc.mul hFc).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 y)]
      calc k y * |F y| ≤ D₁ y * B := mul_le_mul (hkD y) (hB y) (abs_nonneg _) ((hk0 y).trans (hkD y))
        _ = B * D₁ y := mul_comm _ _)
  -- the normalization and the error integral
  have hnorm : ∫ y, k y = 1 / √(G p).det := integral_frozenGauss (hG p hp) ht0 p
  have herr : ∫ y, k y * (F y - F p) = (∫ y, k y * F y) - F p / √(G p).det := by
    have : (fun y => k y * (F y - F p)) = fun y => k y * F y - F p * k y := by funext y; ring
    rw [this, integral_sub hkFi (hki.const_mul _), integral_const_mul, hnorm, mul_one_div]
  show |(∫ y, k y * F y) - F p / √(G p).det| ≤ ε
  rw [← herr]
  -- the pointwise bound
  set R : (Fin n → ℝ) → ℝ := fun y => ε' * D₁ y + 2 * B / δ ^ 2 * (8 * t / lam * D₂ y) with hR
  have hRi : Integrable R := (hD₁i.const_mul _).add ((hD₂i.const_mul _).const_mul _)
  have hpt : ∀ y, |k y * (F y - F p)| ≤ R y := by
    intro y
    have hFF : |F y - F p| ≤ ε' + 2 * B * ‖y - p‖ ^ 2 / δ ^ 2 := by
      by_cases hy : ‖y - p‖ < δ
      · have := hFδ (show dist y p < δ by rwa [dist_eq_norm])
        rw [Real.dist_eq] at this
        have : 0 ≤ 2 * B * ‖y - p‖ ^ 2 / δ ^ 2 := by positivity
        linarith
      · push Not at hy
        have h1 : 1 ≤ ‖y - p‖ ^ 2 / δ ^ 2 := by
          rw [le_div_iff₀ (by positivity), one_mul]; exact pow_le_pow_left₀ hδ.le hy 2
        have h2 : |F y - F p| ≤ 2 * B := by
          have h3 := abs_add_le (F y) (-F p)
          rw [abs_neg, ← sub_eq_add_neg] at h3
          linarith [hB y, hB p]
        have : 2 * B ≤ 2 * B * (‖y - p‖ ^ 2 / δ ^ 2) := le_mul_of_one_le_right (by linarith) h1
        rw [mul_div_assoc]; linarith
    rw [abs_mul, abs_of_nonneg (hk0 y)]
    calc k y * |F y - F p| ≤ k y * (ε' + 2 * B * ‖y - p‖ ^ 2 / δ ^ 2) := by gcongr
      _ = ε' * k y + 2 * B / δ ^ 2 * (k y * ‖y - p‖ ^ 2) := by ring
      _ ≤ ε' * D₁ y + 2 * B / δ ^ 2 * (8 * t / lam * D₂ y) :=
          add_le_add (mul_le_mul_of_nonneg_left (hkD y) hε'0.le)
            (mul_le_mul_of_nonneg_left (frozenGauss_mul_norm_sq_le hlam (hlow p hp) ht0 p y) (by positivity))
  have hint := integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hRi
    (Eventually.of_forall hpt)
  have hRval : ∫ y, R y = ε' * A + 2 * B / δ ^ 2 * (8 * t / lam * A') := by
    have h1 : ∫ y, D₁ y = A := integral_heat_gauss_sum ha₁0 ht0 p
    have h2 : ∫ y, D₂ y = A' := integral_heat_gauss_sum ha₂0 ht0 p
    rw [integral_add (hD₁i.const_mul _) ((hD₂i.const_mul _).const_mul _), integral_const_mul ε',
      integral_const_mul (2 * B / δ ^ 2), integral_const_mul (8 * t / lam), h1, h2]
  calc |∫ y, k y * (F y - F p)| ≤ ∫ y, |k y * (F y - F p)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, R y := hint
    _ = ε' * A + 2 * B / δ ^ 2 * (8 * t / lam * A') := hRval
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        · rw [hε']
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        · have htt : t ≤ t₀ := ht.2.le
          rw [ht₀] at htt
          have h1 : 2 * B / δ ^ 2 * (8 * t / lam * A') = 16 * B * A' * t / (δ ^ 2 * lam) := by
            field_simp; ring
          rw [h1, div_le_iff₀ (by positivity)]
          have h2 : t * (32 * (B + 1) * (A' + 1)) ≤ ε * δ ^ 2 * lam := by
            rwa [le_div_iff₀ (by positivity)] at htt
          nlinarith [mul_nonneg hB0 hA'0]
    _ = ε := by ring

end Lightlike
