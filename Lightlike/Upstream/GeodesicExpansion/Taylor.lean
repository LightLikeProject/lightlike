import Lightlike.Upstream.GeodesicExpansion.Jet
import Mathlib

/-!
# Taylor's theorem along a segment

Taylor's theorem with remainder of order `1, 2, 3` along a segment `s ↦ x + s w`, `s ∈ [0, 1]`,
in an open set `U ⊆ ℝⁿ`, for a smooth function, in terms of the partial derivatives `pd`.

## Main results

* `taylor_one`, `taylor_two`, `taylor_three`: the remainder is bounded by `n^j m ‖w‖^j` if the
  partial derivatives of order `j` are bounded by `m` along the segment.
* `hasDerivAt_comp_pd`: the chain rule through partial derivatives.
-/

open Matrix Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {U : Set (Fin n → ℝ)}

/-- The derivative of `f ∘ γ` through partial derivatives: `(f ∘ γ)' = Σ_k w_k ∂_k f`. -/
theorem hasDerivAt_comp_pd {f : (Fin n → ℝ) → ℝ} {γ : ℝ → Fin n → ℝ} {w : Fin n → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => f (γ s)) (∑ k, w k * pd k f (γ t)) t := by
  refine (hf.hasFDerivAt.comp_hasDerivAt t hγ).congr_deriv ?_
  have hw : w = ∑ k, w k • (Pi.single k 1 : Fin n → ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single w]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext j
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul, pd]

/-- A function vanishing at `0` whose derivative is bounded by `K s^k` on `[0, 1]` is bounded by
`K s^(k+1) / (k+1)` there. -/
theorem abs_le_of_hasDerivAt_le_pow {ψ ψ' : ℝ → ℝ} {K : ℝ} {k : ℕ} (h0 : ψ 0 = 0)
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (ψ' s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, |ψ' s| ≤ K * s ^ k) :
    ∀ s ∈ Icc (0 : ℝ) 1, |ψ s| ≤ K * s ^ (k + 1) / (k + 1) := by
  intro s hs
  have hB : ∀ t, HasDerivAt (fun s : ℝ => K * s ^ (k + 1) / (k + 1)) (K * t ^ k) t := by
    intro t
    have h := ((hasDerivAt_pow (k + 1) t).const_mul K).div_const ((k : ℝ) + 1)
    convert h using 1
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := ψ) (f' := ψ') (a := 0)
    (b := 1) (B := fun s => K * s ^ (k + 1) / (k + 1)) (B' := fun s => K * s ^ k)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (by simp [h0]) hB
    (fun t ht => by simpa [Real.norm_eq_abs] using hb t (Ico_subset_Icc_self ht)) hs
  simpa [Real.norm_eq_abs] using this

/-- One-dimensional Taylor estimate of order `1`. -/
theorem taylor_aux_one {φ0 φ1 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ0 (φ1 s) s) (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ1 s| ≤ K) :
    |φ0 1 - φ0 0| ≤ K := by
  have := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ0 s - φ0 0) (ψ' := φ1) (K := K) (k := 0)
    (by simp) (fun s hs => (d0 s hs).sub_const _) (fun s hs => by simpa using hb s hs) 1
    ⟨zero_le_one, le_rfl⟩
  simpa using this

/-- One-dimensional Taylor estimate of order `2`. -/
theorem taylor_aux_two {φ0 φ1 φ2 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ0 (φ1 s) s)
    (d1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s) (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ2 s| ≤ K) :
    |φ0 1 - φ0 0 - φ1 0| ≤ K := by
  have h1 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ1 s - φ1 0) (ψ' := φ2) (K := K) (k := 0)
    (by simp) (fun s hs => (d1 s hs).sub_const _) (fun s hs => by simpa using hb s hs)
  have h0 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ0 s - φ0 0 - s * φ1 0)
    (ψ' := fun s => φ1 s - φ1 0) (K := K) (k := 1) (by simp)
    (fun s hs => (((d0 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ1 0))).congr_deriv
      (by ring))
    (fun s hs => by simpa using h1 s hs) 1 ⟨zero_le_one, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  norm_num at h0
  linarith [h0]

/-- One-dimensional Taylor estimate of order `3`. -/
theorem taylor_aux_three {φ0 φ1 φ2 φ3 : ℝ → ℝ} {K : ℝ}
    (d0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ0 (φ1 s) s)
    (d1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s)
    (d2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ2 (φ3 s) s) (hb : ∀ s ∈ Icc (0 : ℝ) 1, |φ3 s| ≤ K) :
    |φ0 1 - φ0 0 - φ1 0 - (1 / 2) * φ2 0| ≤ K := by
  have h2 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ2 s - φ2 0) (ψ' := φ3) (K := K) (k := 0)
    (by simp) (fun s hs => (d2 s hs).sub_const _) (fun s hs => by simpa using hb s hs)
  have h1 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ1 s - φ1 0 - s * φ2 0)
    (ψ' := fun s => φ2 s - φ2 0) (K := K) (k := 1) (by simp)
    (fun s hs => (((d1 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ2 0))).congr_deriv
      (by ring))
    (fun s hs => by simpa using h2 s hs)
  have h0 := abs_le_of_hasDerivAt_le_pow (ψ := fun s => φ0 s - φ0 0 - s * φ1 0 - s ^ 2 / 2 * φ2 0)
    (ψ' := fun s => φ1 s - φ1 0 - s * φ2 0) (K := K / 2) (k := 2) (by simp)
    (fun s hs => ((((d0 s hs).sub_const _).sub ((hasDerivAt_id' s).mul_const (φ1 0))).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (φ2 0))).congr_deriv (by simp))
    (fun s hs => (h1 s hs).trans_eq (by push_cast; ring))
    1 ⟨zero_le_one, le_rfl⟩
  have hK : 0 ≤ K := (abs_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  norm_num at h0
  rw [show φ0 1 - φ0 0 - φ1 0 - 1 / 2 * φ2 0 = φ0 1 - φ0 0 - φ1 0 - 2⁻¹ * φ2 0 by ring]
  linarith [h0]

/-- The derivative of `f` along the line `s ↦ x + s w`. -/
theorem hasDerivAt_line {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} {s : ℝ} (hs : x + s • w ∈ U) :
    HasDerivAt (fun s => f (x + s • w)) (∑ k, w k * pd k f (x + s • w)) s := by
  have hγ : HasDerivAt (fun s : ℝ => x + s • w) w s := by
    simpa using ((hasDerivAt_id' s).smul_const w).const_add x
  exact hasDerivAt_comp_pd (differentiableAt_of_contDiffOn hf hU hs) hγ

/-- **Taylor's theorem of order `1`** along a segment in `U`:
`|f(x + w) - f(x)| ≤ n m ‖w‖` if the first partial derivatives are bounded by `m` on the
segment. -/
theorem taylor_one {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ U) {m : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k, |pd k f (x + s • w)| ≤ m) :
    |f (x + w) - f x| ≤ n * m * ‖w‖ := by
  have := taylor_aux_one (φ0 := fun s => f (x + s • w))
    (φ1 := fun s => ∑ k, w k * pd k f (x + s • w)) (K := n * ‖w‖ * m)
    (fun s hs => hasDerivAt_line hf hU (hseg s hs))
    (fun s hs => abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) (hm s hs))
  simp only [one_smul, zero_smul, add_zero] at this
  linarith

/-- **Taylor's theorem of order `2`** along a segment in `U`, with the second partial derivatives
bounded by `m` on the segment. -/
theorem taylor_two {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ U) {m : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k l, |pd l (pd k f) (x + s • w)| ≤ m) :
    |f (x + w) - f x - ∑ k, w k * pd k f x| ≤ n ^ 2 * m * ‖w‖ ^ 2 := by
  have f1 : ∀ k, ContDiffOn ℝ ∞ (pd k f) U := fun k => contDiffOn_pd hf hU k
  have := taylor_aux_two (φ0 := fun s => f (x + s • w))
    (φ1 := fun s => ∑ k, w k * pd k f (x + s • w))
    (φ2 := fun s => ∑ k, w k * ∑ l, w l * pd l (pd k f) (x + s • w))
    (K := n * ‖w‖ * (n * ‖w‖ * m))
    (fun s hs => hasDerivAt_line hf hU (hseg s hs))
    (fun s hs => HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_line (f1 k) hU (hseg s hs)).const_mul (w k))
    (fun s hs => abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun k =>
      abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun l => hm s hs k l)
  simp only [one_smul, zero_smul, add_zero] at this
  calc _ ≤ _ := this
    _ = n ^ 2 * m * ‖w‖ ^ 2 := by ring

/-- **Taylor's theorem of order `3`** along a segment in `U`, with the third partial derivatives
bounded by `m` on the segment:
`|f(x + w) - f(x) - ∂_w f(x) - ½ ∂_w ∂_w f(x)| ≤ n³ m ‖w‖³`. -/
theorem taylor_three {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    {x w : Fin n → ℝ} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ U) {m : ℝ}
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ k l p, |pd p (pd l (pd k f)) (x + s • w)| ≤ m) :
    |f (x + w) - f x - ∑ k, w k * pd k f x
      - (1 / 2) * ∑ k, ∑ l, w k * w l * pd l (pd k f) x| ≤ n ^ 3 * m * ‖w‖ ^ 3 := by
  have f1 : ∀ k, ContDiffOn ℝ ∞ (pd k f) U := fun k => contDiffOn_pd hf hU k
  have f2 : ∀ k l, ContDiffOn ℝ ∞ (pd l (pd k f)) U :=
    fun k l => contDiffOn_pd (f1 k) hU l
  have := taylor_aux_three (φ0 := fun s => f (x + s • w))
    (φ1 := fun s => ∑ k, w k * pd k f (x + s • w))
    (φ2 := fun s => ∑ k, w k * ∑ l, w l * pd l (pd k f) (x + s • w))
    (φ3 := fun s => ∑ k, w k * ∑ l, w l * ∑ p, w p * pd p (pd l (pd k f)) (x + s • w))
    (K := n * ‖w‖ * (n * ‖w‖ * (n * ‖w‖ * m)))
    (fun s hs => hasDerivAt_line hf hU (hseg s hs))
    (fun s hs => HasDerivAt.fun_sum fun k _ =>
      (hasDerivAt_line (f1 k) hU (hseg s hs)).const_mul (w k))
    (fun s hs => HasDerivAt.fun_sum fun k _ => (HasDerivAt.fun_sum fun l _ =>
      (hasDerivAt_line (f2 k l) hU (hseg s hs)).const_mul (w l)).const_mul (w k))
    (fun s hs => abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun k =>
      abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun l =>
        abs_sum_mul_le (norm_nonneg w) (abs_le_norm_apply w) fun p => hm s hs k l p)
  simp only [one_smul, zero_smul, add_zero] at this
  have e : ∑ k, w k * ∑ l, w l * pd l (pd k f) x =
      ∑ k, ∑ l, w k * w l * pd l (pd k f) x := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← e]
  calc _ ≤ _ := this
    _ = n ^ 3 * m * ‖w‖ ^ 3 := by ring

end Lightlike.Upstream.GeodesicExpansion
