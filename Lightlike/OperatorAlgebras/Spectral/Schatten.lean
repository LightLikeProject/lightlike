import Lightlike.OperatorAlgebras.Spectral.CanonicalForm
import Mathlib.Analysis.MeanInequalities

/-!
# The Schatten classes

G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 6.3, (6.19)-(6.23) and Lemma 6.12, pp. 141-142: for a
compact operator `K` with singular values `sⱼ(K)`, `‖K‖_p = (∑ⱼ sⱼ(K)^p)^{1/p}` (6.19), the Schatten `p`-class is
`J_p(H) = {K ∈ C(H) | ‖K‖_p < ∞}` (6.20), `‖K‖ ≤ ‖K‖_p` (6.21), `‖K‖_p = ‖K*‖_p` (6.22), and
`‖K‖_p = sup {(∑ⱼ |⟪ψⱼ, K ϕⱼ⟫|^p)^{1/p} | {ψⱼ}, {ϕⱼ} ONS}` (6.23).

* `schattenSum p K`: the supremum in (6.23), to the power `p`, over pairs of finite orthonormal families;
* `schattenSum_eq_tsum`: for any canonical form (`IsCanonicalForm K φ φ' s`) and `p ≥ 1`, `schattenSum p K = ∑ⱼ sⱼ^p`
  (6.23); in particular `∑ⱼ sⱼ^p` does not depend on the canonical form;
* `schattenSum_adjoint` (6.22) and `norm_rpow_le_schattenSum` (6.21).
-/

open scoped InnerProductSpace NNReal ENNReal

universe u

namespace Lightlike.OperatorAlgebras.CompactSpectral

/-! ### The finite core of Lemma 6.12 -/

/-- Cauchy–Schwarz for finite sums of `ℝ≥0`: `∑ f g ≤ (∑ f²)^{1/2} (∑ g²)^{1/2}`. -/
lemma nnreal_cauchy_schwarz {ι : Type*} (F : Finset ι) (f g : ι → ℝ≥0) :
    ∑ j ∈ F, f j * g j ≤ (∑ j ∈ F, f j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∑ j ∈ F, g j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have h22 : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have h := NNReal.inner_le_Lp_mul_Lq F f g h22
  simpa using h

/-- **The finite core of Teschl, Lemma 6.12**, p. 141: `∑ₙ (∑ⱼ sⱼ aₙⱼ cₙⱼ)^p ≤ ∑ⱼ sⱼ^p` when the square sums of `a`
and `c` in each index are at most `1` (Hölder for the weights `aₙⱼ²`, then Cauchy–Schwarz twice). -/
lemma schatten_core {ι N : Type*} [Fintype N] (F : Finset ι) {p : ℝ} (hp : 1 ≤ p)
    (s : ι → ℝ≥0) (a c : N → ι → ℝ≥0)
    (ha1 : ∀ n, ∑ j ∈ F, a n j ^ 2 ≤ 1) (hc1 : ∀ n, ∑ j ∈ F, c n j ^ 2 ≤ 1)
    (ha2 : ∀ j ∈ F, ∑ n, a n j ^ 2 ≤ 1) (hc2 : ∀ j ∈ F, ∑ n, c n j ^ 2 ≤ 1) :
    ∑ n, (∑ j ∈ F, s j * a n j * c n j) ^ p ≤ ∑ j ∈ F, s j ^ p := by
  set A : N → ℝ≥0 := fun n => ∑ j ∈ F, a n j ^ 2 * s j ^ p
  set C : N → ℝ≥0 := fun n => ∑ j ∈ F, c n j ^ 2 * s j ^ p
  have hhol : ∀ (w : ι → ℝ≥0), ∑ j ∈ F, w j ≤ 1 →
      ∑ j ∈ F, w j * s j ≤ (∑ j ∈ F, w j * s j ^ p) ^ p⁻¹ := by
    intro w hw
    have h := NNReal.inner_le_weight_mul_Lp F hp w s
    have h1 : (∑ j ∈ F, w j) ^ (1 - p⁻¹) ≤ 1 :=
      NNReal.rpow_le_one hw (by have := inv_le_one_of_one_le₀ hp; linarith)
    calc ∑ j ∈ F, w j * s j ≤ (∑ j ∈ F, w j) ^ (1 - p⁻¹) * (∑ j ∈ F, w j * s j ^ p) ^ p⁻¹ := h
      _ ≤ 1 * (∑ j ∈ F, w j * s j ^ p) ^ p⁻¹ := by gcongr
      _ = _ := one_mul _
  have hsq : ∀ (x y : ℝ≥0), (NNReal.sqrt x * y) ^ (2 : ℝ) = y ^ 2 * x := by
    intro x y
    rw [NNReal.rpow_two, mul_pow, NNReal.sq_sqrt]; ring
  have hpt : ∀ n, (∑ j ∈ F, s j * a n j * c n j) ^ p ≤ A n ^ (1 / 2 : ℝ) * C n ^ (1 / 2 : ℝ) := by
    intro n
    have hcs := nnreal_cauchy_schwarz F (fun j => NNReal.sqrt (s j) * a n j)
      (fun j => NNReal.sqrt (s j) * c n j)
    have hl : ∑ j ∈ F, NNReal.sqrt (s j) * a n j * (NNReal.sqrt (s j) * c n j) =
        ∑ j ∈ F, s j * a n j * c n j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      calc NNReal.sqrt (s j) * a n j * (NNReal.sqrt (s j) * c n j)
          = (NNReal.sqrt (s j) * NNReal.sqrt (s j)) * a n j * c n j := by ring
        _ = _ := by rw [NNReal.mul_self_sqrt]
    simp only [hl, hsq] at hcs
    have ha := hhol (fun j => a n j ^ 2) (ha1 n)
    have hc := hhol (fun j => c n j ^ 2) (hc1 n)
    beta_reduce at ha hc
    have hbound : ∑ j ∈ F, s j * a n j * c n j ≤ (A n ^ p⁻¹) ^ (1 / 2 : ℝ) * (C n ^ p⁻¹) ^ (1 / 2 : ℝ) := by
      refine hcs.trans ?_
      gcongr
    have hp0 : 0 ≤ p := by linarith
    calc (∑ j ∈ F, s j * a n j * c n j) ^ p
        ≤ ((A n ^ p⁻¹) ^ (1 / 2 : ℝ) * (C n ^ p⁻¹) ^ (1 / 2 : ℝ)) ^ p := by gcongr
      _ = A n ^ (1 / 2 : ℝ) * C n ^ (1 / 2 : ℝ) := by
          have hpne : p ≠ 0 := by linarith
          have he : p⁻¹ * (1 / 2 * p) = 1 / 2 := by field_simp
          rw [NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_mul, ← NNReal.rpow_mul, he]
  have hA : ∑ n, A n ≤ ∑ j ∈ F, s j ^ p := by
    simp only [A]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← Finset.sum_mul]
    calc (∑ n, a n j ^ 2) * s j ^ p ≤ 1 * s j ^ p := by gcongr; exact ha2 j hj
      _ = _ := one_mul _
  have hC : ∑ n, C n ≤ ∑ j ∈ F, s j ^ p := by
    simp only [C]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [← Finset.sum_mul]
    calc (∑ n, c n j ^ 2) * s j ^ p ≤ 1 * s j ^ p := by gcongr; exact hc2 j hj
      _ = _ := one_mul _
  have hcs2 := nnreal_cauchy_schwarz Finset.univ (fun n => A n ^ (1 / 2 : ℝ)) (fun n => C n ^ (1 / 2 : ℝ))
  have hsq2 : ∀ x : ℝ≥0, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← NNReal.rpow_mul]; norm_num
  simp only [hsq2] at hcs2
  calc ∑ n, (∑ j ∈ F, s j * a n j * c n j) ^ p ≤ ∑ n, A n ^ (1 / 2 : ℝ) * C n ^ (1 / 2 : ℝ) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ ≤ (∑ n, A n) ^ (1 / 2 : ℝ) * (∑ n, C n) ^ (1 / 2 : ℝ) := hcs2
    _ ≤ (∑ j ∈ F, s j ^ p) ^ (1 / 2 : ℝ) * (∑ j ∈ F, s j ^ p) ^ (1 / 2 : ℝ) := by gcongr
    _ = ∑ j ∈ F, s j ^ p := by
      rw [← NNReal.rpow_add' (by norm_num : (1 / 2 : ℝ) + 1 / 2 ≠ 0)]; norm_num

/-! ### The supremum (6.23) -/

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Schatten sum** `‖K‖_p^p` of Teschl (6.23): the supremum of `∑ⱼ |⟪ψⱼ, K ϕⱼ⟫|^p` over pairs of finite
orthonormal families `ψ`, `ϕ`. -/
noncomputable def schattenSum (p : ℝ) (K : E →L[𝕜] E) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (ψ : Fin n → E) (ϕ : Fin n → E) (_ : Orthonormal 𝕜 ψ ∧ Orthonormal 𝕜 ϕ),
    ∑ k, ‖⟪ψ k, K (ϕ k)⟫_𝕜‖ₑ ^ p

lemma sum_le_schattenSum {p : ℝ} {K : E →L[𝕜] E} {N : Type*} [Fintype N] {ψ ϕ : N → E}
    (hψ : Orthonormal 𝕜 ψ) (hϕ : Orthonormal 𝕜 ϕ) :
    ∑ k, ‖⟪ψ k, K (ϕ k)⟫_𝕜‖ₑ ^ p ≤ schattenSum p K := by
  let e := Fintype.equivFin N
  have h : ∑ k, ‖⟪ψ k, K (ϕ k)⟫_𝕜‖ₑ ^ p = ∑ k, ‖⟪(ψ ∘ e.symm) k, K ((ϕ ∘ e.symm) k)⟫_𝕜‖ₑ ^ p :=
    (e.symm.sum_comp (fun k => ‖⟪ψ k, K (ϕ k)⟫_𝕜‖ₑ ^ p)).symm
  rw [h]
  exact le_iSup_of_le (Fintype.card N) (le_iSup_of_le (ψ ∘ e.symm) (le_iSup_of_le (ϕ ∘ e.symm)
    (le_iSup_of_le ⟨hψ.comp _ e.symm.injective, hϕ.comp _ e.symm.injective⟩ le_rfl)))

/-- `‖x‖ₑ` of a real number cast to `𝕜`. -/
lemma enorm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : 𝕜)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, RCLike.norm_ofReal, abs_of_nonneg hr]

/-- **The lower bound in (6.23)**: `∑ⱼ sⱼ^p ≤ ‖K‖_p^p`, from the orthonormal sets of a canonical form. -/
theorem tsum_le_schattenSum {ι : Type*} {K : E →L[𝕜] E} {φ φ' : ι → E} {s : ι → ℝ}
    (hφ : Orthonormal 𝕜 φ) (hφ' : Orthonormal 𝕜 φ') (hs : ∀ j, 0 ≤ s j)
    (hK : ∀ j, K (φ j) = (s j : 𝕜) • φ' j) (p : ℝ) :
    ∑' j, ENNReal.ofReal (s j) ^ p ≤ schattenSum p K := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  have h := sum_le_schattenSum (p := p) (K := K) (N := F) (hφ'.comp _ Subtype.val_injective)
    (hφ.comp _ Subtype.val_injective)
  have hterm : ∀ j, ‖⟪φ' j, K (φ j)⟫_𝕜‖ₑ = ENNReal.ofReal (s j) := by
    intro j
    rw [hK j, inner_smul_right, inner_self_eq_norm_sq_to_K, hφ'.1 j]
    simp only [RCLike.ofReal_one, one_pow, mul_one]
    exact enorm_ofReal_of_nonneg (hs j)
  simp only [Function.comp_apply, hterm] at h
  rwa [Finset.sum_coe_sort F (fun j => ENNReal.ofReal (s j) ^ p)] at h

/-- **The upper bound in (6.23)** (Teschl, Lemma 6.12, p. 141, "the hard part"): for a canonical form
`K x = ∑ⱼ sⱼ ⟪φⱼ, x⟫ φ'ⱼ` and `p ≥ 1`, `∑ₙ |⟪ψₙ, K ϕₙ⟫|^p ≤ ∑ⱼ sⱼ^p` for all finite orthonormal `ψ`, `ϕ`. -/
theorem schattenSum_le_tsum {ι : Type*} {K : E →L[𝕜] E} {φ φ' : ι → E} {s : ι → ℝ}
    (hφ : Orthonormal 𝕜 φ) (hφ' : Orthonormal 𝕜 φ') (hs : ∀ j, 0 ≤ s j)
    (hK : ∀ x, HasSum (fun j => ((s j : 𝕜) * ⟪φ j, x⟫_𝕜) • φ' j) (K x)) {p : ℝ} (hp : 1 ≤ p) :
    schattenSum p K ≤ ∑' j, ENNReal.ofReal (s j) ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  refine iSup_le fun n => iSup_le fun ψ => iSup_le fun ϕ => iSup_le fun hψϕ => ?_
  obtain ⟨hψ, hϕ⟩ := hψϕ
  let sv : ι → ℝ≥0 := fun j => (s j).toNNReal
  let a : Fin n → ι → ℝ≥0 := fun k j => ‖⟪φ j, ϕ k⟫_𝕜‖₊
  let c : Fin n → ι → ℝ≥0 := fun k j => ‖⟪ψ k, φ' j⟫_𝕜‖₊
  let f : Fin n → ι → ℝ≥0 := fun k j => sv j * a k j * c k j
  -- `|⟪ψₖ, K ϕₖ⟫| ≤ ∑ⱼ sⱼ aₖⱼ cₖⱼ`
  have hx : ∀ k, ‖⟪ψ k, K (ϕ k)⟫_𝕜‖ₑ ≤ ∑' j, (f k j : ℝ≥0∞) := by
    intro k
    have h := (hK (ϕ k)).mapL (innerSL 𝕜 (ψ k))
    simp only [innerSL_apply_apply, inner_smul_right] at h
    refine h.enorm_le_of_bounded ENNReal.summable.hasSum fun j => ?_
    rw [enorm_mul, enorm_mul, enorm_ofReal_of_nonneg (hs j)]
    simp only [f, sv, a, c, ENNReal.coe_mul, ← enorm_eq_nnnorm]
    exact le_rfl
  have hmono : ∀ k, Monotone fun F : Finset ι => (∑ j ∈ F, (f k j : ℝ≥0∞)) ^ p := fun k F G hFG =>
    ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset hFG) hp0.le
  calc ∑ k, ‖⟪ψ k, K (ϕ k)⟫_𝕜‖ₑ ^ p ≤ ∑ k, (∑' j, (f k j : ℝ≥0∞)) ^ p :=
        Finset.sum_le_sum fun k _ => ENNReal.rpow_le_rpow (hx k) hp0.le
    _ = ∑ k, ⨆ F : Finset ι, (∑ j ∈ F, (f k j : ℝ≥0∞)) ^ p := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ENNReal.tsum_eq_iSup_sum]
        have := (ENNReal.orderIsoRpow p hp0).map_iSup (fun F : Finset ι => ∑ j ∈ F, (f k j : ℝ≥0∞))
        simpa only [ENNReal.orderIsoRpow_apply] using this
    _ = ⨆ F : Finset ι, ∑ k, (∑ j ∈ F, (f k j : ℝ≥0∞)) ^ p :=
        ENNReal.finsetSum_iSup_of_monotone hmono
    _ ≤ ∑' j, ENNReal.ofReal (s j) ^ p := by
        refine iSup_le fun F => ?_
        -- the Bessel inequalities
        have ha1 : ∀ k, ∑ j ∈ F, a k j ^ 2 ≤ 1 := by
          intro k
          rw [← NNReal.coe_le_coe]; push_cast
          calc ∑ j ∈ F, ‖⟪φ j, ϕ k⟫_𝕜‖ ^ 2 ≤ ‖ϕ k‖ ^ 2 := Orthonormal.sum_inner_products_le (ϕ k) hφ
            _ = 1 := by rw [hϕ.1 k, one_pow]
        have hc1 : ∀ k, ∑ j ∈ F, c k j ^ 2 ≤ 1 := by
          intro k
          rw [← NNReal.coe_le_coe]; push_cast
          calc ∑ j ∈ F, ‖⟪ψ k, φ' j⟫_𝕜‖ ^ 2 = ∑ j ∈ F, ‖⟪φ' j, ψ k⟫_𝕜‖ ^ 2 :=
                Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm]
            _ ≤ ‖ψ k‖ ^ 2 := Orthonormal.sum_inner_products_le (ψ k) hφ'
            _ = 1 := by rw [hψ.1 k, one_pow]
        have ha2 : ∀ j ∈ F, ∑ k, a k j ^ 2 ≤ 1 := by
          intro j _
          rw [← NNReal.coe_le_coe]; push_cast
          calc ∑ k, ‖⟪φ j, ϕ k⟫_𝕜‖ ^ 2 = ∑ k, ‖⟪ϕ k, φ j⟫_𝕜‖ ^ 2 :=
                Finset.sum_congr rfl fun k _ => by rw [norm_inner_symm]
            _ ≤ ‖φ j‖ ^ 2 := Orthonormal.sum_inner_products_le (φ j) hϕ
            _ = 1 := by rw [hφ.1 j, one_pow]
        have hc2 : ∀ j ∈ F, ∑ k, c k j ^ 2 ≤ 1 := by
          intro j _
          rw [← NNReal.coe_le_coe]; push_cast
          calc ∑ k, ‖⟪ψ k, φ' j⟫_𝕜‖ ^ 2 ≤ ‖φ' j‖ ^ 2 := Orthonormal.sum_inner_products_le (φ' j) hψ
            _ = 1 := by rw [hφ'.1 j, one_pow]
        have core := schatten_core F hp sv a c ha1 hc1 ha2 hc2
        have hcast : ∑ k, (∑ j ∈ F, (f k j : ℝ≥0∞)) ^ p =
            ((∑ k, (∑ j ∈ F, sv j * a k j * c k j) ^ p : ℝ≥0) : ℝ≥0∞) := by
          push_cast [ENNReal.coe_rpow_of_nonneg _ hp0.le]
          rfl
        rw [hcast]
        calc ((∑ k, (∑ j ∈ F, sv j * a k j * c k j) ^ p : ℝ≥0) : ℝ≥0∞)
            ≤ ((∑ j ∈ F, sv j ^ p : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast core
          _ = ∑ j ∈ F, ENNReal.ofReal (s j) ^ p := by
              push_cast [ENNReal.coe_rpow_of_nonneg _ hp0.le]
              rfl
          _ ≤ ∑' j, ENNReal.ofReal (s j) ^ p := ENNReal.sum_le_tsum F

/-- **(6.23)** (Teschl, Lemma 6.12, p. 141): for any canonical form of `K` and `p ≥ 1`, `‖K‖_p^p = ∑ⱼ sⱼ^p`; so the
right side does not depend on the canonical form. -/
theorem schattenSum_eq_tsum [CompleteSpace E] {ι : Type*} {K : E →L[𝕜] E} {φ φ' : ι → E} {s : ι → ℝ}
    (hc : IsCanonicalForm K φ φ' s) {p : ℝ} (hp : 1 ≤ p) :
    schattenSum p K = ∑' j, ENNReal.ofReal (s j) ^ p :=
  le_antisymm
    (schattenSum_le_tsum hc.orthonormal_left hc.orthonormal_right (fun j => (hc.pos j).le) hc.hasSum_apply hp)
    (tsum_le_schattenSum hc.orthonormal_left hc.orthonormal_right (fun j => (hc.pos j).le) hc.apply_left p)

/-- A single unit vector is an orthonormal family. -/
lemma orthonormal_unique {x : E} (hx : ‖x‖ = 1) : Orthonormal 𝕜 (fun _ : Fin 1 => x) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [if_pos (Subsingleton.elim i j), inner_self_eq_norm_sq_to_K, hx]
  simp

/-- **(6.21)**: `‖K‖^p ≤ ‖K‖_p^p`. -/
theorem norm_rpow_le_schattenSum {p : ℝ} (hp : 0 < p) (K : E →L[𝕜] E) :
    ENNReal.ofReal ‖K‖ ^ p ≤ schattenSum p K := by
  -- every unit vector `x` gives `‖K x‖^p ≤ ‖K‖_p^p`, with `ψ = K x / ‖K x‖`
  have hunit : ∀ x : E, ‖x‖ = 1 → ENNReal.ofReal ‖K x‖ ^ p ≤ schattenSum p K := by
    intro x hx
    by_cases h0 : K x = 0
    · rw [h0, norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp]; exact bot_le
    · have hn : 0 < ‖K x‖ := norm_pos_iff.mpr h0
      have hψ1 : ‖((‖K x‖⁻¹ : ℝ) : 𝕜) • K x‖ = 1 := by
        rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      have h := sum_le_schattenSum (p := p) (K := K) (orthonormal_unique (𝕜 := 𝕜) hψ1)
        (orthonormal_unique (𝕜 := 𝕜) hx)
      have hterm : ‖⟪((‖K x‖⁻¹ : ℝ) : 𝕜) • K x, K x⟫_𝕜‖ₑ = ENNReal.ofReal ‖K x‖ := by
        rw [inner_smul_left, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K, ← ofReal_norm, norm_mul,
          RCLike.norm_ofReal, norm_pow, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hn), abs_norm]
        congr 1
        field_simp
      simp only [Fin.sum_univ_one] at h
      rwa [hterm] at h
  by_cases htop : schattenSum p K = ⊤
  · rw [htop]; exact le_top
  set S := (schattenSum p K).toReal
  have hS : ∀ x : E, ‖K x‖ ≤ S ^ p⁻¹ * ‖x‖ := by
    intro x
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hu : ‖((‖x‖⁻¹ : ℝ) : 𝕜) • x‖ = 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hxn), inv_mul_cancel₀ hxn.ne']
    have h := hunit _ hu
    rw [map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hxn)] at h
    have h' : (‖x‖⁻¹ * ‖K x‖) ^ p ≤ S := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le] at h
      exact (ENNReal.ofReal_le_iff_le_toReal htop).mp h
    have h'' : ‖x‖⁻¹ * ‖K x‖ ≤ S ^ p⁻¹ := by
      have := Real.rpow_le_rpow (by positivity) h' (inv_nonneg.mpr hp.le)
      rwa [← Real.rpow_mul (by positivity), mul_inv_cancel₀ hp.ne', Real.rpow_one] at this
    rw [inv_mul_le_iff₀ hxn] at h''
    linarith [mul_comm (S ^ p⁻¹) ‖x‖]
  have hK : ‖K‖ ≤ S ^ p⁻¹ := K.opNorm_le_bound (by positivity) hS
  calc ENNReal.ofReal ‖K‖ ^ p ≤ ENNReal.ofReal (S ^ p⁻¹) ^ p := by gcongr
    _ = ENNReal.ofReal S := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le, ← Real.rpow_mul ENNReal.toReal_nonneg,
          inv_mul_cancel₀ hp.ne', Real.rpow_one]
    _ = schattenSum p K := ENNReal.ofReal_toReal htop

/-- **(6.22)**: `‖K*‖_p = ‖K‖_p`. -/
theorem schattenSum_adjoint [CompleteSpace E] (p : ℝ) (K : E →L[𝕜] E) :
    schattenSum p (ContinuousLinearMap.adjoint K) = schattenSum p K := by
  have key : ∀ T : E →L[𝕜] E, schattenSum p (ContinuousLinearMap.adjoint T) ≤ schattenSum p T := by
    intro T
    refine iSup_le fun n => iSup_le fun ψ => iSup_le fun ϕ => iSup_le fun hψϕ => ?_
    have h := sum_le_schattenSum (p := p) (K := T) (ψ := ϕ) (ϕ := ψ) hψϕ.2 hψϕ.1
    refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h
    rw [ContinuousLinearMap.adjoint_inner_right, ← ofReal_norm, ← ofReal_norm, norm_inner_symm]
  refine le_antisymm (key K) ?_
  have := key (ContinuousLinearMap.adjoint K)
  rwa [ContinuousLinearMap.adjoint_adjoint] at this

end Lightlike.OperatorAlgebras.CompactSpectral
