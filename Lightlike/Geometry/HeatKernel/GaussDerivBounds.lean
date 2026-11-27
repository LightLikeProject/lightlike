import Mathlib

/-!
# Derivative bounds for the Gaussian factor

For a smooth `σ` on a set `s` with unique derivatives and a compact `K ⊆ s`, the `ℓ`-th derivative of
`q ↦ e^{-σ(q)/4t}` is bounded on `K` by `C t^{-ℓ} e^{-σ(q)/4t}` for `t ∈ (0, 1]`
(`norm_iteratedFDerivWithin_gauss_le`): Faà di Bruno's bound (`norm_iteratedFDerivWithin_comp_le`) with the
derivatives of `exp` at `-σ(q)/4t` equal to `e^{-σ(q)/4t}` and those of `-σ/4t` bounded by `(C/t)^i`. This is the
first step of the derivative bounds of the heat error of the parametrix.
-/

open Set Real Nat
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The iterated derivatives of `exp` at a point have norm `exp` of that point. -/
theorem norm_iteratedFDerivWithin_exp_univ (i : ℕ) (x : ℝ) :
    ‖iteratedFDerivWithin ℝ i Real.exp univ x‖ = Real.exp x := by
  rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]

/-- **A uniform bound on the derivatives of a smooth function on a compact set**, all orders up to `ℓ`. -/
theorem exists_bound_iteratedFDerivWithin {s : Set E} (hs : UniqueDiffOn ℝ s) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f s) {K : Set E} (hK : IsCompact K) (hKs : K ⊆ s) (ℓ : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ ℓ, ∀ q ∈ K, ‖iteratedFDerivWithin ℝ i f s q‖ ≤ M := by
  have hc : ContinuousOn (fun q => ∑ i ∈ Finset.range (ℓ + 1), ‖iteratedFDerivWithin ℝ i f s q‖) s :=
    continuousOn_finsetSum _ fun i _ =>
      (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top) hs).norm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono hKs)
  refine ⟨|M|, abs_nonneg _, fun i hi q hq => ?_⟩
  have h1 := hM q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  have h2 : ‖iteratedFDerivWithin ℝ i f s q‖ ≤ ∑ j ∈ Finset.range (ℓ + 1), ‖iteratedFDerivWithin ℝ j f s q‖ :=
    Finset.single_le_sum (f := fun j => ‖iteratedFDerivWithin ℝ j f s q‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  linarith [le_abs_self M]

/-- **The derivatives of the Gaussian factor**: `‖D^ℓ e^{-σ/4t}(q)‖ ≤ C t^{-ℓ} e^{-σ(q)/4t}` on a compact set, for
`t ∈ (0, 1]`. -/
theorem norm_iteratedFDerivWithin_gauss_le {s : Set E} (hs : UniqueDiffOn ℝ s) {σ : E → ℝ}
    (hσ : ContDiffOn ℝ ∞ σ s) {K : Set E} (hK : IsCompact K) (hKs : K ⊆ s) (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ q ∈ K,
      ‖iteratedFDerivWithin ℝ ℓ (fun q => Real.exp (-σ q / (4 * t))) s q‖ ≤
        C * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t)) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDerivWithin hs hσ hK hKs ℓ
  set B := M / 4 + 1 with hB
  have hB1 : 1 ≤ B := by rw [hB]; linarith [hM0]
  refine ⟨ℓ ! * B ^ ℓ, by positivity, fun t ht q hq => ?_⟩
  have ht0 : 0 < t := ht.1
  have htinv : 1 ≤ t⁻¹ := one_le_inv₀ ht0 |>.2 ht.2
  set c : ℝ := -(4 * t)⁻¹ with hc
  have hfun : (fun q => Real.exp (-σ q / (4 * t))) = Real.exp ∘ (c • σ) := by
    funext q; simp only [Function.comp, Pi.smul_apply, smul_eq_mul, hc]; congr 1; field_simp
  have hcs : ContDiffOn ℝ ∞ (c • σ) s := hσ.const_smul c
  have hD : ∀ i, 1 ≤ i → i ≤ ℓ → ‖iteratedFDerivWithin ℝ i (c • σ) s q‖ ≤ (B * t⁻¹) ^ i := by
    intro i hi1 hiℓ
    rw [iteratedFDerivWithin_const_smul_apply ((hσ.of_le (by exact_mod_cast le_top)) q (hKs hq)) hs (hKs hq),
      norm_smul, hc, norm_neg, norm_inv, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 4 * t)]
    have h1 : (4 * t)⁻¹ * ‖iteratedFDerivWithin ℝ i σ s q‖ ≤ B * t⁻¹ := by
      have := hM i hiℓ q hq
      rw [mul_inv, mul_comm]
      calc ‖iteratedFDerivWithin ℝ i σ s q‖ * (4⁻¹ * t⁻¹) ≤ M * (4⁻¹ * t⁻¹) := by gcongr
        _ = M / 4 * t⁻¹ := by ring
        _ ≤ B * t⁻¹ := by gcongr; rw [hB]; linarith
    have h2 : B * t⁻¹ ≤ (B * t⁻¹) ^ i := le_self_pow₀ (one_le_mul_of_one_le_of_one_le hB1 htinv) (by omega)
    linarith
  have hC : ∀ i, i ≤ ℓ → ‖iteratedFDerivWithin ℝ i Real.exp univ ((c • σ) q)‖ ≤ Real.exp ((c • σ) q) :=
    fun i _ => (norm_iteratedFDerivWithin_exp_univ i _).le
  have h := norm_iteratedFDerivWithin_comp_le (N := ∞) Real.contDiff_exp.contDiffOn hcs
    (by exact_mod_cast le_top) uniqueDiffOn_univ hs (mapsTo_univ _ _) (hKs hq) hC hD
  rw [hfun]
  have he : Real.exp ((c • σ) q) = Real.exp (-σ q / (4 * t)) := by
    simp only [Pi.smul_apply, smul_eq_mul, hc]; congr 1; field_simp
  rw [he] at h
  calc _ ≤ (ℓ ! : ℝ) * Real.exp (-σ q / (4 * t)) * (B * t⁻¹) ^ ℓ := h
    _ = ℓ ! * B ^ ℓ * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t)) := by rw [mul_pow]; ring

/-- **Off the diagonal the Gaussian factor beats every power**: if `δ ≤ s` with `δ > 0`, then
`t^{-m} e^{-s/4t} ≤ m! (4/δ)^m` for `t > 0`. -/
theorem inv_pow_mul_exp_neg_le {δ s t : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) (ht : 0 < t) (m : ℕ) :
    t⁻¹ ^ m * Real.exp (-s / (4 * t)) ≤ m ! * (4 / δ) ^ m := by
  set u := δ / (4 * t) with hu
  have hu0 : 0 ≤ u := by positivity
  have hinv : t⁻¹ = 4 / δ * u := by rw [hu]; field_simp
  have he : Real.exp (-s / (4 * t)) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.2; rw [hu, neg_div, neg_le_neg_iff]; gcongr
  have hf : u ^ m * Real.exp (-u) ≤ m ! := by
    have h1 := Real.pow_div_factorial_le_exp u hu0 m
    have hfac : (0 : ℝ) < m ! := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hfac] at h1
    have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-u)]
  rw [hinv, mul_pow]
  calc (4 / δ) ^ m * u ^ m * Real.exp (-s / (4 * t)) ≤ (4 / δ) ^ m * u ^ m * Real.exp (-u) := by gcongr
    _ = (4 / δ) ^ m * (u ^ m * Real.exp (-u)) := by ring
    _ ≤ (4 / δ) ^ m * m ! := by gcongr
    _ = m ! * (4 / δ) ^ m := mul_comm _ _

/-- The Gaussian factor is smooth wherever `σ` is. -/
theorem contDiffOn_gauss {s : Set E} {σ : E → ℝ} (hσ : ContDiffOn ℝ ∞ σ s) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun q => Real.exp (-σ q / (4 * t))) s :=
  Real.contDiff_exp.comp_contDiffOn (hσ.neg.div_const _)

/-- **The derivatives of a smooth multiple of the Gaussian factor**:
`‖D^ℓ (a e^{-σ/4t})(q)‖ ≤ C t^{-ℓ} e^{-σ(q)/4t}` on a compact set, for `t ∈ (0, 1]`. -/
theorem norm_iteratedFDerivWithin_mul_gauss_le {s : Set E} (hs : UniqueDiffOn ℝ s) {a σ : E → ℝ}
    (ha : ContDiffOn ℝ ∞ a s) (hσ : ContDiffOn ℝ ∞ σ s) {K : Set E} (hK : IsCompact K) (hKs : K ⊆ s)
    (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ q ∈ K,
      ‖iteratedFDerivWithin ℝ ℓ (fun q => a q * Real.exp (-σ q / (4 * t))) s q‖ ≤
        C * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t)) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDerivWithin hs ha hK hKs ℓ
  have hG := fun j => norm_iteratedFDerivWithin_gauss_le hs hσ hK hKs j
  choose Cg hCg0 hCg using hG
  refine ⟨∑ i ∈ Finset.range (ℓ + 1), (ℓ.choose i : ℝ) * M * Cg (ℓ - i),
    Finset.sum_nonneg fun i _ => by have := hCg0 (ℓ - i); positivity, fun t ht q hq => ?_⟩
  have ht0 : 0 < t := ht.1
  have htinv : 1 ≤ t⁻¹ := one_le_inv₀ ht0 |>.2 ht.2
  have he0 : 0 ≤ Real.exp (-σ q / (4 * t)) := (Real.exp_pos _).le
  have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) ha (contDiffOn_gauss hσ t) hs (hKs hq)
    (n := ℓ) (by exact_mod_cast le_top)
  refine hL.trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hiℓ : i ≤ ℓ := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 := hM i hiℓ q hq
  have h2 := hCg (ℓ - i) t ht q hq
  have h3 : t⁻¹ ^ (ℓ - i) ≤ t⁻¹ ^ ℓ := pow_le_pow_right₀ htinv (Nat.sub_le ℓ i)
  have hc0 : (0 : ℝ) ≤ ℓ.choose i := by positivity
  have hCg0' := hCg0 (ℓ - i)
  calc (ℓ.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i a s q‖ *
        ‖iteratedFDerivWithin ℝ (ℓ - i) (fun q => Real.exp (-σ q / (4 * t))) s q‖
      ≤ (ℓ.choose i : ℝ) * M * (Cg (ℓ - i) * t⁻¹ ^ (ℓ - i) * Real.exp (-σ q / (4 * t))) := by
        gcongr
    _ ≤ (ℓ.choose i : ℝ) * M * (Cg (ℓ - i) * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t))) := by gcongr
    _ = (ℓ.choose i : ℝ) * M * Cg (ℓ - i) * t⁻¹ ^ ℓ * Real.exp (-σ q / (4 * t)) := by ring

end Lightlike
