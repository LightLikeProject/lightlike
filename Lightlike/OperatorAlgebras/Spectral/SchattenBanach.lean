import Lightlike.OperatorAlgebras.Spectral.Schatten

/-!
# The Schatten classes are Banach spaces

G. Teschl, *Mathematical Methods in Quantum Mechanics*, Section 6.3, Lemma 6.12, pp. 141-142: "The spaces `J_p(H)`
together with the norm `‖.‖_p` are Banach spaces." The proof: the triangle inequality from (6.23) and Minkowski's
inequality, and completeness since a `‖.‖_p`-Cauchy sequence is `‖.‖`-Cauchy by (6.21), its norm limit `K` is compact,
and the finite sums of (6.23) pass to the limit.

* `schattenNorm p K = ‖K‖_p` (in `ℝ≥0∞`);
* `schattenNorm_add_le` (the triangle inequality), `schattenSum_smul` (homogeneity),
  `schattenNorm_eq_zero_iff` (definiteness);
* `schattenSum_le_of_tendsto`: if `Kₙ → K` in norm and `‖Kₙ‖_p^p ≤ C`, then `‖K‖_p^p ≤ C`;
* `exists_tendsto_schattenNorm`: completeness.
-/

open scoped InnerProductSpace NNReal ENNReal Topology
open Filter

namespace Lightlike.OperatorAlgebras.CompactSpectral

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Schatten norm** `‖K‖_p = (‖K‖_p^p)^{1/p}` (Teschl (6.19), (6.23)), in `ℝ≥0∞`. -/
noncomputable def schattenNorm (p : ℝ) (K : E →L[𝕜] E) : ℝ≥0∞ := schattenSum p K ^ (1 / p)

lemma schattenNorm_rpow {p : ℝ} (hp : 0 < p) (K : E →L[𝕜] E) : schattenNorm p K ^ p = schattenSum p K := by
  rw [schattenNorm, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- **The triangle inequality** (Teschl, Lemma 6.12, p. 142): `‖K₁ + K₂‖_p ≤ ‖K₁‖_p + ‖K₂‖_p` for `p ≥ 1`. -/
theorem schattenNorm_add_le {p : ℝ} (hp : 1 ≤ p) (K₁ K₂ : E →L[𝕜] E) :
    schattenNorm p (K₁ + K₂) ≤ schattenNorm p K₁ + schattenNorm p K₂ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have key : schattenSum p (K₁ + K₂) ≤ (schattenNorm p K₁ + schattenNorm p K₂) ^ p := by
    refine iSup_le fun n => iSup_le fun ψ => iSup_le fun ϕ => iSup_le fun hψϕ => ?_
    set a : Fin n → ℝ≥0∞ := fun k => ‖⟪ψ k, K₁ (ϕ k)⟫_𝕜‖ₑ
    set b : Fin n → ℝ≥0∞ := fun k => ‖⟪ψ k, K₂ (ϕ k)⟫_𝕜‖ₑ
    have h1 : ∑ k, ‖⟪ψ k, (K₁ + K₂) (ϕ k)⟫_𝕜‖ₑ ^ p ≤ ∑ k, (a k + b k) ^ p := by
      refine Finset.sum_le_sum fun k _ => ENNReal.rpow_le_rpow ?_ hp0.le
      rw [ContinuousLinearMap.add_apply, inner_add_right]
      exact enorm_add_le _ _
    have hmink := ENNReal.Lp_add_le Finset.univ a b hp
    have ha : (∑ k, a k ^ p) ^ (1 / p) ≤ schattenNorm p K₁ :=
      ENNReal.rpow_le_rpow (sum_le_schattenSum hψϕ.1 hψϕ.2) (by positivity)
    have hb : (∑ k, b k ^ p) ^ (1 / p) ≤ schattenNorm p K₂ :=
      ENNReal.rpow_le_rpow (sum_le_schattenSum hψϕ.1 hψϕ.2) (by positivity)
    have h2 : (∑ k, (a k + b k) ^ p) ^ (1 / p) ≤ schattenNorm p K₁ + schattenNorm p K₂ :=
      hmink.trans (add_le_add ha hb)
    calc ∑ k, ‖⟪ψ k, (K₁ + K₂) (ϕ k)⟫_𝕜‖ₑ ^ p ≤ ∑ k, (a k + b k) ^ p := h1
      _ = ((∑ k, (a k + b k) ^ p) ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
      _ ≤ _ := ENNReal.rpow_le_rpow h2 hp0.le
  calc schattenNorm p (K₁ + K₂) = schattenSum p (K₁ + K₂) ^ (1 / p) := rfl
    _ ≤ ((schattenNorm p K₁ + schattenNorm p K₂) ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow key (by positivity)
    _ = _ := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- **Homogeneity**: `‖c K‖_p^p = |c|^p ‖K‖_p^p`. -/
theorem schattenSum_smul {p : ℝ} (hp : 0 ≤ p) (c : 𝕜) (K : E →L[𝕜] E) :
    schattenSum p (c • K) = ‖c‖ₑ ^ p * schattenSum p K := by
  simp only [schattenSum, ENNReal.mul_iSup, Finset.mul_sum]
  refine iSup_congr fun n => iSup_congr fun ψ => iSup_congr fun ϕ => iSup_congr fun _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp]

/-- **Definiteness**: `‖K‖_p = 0` iff `K = 0`, for `p > 0` (by (6.21)). -/
theorem schattenNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (K : E →L[𝕜] E) : schattenNorm p K = 0 ↔ K = 0 := by
  constructor
  · intro h
    have h1 := norm_rpow_le_schattenSum hp K
    rw [← schattenNorm_rpow hp, h, ENNReal.zero_rpow_of_pos hp, nonpos_iff_eq_zero,
      ENNReal.rpow_eq_zero_iff] at h1
    rcases h1 with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact norm_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp h1) (norm_nonneg _))
    · exact absurd h1 (not_lt.mpr hp.le)
  · rintro rfl
    have : schattenSum p (0 : E →L[𝕜] E) = 0 := by
      have h := schattenSum_smul hp.le (0 : 𝕜) (0 : E →L[𝕜] E)
      rwa [zero_smul, enorm_zero, ENNReal.zero_rpow_of_pos hp, zero_mul] at h
    rw [schattenNorm, this, ENNReal.zero_rpow_of_pos (by positivity)]

/-- **Lower semicontinuity**: if `Kₙ → K` in norm and `‖Kₙ‖_p^p ≤ C` for all `n`, then `‖K‖_p^p ≤ C` (Teschl,
Lemma 6.12, p. 142: the finite sums of (6.23) pass to the limit). -/
theorem schattenSum_le_of_tendsto {p : ℝ} (hp : 0 ≤ p) {Kn : ℕ → E →L[𝕜] E} {K : E →L[𝕜] E}
    (hK : Tendsto Kn atTop (𝓝 K)) {C : ℝ≥0∞} (hC : ∀ᶠ n in atTop, schattenSum p (Kn n) ≤ C) :
    schattenSum p K ≤ C := by
  refine iSup_le fun n => iSup_le fun ψ => iSup_le fun ϕ => iSup_le fun hψϕ => ?_
  have hcont : Continuous fun T : E →L[𝕜] E => ∑ k, ‖⟪ψ k, T (ϕ k)⟫_𝕜‖ₑ ^ p := by
    refine continuous_finset_sum _ fun k _ => ?_
    exact (ENNReal.continuous_rpow_const).comp (continuous_enorm.comp
      ((continuous_const.inner (continuous_id.clm_apply continuous_const))))
  refine le_of_tendsto ((hcont.tendsto K).comp hK) ?_
  filter_upwards [hC] with m hm
  exact (sum_le_schattenSum hψϕ.1 hψϕ.2).trans hm

/-- **(6.21) for the norm**: `‖K‖ ≤ ‖K‖_p`. -/
lemma ofReal_norm_le_schattenNorm {p : ℝ} (hp : 0 < p) (K : E →L[𝕜] E) :
    ENNReal.ofReal ‖K‖ ≤ schattenNorm p K := by
  have h := ENNReal.rpow_le_rpow (norm_rpow_le_schattenSum hp K) (by positivity : (0 : ℝ) ≤ 1 / p)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] at h

/-- `‖-K‖_p = ‖K‖_p`. -/
lemma schattenNorm_neg {p : ℝ} (hp : 0 ≤ p) (K : E →L[𝕜] E) : schattenNorm p (-K) = schattenNorm p K := by
  have h := schattenSum_smul hp (-1 : 𝕜) K
  rw [neg_one_smul, enorm_neg, enorm_one, ENNReal.one_rpow, one_mul] at h
  rw [schattenNorm, schattenNorm, h]

/-- **Completeness** (Teschl, Lemma 6.12, p. 142): a sequence of compact operators with finite `‖.‖_p` that is Cauchy
for `‖.‖_p` converges in `‖.‖_p` to a compact operator with finite `‖.‖_p`. -/
theorem exists_tendsto_schattenNorm [CompleteSpace E] {p : ℝ} (hp : 1 ≤ p) {Kn : ℕ → E →L[𝕜] E}
    (hcomp : ∀ n, IsCompactOperator (Kn n)) (hfin : ∀ n, schattenNorm p (Kn n) < ⊤)
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, schattenNorm p (Kn m - Kn n) ≤ ε) :
    ∃ K : E →L[𝕜] E, IsCompactOperator K ∧ schattenNorm p K < ⊤ ∧
      Tendsto (fun n => schattenNorm p (Kn n - K)) atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  -- Cauchy in the operator norm, by (6.21)
  have hcs : CauchySeq Kn := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ENNReal.ofReal (ε / 2)) (by simpa using half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := (ofReal_norm_le_schattenNorm hp0 (Kn m - Kn n)).trans (hN m hm n hn)
    rw [dist_eq_norm]
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    linarith
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete hcs
  have hKc : IsCompactOperator K := isCompactOperator_of_tendsto hK (Eventually.of_forall hcomp)
  -- the tail bound `‖Kₙ - K‖_p ≤ ε`
  have htail : ∀ ε > 0, ∃ N, ∀ n ≥ N, schattenNorm p (Kn n - K) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hlim : Tendsto (fun m => Kn n - Kn m) atTop (𝓝 (Kn n - K)) := tendsto_const_nhds.sub hK
    have hbound : ∀ᶠ m in atTop, schattenSum p (Kn n - Kn m) ≤ ε ^ p := by
      filter_upwards [eventually_ge_atTop N] with m hm
      rw [← schattenNorm_rpow hp0]
      exact ENNReal.rpow_le_rpow (hN n hn m hm) hp0.le
    have h := schattenSum_le_of_tendsto hp0.le hlim hbound
    have h' := ENNReal.rpow_le_rpow h (by positivity : (0 : ℝ) ≤ 1 / p)
    rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at h'
  refine ⟨K, hKc, ?_, ENNReal.tendsto_atTop_zero.mpr htail⟩
  obtain ⟨N, hN⟩ := htail 1 one_pos
  have hK' : K = Kn N + -(Kn N - K) := by abel
  calc schattenNorm p K = schattenNorm p (Kn N + -(Kn N - K)) := by rw [← hK']
    _ ≤ schattenNorm p (Kn N) + schattenNorm p (-(Kn N - K)) := schattenNorm_add_le hp _ _
    _ = schattenNorm p (Kn N) + schattenNorm p (Kn N - K) := by rw [schattenNorm_neg hp0.le]
    _ ≤ schattenNorm p (Kn N) + 1 := by gcongr; exact hN N le_rfl
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hfin N, ENNReal.one_lt_top⟩

end Lightlike.OperatorAlgebras.CompactSpectral
