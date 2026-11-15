import Lightlike.Asymptotics.EPRL.ChartPieces
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Localisation of an `SU(2)^4` integral at finitely many points

Let `F` be a continuous function on `SU(2)^4` with `|F| ≤ 1` whose modulus is one only on a finite
set `K`. Around each `p ∈ K` use the gnomonic chart `q ↦ (p_a γ(q_a))_a` and a smooth cutoff `χ`
of small radius. Then, for every `λ`,
`∫ F^λ = Σ_{p ∈ K} ∫ density(q) χ(q) F(chart_p q)^λ dq + O(ρ^λ)` with `ρ < 1`
(`localise_pieces`), and on the support of `χ` the modulus of `F ∘ chart_p` is one only at `q = 0`.
-/

open MeasureTheory Set Metric Filter

namespace Lightlike.Asymptotics.EPRL

open Lightlike Lightlike.Spin4

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- The cutoff `χ(tailY p Y)` on the domain of the chart around `p`, zero elsewhere. -/
noncomputable def kappa (p : Fin 4 → SU2) (χ : (Fin 12 → ℝ) → ℝ) (Y : Fin 4 → SU2) : ℝ :=
  (hemiY p).indicator (fun Y => χ (tailY p Y)) Y

lemma kappa_chartMap (p : Fin 4 → SU2) (χ : (Fin 12 → ℝ) → ℝ) (q : Fin 12 → ℝ) :
    kappa p χ (chartMap p q) = χ q := by
  simp [kappa, indicator_of_mem (chartMap_mem_hemiY p q), tailY_chartMap]

lemma kappa_ne_zero {p : Fin 4 → SU2} {χ : (Fin 12 → ℝ) → ℝ} {Y : Fin 4 → SU2}
    (h : kappa p χ Y ≠ 0) : Y ∈ hemiY p ∧ χ (tailY p Y) ≠ 0 := by
  by_cases hY : Y ∈ hemiY p
  · exact ⟨hY, by simpa [kappa, indicator_of_mem hY] using h⟩
  · exact absurd (by simp [kappa, indicator_of_notMem hY]) h

lemma measurable_tailM : Measurable fun M : SU2 => tailM (M : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hc : ∀ i j : Fin 2, Measurable fun M : SU2 => ((M : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    fun i j => (show Continuous fun M : SU2 => ((M : Matrix (Fin 2) (Fin 2) ℂ) i j) from
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)).measurable
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i
  · exact (Complex.measurable_im.comp (hc 0 0)).div (Complex.measurable_re.comp (hc 0 0))
  · exact (Complex.measurable_re.comp (hc 0 1)).div (Complex.measurable_re.comp (hc 0 0))
  · exact (Complex.measurable_im.comp (hc 0 1)).div (Complex.measurable_re.comp (hc 0 0))

lemma measurable_tailY (p : Fin 4 → SU2) : Measurable (tailY p) :=
  reshape.measurable.comp (measurable_pi_iff.mpr fun a =>
    measurable_tailM.comp (continuous_const.mul (continuous_apply a)).measurable)

lemma measurable_kappa (p : Fin 4 → SU2) {χ : (Fin 12 → ℝ) → ℝ} (hχ : Measurable χ) :
    Measurable (kappa p χ) :=
  (hχ.comp (measurable_tailY p)).indicator (isOpen_hemiY p).measurableSet

/-- **Localisation at finitely many maxima.** `F` continuous with `|F| ≤ 1` and `|F| = 1` only on
the finite set `K`. For a cutoff `χ` of small enough radius, the integral of `F^λ` over `SU(2)^4`
is the sum of the chart integrals of `χ F^λ` around the points of `K`, up to `ρ^λ` with `ρ < 1`;
and on the support of `χ` the chart `F ∘ chart_p` has modulus one only at `q = 0`. -/
theorem localise_pieces (F : (Fin 4 → SU2) → ℂ) (hF : Continuous F) (hle : ∀ Y, ‖F Y‖ ≤ 1)
    (K : Finset (Fin 4 → SU2)) (hK : ∀ Y, ‖F Y‖ = 1 → Y ∈ K) :
    ∃ r1 : ℝ, 0 < r1 ∧ ∀ χ : ContDiffBump (0 : Fin 12 → ℝ), χ.rOut < r1 →
      (∀ p ∈ K, ∀ q ∈ closedBall (0 : Fin 12 → ℝ) χ.rOut,
        ‖F (chartMap p q)‖ = 1 → q = 0) ∧
      ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ lam : ℕ,
        ‖(∫ Y, F Y ^ lam ∂(haarN 4)) - ∑ p ∈ K, ∫ q : Fin 12 → ℝ,
            haarDensity4 (reshape.symm q) • ((χ q : ℂ) * F (chartMap p q) ^ lam)‖ ≤ ρ ^ lam := by
  classical
  obtain ⟨W, hW, hdisj⟩ := (K.finite_toSet).t2_separation
  have hev : ∀ᶠ q in nhds (0 : Fin 12 → ℝ), ∀ p ∈ K, chartMap p q ∈ W p := by
    rw [Filter.eventually_all_finset]
    intro p _
    refine (continuous_chartMap p).continuousAt.eventually_mem ?_
    rw [chartMap_zero]
    exact (hW p).2.mem_nhds (hW p).1
  obtain ⟨ε, hε, hεW⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun χ hχ => ?_⟩
  have hball : ∀ q, ‖q‖ < ε → ∀ p ∈ K, chartMap p q ∈ W p := fun q hq p hp =>
    hεW (by simpa using hq) p hp
  -- uniqueness of the chart point in `K`
  have hKW : ∀ p ∈ K, ∀ Y ∈ K, Y ∈ W p → Y = p := by
    intro p hp Y hY hYW
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj hY hp hne)) (hW Y).1 hYW
  refine ⟨?_, ?_⟩
  · intro p hp q hq h1
    have hq' : ‖q‖ < ε := lt_of_le_of_lt (by simpa using mem_closedBall_zero_iff.mp hq) hχ
    have hmem := hK _ h1
    have := hKW p hp _ hmem (hball q hq' p hp)
    have h2 := tailY_chartMap p q
    have h3 : tailY p p = 0 := by simpa [chartMap_zero] using tailY_chartMap p 0
    rw [this] at h2
    exact h2.symm.trans h3
  -- the cutoffs
  have hsupp : ∀ p ∈ K, ∀ Y, kappa p χ Y ≠ 0 → Y ∈ W p := by
    intro p hp Y hY
    obtain ⟨hYh, hχY⟩ := kappa_ne_zero hY
    have : tailY p Y ∈ Function.support χ := hχY
    rw [χ.support_eq] at this
    have hn : ‖tailY p Y‖ < ε := lt_trans (by simpa using this) hχ
    have := hball _ hn p hp
    rwa [chartMap_tailY hYh] at this
  have hk0 : ∀ p Y, 0 ≤ kappa p χ Y := fun p Y => by
    unfold kappa
    exact indicator_nonneg (fun Y _ => χ.nonneg) Y
  have hk1 : ∀ p Y, kappa p χ Y ≤ 1 := fun p Y => by
    unfold kappa
    exact indicator_apply_le' (fun _ => χ.le_one) (fun _ => zero_le_one)
  have hdis : ∀ p ∈ K, ∀ p' ∈ K, p ≠ p' → ∀ Y, kappa p χ Y ≠ 0 → kappa p' χ Y = 0 := by
    intro p hp p' hp' hne Y hY
    by_contra h
    exact (Set.disjoint_left.mp (hdisj hp hp' hne)) (hsupp p hp Y hY) (hsupp p' hp' Y h)
  set S : (Fin 4 → SU2) → ℝ := fun Y => ∑ p ∈ K, kappa p χ Y with hS
  have hS01 : ∀ Y, 0 ≤ S Y ∧ S Y ≤ 1 := by
    intro Y
    by_cases h : ∃ p ∈ K, kappa p χ Y ≠ 0
    · obtain ⟨p, hp, hpY⟩ := h
      have : S Y = kappa p χ Y := Finset.sum_eq_single p
        (fun p' hp' hne => hdis p hp p' hp' (Ne.symm hne) Y hpY) (fun h => absurd hp h)
      rw [this]; exact ⟨hk0 _ _, hk1 _ _⟩
    · push Not at h
      have : S Y = 0 := Finset.sum_eq_zero fun p hp => h p hp
      rw [this]; norm_num
  -- the neighbourhood of the maximum set
  set U : Set (Fin 4 → SU2) := ⋃ p ∈ K, hemiY p ∩ tailY p ⁻¹' ball 0 χ.rIn with hU
  have hUo : IsOpen U :=
    isOpen_biUnion fun p _ => (continuousOn_tailY p).isOpen_inter_preimage (isOpen_hemiY p)
      isOpen_ball
  have hS1 : ∀ Y ∈ U, S Y = 1 := by
    intro Y hY
    simp only [hU, mem_iUnion] at hY
    obtain ⟨p, hp, hYh, hYt⟩ := hY
    have hkp : kappa p χ Y = 1 := by
      simp only [kappa, indicator_of_mem hYh]
      exact χ.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr (le_of_lt (by simpa using hYt)))
    have : S Y = kappa p χ Y := Finset.sum_eq_single p
      (fun p' hp' hne => hdis p hp p' hp' (Ne.symm hne) Y (by rw [hkp]; norm_num)) (fun h => absurd hp h)
    rw [this, hkp]
  have hmaxU : ∀ Y, ‖F Y‖ = 1 → Y ∈ U := by
    intro Y hY
    have hYK := hK Y hY
    simp only [hU, mem_iUnion]
    refine ⟨Y, hYK, ?_, ?_⟩
    · intro a; simpa using one_mem_hemiSU
    · have : tailY Y Y = 0 := by
        have := tailY_chartMap Y 0
        rwa [chartMap_zero] at this
      simpa [this] using χ.rIn_pos
  -- the sup of `|F|` off `U`
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ Y, Y ∉ U → ‖F Y‖ ≤ ρ := by
    by_cases hne : Uᶜ.Nonempty
    · obtain ⟨x₀, hx₀, hmx⟩ := hUo.isClosed_compl.isCompact.exists_isMaxOn hne hF.norm.continuousOn
      exact ⟨_, norm_nonneg _, lt_of_le_of_ne (hle x₀) fun h => hx₀ (hmaxU x₀ h),
        fun x hx => hmx hx⟩
    · exact ⟨0, le_rfl, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  refine ⟨ρ, hρ0, hρ1, fun lam => ?_⟩
  have hmeasχ : Measurable (χ : (Fin 12 → ℝ) → ℝ) := χ.continuous.measurable
  have hFm : Measurable fun Y => F Y ^ lam := (hF.pow lam).measurable
  have hfm : ∀ p, Measurable fun Y => (kappa p χ Y : ℂ) * F Y ^ lam := fun p =>
    (Complex.measurable_ofReal.comp (measurable_kappa p hmeasχ)).mul hFm
  have hfb : ∀ p Y, ‖(kappa p χ Y : ℂ) * F Y ^ lam‖ ≤ 1 := by
    intro p Y
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hk0 p Y)]
    calc _ ≤ (1 : ℝ) * 1 := mul_le_mul (hk1 p Y) (pow_le_one₀ (norm_nonneg _) (hle Y))
          (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = 1 := one_mul 1
  have hfi : ∀ p, Integrable (fun Y => (kappa p χ Y : ℂ) * F Y ^ lam) (haarN 4) := fun p =>
    Integrable.of_bound (hfm p).aestronglyMeasurable 1 (ae_of_all _ (hfb p))
  have hFi : Integrable (fun Y => F Y ^ lam) (haarN 4) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1
      (ae_of_all _ fun Y => by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hle Y))
  have hpiece : ∀ p, ∫ Y, (kappa p χ Y : ℂ) * F Y ^ lam ∂(haarN 4) =
      ∫ q : Fin 12 → ℝ, haarDensity4 (reshape.symm q) • ((χ q : ℂ) * F (chartMap p q) ^ lam) := by
    intro p
    rw [integral_haar4_chart p _ (hfm p) (fun Y hY a =>
      (kappa_ne_zero (p := p) (χ := χ) (Y := Y) (fun h => hY (by rw [h]; simp))).1 a)]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    show _ • ((kappa p χ (chartMap p q) : ℂ) * _) = _
    rw [kappa_chartMap]
    rfl
  rw [Finset.sum_congr rfl (fun p _ => (hpiece p).symm),
    ← integral_finsetSum _ (fun p _ => hfi p),
    ← integral_sub hFi (integrable_finsetSum _ fun p _ => hfi p)]
  have hb : ∀ Y, ‖F Y ^ lam - ∑ p ∈ K, (kappa p χ Y : ℂ) * F Y ^ lam‖ ≤ ρ ^ lam := by
    intro Y
    have : F Y ^ lam - ∑ p ∈ K, (kappa p χ Y : ℂ) * F Y ^ lam =
        ((1 - S Y : ℝ) : ℂ) * F Y ^ lam := by
      rw [← Finset.sum_mul]
      simp only [hS, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_sum]
      ring
    rw [this]
    by_cases hY : Y ∈ U
    · rw [hS1 Y hY]; simpa using pow_nonneg hρ0 lam
    · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [(hS01 Y).2])]
      calc _ ≤ 1 * ‖F Y‖ ^ lam := by
            gcongr
            linarith [(hS01 Y).1]
        _ ≤ ρ ^ lam := by rw [one_mul]; exact pow_le_pow_left₀ (norm_nonneg _) (hρ Y hY) lam
  calc _ ≤ ρ ^ lam * (haarN (N := 4)).real Set.univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ hb)
    _ = ρ ^ lam := by simp [measureReal_def]

end Lightlike.Asymptotics.EPRL
