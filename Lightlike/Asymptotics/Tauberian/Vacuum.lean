import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The vacuum from the low-temperature form of the partition function

For a positive measure `σ` with `Z(β) = ∫ e^{-β x} dσ` finite, the bound `e^{-v β} Z(β) ≤ K` for all
large `β` forces `σ (-∞, -v) = 0` (`no_mass_below`): the ground state is at `-v` (MZ (2.5) with the
modular transformation `β' = 4π²/β`).
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- **No mass below the vacuum.** -/
theorem no_mass_below (σ : Measure ℝ) {v K B : ℝ} (hB : 0 < B)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) σ)
    (hK : ∀ β : ℝ, B ≤ β → Real.exp (-(v * β)) * ∫ x, Real.exp (-β * x) ∂σ ≤ K) :
    σ (Iio (-v)) = 0 := by
  by_contra hne
  have h1 : (⋃ n : ℕ, Iio (-v - 1 / ((n : ℝ) + 1))) = Iio (-v) := by
    ext x
    simp only [mem_iUnion, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < -v - x by linarith)
      exact ⟨n, by linarith⟩
  have h2 : ∃ n : ℕ, σ (Iio (-v - 1 / ((n : ℝ) + 1))) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    rw [← h1]
    exact measure_iUnion_null hall
  obtain ⟨n, hn⟩ := h2
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  set m : ℝ := σ.real (Iio (-v - ε)) with hm
  have hmpos : 0 < m := by
    have hfin : σ (Iio (-v - ε)) ≠ ⊤ := by
      have := (hint 1 one_pos).measure_ge_lt_top (ε := Real.exp (v + ε)) (Real.exp_pos _)
      refine ne_top_of_le_ne_top this.ne ?_
      refine measure_mono fun x hx => ?_
      simp only [mem_Iio] at hx
      simp only [mem_ofPred_eq]
      exact Real.exp_le_exp.2 (by linarith)
    exact ENNReal.toReal_pos hn hfin
  -- `e^{-vβ} Z(β) ≥ e^{εβ} m`
  have hlow : ∀ β : ℝ, 0 < β → Real.exp (ε * β) * m ≤ Real.exp (-(v * β)) * ∫ x, Real.exp (-β * x) ∂σ := by
    intro β hβ
    have hM := mul_meas_ge_le_integral_of_nonneg (μ := σ)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos (-β * x)).le) (hint β hβ)
      (Real.exp (β * (v + ε)))
    have hsub : Iio (-v - ε) ⊆ {x : ℝ | Real.exp (β * (v + ε)) ≤ Real.exp (-β * x)} := by
      intro x hx
      simp only [mem_Iio] at hx
      simp only [mem_ofPred_eq]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hmeas : σ.real (Iio (-v - ε)) ≤ σ.real {x : ℝ | Real.exp (β * (v + ε)) ≤ Real.exp (-β * x)} :=
      measureReal_mono hsub ((hint β hβ).measure_ge_lt_top (ε := Real.exp (β * (v + ε)))
        (Real.exp_pos _)).ne
    have h3 : Real.exp (β * (v + ε)) * m ≤ ∫ x, Real.exp (-β * x) ∂σ :=
      (mul_le_mul_of_nonneg_left hmeas (Real.exp_pos _).le).trans hM
    calc Real.exp (ε * β) * m = Real.exp (-(v * β)) * (Real.exp (β * (v + ε)) * m) := by
          rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
  -- contradiction for large β
  have hK' : ∀ β : ℝ, B ≤ β → Real.exp (ε * β) * m ≤ K := fun β hβ =>
    (hlow β (by linarith)).trans (hK β hβ)
  have htend : Tendsto (fun β : ℝ => Real.exp (ε * β) * m) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hmpos ((Real.tendsto_exp_atTop).comp
      (Filter.Tendsto.const_mul_atTop hε0 tendsto_id))
  obtain ⟨β, hβ⟩ := (htend.eventually_gt_atTop K).and (eventually_ge_atTop B) |>.exists
  exact absurd (hK' β hβ.2) (not_le.2 hβ.1)

/-- `e^{-vβ} Z(β) = σ{-v} + ∫_{x > -v} e^{-β (x + v)} dσ` when there is no mass below `-v`. -/
lemma exp_mul_Z_eq (σ : Measure ℝ) {v : ℝ} (hno : σ (Iio (-v)) = 0)
    {β : ℝ} (hβ : 0 < β) (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) σ) :
    Real.exp (-(v * β)) * ∫ x, Real.exp (-β * x) ∂σ =
      σ.real {-v} + ∫ x in Ioi (-v), Real.exp (-β * (x + v)) ∂σ := by
  have hae : ∀ᵐ x ∂σ, x ∉ Iio (-v) := measure_eq_zero_iff_ae_notMem.1 hno
  rw [← integral_const_mul]
  have h1 : ∀ x : ℝ, Real.exp (-(v * β)) * Real.exp (-β * x) = Real.exp (-β * (x + v)) := fun x => by
    rw [← Real.exp_add]; congr 1; ring
  simp_rw [h1]
  have hint' : Integrable (fun x : ℝ => Real.exp (-β * (x + v))) σ := by
    have := hint.const_mul (Real.exp (-(v * β)))
    exact this.congr (Filter.Eventually.of_forall fun x => h1 x)
  have hsplit : Set.univ =ᵐ[σ] ({-v} ∪ Ioi (-v) : Set ℝ) := by
    filter_upwards [hae] with x hx
    simp only [mem_Iio, not_lt] at hx
    simp only [eq_iff_iff, mem_univ, mem_union, mem_singleton_iff, mem_Ioi, true_iff]
    rcases eq_or_lt_of_le hx with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  have hres : σ.restrict ({-v} ∪ Ioi (-v)) = σ := by
    rw [← Measure.restrict_congr_set hsplit, Measure.restrict_univ]
  have hU : ∫ a, Real.exp (-β * (a + v)) ∂σ =
      ∫ a in ({-v} ∪ Ioi (-v) : Set ℝ), Real.exp (-β * (a + v)) ∂σ := by rw [hres]
  rw [hU, setIntegral_union (by simp) measurableSet_Ioi hint'.integrableOn hint'.integrableOn]
  simp [measureReal_def]

/-- **The vacuum atom.** If `e^{-vβ} Z(β) → 1` and there is no mass below `-v`, then `σ{-v} = 1`. -/
theorem atom_eq_one (σ : Measure ℝ) {v B : ℝ} (hB : 0 < B)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) σ)
    (hno : σ (Iio (-v)) = 0)
    (hlim : Tendsto (fun β : ℝ => Real.exp (-(v * β)) * ∫ x, Real.exp (-β * x) ∂σ) atTop (𝓝 1)) :
    σ.real {-v} = 1 := by
  have hbound : Integrable (fun x : ℝ => Real.exp (-B * (x + v))) (σ.restrict (Ioi (-v))) := by
    have h1 : ∀ x : ℝ, Real.exp (-(v * B)) * Real.exp (-B * x) = Real.exp (-B * (x + v)) := fun x => by
      rw [← Real.exp_add]; congr 1; ring
    have := ((hint B hB).const_mul (Real.exp (-(v * B)))).congr (Filter.Eventually.of_forall fun x => h1 x)
    exact this.integrableOn
  have hR : Tendsto (fun β : ℝ => ∫ x in Ioi (-v), Real.exp (-β * (x + v)) ∂σ) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := σ.restrict (Ioi (-v)))
      (l := atTop) (F := fun (β : ℝ) (x : ℝ) => Real.exp (-β * (x + v)))
      (f := fun _ => (0 : ℝ)) (fun x => Real.exp (-B * (x + v)))
      (Filter.Eventually.of_forall fun β => by fun_prop)
      ?_ hbound ?_
    · simpa using this
    · filter_upwards [eventually_ge_atTop B] with β hβ
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx' : 0 < x + v := by simp only [mem_Ioi] at hx; linarith
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.2 (by nlinarith)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx' : 0 < x + v := by simp only [mem_Ioi] at hx; linarith
      have h1 : Tendsto (fun β : ℝ => β * (x + v)) atTop atTop :=
        tendsto_id.atTop_mul_const hx'
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      refine h2.congr (fun β => ?_)
      simp [neg_mul]
  have hEq : ∀ᶠ β : ℝ in atTop, Real.exp (-(v * β)) * ∫ x, Real.exp (-β * x) ∂σ =
      σ.real {-v} + ∫ x in Ioi (-v), Real.exp (-β * (x + v)) ∂σ := by
    filter_upwards [eventually_ge_atTop B] with β hβ
    exact exp_mul_Z_eq σ hno (by linarith) (hint β (by linarith))
  have h2 : Tendsto (fun β : ℝ => σ.real {-v} + ∫ x in Ioi (-v), Real.exp (-β * (x + v)) ∂σ) atTop
      (𝓝 (σ.real {-v} + 0)) := tendsto_const_nhds.add hR
  have h3 := hlim.congr' hEq
  rw [add_zero] at h2
  exact tendsto_nhds_unique h2 h3

/-- **The gap.** If there is no mass below `-v`, the vacuum atom has mass `1`, and
`e^{-vβ} Z(β) - 1 ≤ K e^{-gβ}` for large `β`, then `σ (-v, -v + g) = 0`. -/
theorem no_mass_gap (σ : Measure ℝ) {v g K B : ℝ} (hB : 0 < B) (hg : 0 < g)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) σ)
    (hno : σ (Iio (-v)) = 0) (hatom : σ.real {-v} = 1)
    (hK : ∀ β : ℝ, B ≤ β → Real.exp (-(v * β)) * ∫ x, Real.exp (-β * x) ∂σ - 1 ≤ K * Real.exp (-(g * β))) :
    σ (Ioo (-v) (-v + g)) = 0 := by
  by_contra hne
  have h1 : (⋃ n : ℕ, Ioo (-v) (-v + g - 1 / ((n : ℝ) + 1))) = Ioo (-v) (-v + g) := by
    ext x
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨n, hn1, hn2⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨hn1, by linarith⟩
    · rintro ⟨hx1, hx2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < -v + g - x by linarith)
      exact ⟨n, hx1, by linarith⟩
  have h2 : ∃ n : ℕ, σ (Ioo (-v) (-v + g - 1 / ((n : ℝ) + 1))) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hne
    rw [← h1]
    exact measure_iUnion_null hall
  obtain ⟨n, hn⟩ := h2
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  set S : Set ℝ := Ioo (-v) (-v + g - ε) with hS
  have hSfin : σ S ≠ ⊤ := by
    have := (hint B hB).measure_ge_lt_top (ε := Real.exp (-B * (-v + g))) (Real.exp_pos _)
    refine ne_top_of_le_ne_top this.ne (measure_mono fun x hx => ?_)
    simp only [hS, mem_Ioo] at hx
    simp only [mem_ofPred_eq]
    exact Real.exp_le_exp.2 (by nlinarith [hx.2, hε0])
  set m : ℝ := σ.real S with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hn hSfin
  have hlow : ∀ β : ℝ, B ≤ β → Real.exp (-(β * (g - ε))) * m ≤ K * Real.exp (-(g * β)) := by
    intro β hβ
    have hβ0 : 0 < β := by linarith
    have hEq := exp_mul_Z_eq σ hno hβ0 (hint β hβ0)
    have hR : Real.exp (-(β * (g - ε))) * m ≤ ∫ x in Ioi (-v), Real.exp (-β * (x + v)) ∂σ := by
      have hint' : IntegrableOn (fun x : ℝ => Real.exp (-β * (x + v))) (Ioi (-v)) σ := by
        have h1 : ∀ x : ℝ, Real.exp (-(v * β)) * Real.exp (-β * x) = Real.exp (-β * (x + v)) := fun x => by
          rw [← Real.exp_add]; congr 1; ring
        exact (((hint β hβ0).const_mul (Real.exp (-(v * β)))).congr
          (Filter.Eventually.of_forall fun x => h1 x)).integrableOn
      calc Real.exp (-(β * (g - ε))) * m
          ≤ ∫ x in S, Real.exp (-β * (x + v)) ∂σ := by
            have key := setIntegral_ge_of_const_le (c := Real.exp (-(β * (g - ε))))
              (measurableSet_Ioo : MeasurableSet S) hSfin (fun x hx => ?_)
              (hint'.mono_set Set.Ioo_subset_Ioi_self)
            · calc Real.exp (-(β * (g - ε))) * m = σ.real S • Real.exp (-(β * (g - ε))) := by
                    rw [smul_eq_mul, mul_comm]
                _ ≤ _ := key
            · simp only [hS, mem_Ioo] at hx
              exact Real.exp_le_exp.2 (by nlinarith [hx.2, hβ0])
        _ ≤ ∫ x in Ioi (-v), Real.exp (-β * (x + v)) ∂σ :=
            setIntegral_mono_set hint' (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
              (Filter.Eventually.of_forall Set.Ioo_subset_Ioi_self)
    have := hK β hβ
    rw [hEq, hatom] at this
    linarith
  -- the contradiction: `m ≤ K e^{-ε β}`
  have hlim : Tendsto (fun β : ℝ => K * Real.exp (-(ε * β))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hε0 tendsto_id)).const_mul K
    simpa using this
  have hm_le : ∀ β : ℝ, B ≤ β → m ≤ K * Real.exp (-(ε * β)) := by
    intro β hβ
    have := hlow β hβ
    have e : K * Real.exp (-(g * β)) = Real.exp (-(β * (g - ε))) * (K * Real.exp (-(ε * β))) := by
      rw [← mul_assoc, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [e] at this
    exact le_of_mul_le_mul_left this (Real.exp_pos _)
  obtain ⟨β, hβ⟩ := ((hlim.eventually (gt_mem_nhds hmpos)).and (eventually_ge_atTop B)).exists
  exact absurd (hm_le β hβ.2) (not_le.2 hβ.1)

/-- **The low-temperature form** from the high-temperature form and real modular invariance:
`|e^{-vβ'} Z(β') - 1| ≤ C e^{-(g/4π²) β'}` for `β' ≥ 4π²/β₀ + 1`. -/
theorem low_temp_bound (σ : Measure ℝ) {v g C β₀ : ℝ} (hv : 0 < v) (hβ₀ : 0 < β₀)
    (hmod : ∀ β : ℝ, 0 < β → ∫ x, Real.exp (-β * x) ∂σ = ∫ x, Real.exp (-(4 * Real.pi ^ 2 / β) * x) ∂σ)
    (hasym : ∀ β : ℝ, 0 < β → β < β₀ →
      |(∫ x, Real.exp (-β * x) ∂σ) - Real.exp (4 * Real.pi ^ 2 * v / β)| ≤
        C * Real.exp ((4 * Real.pi ^ 2 * v - g) / β))
    {β' : ℝ} (hβ' : 4 * Real.pi ^ 2 / β₀ + 1 ≤ β') :
    |Real.exp (-(v * β')) * (∫ x, Real.exp (-β' * x) ∂σ) - 1| ≤
      C * Real.exp (-(g / (4 * Real.pi ^ 2) * β')) := by
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  have hβ'0 : 0 < β' := by
    have : 0 < 4 * Real.pi ^ 2 / β₀ := by positivity
    linarith
  set β : ℝ := 4 * Real.pi ^ 2 / β' with hβdef
  have hβpos : 0 < β := by positivity
  have hβlt : β < β₀ := by
    rw [hβdef, div_lt_iff₀ hβ'0]
    have : 4 * Real.pi ^ 2 / β₀ < β' := by linarith
    rw [div_lt_iff₀ hβ₀] at this
    linarith
  have hβinv : 4 * Real.pi ^ 2 / β = β' := by rw [hβdef]; field_simp
  have h1 := hasym β hβpos hβlt
  have hZ : ∫ x, Real.exp (-β' * x) ∂σ = ∫ x, Real.exp (-β * x) ∂σ := by
    have := hmod β hβpos
    rw [hβinv] at this
    exact this.symm
  have e1 : 4 * Real.pi ^ 2 * v / β = v * β' := by rw [hβdef]; field_simp
  have e2 : (4 * Real.pi ^ 2 * v - g) / β = v * β' - g / (4 * Real.pi ^ 2) * β' := by
    rw [hβdef]; field_simp
  rw [hZ]
  rw [e1, e2] at h1
  have h2 : Real.exp (-(v * β')) * (∫ x, Real.exp (-β * x) ∂σ) - 1 =
      Real.exp (-(v * β')) * ((∫ x, Real.exp (-β * x) ∂σ) - Real.exp (v * β')) := by
    rw [mul_sub, ← Real.exp_add]; simp
  rw [h2, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(v * β')) * |(∫ x, Real.exp (-β * x) ∂σ) - Real.exp (v * β')|
      ≤ Real.exp (-(v * β')) * (C * Real.exp (v * β' - g / (4 * Real.pi ^ 2) * β')) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = C * Real.exp (-(g / (4 * Real.pi ^ 2) * β')) := by
        rw [← mul_assoc, mul_comm (Real.exp _) C, mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **MZ's hypothesis gives the vacuum and the gap.** Let `σ` be a positive measure with `Z(β) = ∫ e^{-β x} dσ`
finite for `β > 0`, real modular invariance `Z(β) = Z(4π²/β)`, and the high-temperature form
`|Z(β) - e^{a/β}| ≤ C e^{(a - g)/β}` for `0 < β < β₀`, `a = 4π² v`. Then there is no mass below `-v`, the
atom at `-v` has mass `1`, and there is no mass in `(-v, -v + g/(4π²))`. -/
theorem vacuum_gap_of_modular (σ : Measure ℝ) {v g C β₀ : ℝ} (hv : 0 < v) (hg : 0 < g) (hβ₀ : 0 < β₀)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) σ)
    (hmod : ∀ β : ℝ, 0 < β → ∫ x, Real.exp (-β * x) ∂σ = ∫ x, Real.exp (-(4 * Real.pi ^ 2 / β) * x) ∂σ)
    (hasym : ∀ β : ℝ, 0 < β → β < β₀ →
      |(∫ x, Real.exp (-β * x) ∂σ) - Real.exp (4 * Real.pi ^ 2 * v / β)| ≤
        C * Real.exp ((4 * Real.pi ^ 2 * v - g) / β)) :
    σ (Iio (-v)) = 0 ∧ σ.real {-v} = 1 ∧ σ (Ioo (-v) (-v + g / (4 * Real.pi ^ 2))) = 0 := by
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  set B : ℝ := 4 * Real.pi ^ 2 / β₀ + 1 with hBdef
  have hB : 0 < B := by positivity
  have hkey : ∀ β' : ℝ, B ≤ β' →
      |Real.exp (-(v * β')) * (∫ x, Real.exp (-β' * x) ∂σ) - 1| ≤
        C * Real.exp (-(g / (4 * Real.pi ^ 2) * β')) :=
    fun β' hβ' => low_temp_bound σ hv hβ₀ hmod hasym hβ'
  have hC0 : 0 ≤ C := by
    have := hkey B le_rfl
    have h0 := abs_nonneg (Real.exp (-(v * B)) * (∫ x, Real.exp (-B * x) ∂σ) - 1)
    have hp : 0 < Real.exp (-(g / (4 * Real.pi ^ 2) * B)) := Real.exp_pos _
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hp]
  have hno : σ (Iio (-v)) = 0 := by
    refine no_mass_below σ (K := 1 + C) hB hint (fun β hβ => ?_)
    have := hkey β hβ
    have hle : Real.exp (-(g / (4 * Real.pi ^ 2) * β)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [div_pos hg hπ, show 0 < β by linarith])
    have := (abs_le.1 this).2
    nlinarith [mul_le_mul_of_nonneg_left hle hC0]
  have hlim : Tendsto (fun β : ℝ => Real.exp (-(v * β)) * ∫ x, Real.exp (-β * x) ∂σ) atTop (𝓝 1) := by
    have hl : Tendsto (fun β : ℝ => C * Real.exp (-(g / (4 * Real.pi ^ 2) * β))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.Tendsto.const_mul_atTop (div_pos hg hπ) tendsto_id)).const_mul C
      simpa using this
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hl
    filter_upwards [eventually_ge_atTop B] with β hβ
    rw [Real.dist_eq]
    exact hkey β hβ
  have hatom := atom_eq_one σ hB hint hno hlim
  refine ⟨hno, hatom, no_mass_gap σ (K := C) hB (div_pos hg hπ) hint hno hatom (fun β hβ => ?_)⟩
  exact (le_abs_self _).trans (hkey β hβ)

end Lightlike.Tauberian
