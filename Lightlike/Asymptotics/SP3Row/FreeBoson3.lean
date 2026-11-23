import Mathlib
import Lightlike.Asymptotics.SP3Row.FreeBoson2
import Lightlike.Asymptotics.SP3Row.BosonLog
import Lightlike.Asymptotics.Tauberian.Ingham

/-!
# Growth of the spectrum of a free boson (trust check for Ingham's theorem)

The chiral free boson has `p(n)` states at level `n` (`p(n)` = number of partitions of `n`), so its
density of states is the measure `ρ = ∑ₙ p(n) δₙ` on `[0, ∞)` (`partitionMeasure`). Its Laplace
transform is the partition function `Z(β) = ∑ p(n) e^{-βn} = ∏ (1 - e^{-βk})⁻¹`
(`laplace_partitionMeasure`), and `β log Z(β) → π²/6` (`tendsto_mul_bosonLogZ`). Ingham's logarithmic
Tauberian theorem (`Tauberian.ingham_log`) then gives the Hardy–Ramanujan growth of the number of states
`log (∑_{n ≤ X} p(n)) ~ 2 √(π² X / 6)` (`free_boson_growth`).
-/

open MeasureTheory Set Filter Topology ENNReal

noncomputable section

namespace Lightlike.SP3Row

/-- The spectral measure of the chiral free boson: `p(n)` states at energy `n`. -/
def partitionMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (pcount n) • Measure.dirac (n : ℝ)

lemma lintegral_partitionMeasure (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂partitionMeasure = ∑' n : ℕ, ENNReal.ofReal (pcount n) * f (n : ℝ) := by
  rw [partitionMeasure, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- `∑ p(n) e^{-βn}` as an extended-real series, for `β > 0`. -/
lemma lintegral_exp_partitionMeasure {β : ℝ} (hβ : 0 < β) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-β * x)) ∂partitionMeasure =
      ENNReal.ofReal (∑' n : ℕ, pcount n * Real.exp (-β * n)) := by
  have hq0 : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  have hq1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpow : ∀ n : ℕ, Real.exp (-β * n) = Real.exp (-β) ^ n := fun n => by
    rw [← Real.exp_nat_mul]; ring_nf
  have hs := (tsum_pcount_mul_pow hq0 hq1).1
  have hs' : Summable fun n : ℕ => pcount n * Real.exp (-β * n) :=
    hs.congr fun n => by rw [hpow]
  rw [lintegral_partitionMeasure,
    ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (pcount_nonneg n) (Real.exp_pos _).le) hs']
  exact tsum_congr fun n => by
    rw [ENNReal.ofReal_mul (pcount_nonneg n)]

lemma lintegral_exp_lt_top {β : ℝ} (hβ : 0 < β) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-β * x)) ∂partitionMeasure < ⊤ := by
  rw [lintegral_exp_partitionMeasure hβ]; exact ENNReal.ofReal_lt_top

lemma integrable_exp_partitionMeasure {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ => Real.exp (-β * x)) partitionMeasure := by
  refine ⟨(by fun_prop : Continuous fun x : ℝ => Real.exp (-β * x)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  exact lintegral_exp_lt_top hβ

lemma partitionMeasure_Iio : partitionMeasure (Iio 0) = 0 := by
  rw [← lintegral_indicator_one measurableSet_Iio, lintegral_partitionMeasure]
  refine ENNReal.tsum_eq_zero.2 fun n => ?_
  have : ¬ ((n : ℝ) ∈ Iio (0 : ℝ)) := by simp
  simp

instance : IsFiniteMeasureOnCompacts partitionMeasure := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.bddAbove
  have h1 := lintegral_exp_lt_top (β := 1) one_pos
  rw [← lintegral_indicator_one hK.measurableSet]
  calc ∫⁻ x, K.indicator 1 x ∂partitionMeasure
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp R) * ENNReal.ofReal (Real.exp (-1 * x)) ∂partitionMeasure := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ K
        · rw [Set.indicator_of_mem hx, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          have : (1 : ℝ) ≤ Real.exp R * Real.exp (-1 * x) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [hR hx])
          simpa using ENNReal.ofReal_le_ofReal this
        · simp [Set.indicator_of_notMem hx]
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

/-- The Laplace transform of `partitionMeasure` is the partition function `∑ p(n) e^{-βn}`. -/
lemma laplace_partitionMeasure {β : ℝ} (hβ : 0 < β) :
    Tauberian.laplace partitionMeasure β = ∑' n : ℕ, pcount n * Real.exp (-β * n) := by
  have hq0 : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  have hnn : 0 ≤ ∑' n : ℕ, pcount n * Real.exp (-β * n) :=
    tsum_nonneg fun n => mul_nonneg (pcount_nonneg n) (Real.exp_pos _).le
  unfold Tauberian.laplace
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-β * x)).aestronglyMeasurable,
    lintegral_exp_partitionMeasure hβ, ENNReal.toReal_ofReal hnn]

/-- `log Z(β) = bosonLogZ β` for the partition function of the chiral boson. -/
lemma log_laplace_partitionMeasure {β : ℝ} (hβ : 0 < β) :
    Real.log (Tauberian.laplace partitionMeasure β) = bosonLogZ β := by
  have hq0 : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  have hq1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hpow : ∀ n : ℕ, Real.exp (-β * n) = Real.exp (-β) ^ n := fun n => by
    rw [← Real.exp_nat_mul]; ring_nf
  have hT := (tsum_pcount_mul_pow hq0 hq1).2
  rw [laplace_partitionMeasure hβ, tsum_congr fun n => by rw [hpow n], hT, Real.log_exp]
  unfold bosonLogZ
  refine tsum_congr fun k => ?_
  have : Real.exp (-β) ^ (k + 1) = Real.exp (-(β * ((k : ℝ) + 1))) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [this]

/-- **Growth of the spectrum of a free boson.** With `p(n)` states at level `n`, the number of states
of energy at most `X` satisfies `log N(X) / (2 √(π² X / 6)) → 1` (Hardy–Ramanujan, logarithmic form),
by `Tauberian.ingham_log` applied to `β log Z(β) → π²/6`. -/
theorem free_boson_growth :
    Tendsto (fun X : ℝ => Real.log (Tauberian.counting partitionMeasure X) /
      (2 * Real.sqrt (Real.pi ^ 2 / 6 * X))) atTop (𝓝 1) := by
  refine Tauberian.ingham_log (ρ := partitionMeasure) partitionMeasure_Iio
    (fun β hβ => integrable_exp_partitionMeasure hβ) (a := Real.pi ^ 2 / 6)
    (by positivity) ?_
  refine tendsto_mul_bosonLogZ.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  rw [log_laplace_partitionMeasure hβ]

end Lightlike.SP3Row
