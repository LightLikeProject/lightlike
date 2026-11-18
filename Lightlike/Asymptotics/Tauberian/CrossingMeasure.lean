import Lightlike.Asymptotics.Tauberian.ComplexLaplace
import Lightlike.Asymptotics.Tauberian.CrossingBound
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Lightlike.Asymptotics.Tauberian.LocalBound

/-!
# The crossing measure

`crossingDensity a` is continuous on `[0, ∞)` (locally uniform convergence of the series), hence measurable
on `(0, ∞)`; the crossing measure `rho0 a = δ₀ + crossingDensity a dx` on `(0, ∞)` has complex Laplace
transform `e^{a/z}` (`laplaceC_rho0`), the vacuum contribution of the dual channel in MZ (2.7).
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace Lightlike.Tauberian

lemma continuousOn_crossingTerm (a : ℝ) (k : ℕ) : Continuous (crossingTerm a k) := by
  unfold crossingTerm; fun_prop

lemma continuousOn_crossingDensity {a : ℝ} (ha : 0 < a) : ContinuousOn (crossingDensity a) (Ici 0) := by
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt x
  refine ⟨Iio ((N : ℝ) + 1), isOpen_Iio, by simp only [mem_Iio]; linarith, ?_⟩
  set u : ℕ → ℝ := fun k => a * (a * ((N : ℝ) + 1)) ^ k / (k.factorial : ℝ) with hu
  have hsum : Summable u := by
    have := (hasSum_exp_div (z := a * ((N : ℝ) + 1))).summable.mul_left a
    refine this.congr fun k => ?_
    simp only [hu]; ring
  have hbd : ∀ (k : ℕ) (y : ℝ), y ∈ Ico (0 : ℝ) ((N : ℝ) + 1) → ‖crossingTerm a k y‖ ≤ u k := by
    intro k y hy
    have hy0 : 0 ≤ y := hy.1
    have hy1 : y < (N : ℝ) + 1 := hy.2
    rw [Real.norm_of_nonneg (crossingTerm_nonneg ha k hy0)]
    unfold crossingTerm
    have h1 : a ^ (k + 1) * y ^ k = a * (a * y) ^ k := by rw [pow_succ, mul_pow]; ring
    rw [h1]
    have h2 : (a * y) ^ k ≤ (a * ((N : ℝ) + 1)) ^ k :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hy1.le ha.le) k
    have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.2 (Nat.factorial_pos k)
    have hf1 : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    simp only [hu]
    calc a * (a * y) ^ k / (((k + 1).factorial : ℝ) * (k.factorial : ℝ))
        ≤ a * (a * y) ^ k / (k.factorial : ℝ) := by
          refine div_le_div_of_nonneg_left (by positivity) hf ?_
          nlinarith
      _ ≤ a * (a * ((N : ℝ) + 1)) ^ k / (k.factorial : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 ha.le) hf.le
  have hC : ContinuousOn (fun y => ∑' n, crossingTerm a n y) (Ico (0 : ℝ) ((N : ℝ) + 1)) :=
    continuousOn_tsum (s := Ico (0 : ℝ) ((N : ℝ) + 1)) (u := u)
      (fun k => (continuousOn_crossingTerm a k).continuousOn) hsum hbd
  refine hC.mono ?_
  intro y hy
  exact ⟨hy.1, hy.2⟩

lemma crossingDensity_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) : 0 ≤ crossingDensity a x :=
  tsum_nonneg fun k => crossingTerm_nonneg ha k hx

lemma aemeasurable_crossingDensity {a : ℝ} (ha : 0 < a) :
    AEMeasurable (crossingDensity a) (volume.restrict (Ioi (0 : ℝ))) :=
  ((continuousOn_crossingDensity ha).mono Set.Ioi_subset_Ici_self).aemeasurable measurableSet_Ioi

/-- **The crossing measure** `δ₀ + ρ₀(x) dx` on `[0, ∞)` (MZ (2.6): the vacuum atom and the continuous part). -/
def rho0 (a : ℝ) : Measure ℝ :=
  Measure.dirac 0 + (volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (crossingDensity a x))

instance (a : ℝ) : SFinite (rho0 a) := by unfold rho0; infer_instance

/-- `ρ₀(x) e^{-β x}` is integrable on `(0, ∞)` for `β > 0`. -/
lemma integrableOn_crossing_exp {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    IntegrableOn (fun x : ℝ => crossingDensity a x * Real.exp (-β * x)) (Ioi 0) := by
  have hI : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ)) * Real.exp (-(β / 2) * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) one_pos (by positivity)
  have hI' : IntegrableOn (fun x : ℝ => a ^ (1 / 4 : ℝ) * Real.exp (2 * a / β) *
      (x ^ (-(3 / 4 : ℝ)) * Real.exp (-(β / 2) * x))) (Ioi 0) := by
    exact IntegrableOn.congr_fun (Integrable.const_mul hI (a ^ (1 / 4 : ℝ) * Real.exp (2 * a / β)))
      (fun x _ => by simp only [Real.rpow_one]) measurableSet_Ioi
  refine Integrable.mono' hI' ?_ ?_
  · exact ((aemeasurable_crossingDensity ha).mul
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (-β * x)).measurable.aemeasurable)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := hx
    rw [Real.norm_of_nonneg (mul_nonneg (crossingDensity_nonneg ha hx0.le) (Real.exp_pos _).le)]
    have h1 := crossingDensity_le ha hx0
    set z := 2 * Real.sqrt (a * x) with hz
    have hzpos : 0 < z := by positivity
    have hz2 : z ≤ (β / 2) * x + 2 * a / β := by
      have h2 : z ^ 2 ≤ ((β / 2) * x + 2 * a / β) ^ 2 := by
        have : z ^ 2 = 4 * (a * x) := by rw [hz, mul_pow, Real.sq_sqrt (by positivity)]; ring
        rw [this]
        have hβ0 := hβ.ne'
        have : ((β / 2) * x + 2 * a / β) ^ 2 - 4 * (a * x) = ((β / 2) * x - 2 * a / β) ^ 2 := by
          field_simp; ring
        nlinarith [sq_nonneg ((β / 2) * x - 2 * a / β)]
      exact le_of_sq_le_sq h2 (by positivity)
    have h3 : Real.exp z * Real.exp (-β * x) ≤ Real.exp (2 * a / β) * Real.exp (-(β / 2) * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hcoef := coeff_eq ha hx0
    calc crossingDensity a x * Real.exp (-β * x)
        ≤ ((2 * Real.sqrt 2 * a / z) * (Real.exp z / Real.sqrt z)) * Real.exp (-β * x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (2 * Real.sqrt 2 * a / z / Real.sqrt z) * (Real.exp z * Real.exp (-β * x)) := by ring
      _ ≤ (2 * Real.sqrt 2 * a / z / Real.sqrt z) * (Real.exp (2 * a / β) * Real.exp (-(β / 2) * x)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = a ^ (1 / 4 : ℝ) * Real.exp (2 * a / β) * (x ^ (-(3 / 4 : ℝ)) * Real.exp (-(β / 2) * x)) := by
          rw [hcoef]; ring

lemma integrable_cexp_dirac (z : ℂ) : Integrable (fun x : ℝ => Complex.exp (-(z * x))) (Measure.dirac (0 : ℝ)) :=
  integrable_dirac' (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(z * x))).stronglyMeasurable
    (by simp)

lemma integrable_cexp_density {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun x : ℝ => Complex.exp (-(z * x)))
      ((volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (crossingDensity a x))) := by
  rw [integrable_withDensity_iff_integrable_smul₀' ((aemeasurable_crossingDensity ha).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h := integrableOn_crossing_exp ha hz
  refine (integrable_norm_iff ?_).mp ?_
  · exact (((aemeasurable_crossingDensity ha).ennreal_ofReal.ennreal_toReal).smul
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(z * x))).measurable.aemeasurable).aestronglyMeasurable
  · refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    simp only [norm_smul, Complex.norm_exp, Real.norm_eq_abs]
    rw [ENNReal.toReal_ofReal (crossingDensity_nonneg ha hx0.le),
      abs_of_nonneg (crossingDensity_nonneg ha hx0.le)]
    simp

/-- **The Laplace transform of the crossing measure** (MZ (2.7)): `L_{ρ₀}(z) = e^{a/z}` for `Re z > 0`. -/
theorem laplaceC_rho0 {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    laplaceC (rho0 a) z = Complex.exp ((a : ℂ) / z) := by
  unfold laplaceC rho0
  rw [integral_add_measure (integrable_cexp_dirac z) (integrable_cexp_density ha hz),
    integral_dirac, integral_withDensity_eq_integral_toReal_smul₀
      ((aemeasurable_crossingDensity ha).ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h1 : ∫ x in Ioi (0 : ℝ), (ENNReal.ofReal (crossingDensity a x)).toReal • Complex.exp (-(z * x)) =
      ∫ x in Ioi (0 : ℝ), (crossingDensity a x : ℂ) * Complex.exp (-(z * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    rw [ENNReal.toReal_ofReal (crossingDensity_nonneg ha hx0.le), Complex.real_smul]
  rw [h1, integral_crossing_cexp ha hz]
  simp

/-- **Integration against the crossing measure.** For a continuous `F` with `|F x| ≤ M e^{-β x}` on
`[0, ∞)`: `F` is `ρ₀`-integrable and `∫ F dρ₀ = F 0 + ∫₀^∞ ρ₀(x) F(x) dx`. -/
lemma integral_rho0 {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {F : ℝ → ℝ} (hFc : Continuous F)
    (hF : ∀ x : ℝ, 0 ≤ x → |F x| ≤ M * Real.exp (-β * x)) :
    Integrable F (rho0 a) ∧
      ∫ x, F x ∂(rho0 a) = F 0 + ∫ x in Ioi (0 : ℝ), crossingDensity a x * F x := by
  have hdir : Integrable F (Measure.dirac (0 : ℝ)) := integrable_dirac' hFc.stronglyMeasurable (by simp)
  have hden : Integrable F
      ((volume.restrict (Ioi (0 : ℝ))).withDensity (fun x => ENNReal.ofReal (crossingDensity a x))) := by
    rw [integrable_withDensity_iff_integrable_smul₀' ((aemeasurable_crossingDensity ha).ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have h := (integrableOn_crossing_exp ha hβ).const_mul M
    refine Integrable.mono' h ?_ ?_
    · exact (((aemeasurable_crossingDensity ha).ennreal_ofReal.ennreal_toReal).smul
        hFc.measurable.aemeasurable).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
      have hx0 : (0 : ℝ) < x := hx
      simp only [smul_eq_mul, norm_mul, Real.norm_eq_abs]
      rw [ENNReal.toReal_ofReal (crossingDensity_nonneg ha hx0.le),
        abs_of_nonneg (crossingDensity_nonneg ha hx0.le)]
      calc crossingDensity a x * |F x| ≤ crossingDensity a x * (M * Real.exp (-β * x)) :=
            mul_le_mul_of_nonneg_left (hF x hx0.le) (crossingDensity_nonneg ha hx0.le)
        _ = M * (crossingDensity a x * Real.exp (-β * x)) := by ring
  refine ⟨hdir.add_measure hden, ?_⟩
  unfold rho0
  rw [integral_add_measure hdir hden, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul₀ ((aemeasurable_crossingDensity ha).ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (crossingDensity_nonneg ha hx0.le)]

end Lightlike.Tauberian
