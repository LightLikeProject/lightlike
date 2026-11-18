import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Window estimates for a Laplace transform of a positive measure

Let `ρ` be a measure on `ℝ` with `ρ (Iio 0) = 0`, finite on compact sets, with `x ↦ exp (-β x)`
integrable for every `β > 0`. Write `L β = ∫ exp (-β x) dρ` and `F X = ρ [0, X]`. Elementary window
estimates, used in the proof of the logarithmic Tauberian theorem (`Tauberian.ingham_log`):

* `F X * exp (-β X) ≤ L β`;
* for `β < β'`: `∫_{[0, Y]} exp (-β x) dρ ≤ exp ((β' - β) Y) L β'`;
* for `β' < β`: `∫_{(Y, ∞)} exp (-β x) dρ ≤ exp (-(β - β') Y) L β'`;
* for `X ≤ Y`: `∫_{(X, Y]} exp (-β x) dρ ≤ exp (-β X) F Y`.
-/

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Tauberian

variable {ρ : Measure ℝ}

/-- The Laplace transform `∫ exp (-β x) dρ`. -/
def laplace (ρ : Measure ℝ) (β : ℝ) : ℝ := ∫ x, Real.exp (-β * x) ∂ρ

/-- The counting function `ρ [0, X]`. -/
def counting (ρ : Measure ℝ) (X : ℝ) : ℝ := (ρ (Icc 0 X)).toReal

lemma laplace_nonneg (ρ : Measure ℝ) (β : ℝ) : 0 ≤ laplace ρ β :=
  integral_nonneg fun x => (Real.exp_pos _).le

variable [IsFiniteMeasureOnCompacts ρ]

omit [IsFiniteMeasureOnCompacts ρ] in
lemma counting_nonneg (X : ℝ) : 0 ≤ counting ρ X := ENNReal.toReal_nonneg

variable (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
include hint

lemma integrableOn_exp {β : ℝ} (hβ : 0 < β) (s : Set ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-β * x)) s ρ := (hint β hβ).integrableOn

/-- `F X * exp (-β X) ≤ L β`. -/
lemma counting_mul_exp_le {β X : ℝ} (hβ : 0 < β) (hX : 0 ≤ X) :
    counting ρ X * Real.exp (-β * X) ≤ laplace ρ β := by
  have hfin : ρ (Icc 0 X) ≠ ⊤ := isCompact_Icc.measure_lt_top.ne
  have h1 : ∫ x in Icc (0 : ℝ) X, Real.exp (-β * X) ∂ρ ≤ ∫ x in Icc (0 : ℝ) X, Real.exp (-β * x) ∂ρ := by
    refine setIntegral_mono_on (integrableOn_const hfin) (integrableOn_exp hint hβ _) measurableSet_Icc ?_
    intro x hx
    exact Real.exp_le_exp.2 (by nlinarith [hx.2, hβ])
  have h2 : ∫ x in Icc (0 : ℝ) X, Real.exp (-β * x) ∂ρ ≤ laplace ρ β :=
    setIntegral_le_integral (hint β hβ) (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
  rw [setIntegral_const, smul_eq_mul] at h1
  have : counting ρ X * Real.exp (-β * X) = (ρ (Icc 0 X)).toReal * Real.exp (-β * X) := rfl
  rw [this]
  simp only [Measure.real] at h1
  linarith

/-- `∫_{[0, Y]} exp (-β x) dρ ≤ exp ((β' - β) Y) L β'` for `β ≤ β'`. -/
lemma setIntegral_Icc_le {β β' Y : ℝ} (hβ : 0 < β) (hββ' : β ≤ β') (hY : 0 ≤ Y) :
    ∫ x in Icc (0 : ℝ) Y, Real.exp (-β * x) ∂ρ ≤ Real.exp ((β' - β) * Y) * laplace ρ β' := by
  have hβ' : 0 < β' := lt_of_lt_of_le hβ hββ'
  have h1 : ∫ x in Icc (0 : ℝ) Y, Real.exp (-β * x) ∂ρ ≤
      ∫ x in Icc (0 : ℝ) Y, Real.exp ((β' - β) * Y) * Real.exp (-β' * x) ∂ρ := by
    refine setIntegral_mono_on (integrableOn_exp hint hβ _) ?_ measurableSet_Icc ?_
    · exact (integrableOn_exp hint hβ' _).const_mul _
    · intro x hx
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [hx.1, hx.2, sub_nonneg.2 hββ'])
  rw [integral_const_mul] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact setIntegral_le_integral (hint β' hβ') (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)

/-- `∫_{(Y, ∞)} exp (-β x) dρ ≤ exp (-(β - β') Y) L β'` for `0 < β' ≤ β`. -/
lemma setIntegral_Ioi_le {β β' Y : ℝ} (hβ' : 0 < β') (hββ' : β' ≤ β) :
    ∫ x in Ioi Y, Real.exp (-β * x) ∂ρ ≤ Real.exp (-(β - β') * Y) * laplace ρ β' := by
  have hβ : 0 < β := lt_of_lt_of_le hβ' hββ'
  have h1 : ∫ x in Ioi Y, Real.exp (-β * x) ∂ρ ≤
      ∫ x in Ioi Y, Real.exp (-(β - β') * Y) * Real.exp (-β' * x) ∂ρ := by
    refine setIntegral_mono_on (integrableOn_exp hint hβ _) ?_ measurableSet_Ioi ?_
    · exact (integrableOn_exp hint hβ' _).const_mul _
    · intro x hx
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [hx.out, sub_nonneg.2 hββ'])
  rw [integral_const_mul] at h1
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact setIntegral_le_integral (hint β' hβ') (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)

/-- `∫_{(X, Y]} exp (-β x) dρ ≤ exp (-β X) F Y` for `0 ≤ X ≤ Y`. -/
lemma setIntegral_Ioc_le {β X Y : ℝ} (hβ : 0 < β) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    ∫ x in Ioc X Y, Real.exp (-β * x) ∂ρ ≤ Real.exp (-β * X) * counting ρ Y := by
  have hfin : ρ (Ioc X Y) ≠ ⊤ :=
    (measure_mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left hX))).trans_lt
      (isCompact_Icc (a := 0) (b := Y)).measure_lt_top |>.ne
  have h1 : ∫ x in Ioc X Y, Real.exp (-β * x) ∂ρ ≤ ∫ x in Ioc X Y, Real.exp (-β * X) ∂ρ := by
    refine setIntegral_mono_on (integrableOn_exp hint hβ _) (integrableOn_const hfin)
      measurableSet_Ioc ?_
    intro x hx
    exact Real.exp_le_exp.2 (by nlinarith [hx.1])
  rw [setIntegral_const, smul_eq_mul] at h1
  refine h1.trans ?_
  simp only [Measure.real, counting]
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact ENNReal.toReal_mono (isCompact_Icc.measure_lt_top.ne)
    (measure_mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc_left hX)))

/-- **Splitting** `L β` into the three windows `[0, Xl]`, `(Xl, Xh]`, `(Xh, ∞)`. -/
lemma laplace_eq_split (hρ : ρ (Iio 0) = 0) {β : ℝ} (hβ : 0 < β) {Xl Xh : ℝ} (h0 : 0 ≤ Xl)
    (hle : Xl ≤ Xh) :
    laplace ρ β = (∫ x in Icc (0 : ℝ) Xl, Real.exp (-β * x) ∂ρ) +
      (∫ x in Ioc Xl Xh, Real.exp (-β * x) ∂ρ) + ∫ x in Ioi Xh, Real.exp (-β * x) ∂ρ := by
  have hI := hint β hβ
  have h1 : laplace ρ β = ∫ x in Ici (0 : ℝ), Real.exp (-β * x) ∂ρ := by
    unfold laplace
    rw [← integral_add_compl measurableSet_Ici hI, compl_Ici, Measure.restrict_eq_zero.2 hρ,
      integral_zero_measure, add_zero]
  have hU : Ici (0 : ℝ) = (Icc 0 Xl ∪ Ioc Xl Xh) ∪ Ioi Xh := by
    ext x
    simp only [mem_Ici, mem_union, mem_Icc, mem_Ioc, mem_Ioi]
    constructor
    · intro hx
      by_cases h : x ≤ Xl
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · by_cases h' : x ≤ Xh
        · exact Or.inl (Or.inr ⟨not_le.1 h, h'⟩)
        · exact Or.inr (not_le.1 h')
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | h)
      · exact h
      · linarith
      · linarith
  have hd1 : Disjoint (Icc (0 : ℝ) Xl) (Ioc Xl Xh) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  have hd2 : Disjoint (Icc (0 : ℝ) Xl ∪ Ioc Xl Xh) (Ioi Xh) :=
    Set.disjoint_left.2 fun x hx hx' => by
      rcases hx with hx | hx
      · exact absurd (hx.2.trans hle) (not_le.2 hx')
      · exact absurd hx.2 (not_le.2 hx')
  rw [h1, hU, setIntegral_union hd2 measurableSet_Ioi hI.integrableOn hI.integrableOn,
    setIntegral_union hd1 measurableSet_Ioc hI.integrableOn hI.integrableOn]

end Lightlike.Tauberian
