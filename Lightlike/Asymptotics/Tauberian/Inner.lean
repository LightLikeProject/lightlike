import Lightlike.Asymptotics.Tauberian.WindowWeights
import Lightlike.Asymptotics.Tauberian.Tangent

/-!
# The inner region of the comparison

`inner_le`: on `Ioc (Δ - n) (Δ + n)` the error `|ρ(Δ - x)|` integrates against a measure with the local
window bound `μ [c - ½, c + ½] ≤ K c^{-3/4} e^{2√(a c)}` to at most
`K (Δ/2)^{-3/4} e^{2√(aΔ)} e^{β/2} ∑_j A_{n-j}`, with `β = √(a/Δ)` (tangent-line bound).
-/

open MeasureTheory Set Real Filter

noncomputable section

namespace Lightlike.Tauberian

/-- `ψ` is monotone. -/
lemma psiS_mono {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) : Monotone (psiS b β) := by
  intro y1 y2 h
  unfold psiS
  refine mul_le_mul_of_nonneg_left ?_ (by have := kapN_pos hb; positivity)
  exact setIntegral_mono_set (integrableOn_exp_kap hb hβ y2)
    (Filter.Eventually.of_forall fun u => mul_nonneg (Real.exp_pos _).le (kap_nonneg b u))
    (Filter.Eventually.of_forall (Iio_subset_Iio h))

/-- The error function is measurable. -/
lemma measurable_rhoErr {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) : Measurable (rhoErr b β) := by
  unfold rhoErr
  refine Measurable.sub ?_ (psiS_mono hb hβ).measurable
  exact Measurable.ite (measurableSet_Ici : MeasurableSet {y : ℝ | 0 ≤ y}) measurable_const measurable_const

/-- The window weight is nonnegative. -/
lemma Aw_nonneg {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (t : ℤ) : 0 ≤ Aw b β t := by
  have hN := kapN_pos hb
  have hM := kapM2_nonneg b
  unfold Aw
  split_ifs with ht
  · positivity
  · have ht2 : 2 ≤ |t| := by omega
    have ht2' : (2 : ℝ) ≤ |(t : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast ht2
    have h1 : 0 ≤ |(t : ℝ)| - 1 := by linarith
    have hC : 0 ≤ farC b := by unfold farC; positivity
    have : 0 ≤ 1 / (|(t : ℝ)| - 1) ^ 3 := by positivity
    positivity

/-- **The inner region.** -/
theorem inner_le (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] {b β a Δ K X₀ : ℝ} (hb : 0 < b)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (ha : 0 < a) (hΔ : 0 < Δ) (hβ : β = √(a / Δ)) (n : ℕ)
    (hn : (n : ℝ) ≤ Δ / 2) (hX : X₀ ≤ Δ / 2) (hK : 0 ≤ K)
    (hW : ∀ c : ℝ, X₀ ≤ c →
      μ.real (Icc (c - 1 / 2) (c + 1 / 2)) ≤ K * c ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * c))) :
    ∫ x in Ioc (Δ - n) (Δ + n), |rhoErr b β (Δ - x)| ∂μ ≤
      K * (Δ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * Δ)) * Real.exp (β / 2) *
        (4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (farC b * β ^ 2) + 4 * (farC b * (β + 1))) := by
  set p : ℝ := Δ - n with hp
  set K' : ℝ := K * (Δ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * Δ)) with hK'
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  have hmeas : Measurable fun x : ℝ => |rhoErr b β (Δ - x)| :=
    (continuous_abs.measurable.comp ((measurable_rhoErr hb hβ0).comp (measurable_const.sub measurable_id)))
  have hbdd : ∀ x, |rhoErr b β (Δ - x)| ≤ 1 + Real.exp (β * max (Δ - x) 0) := fun x =>
    rhoErr_abs_le hb hβ0 _
  -- integrability on compact sets
  have hint : ∀ m : ℕ, IntegrableOn (fun x : ℝ => |rhoErr b β (Δ - x)|) (Ioc p (p + m)) μ := by
    intro m
    refine Measure.integrableOn_of_bounded (M := 1 + Real.exp (β * (n + m + |Δ|))) ?_ ?_ ?_
    · exact (measure_Ioc_lt_top).ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      refine (hbdd x).trans ?_
      have : max (Δ - x) 0 ≤ n + m + |Δ| := by
        refine max_le ?_ (by positivity)
        have := hx.1; have := hx.2
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have := le_abs_self Δ
        have := neg_abs_le Δ
        linarith
      have := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left this hβ0)
      linarith
  have hc : ∀ j : ℕ, ∀ x ∈ Ioc (p + j) (p + j + 1),
      |rhoErr b β (Δ - x)| ≤ Aw b β ((n : ℤ) - j) * Real.exp (β * (((n : ℤ) - j : ℤ) : ℝ)) := by
    intro j x hx
    refine rhoErr_window hb hβ0 hβ1 ((n : ℤ) - j) ?_ ?_
    · push_cast; have := hx.2; rw [hp] at this; linarith
    · push_cast; have := hx.1; rw [hp] at this; linarith
  have key := setIntegral_Ioc_le_sum μ p (fun j => Aw b β ((n : ℤ) - j) * Real.exp (β * (((n : ℤ) - j : ℤ) : ℝ)))
    (fun x => abs_nonneg _) hint hc (2 * n)
  have hend : p + ((2 * n : ℕ) : ℝ) = Δ + n := by rw [hp]; push_cast; ring
  rw [hend] at key
  refine key.trans ?_
  -- bound each window
  have hwin : ∀ j ∈ Finset.range (2 * n),
      Aw b β ((n : ℤ) - j) * Real.exp (β * (((n : ℤ) - j : ℤ) : ℝ)) * μ.real (Ioc (p + j) (p + j + 1)) ≤
        K' * Real.exp (β / 2) * Aw b β ((n : ℤ) - j) := by
    intro j hj
    have hj' : j < 2 * n := Finset.mem_range.1 hj
    have hjr : (j : ℝ) + 1 ≤ 2 * n := by exact_mod_cast hj'
    set c : ℝ := p + j + 1 / 2 with hcdef
    have hcΔ : Δ / 2 ≤ c := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      rw [hcdef, hp]; linarith
    have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hcΔ
    set k : ℝ := Δ - c with hkdef
    have hkΔ : k ≤ Δ := by rw [hkdef]; linarith
    have hkc : c = Δ - k := by rw [hkdef]; ring
    have hset : Ioc (p + j) (p + j + 1) ⊆ Icc (c - 1 / 2) (c + 1 / 2) := by
      intro x hx
      constructor
      · rw [hcdef]; linarith [hx.1]
      · rw [hcdef]; linarith [hx.2]
    have h1 : μ.real (Ioc (p + j) (p + j + 1)) ≤ μ.real (Icc (c - 1 / 2) (c + 1 / 2)) :=
      measureReal_mono hset (measure_Icc_lt_top).ne
    have h2 := hW c (le_trans hX hcΔ)
    have h3 : c ^ (-(3 / 4 : ℝ)) ≤ (Δ / 2) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcΔ (by norm_num)
    have h4 : Real.exp (2 * √(a * c)) ≤ Real.exp (2 * √(a * Δ)) * Real.exp (-(β * k)) := by
      have := exp_two_sqrt_le ha hΔ hkΔ
      rw [← hβ] at this
      rw [hkc]; exact this
    have hAw := Aw_nonneg hb hβ0 ((n : ℤ) - j)
    have hμ : μ.real (Ioc (p + j) (p + j + 1)) ≤ K' * Real.exp (-(β * k)) := by
      refine h1.trans (h2.trans ?_)
      have e1 : K * c ^ (-(3 / 4 : ℝ)) ≤ K * (Δ / 2) ^ (-(3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 hK
      have e2 := mul_le_mul e1 h4 (Real.exp_pos _).le (by positivity)
      calc K * c ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * c))
          ≤ K * (Δ / 2) ^ (-(3 / 4 : ℝ)) * (Real.exp (2 * √(a * Δ)) * Real.exp (-(β * k))) := e2
        _ = K' * Real.exp (-(β * k)) := by rw [hK']; ring
    have ht : (((n : ℤ) - j : ℤ) : ℝ) = k + 1 / 2 := by
      rw [hkdef, hcdef, hp]; push_cast; ring
    rw [ht]
    calc Aw b β ((n : ℤ) - j) * Real.exp (β * (k + 1 / 2)) * μ.real (Ioc (p + j) (p + j + 1))
        ≤ Aw b β ((n : ℤ) - j) * Real.exp (β * (k + 1 / 2)) * (K' * Real.exp (-(β * k))) :=
          mul_le_mul_of_nonneg_left hμ (by positivity)
      _ = K' * Real.exp (β / 2) * Aw b β ((n : ℤ) - j) := by
          have : Real.exp (β * (k + 1 / 2)) * Real.exp (-(β * k)) = Real.exp (β / 2) := by
            rw [← Real.exp_add]; congr 1; ring
          calc Aw b β ((n : ℤ) - j) * Real.exp (β * (k + 1 / 2)) * (K' * Real.exp (-(β * k)))
              = Aw b β ((n : ℤ) - j) * K' * (Real.exp (β * (k + 1 / 2)) * Real.exp (-(β * k))) := by ring
            _ = _ := by rw [this]; ring
  refine (Finset.sum_le_sum hwin).trans ?_
  rw [← Finset.mul_sum]
  have := sum_Aw_le hb hβ0 n
  have hE : 0 ≤ K' * Real.exp (β / 2) := by positivity
  calc K' * Real.exp (β / 2) * ∑ j ∈ Finset.range (2 * n), Aw b β ((n : ℤ) - j)
      ≤ K' * Real.exp (β / 2) * (4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (farC b * β ^ 2) +
        4 * (farC b * (β + 1))) := mul_le_mul_of_nonneg_left this hE
    _ = _ := by rw [hK']

end Lightlike.Tauberian
