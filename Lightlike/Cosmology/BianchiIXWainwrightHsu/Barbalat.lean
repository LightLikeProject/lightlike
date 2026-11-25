import Mathlib

/-!
# A Barbalat-type lemma towards the past (row G1-040, milestone CO14)

Used in the attractor argument for Bianchi IX: along a bounded solution the function `q = 2Σ²` is
uniformly continuous, and `∫_{-∞}^0 q P < ∞` with `P = N₁N₂N₃ ≥ L > 0` forces `∫_{-∞}^0 q < ∞`;
the lemma below then gives `q → 0` as `τ → -∞`.
-/

namespace Lightlike.Cosmology.BianchiIXWainwrightHsu

open Filter Topology MeasureTheory

/-- **Barbalat's lemma towards `-∞`**: a nonnegative, continuous, uniformly continuous function
with bounded integrals `∫_a^0 q ≤ C` (`a ≤ 0`) tends to `0` at `-∞`. -/
lemma barbalat_atBot {q : ℝ → ℝ} (hq0 : ∀ t, 0 ≤ q t) (hqc : Continuous q)
    (hu : UniformContinuous q) (C : ℝ) (hC : ∀ a ≤ 0, ∫ x in a..0, q x ≤ C) :
    Tendsto q atBot (𝓝 0) := by
  set F : ℝ → ℝ := fun a => ∫ x in a..0, q x with hF
  have hint : ∀ a b : ℝ, IntervalIntegrable q volume a b := fun a b =>
    hqc.intervalIntegrable a b
  have hanti : Antitone F := by
    intro a b hab
    have := intervalIntegral.integral_add_adjacent_intervals (hint a b) (hint b 0)
    have hnn : 0 ≤ ∫ x in a..b, q x :=
      intervalIntegral.integral_nonneg hab (fun x _ => hq0 x)
    simp only [hF]
    linarith
  have hbdd : BddAbove (Set.range F) := by
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨a, rfl⟩
    rcases le_total a 0 with ha | ha
    · exact le_trans (hC a ha) (le_max_left _ _)
    · have : 0 ≤ ∫ x in (0:ℝ)..a, q x :=
        intervalIntegral.integral_nonneg ha (fun x _ => hq0 x)
      have h2 : F a = - ∫ x in (0:ℝ)..a, q x := by
        simp only [hF]; rw [intervalIntegral.integral_symm]
      rw [h2]; exact le_trans (by linarith) (le_max_right _ _)
  have hlim := tendsto_atBot_ciSup hanti hbdd
  set L := ⨆ i, F i
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 hu (ε / 2) (by linarith)
  have hev := (Metric.tendsto_nhds.1 hlim) (ε * δ / 8) (by positivity)
  obtain ⟨T, hT⟩ := eventually_atBot.1 hev
  rw [eventually_atBot]
  refine ⟨T, fun t ht => ?_⟩
  by_contra hcon
  have hqt : ε ≤ q t := by
    have : ¬ dist (q t) 0 < ε := hcon
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hq0 t)] at this
    linarith
  have hlow : ∀ x ∈ Set.Icc (t - δ / 2) t, ε / 2 ≤ q x := by
    intro x hx
    have h1 := hδu (a := x) (b := t) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
    rw [Real.dist_eq, abs_lt] at h1
    linarith [h1.1]
  have hle : t - δ / 2 ≤ t := by linarith
  have hmono : ∫ x in (t - δ / 2)..t, (ε / 2) ≤ ∫ x in (t - δ / 2)..t, q x :=
    intervalIntegral.integral_mono_on hle (by simp) (hint _ _) hlow
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hadj := intervalIntegral.integral_add_adjacent_intervals (hint (t - δ / 2) t) (hint t 0)
  have h1 := hT t ht
  have h2 := hT (t - δ / 2) (by linarith)
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hFt : F t = ∫ x in t..0, q x := rfl
  have hFt2 : F (t - δ / 2) = ∫ x in (t - δ / 2)..0, q x := rfl
  have : (t - (t - δ / 2)) * (ε / 2) = ε * δ / 4 := by ring
  nlinarith [h1.1, h1.2, h2.1, h2.2]

end Lightlike.Cosmology.BianchiIXWainwrightHsu

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_040.barbalat_atBot := _root_.Lightlike.Cosmology.BianchiIXWainwrightHsu.barbalat_atBot
