import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.MinkowskiCausal

/-!
# The causal future of Minkowski space

The causal future `J⁺(x)` of a point of Minkowski space `ℝ^{d+1}` is the closed future light cone
`{y | 0 ≤ (y - x)⁰ ∧ η(y - x, y - x) ≤ 0}` (`minkowski_causalFuture`). A point of the cone is
reached by a straight line, which is a causal curve. Conversely the displacement along a
causal curve lies in the cone: for every `u` with `Σ uᵢ² ≤ 1` the function `v ↦ v⁰ - Σ uᵢ vⁱ` is
nonnegative on future causal vectors, so it does not decrease along a locally Lipschitz causal curve
(its derivative, which exists almost everywhere, is nonnegative, and a Lipschitz function is the
integral of its derivative), and a vector `Δ` with all these quantities nonnegative has
`Δ⁰ ≥ |Δ_space|`.

## References

* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1.
* E. Minguzzi, *Lorentzian causality theory*, Living Reviews in Relativity 22 (2019), Section 2.

The comparison of the statements with these sources at a location is pending.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {d : ℕ}

/-- The linear form `v ↦ v⁰ - Σ uᵢ vⁱ`, `u` a spatial direction. -/
def timeMinus (u : Fin d → ℝ) : (Fin (d + 1) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 - ∑ i : Fin d, u i • ContinuousLinearMap.proj i.succ

lemma timeMinus_apply (u : Fin d → ℝ) (v : Fin (d + 1) → ℝ) :
    timeMinus u v = v 0 - ∑ i, u i * v i.succ := by
  simp [timeMinus]

lemma minkowskiForm_e0 (v : Fin (d + 1) → ℝ) :
    minkowskiForm (d + 1) v (Pi.single 0 1) = -v 0 := by
  rw [minkowskiForm_eq]
  simp [Fin.succ_ne_zero]

/-- `timeMinus u` is nonnegative on a future-directed causal vector, for `|u| ≤ 1`. -/
lemma timeMinus_nonneg {u : Fin d → ℝ} (hu : ∑ i, u i ^ 2 ≤ 1) {v : Fin (d + 1) → ℝ}
    (h1 : minkowskiForm (d + 1) v v ≤ 0) (h2 : minkowskiForm (d + 1) v (Pi.single 0 1) < 0) :
    0 ≤ timeMinus u v := by
  rw [minkowskiForm_e0] at h2
  rw [minkowskiForm_eq] at h1
  rw [timeMinus_apply]
  have hS : ∑ i : Fin d, v i.succ * v i.succ ≤ v 0 * v 0 := by linarith
  have hcs : (∑ i : Fin d, u i * v i.succ) ^ 2 ≤ (∑ i, u i ^ 2) * ∑ i : Fin d, v i.succ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv2 : 0 ≤ ∑ i : Fin d, v i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS' : ∑ i : Fin d, v i.succ ^ 2 ≤ v 0 ^ 2 := by
    simpa [sq] using hS
  have : (∑ i : Fin d, u i * v i.succ) ^ 2 ≤ v 0 ^ 2 := by nlinarith
  by_contra hneg
  push Not at hneg
  nlinarith

set_option synthInstance.maxHeartbeats 200000 in
/-- A future-directed causal curve in Minkowski space on `[a, b]` is locally Lipschitz in the
ordinary sense (the chart at every point is the identity). -/
lemma locallyLipschitzOn_of_curve {γ : ℝ → Fin (d + 1) → ℝ} {s : Set ℝ}
    (h : IsLocallyLipschitzOn (I := 𝓘(ℝ, Fin (d + 1) → ℝ)) γ s) : LocallyLipschitzOn s γ := by
  intro t ht
  obtain ⟨K, U, hU, -, hl⟩ := h t ht
  refine ⟨K, U, hU, ?_⟩
  simpa [extChartAt_model_space_eq_id] using hl

set_option synthInstance.maxHeartbeats 200000 in
/-- **Monotonicity along a causal curve**: for `|u| ≤ 1` the quantity `γ⁰ - Σ uᵢ γⁱ` does not
decrease along a future-directed causal curve of Minkowski space. -/
theorem timeMinus_mono {γ : ℝ → Fin (d + 1) → ℝ} {a b : ℝ} (hab : a < b)
    (h : IsFutureCausalCurve (minkowskiOrientation d) γ (Icc a b)) {u : Fin d → ℝ}
    (hu : ∑ i, u i ^ 2 ≤ 1) : timeMinus u (γ a) ≤ timeMinus u (γ b) := by
  obtain ⟨K, hK⟩ := (locallyLipschitzOn_of_curve h.lipschitz).exists_lipschitzOnWith_of_compact
    isCompact_Icc
  set f : ℝ → ℝ := fun t => timeMinus u (γ t) with hf
  have hfL : LipschitzOnWith (‖timeMinus u‖₊ * K) f (Icc a b) :=
    (timeMinus u).lipschitzWith.comp_lipschitzOnWith hK
  have hAC : AbsolutelyContinuousOnInterval f a b := by
    refine LipschitzOnWith.absolutelyContinuousOnInterval (K := ‖timeMinus u‖₊ * K) ?_
    rw [uIcc_of_le hab.le]
    exact hfL
  have hint := hAC.integral_deriv_eq_sub
  have hnn : 0 ≤ ∫ x in a..b, deriv f x := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hab.le ?_
    filter_upwards [h.ae_velocity, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae ((Set.toFinite ({a, b} : Set ℝ)).countable.ae_notMem _)] with
      t ⟨hd, hP⟩ ht hne
    have hne' : t ≠ a ∧ t ≠ b := by simpa [not_or] using hne
    have hmem : Icc a b ∈ 𝓝 t := Icc_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm hne'.1))
      (lt_of_le_of_ne ht.2 hne'.2)
    have hd' : DifferentiableWithinAt ℝ γ (Icc a b) t :=
      (mdifferentiableWithinAt_iff_differentiableWithinAt).1 hd
    have hda : DifferentiableAt ℝ γ t := hd'.differentiableAt hmem
    have hvel : velocity 𝓘(ℝ, Fin (d + 1) → ℝ) γ (Icc a b) t = deriv γ t := by
      unfold velocity
      rw [mfderivWithin_eq_fderivWithin, fderivWithin_of_mem_nhds hmem]
      change fderiv ℝ γ t (1 : ℝ) = deriv γ t
      exact (fderiv_eq_smul_deriv 1).trans (one_smul _ _)
    have hder : HasDerivAt f (timeMinus u (deriv γ t)) t :=
      (timeMinus u).hasFDerivAt.comp_hasDerivAt t hda.hasDerivAt
    rw [hder.deriv]
    rw [hvel] at hP
    exact timeMinus_nonneg hu hP.2.1 hP.2.2
  linarith

/-- A vector `Δ` for which `Δ⁰ - Σ uᵢ Δⁱ ≥ 0` for every `|u| ≤ 1` is in the closed future cone. -/
lemma mem_cone_of_timeMinus {Δ : Fin (d + 1) → ℝ} (h : ∀ u : Fin d → ℝ, ∑ i, u i ^ 2 ≤ 1 →
    0 ≤ timeMinus u Δ) : 0 ≤ Δ 0 ∧ minkowskiForm (d + 1) Δ Δ ≤ 0 := by
  have h0 : 0 ≤ Δ 0 := by simpa [timeMinus_apply] using h 0 (by simp)
  refine ⟨h0, ?_⟩
  rw [minkowskiForm_eq]
  set S : ℝ := ∑ i : Fin d, Δ i.succ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : S ≤ Δ 0 ^ 2 := by
    rcases hS0.eq_or_lt with h' | h'
    · rw [← h']; positivity
    · set N := Real.sqrt S with hN
      have hN0 : 0 < N := Real.sqrt_pos.2 h'
      have hNN : N ^ 2 = S := Real.sq_sqrt hS0
      have := h (fun i => Δ i.succ / N) (by
        have : ∑ i : Fin d, (Δ i.succ / N) ^ 2 = S / N ^ 2 := by
          rw [hS, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by rw [div_pow]
        rw [this, hNN, div_self h'.ne'])
      rw [timeMinus_apply] at this
      have h2 : ∑ i : Fin d, Δ i.succ / N * Δ i.succ = S / N := by
        rw [hS, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h2] at this
      have h3 : N ≤ Δ 0 := by
        have : S / N = N := by rw [← hNN]; field_simp
        linarith
      nlinarith
  have : ∑ i : Fin d, Δ i.succ * Δ i.succ = S := by
    rw [hS]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  nlinarith

set_option synthInstance.maxHeartbeats 200000 in
/-- A straight line with a future-directed causal direction is a future-directed causal curve. -/
theorem isFutureCausalCurve_line (x v : Fin (d + 1) → ℝ) {a b : ℝ} (hab : a < b)
    (hv : v ≠ 0 ∧ minkowskiForm (d + 1) v v ≤ 0 ∧ minkowskiForm (d + 1) v (Pi.single 0 1) < 0) :
    IsFutureCausalCurve (minkowskiOrientation d) (fun t : ℝ => x + t • v) (Icc a b) := by
  refine ⟨ordConnected_Icc, isLocallyLipschitzOn_line x v _, ?_⟩
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  obtain ⟨h1, h2⟩ := velocity_line x v hab ht
  refine ⟨h2, ?_⟩
  rw [h1]
  exact hv

/-- **The causal future in Minkowski space is the closed light cone.** The inclusion `⊇` is a
straight line; `⊆` integrates the nonnegative derivative of `γ⁰ - Σ uᵢ γⁱ` along a Lipschitz causal
curve (`timeMinus_mono`). (The comparison with the sources at a location is pending.) -/
theorem minkowski_causalFuture_eq (x : Fin (d + 1) → ℝ) :
    causalFuture (minkowskiOrientation d) x =
      {y | 0 ≤ (y - x) 0 ∧ minkowskiForm (d + 1) (y - x) (y - x) ≤ 0} := by
  ext y
  constructor
  · rintro ⟨γ, a, b, hab, h, e1, e2⟩
    rcases hab.eq_or_lt with rfl | hab'
    · have : y = x := by rw [← e1, ← e2]
      subst this
      simp
    · refine mem_cone_of_timeMinus fun u hu => ?_
      have := timeMinus_mono hab' h hu
      rw [e1, e2] at this
      simpa [map_sub] using this
  · rintro ⟨h0, h1⟩
    by_cases hv : y - x = 0
    · have : y = x := sub_eq_zero.1 hv
      subst this
      exact self_mem_causalFuture _ _
    · have hpos : 0 < (y - x) 0 := by
        refine lt_of_le_of_ne h0 fun h0' => hv ?_
        rw [minkowskiForm_eq, ← h0'] at h1
        simp only [mul_zero, neg_zero, zero_add] at h1
        have hz : ∀ i : Fin d, (y - x) i.succ = 0 := by
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg ((y - x) i.succ))).1
            (le_antisymm h1 (Finset.sum_nonneg fun i _ => mul_self_nonneg _))
          exact fun i => mul_self_eq_zero.1 (this i (Finset.mem_univ _))
        ext j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact h0'.symm
        · exact hz i
      refine ⟨fun t : ℝ => x + t • (y - x), 0, 1, zero_le_one,
        isFutureCausalCurve_line x (y - x) zero_lt_one ⟨hv, h1, ?_⟩, by simp, by simp⟩
      rw [minkowskiForm_e0]
      linarith

end Lightlike.Causal
