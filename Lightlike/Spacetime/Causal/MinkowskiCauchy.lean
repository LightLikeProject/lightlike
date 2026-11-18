import Lightlike.Spacetime.Causal.MinkowskiFuture
import Lightlike.Spacetime.Causal.Ladder

/-!
# The slice `t = 0` is a Cauchy surface of Minkowski space

Along a future-directed causal curve of Minkowski space the time `γ⁰` does not decrease and the
spatial displacement is bounded by the time elapsed (`timeMinus_mono` with `u = ±eᵢ`). On a
timelike curve the time strictly increases, since a curve with constant time has constant space
coordinates and a timelike curve is not constant. So an inextendible curve meets the slice at most
once; it meets it at least once, since otherwise its time has a sign and is monotone and bounded,
the curve is Cauchy at one end, and a limit exists there, an endpoint.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Chapter 6.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

section Generic

variable {F : Type*} [MetricSpace F] [CompleteSpace F]

/-- **A curve whose displacement is bounded by the increase of a function `τ` that is bounded
below has a past endpoint.** -/
theorem exists_hasPastEndpoint {γ : ℝ → F} {τ : ℝ → ℝ} {s : Set ℝ} (hne : s.Nonempty)
    (hlip : ∀ t ∈ s, ∀ t' ∈ s, t ≤ t' → dist (γ t) (γ t') ≤ τ t' - τ t)
    (hb : BddBelow (τ '' s)) : ∃ p, HasPastEndpoint γ s p := by
  have : Nonempty (↥s)ᵒᵈ := ⟨OrderDual.toDual ⟨hne.some, hne.some_mem⟩⟩
  set u : (↥s)ᵒᵈ → F := fun x => γ (OrderDual.ofDual x).val with hu
  have hL : ∀ t ∈ s, sInf (τ '' s) ≤ τ t := fun t ht => csInf_le hb ⟨t, ht, rfl⟩
  have hcs : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨_, ⟨c, hc, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image τ)
      (lt_add_of_pos_right (sInf (τ '' s)) hε)
    refine ⟨OrderDual.toDual ⟨c, hc⟩, fun n hn => ?_⟩
    have hn' : (OrderDual.ofDual n).val ≤ c := hn
    have h1 := hlip _ (OrderDual.ofDual n).2 c hc hn'
    have h2 := hL _ (OrderDual.ofDual n).2
    show dist (γ (OrderDual.ofDual n).val) (γ c) < ε
    linarith
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨p, fun U hU => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp.eventually (Filter.mem_of_superset hU subset_rfl))
  refine ⟨(OrderDual.ofDual N).val, (OrderDual.ofDual N).2, fun t ht htc => ?_⟩
  exact hN (OrderDual.toDual ⟨t, ht⟩) htc

/-- **A curve whose displacement is bounded by the increase of a function `τ` that is bounded
above has a future endpoint.** -/
theorem exists_hasFutureEndpoint {γ : ℝ → F} {τ : ℝ → ℝ} {s : Set ℝ} (hne : s.Nonempty)
    (hlip : ∀ t ∈ s, ∀ t' ∈ s, t ≤ t' → dist (γ t) (γ t') ≤ τ t' - τ t)
    (hb : BddAbove (τ '' s)) : ∃ p, HasFutureEndpoint γ s p := by
  have : Nonempty ↥s := ⟨⟨hne.some, hne.some_mem⟩⟩
  set u : ↥s → F := fun x => γ x.val with hu
  have hU : ∀ t ∈ s, τ t ≤ sSup (τ '' s) := fun t ht => le_csSup hb ⟨t, ht, rfl⟩
  have hcs : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨_, ⟨c, hc, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne.image τ)
      (sub_lt_self (sSup (τ '' s)) hε)
    refine ⟨⟨c, hc⟩, fun n hn => ?_⟩
    have hn' : c ≤ n.val := hn
    have h1 := hlip c hc _ n.2 hn'
    have h2 := hU _ n.2
    show dist (γ n.val) (γ c) < ε
    rw [dist_comm]
    linarith
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨p, fun V hV => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp.eventually (Filter.mem_of_superset hV subset_rfl))
  exact ⟨N.val, N.2, fun t ht htc => hN ⟨t, ht⟩ htc⟩

end Generic

section Minkowski

variable {d : ℕ}

lemma timeMinus_unit (i : Fin d) (σ : ℝ) (v : Fin (d + 1) → ℝ) :
    timeMinus (fun j => if j = i then σ else 0) v = v 0 - σ * v i.succ := by
  rw [timeMinus_apply]
  simp [ite_mul]

set_option synthInstance.maxHeartbeats 200000 in
/-- Along a future-directed causal curve of Minkowski space on `[a, b]` the time does not decrease
and every coordinate changes by at most the time elapsed. -/
theorem coord_sub_le {γ : ℝ → Fin (d + 1) → ℝ} {a b : ℝ} (hab : a < b)
    (h : IsFutureCausalCurve (minkowskiOrientation d) γ (Icc a b)) :
    γ a 0 ≤ γ b 0 ∧ ∀ j, |γ b j - γ a j| ≤ γ b 0 - γ a 0 := by
  have h0 : γ a 0 ≤ γ b 0 := by
    have := timeMinus_mono hab h (u := 0) (by simp)
    simpa [timeMinus_apply] using this
  refine ⟨h0, fun j => ?_⟩
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [abs_of_nonneg (by linarith)]
  · have h1 := timeMinus_mono hab h (u := fun j => if j = i then 1 else 0) (by simp)
    have h2 := timeMinus_mono hab h (u := fun j => if j = i then -1 else 0) (by simp)
    rw [timeMinus_unit, timeMinus_unit] at h1 h2
    rw [abs_le]
    constructor <;> linarith

set_option synthInstance.maxHeartbeats 200000 in
/-- **Space is bounded by time along a causal curve**: for `t ≤ t'` in the domain the time does not
decrease and `dist (γ t) (γ t') ≤ γ t'⁰ - γ t⁰`. -/
theorem dist_le_time_sub {γ : ℝ → Fin (d + 1) → ℝ} {s : Set ℝ}
    (h : IsFutureCausalCurve (minkowskiOrientation d) γ s) {t t' : ℝ} (ht : t ∈ s) (ht' : t' ∈ s)
    (htt' : t ≤ t') : γ t 0 ≤ γ t' 0 ∧ dist (γ t) (γ t') ≤ γ t' 0 - γ t 0 := by
  rcases htt'.eq_or_lt with rfl | hlt
  · simp
  · obtain ⟨h0, hb⟩ := coord_sub_le hlt
      (IsCurveWith.restrict h (fun r hr => h.ordConnected.out ht ht' hr) hlt)
    refine ⟨h0, ?_⟩
    rw [dist_pi_le_iff (by linarith)]
    intro j
    rw [Real.dist_eq, abs_sub_comm]
    exact hb j

set_option synthInstance.maxHeartbeats 200000 in
/-- **The time strictly increases along a future-directed timelike curve of Minkowski space.** -/
theorem time_lt_of_timelike {γ : ℝ → Fin (d + 1) → ℝ} {s : Set ℝ}
    (h : IsFutureTimelikeCurve (minkowskiOrientation d) γ s) {t t' : ℝ} (ht : t ∈ s)
    (ht' : t' ∈ s) (htt' : t < t') : γ t 0 < γ t' 0 := by
  have hc := isFutureCausalCurve_of_isFutureTimelikeCurve _ h
  by_contra hcon
  push Not at hcon
  have hsub : Icc t t' ⊆ s := fun r hr => h.1.ordConnected.out ht ht' hr
  have hconst : ∀ r ∈ Icc t t', γ r = γ t := by
    intro r hr
    have h1 := dist_le_time_sub hc ht (hsub hr) hr.1
    have h2 := dist_le_time_sub hc (hsub hr) ht' hr.2
    have : dist (γ t) (γ r) ≤ 0 := by linarith [h1.2, h2.1]
    exact (dist_le_zero.1 this).symm
  have hT : IsFutureTimelikeCurve (minkowskiOrientation d) γ (Icc t t') :=
    ⟨IsCurveWith.restrict h.1 hsub htt', fun a b hab hab' => h.2 a b hab (hab'.trans hsub)⟩
  obtain ⟨r, hr, hne⟩ := exists_ne_of_isFutureTimelikeCurve _ htt' hT (γ t)
  exact hne (hconst r hr)

set_option synthInstance.maxHeartbeats 200000 in
/-- **The slice `t = 0` is a Cauchy surface of Minkowski space.** Every inextendible
future-directed timelike curve meets it exactly once. (Hawking–Ellis, Chapter 6; the comparison
with the book at its location is pending.) -/
theorem minkowski_slice_isCauchySurface :
    IsCauchySurface (minkowskiOrientation d) {y : Fin (d + 1) → ℝ | y 0 = 0} := by
  intro γ s ⟨hT, hne, hnf, hnp⟩
  have hc := isFutureCausalCurve_of_isFutureTimelikeCurve _ hT
  have hcont : ContinuousOn (fun t => γ t 0) s :=
    (continuous_apply 0).comp_continuousOn (locallyLipschitzOn_of_curve hc.lipschitz).continuousOn
  have hlip : ∀ t ∈ s, ∀ t' ∈ s, t ≤ t' → dist (γ t) (γ t') ≤ (fun r => γ r 0) t' - (fun r => γ r 0) t :=
    fun t ht t' ht' htt' => (dist_le_time_sub hc ht ht' htt').2
  have hex : ∃ t ∈ s, γ t 0 = 0 := by
    by_contra hno
    push Not at hno
    by_cases hneg : ∃ t ∈ s, γ t 0 < 0
    · by_cases hpos : ∃ t ∈ s, 0 < γ t 0
      · obtain ⟨t₁, ht₁, h₁⟩ := hneg
        obtain ⟨t₂, ht₂, h₂⟩ := hpos
        obtain ⟨t, ht, h0⟩ := (hT.1.ordConnected.isPreconnected.intermediate_value ht₁ ht₂ hcont)
          ⟨h₁.le, h₂.le⟩
        exact hno t ht h0
      · push Not at hpos
        obtain ⟨p, hp⟩ := exists_hasFutureEndpoint hne hlip
          ⟨0, by rintro _ ⟨t, ht, rfl⟩; exact hpos t ht⟩
        exact hnf p hp
    · push Not at hneg
      obtain ⟨p, hp⟩ := exists_hasPastEndpoint hne hlip
        ⟨0, by rintro _ ⟨t, ht, rfl⟩; exact hneg t ht⟩
      exact hnp p hp
  obtain ⟨t₀, ht₀, h₀⟩ := hex
  refine ⟨t₀, ⟨ht₀, h₀⟩, fun t' ⟨ht', h'⟩ => ?_⟩
  rcases lt_trichotomy t' t₀ with hlt | heq | hgt
  · have := time_lt_of_timelike hT ht' ht₀ hlt
    simp only [mem_ofPred_eq] at h'
    linarith
  · exact heq
  · have := time_lt_of_timelike hT ht₀ ht' hgt
    simp only [mem_ofPred_eq] at h'
    linarith

end Minkowski

end Lightlike.Causal
