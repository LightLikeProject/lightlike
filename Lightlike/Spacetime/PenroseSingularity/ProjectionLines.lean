import Lightlike.Spacetime.PenroseSingularity.FieldFlow
import Lightlike.Spacetime.PenroseSingularity.ClosedFuture
import Lightlike.Spacetime.Causal.CauchyCover
import Lightlike.Spacetime.Causal.CauchySeparation
import Lightlike.Spacetime.Causal.TimelikeBelowCurve

/-!
# Integral lines of a timelike vector field as inextendible timelike curves (G1-012, hproj / hopen)

The maximal integral curves `curveMax X y` of a smooth future-directed timelike field `X` are
inextendible future-directed timelike curves on `domMax X y`.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

open Lightlike.Causal in
/-- **The maximal integral curve of a timelike field has no past endpoint.** -/
theorem curveMax_not_hasPastEndpoint {X : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
    (hX : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hX0 : ∀ x, X x ≠ 0) (y p : M) : ¬ HasPastEndpoint (curveMax X y) (domMax X y) p := by
  have hX' : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 1
      (fun x ↦ (⟨x, (-X) x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) := hX.neg_section
  intro hp
  refine curveMax_not_hasFutureEndpoint hX' (fun x => neg_ne_zero.2 (hX0 x)) y p fun U hU => ?_
  obtain ⟨c, hc, hcU⟩ := hp U hU
  have h0 := zero_mem_domMax hX y
  set c' : ℝ := min c 0 with hc'
  have hc'mem : c' ∈ domMax X y := by
    rcases le_total c 0 with h | h
    · simpa [hc', min_eq_left h] using hc
    · simpa [hc', min_eq_right h] using h0
  refine ⟨-c', ⟨(domMax_neg y (-c')).2 (by simpa using hc'mem), by simp [hc']⟩, fun t ht htc => ?_⟩
  have htd : -t ∈ domMax X y := by
    have := (domMax_neg (Y := X) y t).1 ht.1
    exact this
  have hle : -t ≤ c := by linarith [min_le_left c 0]
  have := hcU (-t) htd hle
  rwa [← curveMax_neg hX y htd, neg_neg] at this

open Lightlike.Causal in
/-- **The maximal integral curves of a smooth future timelike field are inextendible future timelike
curves.** -/
theorem isInextendibleFutureTimelike_curveMax (T : TimeOrientation g)
    {X : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
    (hXs : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hXT : ∀ x, T.IsFutureTimelike (X x)) (y : M) :
    IsInextendibleFutureTimelike T (curveMax X y) (domMax X y) := by
  have hX : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) := hXs.of_le (by norm_num)
  have hX0 : ∀ x, X x ≠ 0 := fun x h0 => by
    have := (hXT x).1
    rw [h0] at this
    simp at this
  refine ⟨isFutureTimelikeCurve_of_integralCurve T hX.continuous hXT (isOpen_domMax hX y)
    (ordConnected_domMax y) (isMIntegralCurveOn_curveMax hX y), ⟨⟨0, zero_mem_domMax hX y⟩, ?_, ?_⟩⟩
  · intro p hp
    refine curveMax_not_hasFutureEndpoint hX hX0 y p fun U hU => ?_
    obtain ⟨c, hc, hcU⟩ := hp U hU
    have h0 := zero_mem_domMax hX y
    refine ⟨max c 0, ⟨?_, mem_Ici.2 (le_max_right _ _)⟩,
      fun t ht htc => hcU t ht.1 ((le_max_left _ _).trans htc)⟩
    rcases le_total c 0 with h | h
    · simpa [max_eq_right h] using h0
    · simpa [max_eq_left h] using hc
  · exact curveMax_not_hasPastEndpoint hX hX0 y

section Lines

open Lightlike.Causal

variable (T : TimeOrientation g) {X : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
  (hXs : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
  (hXT : ∀ x, T.IsFutureTimelike (X x))

include hXs in
theorem hX1 : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) 1
    (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) := hXs.of_le (by norm_num)

include hXs hXT in
/-- **A later point of a maximal integral line is in the chronological future of an earlier one.** -/
theorem curveMax_mem_chronFuture {y : M} {u v : ℝ} (hu : u ∈ domMax X y) (hv : v ∈ domMax X y)
    (huv : u < v) : curveMax X y v ∈ chronFuture T (curveMax X y u) := by
  have hG := (isInextendibleFutureTimelike_curveMax T hXs hXT y).1
  exact ⟨curveMax X y, u, v, huv, hG.restrict T
    (fun r hr => (ordConnected_domMax (Y := X) y).out hu hv hr) huv, rfl, rfl⟩

include hXs hXT in
/-- **Every maximal integral line crosses a Cauchy surface exactly once.** -/
theorem exists_unique_crossing {Sig : Set M} (hCS : IsCauchySurface T Sig) (y : M) :
    ∃! t, t ∈ domMax X y ∧ curveMax X y t ∈ Sig :=
  hCS _ _ (isInextendibleFutureTimelike_curveMax T hXs hXT y)

open Classical in
/-- The time at which the maximal integral line through `y` meets `Sig` (junk, `0`, if it does not). -/
def hitTime (X : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (Sig : Set M) (y : M) : ℝ :=
  if h : ∃ t, t ∈ domMax X y ∧ curveMax X y t ∈ Sig then Classical.choose h else 0

variable {Sig : Set M}

include hXs hXT in
theorem hitTime_spec (hCS : IsCauchySurface T Sig) (y : M) :
    hitTime X Sig y ∈ domMax X y ∧ curveMax X y (hitTime X Sig y) ∈ Sig := by
  have h := (exists_unique_crossing T hXs hXT hCS y).exists
  unfold hitTime
  rw [dif_pos h]
  exact Classical.choose_spec h

include hXs hXT in
theorem hitTime_eq (hCS : IsCauchySurface T Sig) {y : M} {t : ℝ} (ht : t ∈ domMax X y)
    (hS : curveMax X y t ∈ Sig) : hitTime X Sig y = t :=
  (exists_unique_crossing T hXs hXT hCS y).unique (hitTime_spec T hXs hXT hCS y) ⟨ht, hS⟩

include hXs hXT in
/-- **The hitting time of a Cauchy surface is continuous.** -/
theorem continuousAt_hitTime (hCS : IsCauchySurface T Sig) (y₀ : M) :
    ContinuousAt (hitTime X Sig) y₀ := by
  have hX := hX1 hXs
  obtain ⟨hD, hc⟩ := isOpen_flowDomain_continuousOn (Y := X) hX
  have hA : IsAchronal T Sig := hCS.isAchronal_of_boundaryless
  have hFo : IsOpen (chronFutureSet T Sig) := isOpen_biUnion fun x _ => isOpen_chronFuture_of_reach T x
  have hPo : IsOpen (chronPastSet T Sig) := isOpen_biUnion fun x _ => isOpen_chronPast T x
  have hdisj := chronFutureSet_disjoint_chronPastSet T hA
  set τ₀ := hitTime X Sig y₀ with hτ₀
  obtain ⟨hτ₀d, hτ₀S⟩ := hitTime_spec T hXs hXT hCS y₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- a small closed interval around `τ₀` inside the domain
  obtain ⟨η, hη, hηsub⟩ : ∃ η > 0, Icc (τ₀ - η) (τ₀ + η) ⊆ domMax X y₀ := by
    obtain ⟨η, hη, hb⟩ := Metric.isOpen_iff.1 (isOpen_domMax hX y₀) τ₀ hτ₀d
    refine ⟨η / 2, by linarith, fun s hs => hb ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  set e : ℝ := min η (ε / 2) with he
  have hepos : 0 < e := lt_min hη (by linarith)
  have hsubI : Icc (τ₀ - e) (τ₀ + e) ⊆ domMax X y₀ := fun s hs => hηsub
    ⟨by linarith [hs.1, min_le_left η (ε / 2)], by linarith [hs.2, min_le_left η (ε / 2)]⟩
  -- a neighbourhood on which the whole interval is in the domain
  obtain ⟨u, v, hu, hv, hy₀u, hIv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := y₀))
    (isCompact_Icc (a := τ₀ - e) (b := τ₀ + e)) hD (n := {p : M × ℝ | p.2 ∈ domMax X p.1})
    (fun p hp => by
      rw [mem_prod] at hp
      rw [mem_singleton_iff] at hp
      obtain ⟨h1, h2⟩ := hp
      show p.2 ∈ domMax X p.1
      rw [h1]
      exact hsubI h2)
  have hy₀u' : y₀ ∈ u := hy₀u rfl
  -- the endpoints are in `I⁺(Σ)` and `I⁻(Σ)`
  have hb₀ : curveMax X y₀ (τ₀ + e) ∈ chronFutureSet T Sig :=
    mem_biUnion hτ₀S (curveMax_mem_chronFuture T hXs hXT hτ₀d (hsubI ⟨by linarith, le_rfl⟩)
      (by linarith))
  have ha₀ : curveMax X y₀ (τ₀ - e) ∈ chronPastSet T Sig :=
    mem_biUnion hτ₀S (curveMax_mem_chronFuture T hXs hXT (hsubI ⟨le_rfl, by linarith⟩) hτ₀d
      (by linarith))
  have hcts : ∀ s ∈ Icc (τ₀ - e) (τ₀ + e), ContinuousAt (fun y => curveMax X y s) y₀ := by
    intro s hs
    have hmem : (y₀, s) ∈ {p : M × ℝ | p.2 ∈ domMax X p.1} := hsubI hs
    have h1 := (hc (y₀, s) hmem).continuousAt (hD.mem_nhds hmem)
    exact h1.comp (f := fun y : M => (y, s)) (continuousAt_id.prodMk continuousAt_const)
  have hE2 : ∀ᶠ y in 𝓝 y₀, curveMax X y (τ₀ + e) ∈ chronFutureSet T Sig :=
    (hcts _ ⟨by linarith, le_rfl⟩).eventually (hFo.mem_nhds hb₀)
  have hE3 : ∀ᶠ y in 𝓝 y₀, curveMax X y (τ₀ - e) ∈ chronPastSet T Sig :=
    (hcts _ ⟨le_rfl, by linarith⟩).eventually (hPo.mem_nhds ha₀)
  filter_upwards [hu.mem_nhds hy₀u', hE2, hE3] with y hyu hy2 hy3
  have hIy : Icc (τ₀ - e) (τ₀ + e) ⊆ domMax X y := fun s hs =>
    huv (mk_mem_prod hyu (hIv hs))
  -- the line through `y` crosses `Σ` in the interval
  have hcross : ∃ s ∈ Icc (τ₀ - e) (τ₀ + e), curveMax X y s ∈ Sig := by
    by_contra hno
    push_neg at hno
    have hcont : ContinuousOn (curveMax X y) (Icc (τ₀ - e) (τ₀ + e)) :=
      (isMIntegralCurveOn_curveMax hX y).continuousOn.mono hIy
    have hC : IsPreconnected (curveMax X y '' Icc (τ₀ - e) (τ₀ + e)) :=
      isPreconnected_Icc.image _ hcont
    have hcov : curveMax X y '' Icc (τ₀ - e) (τ₀ + e) ⊆ chronFutureSet T Sig ∪ chronPastSet T Sig := by
      rintro _ ⟨s, hs, rfl⟩
      rcases hCS.cover T (curveMax X y s) with h | ⟨x, hx, h⟩ | ⟨x, hx, h⟩
      · exact absurd h (hno s hs)
      · exact Or.inl (mem_biUnion hx h)
      · exact Or.inr (mem_biUnion hx h)
    rcases hC.subset_or_subset hFo hPo hdisj hcov with h | h
    · exact (disjoint_left.1 hdisj (h ⟨τ₀ - e, ⟨le_rfl, by linarith⟩, rfl⟩)) hy3
    · exact (disjoint_left.1 hdisj hy2) (h ⟨τ₀ + e, ⟨by linarith, le_rfl⟩, rfl⟩)
  obtain ⟨s, hs, hsS⟩ := hcross
  rw [hitTime_eq T hXs hXT hCS (hIy hs) hsS, Real.dist_eq, abs_lt]
  constructor <;> linarith [hs.1, hs.2, min_le_right η (ε / 2)]

include hXs hXT in
/-- **The projection along the integral lines to the Cauchy surface is continuous.** -/
theorem continuous_proj (hCS : IsCauchySurface T Sig) :
    Continuous (fun y => curveMax X y (hitTime X Sig y)) := by
  have hX := hX1 hXs
  obtain ⟨hD, hc⟩ := isOpen_flowDomain_continuousOn (Y := X) hX
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  have hmem : (y₀, hitTime X Sig y₀) ∈ {p : M × ℝ | p.2 ∈ domMax X p.1} :=
    (hitTime_spec T hXs hXT hCS y₀).1
  have h1 := (hc _ hmem).continuousAt (hD.mem_nhds hmem)
  exact h1.comp (f := fun y : M => (y, hitTime X Sig y))
    (continuousAt_id.prodMk (continuousAt_hitTime T hXs hXT hCS y₀))

end Lines

end Lightlike.Penrose
