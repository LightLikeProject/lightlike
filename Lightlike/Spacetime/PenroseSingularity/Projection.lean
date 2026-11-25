import Lightlike.Spacetime.PenroseSingularity.ProjectionLines
import Lightlike.Spacetime.PenroseSingularity.AchronalBoundary

/-!
# The projection of `∂J⁺(S)` along a timelike flow into a Cauchy surface (G1-012, hproj / hopen)

Let `X` be a smooth future-directed timelike field, `Σ` a Cauchy surface and `S` a set with closed causal
future. Sending `q ∈ ∂J⁺(S)` to the point where the maximal integral line of `X` through `q` meets `Σ`
is a continuous map (`continuous_proj`).

The range of this map is the set of `σ ∈ Σ` whose integral line meets `∂J⁺(S)`. A line that meets
`∂J⁺(S)` enters `I⁺(S)` and leaves `J⁺(S)`, and each of these two conditions is stable under small
changes of the line; hence the range is a neighbourhood of each of its points in `Σ`. Only the stability of
these conditions and the continuity of the flow are used.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

open Lightlike.Causal

variable (T : TimeOrientation g) {X : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
  (hXs : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
  (hXT : ∀ x, T.IsFutureTimelike (X x)) {Sig : Set M}

/-- A preconnected set that meets a closed set and its complement meets its frontier. -/
theorem IsPreconnected.inter_frontier_of_isClosed {α : Type*} [TopologicalSpace α] {C J : Set α}
    (hC : IsPreconnected C) (hJ : IsClosed J) (h1 : (C ∩ J).Nonempty) (h2 : (C ∩ Jᶜ).Nonempty) :
    (C ∩ frontier J).Nonempty := by
  by_contra hno
  rw [not_nonempty_iff_eq_empty] at hno
  have hsub : C ⊆ interior J ∪ Jᶜ := by
    intro x hx
    by_cases hxJ : x ∈ J
    · left
      by_contra hxi
      exact (eq_empty_iff_forall_notMem.1 hno x) ⟨hx, subset_closure hxJ, hxi⟩
    · right; exact hxJ
  obtain ⟨x, hxC, hxJ⟩ := h1
  have hxi : x ∈ interior J := by
    rcases hsub hxC with h | h
    · exact h
    · exact absurd hxJ h
  obtain ⟨_, _, hz⟩ := hC _ _ isOpen_interior hJ.isOpen_compl hsub ⟨x, hxC, hxi⟩ h2
  exact hz.2 (interior_subset hz.1)

include hXs hXT in
/-- **The set of points whose integral line meets `∂J⁺(S)` is open.** -/
theorem isOpen_meets_frontier {S : Set M} (hclosed : IsClosed (causalFutureSet T S)) :
    IsOpen {σ : M | ∃ s ∈ domMax X σ, curveMax X σ s ∈ frontier (causalFutureSet T S)} := by
  have hX := hX1 hXs
  obtain ⟨hD, hc⟩ := isOpen_flowDomain_continuousOn (Y := X) hX
  rw [isOpen_iff_mem_nhds]
  rintro σ₀ ⟨s₀, hs₀, hq⟩
  set q := curveMax X σ₀ s₀ with hqd
  have hqJ : q ∈ causalFutureSet T S := hclosed.frontier_subset hq
  have hqI : q ∉ interior (causalFutureSet T S) := hq.2
  -- a closed interval around `s₀` in the domain
  obtain ⟨η, hη, hηsub⟩ : ∃ η > 0, Icc (s₀ - η) (s₀ + η) ⊆ domMax X σ₀ := by
    obtain ⟨η, hη, hb⟩ := Metric.isOpen_iff.1 (isOpen_domMax hX σ₀) s₀ hs₀
    refine ⟨η / 2, by linarith, fun s hs => hb ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hplus : curveMax X σ₀ (s₀ + η) ∈ chronFutureSet T S := by
    obtain ⟨s, hsS, hs⟩ := (mem_causalFutureSet T).1 hqJ
    exact mem_biUnion hsS (causalFuture_chronFuture_trans_of_isOpen T
      (isOpen_chronFuture_of_reach T.neg) hs
      (curveMax_mem_chronFuture T hXs hXT hs₀ (hηsub ⟨by linarith, le_rfl⟩) (by linarith)))
  have hminus : curveMax X σ₀ (s₀ - η) ∈ (causalFutureSet T S)ᶜ := by
    intro hP
    obtain ⟨s, hsS, hs⟩ := (mem_causalFutureSet T).1 hP
    have hqI' : q ∈ chronFuture T s := causalFuture_chronFuture_trans_of_isOpen T
      (isOpen_chronFuture_of_reach T.neg) hs
      (curveMax_mem_chronFuture T hXs hXT (hηsub ⟨le_rfl, by linarith⟩) hs₀ (by linarith))
    exact hqI (chronFutureSet_subset_interior T S (mem_biUnion hsS hqI'))
  have hcts : ∀ s ∈ Icc (s₀ - η) (s₀ + η), ContinuousAt (fun y => curveMax X y s) σ₀ := by
    intro s hs
    have hmem : (σ₀, s) ∈ {p : M × ℝ | p.2 ∈ domMax X p.1} := hηsub hs
    have h1 := (hc (σ₀, s) hmem).continuousAt (hD.mem_nhds hmem)
    exact h1.comp (f := fun y : M => (y, s)) (continuousAt_id.prodMk continuousAt_const)
  obtain ⟨u, v, hu, hv, hσu, hIv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := σ₀))
    (isCompact_Icc (a := s₀ - η) (b := s₀ + η)) hD (n := {p : M × ℝ | p.2 ∈ domMax X p.1})
    (fun p hp => by
      rw [mem_prod, mem_singleton_iff] at hp
      obtain ⟨h1, h2⟩ := hp
      show p.2 ∈ domMax X p.1
      rw [h1]
      exact hηsub h2)
  have hE2 : ∀ᶠ y in 𝓝 σ₀, curveMax X y (s₀ + η) ∈ chronFutureSet T S :=
    (hcts _ ⟨by linarith, le_rfl⟩).eventually
      ((isOpen_biUnion fun x _ => isOpen_chronFuture_of_reach T x).mem_nhds hplus)
  have hE3 : ∀ᶠ y in 𝓝 σ₀, curveMax X y (s₀ - η) ∈ (causalFutureSet T S)ᶜ :=
    (hcts _ ⟨le_rfl, by linarith⟩).eventually (hclosed.isOpen_compl.mem_nhds hminus)
  filter_upwards [hu.mem_nhds (hσu rfl), hE2, hE3] with y hyu hy2 hy3
  have hIy : Icc (s₀ - η) (s₀ + η) ⊆ domMax X y := fun s hs =>
    huv (mk_mem_prod hyu (hIv hs))
  have hcont : ContinuousOn (curveMax X y) (Icc (s₀ - η) (s₀ + η)) :=
    (isMIntegralCurveOn_curveMax hX y).continuousOn.mono hIy
  have hC : IsPreconnected (curveMax X y '' Icc (s₀ - η) (s₀ + η)) :=
    isPreconnected_Icc.image _ hcont
  have h1 : (curveMax X y '' Icc (s₀ - η) (s₀ + η) ∩ causalFutureSet T S).Nonempty :=
    ⟨curveMax X y (s₀ + η), ⟨s₀ + η, ⟨by linarith, le_rfl⟩, rfl⟩,
      (chronFutureSet_subset_interior T S hy2 |> interior_subset)⟩
  have h2 : (curveMax X y '' Icc (s₀ - η) (s₀ + η) ∩ (causalFutureSet T S)ᶜ).Nonempty :=
    ⟨curveMax X y (s₀ - η), ⟨s₀ - η, ⟨le_rfl, by linarith⟩, rfl⟩, hy3⟩
  obtain ⟨_, ⟨s, hs, rfl⟩, hsf⟩ := IsPreconnected.inter_frontier_of_isClosed hC hclosed h1 h2
  exact ⟨s, hIy hs, hsf⟩

include hXs hXT in
/-- **The projection of `∂J⁺(S)` along a timelike flow into a Cauchy surface is continuous with open
range.** This discharges the hypotheses `hproj` and `hopen` of `penrose_of_covering`. -/
theorem exists_projection (hCS : IsCauchySurface T Sig) {S : Set M}
    (hclosed : IsClosed (causalFutureSet T S)) :
    ∃ proj : frontier (causalFutureSet T S) → Sig, Continuous proj ∧ IsOpen (range proj) := by
  have hX := hX1 hXs
  set proj : frontier (causalFutureSet T S) → Sig := fun q =>
    ⟨curveMax X q.1 (hitTime X Sig q.1), (hitTime_spec T hXs hXT hCS q.1).2⟩ with hproj
  refine ⟨proj, ?_, ?_⟩
  · exact ((continuous_proj T hXs hXT hCS).comp continuous_subtype_val).subtype_mk
      fun q => (hitTime_spec T hXs hXT hCS q.1).2
  · have hW := isOpen_meets_frontier T hXs hXT hclosed
    have hrange : range proj = Subtype.val ⁻¹'
        {σ : M | ∃ s ∈ domMax X σ, curveMax X σ s ∈ frontier (causalFutureSet T S)} := by
      ext σ
      constructor
      · rintro ⟨q, rfl⟩
        obtain ⟨hd, hv⟩ := curveMax_shift hX (hitTime_spec T hXs hXT hCS q.1).1
        exact ⟨-hitTime X Sig q.1, hd, by rw [hv]; exact q.2⟩
      · rintro ⟨s, hs, hq⟩
        obtain ⟨hd, hv⟩ := curveMax_shift hX hs
        refine ⟨⟨curveMax X σ.1 s, hq⟩, ?_⟩
        apply Subtype.ext
        show curveMax X (curveMax X σ.1 s) (hitTime X Sig (curveMax X σ.1 s)) = σ.1
        rw [hitTime_eq T hXs hXT hCS hd (by rw [hv]; exact σ.2), hv]
    rw [hrange]
    exact hW.preimage continuous_subtype_val

end Lightlike.Penrose
