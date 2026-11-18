import Lightlike.Spacetime.Causal.CurveOps
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Curves on an open interval from curves on its compact subintervals

A curve is locally Lipschitz with velocity in `P` almost everywhere on an open interval `s` as soon
as it is so on every compact subinterval `[a, b] ⊆ s`: the conditions are local, and `s` is a
countable union of compact subintervals. With the margin of a timelike curve (which is already
stated on compact subintervals) this gives `IsFutureTimelikeCurve` on an open interval from the
same on its compact subintervals.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {P : ∀ x : M, TangentSpace I x → Prop}

/-- **A curve on an open interval, from its compact subintervals**: if the curve has its velocity
in `P` on every `[a, b] ⊆ s`, `a < b`, with `s` an open interval, it has it on `s`. -/
theorem IsCurveWith.of_Icc {γ : ℝ → M} {s : Set ℝ} (hso : IsOpen s) (hsc : s.OrdConnected)
    (h : ∀ a b : ℝ, a < b → Icc a b ⊆ s → IsCurveWith (I := I) P γ (Icc a b)) :
    IsCurveWith (I := I) P γ s := by
  have hloc : ∀ t ∈ s, ∃ a b : ℝ, a < t ∧ t < b ∧ Icc a b ⊆ s := by
    intro t ht
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hso t ht
    refine ⟨t - ε / 2, t + ε / 2, by linarith, by linarith, fun y hy => hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  refine ⟨hsc, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, b, hat, htb, hsub⟩ := hloc t ht
    obtain ⟨K, U, hU, hm, hl⟩ := (h a b (hat.trans htb) hsub).lipschitz t ⟨hat.le, htb.le⟩
    refine ⟨K, U ∩ Icc a b, inter_mem ?_ ?_, fun y hy => hm hy.1, hl.mono inter_subset_left⟩
    · have : Icc a b ∈ 𝓝 t := Icc_mem_nhds hat htb
      exact (nhdsWithin_le_of_mem (mem_nhdsWithin_of_mem_nhds this)) hU
    · exact mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds hat htb)
  · -- the rational compact subintervals cover `s`
    set Q : Set (ℚ × ℚ) := {pq | (pq.1 : ℝ) < pq.2 ∧ Icc (pq.1 : ℝ) pq.2 ⊆ s} with hQ
    have hcov : s ⊆ ⋃ pq ∈ Q, Icc (pq.1 : ℝ) pq.2 := by
      intro t ht
      obtain ⟨a, b, hat, htb, hsub⟩ := hloc t ht
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hat
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn htb
      refine mem_biUnion (x := (p, q)) ⟨by simp only; linarith, fun y hy =>
        hsub ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩ ⟨hp2.le, hq1.le⟩
    have hae : ∀ pq ∈ Q, ∀ᵐ t ∂(volume.restrict (Icc (pq.1 : ℝ) pq.2)),
        MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t ∧ P (γ t) (velocity I γ s t) := by
      intro pq hpq
      have hc := h _ _ hpq.1 hpq.2
      have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({(pq.1 : ℝ), (pq.2 : ℝ)} : Set ℝ) :=
        (Set.toFinite ({(pq.1 : ℝ), (pq.2 : ℝ)} : Set ℝ)).countable.ae_notMem _
      filter_upwards [hc.ae_velocity, ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae hne] with t ⟨hd, hP⟩ ht hn
      have hn' : t ≠ pq.1 ∧ t ≠ pq.2 := by simpa [not_or] using hn
      have hmem : Icc (pq.1 : ℝ) pq.2 ∈ 𝓝 t :=
        Icc_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm hn'.1)) (lt_of_le_of_ne ht.2 hn'.2)
      have hsmem : s ∈ 𝓝 t := mem_of_superset hmem hpq.2
      have hda : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := hd.mdifferentiableAt hmem
      refine ⟨hda.mdifferentiableWithinAt, ?_⟩
      have : velocity I γ s t = velocity I γ (Icc (pq.1 : ℝ) pq.2) t := by
        unfold velocity
        rw [mfderivWithin_of_mem_nhds hsmem, mfderivWithin_of_mem_nhds hmem]
      rw [this]
      exact hP
    have hQc : Q.Countable := Set.to_countable Q
    have := ((ae_restrict_biUnion_iff (μ := volume) (fun pq : ℚ × ℚ => (Icc (pq.1 : ℝ) pq.2)) hQc)
      (fun t => MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t ∧ P (γ t) (velocity I γ s t))).2 hae
    exact ae_restrict_of_ae_restrict_of_subset hcov this

variable [IsManifold I ∞ M] {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A timelike curve on an open interval, from its compact subintervals.** -/
theorem isFutureTimelikeCurve_of_Icc {γ : ℝ → M} {s : Set ℝ} (hso : IsOpen s)
    (hsc : s.OrdConnected)
    (h : ∀ a b : ℝ, a < b → Icc a b ⊆ s → IsFutureTimelikeCurve T γ (Icc a b)) :
    IsFutureTimelikeCurve T γ s :=
  ⟨IsCurveWith.of_Icc hso hsc fun a b hab hsub => (h a b hab hsub).1,
    fun a b hab hsub => (h a b hab hsub).2 a b hab subset_rfl⟩

end Causal

end Lightlike
