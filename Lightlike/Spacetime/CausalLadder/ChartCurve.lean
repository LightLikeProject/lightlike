import Lightlike.Spacetime.CausalLadder.ChartVelocity
import Lightlike.Spacetime.CausalLadder.ChartLipschitz
import Lightlike.Spacetime.CausalLadder.ConeAlgebra

/-!
# A differentiable chart curve gives a differentiable curve in the manifold

If `u : ℝ → E` has derivative `D` within `s` at `t` and takes values in the target of the chart at
`p`, then `γ = (extChartAt I p).symm ∘ u` is differentiable within `s` at `t` as a map into `M`,
and the coordinates of its velocity in the trivialization of the tangent bundle at `p` are `D`.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The curve `(extChartAt I p).symm ∘ u` is differentiable within `s` at `t` if `u` is, and its
velocity has coordinates `D` in the trivialization at `p`. -/
theorem mdifferentiableWithinAt_chart_symm {u : ℝ → E} {D : E} {s : Set ℝ} {t : ℝ} (p : M)
    (hs : UniqueDiffWithinAt ℝ s t) (ht : t ∈ s) (hu : HasDerivWithinAt u D s t)
    (htarget : ∀ t' ∈ s, u t' ∈ (extChartAt I p).target) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I ((extChartAt I p).symm ∘ u) s t ∧
      (tTriv I M p ⟨((extChartAt I p).symm ∘ u) t, velocity I ((extChartAt I p).symm ∘ u) s t⟩).2
        = D := by
  have hmd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I ((extChartAt I p).symm ∘ u) s t :=
    ((mdifferentiableOn_extChartAt_symm (I := I) (x := p)) (u t) (htarget t ht)).comp t
      hu.differentiableWithinAt.mdifferentiableWithinAt (fun t' ht' => htarget t' ht')
  refine ⟨hmd, ?_⟩
  have hsrc : ((extChartAt I p).symm ∘ u) t ∈ (extChartAt I p).source :=
    (extChartAt I p).map_target (htarget t ht)
  have h1 := hasDerivWithinAt_chart_comp (I := I) p hmd hsrc
  have heq : EqOn u (extChartAt I p ∘ ((extChartAt I p).symm ∘ u)) s := fun t' ht' =>
    ((extChartAt I p).right_inv (htarget t' ht')).symm
  have h1' := h1.congr heq (heq ht)
  exact (hs.eq_deriv s h1' hu)

variable {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A vector with nonpositive product against every transported future timelike vector is future
causal.** Let `D ≠ 0` be coordinates, in the trivialization at `p`, of a vector at `x₀`. If
`g(V', d) ≤ 0` for every `V'` at `x₀` that is future timelike, then `d = (tTriv p).symm x₀ D` is
future-directed causal. -/
theorem isFutureCausal_of_forall_nonpos (p x₀ : M) (hx₀ : x₀ ∈ (tTriv I M p).baseSet) {D : E}
    (hD0 : D ≠ 0)
    (hD : ∀ u : TangentSpace I x₀, g.g x₀ u u < 0 → g.g x₀ u (T.X x₀) < 0 →
      g.g x₀ u ((tTriv I M p).symm x₀ D) ≤ 0) :
    T.IsFutureCausal ((tTriv I M p).symm x₀ D) := by
  set d : TangentSpace I x₀ := (tTriv I M p).symm x₀ D with hd
  obtain ⟨h1, h2⟩ := (g.lorentzian x₀).futureCausal_of_forall_nonpos (X := T.X x₀)
    (T.timelike x₀) hD
  have hdne : d ≠ 0 := by
    intro h0
    apply hD0
    have := (tTriv I M p).apply_mk_symm hx₀ D
    rw [← hd, h0] at this
    have h3 : (tTriv I M p ⟨x₀, (0 : TangentSpace I x₀)⟩).2 = 0 :=
      (map_zero ((tTriv I M p).linearEquivAt ℝ x₀ hx₀))
    have h4 := congrArg Prod.snd this
    simp only at h4
    rw [← h4]; exact h3
  refine ⟨hdne, h1, lt_of_le_of_ne h2 ?_⟩
  intro h0
  exact hdne ((g.lorentzian x₀).eq_zero_of_orthogonal_timelike (T.timelike x₀) h0 h1)

end Lightlike.Causal
