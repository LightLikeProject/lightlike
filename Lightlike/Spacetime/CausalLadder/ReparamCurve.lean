import Lightlike.Spacetime.CausalLadder.ConeCurve
import Lightlike.Spacetime.Causal.CurveOps

/-!
# Monotonicity estimates for the reparametrised chart image of a causal curve

If `f` is a reparametrisation of the chart image `c = extChartAt I p ∘ γ` of a causal curve `γ`
through the monotone functional `ℓ` (that is, `f (ℓ (c t)) = c t`), the one-sided estimates of
`sub_le_sub_along_curve` hold for `f` over every interval `[σ₁, σ₂]` of `ℓ`-values whose preimage
lies in the region where the pointwise estimate is valid.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Estimate in the reparametrised variable.** Let `γ` be a future causal curve on `[a, b]`,
`f` with `f (ℓ (c t)) = c t` on `[a, b]` (`c = extChartAt I p ∘ γ`) and `ℓ ∘ c` nondecreasing. Let
`F`, `G` be continuous linear functionals with `F w ≤ G w` for the coordinates of every future
causal vector at every point of `W' ⊆ (tTriv p).baseSet`. If `σ₁ ≤ σ₂` are values of `ℓ ∘ c`
and `γ t ∈ W'` whenever `ℓ (c t) ∈ [σ₁, σ₂]`, then
`F (f σ₂) - F (f σ₁) ≤ G (f σ₂) - G (f σ₁)`. -/
theorem sub_le_sub_reparam (p : M) {W : Set M} (hWb : W ⊆ (tTriv I M p).baseSet)
    (F G : E →L[ℝ] ℝ)
    (hFG : ∀ q ∈ W, ∀ v : TangentSpace I q, T.IsFutureCausal v →
      F (tTriv I M p ⟨q, v⟩).2 ≤ G (tTriv I M p ⟨q, v⟩).2)
    {ℓ : E →L[ℝ] ℝ} {γ : ℝ → M} {a b : ℝ} (hγ : IsFutureCausalCurve T γ (Icc a b))
    (hmono : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      ℓ (extChartAt I p (γ s)) ≤ ℓ (extChartAt I p (γ t)))
    {f : ℝ → E} (hf : ∀ t ∈ Icc a b, f (ℓ (extChartAt I p (γ t))) = extChartAt I p (γ t))
    {σ₁ σ₂ : ℝ} (h12 : σ₁ ≤ σ₂) (h1 : ∃ t ∈ Icc a b, ℓ (extChartAt I p (γ t)) = σ₁)
    (h2 : ∃ t ∈ Icc a b, ℓ (extChartAt I p (γ t)) = σ₂)
    (hW : ∀ t ∈ Icc a b, σ₁ ≤ ℓ (extChartAt I p (γ t)) → ℓ (extChartAt I p (γ t)) ≤ σ₂ →
      γ t ∈ W) :
    F (f σ₂) - F (f σ₁) ≤ G (f σ₂) - G (f σ₁) := by
  obtain ⟨t₁, ht₁, e₁⟩ := h1
  obtain ⟨t₂, ht₂, e₂⟩ := h2
  have f1 : f σ₁ = extChartAt I p (γ t₁) := by rw [← e₁]; exact hf t₁ ht₁
  have f2 : f σ₂ = extChartAt I p (γ t₂) := by rw [← e₂]; exact hf t₂ ht₂
  rw [f1, f2]
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · -- a genuine subinterval
    have hsub : IsFutureCausalCurve T γ (Icc t₁ t₂) :=
      IsCurveWith.mono hγ ht₁.1 ht₂.2 hlt
    refine sub_le_sub_along_curve T p hWb F G hFG hsub ?_ ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt.le
    intro t ht
    have htab : t ∈ Icc a b := ⟨ht₁.1.trans ht.1, ht.2.trans ht₂.2⟩
    refine hW t htab ?_ ?_
    · rw [← e₁]; exact hmono t₁ ht₁ t htab ht.1
    · rw [← e₂]; exact hmono t htab t₂ ht₂ ht.2
  · subst heq; simp
  · -- `t₂ < t₁` forces `σ₂ ≤ σ₁`, so the two points have the same `ℓ`-value and coincide
    have hle : ℓ (extChartAt I p (γ t₂)) ≤ ℓ (extChartAt I p (γ t₁)) := hmono t₂ ht₂ t₁ ht₁ hgt.le
    rw [e₁, e₂] at hle
    have hσ : σ₁ = σ₂ := le_antisymm h12 hle
    have : f σ₁ = f σ₂ := by rw [hσ]
    rw [f1, f2] at this
    rw [this]; simp

end Lightlike.Causal
