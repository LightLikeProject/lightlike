import Lightlike.Spacetime.PenroseSingularity.FlowFamily
import Lightlike.Spacetime.PenroseSingularity.JacobiLocal

/-!
# Jacobi fields of a chart family (G1-012, step D3b wiring)

A direction `e` in the parameter space of a chart family `H (t, σ)` gives the Jacobi field
`J = ∂_e H (·, σ₀)` along `H (·, σ₀)`, on a small interval around `t₀`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Jacobi fields of a chart family.** -/
theorem isJacobiOn_of_chartFamily (hg : Lightlike.IsCoordMetric g U)
    {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))} (hCF : ChartFamily g U H W)
    {t₀ : ℝ} {σ₀ : Fin m → ℝ} (h : (t₀, σ₀) ∈ W) (e : Fin m → ℝ) :
    ∃ δ > 0, (∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), ((t, σ₀) : ℝ × (Fin m → ℝ)) ∈ W) ∧
      ∃ P, Lightlike.Geodesic.IsJacobiOn g (fun t => H (t, σ₀)) (fun t => fderiv ℝ H (t, σ₀) (1, 0))
        (fun t => fderiv ℝ H (t, σ₀) (0, e)) P (Ioo (t₀ - δ) (t₀ + δ)) := by
  classical
  set c : ℝ × ℝ → ℝ × (Fin m → ℝ) := fun q => (q.1, σ₀ + q.2 • e) with hc
  have hcd : ∀ q : ℝ × ℝ, HasFDerivAt c
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight e)) q := fun q =>
    (hasFDerivAt_fst).prodMk (((hasFDerivAt_snd).smul_const e).const_add σ₀)
  have hcc : Continuous c := by fun_prop
  have hcs : ContDiff ℝ 3 c := by fun_prop
  set He : ℝ × ℝ → Fin n → ℝ := fun q => H (c q) with hHe
  set We : Set (ℝ × ℝ) := c ⁻¹' W with hWe
  have hWeo : IsOpen We := hCF.isOpen.preimage hcc
  have ht₀e : ((t₀, (0 : ℝ)) : ℝ × ℝ) ∈ We := by simpa [hWe, hc] using h
  have hHeC : ContDiffOn ℝ 3 He We := hCF.smooth.comp hcs.contDiffOn (fun q hq => hq)
  have hdiffH : ∀ q ∈ We, DifferentiableAt ℝ H (c q) := fun q hq =>
    (hCF.smooth.contDiffAt (hCF.isOpen.mem_nhds hq)).differentiableAt (by simp)
  have hfd : ∀ q ∈ We, ∀ v : ℝ × ℝ, fderiv ℝ He q v =
      fderiv ℝ H (c q) ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight e) v) := by
    intro q hq v
    have := (hdiffH q hq).hasFDerivAt.comp q (hcd q)
    exact congrArg (fun L => L v) this.fderiv
  have hgeoe : ∀ p ∈ We, Lightlike.Geodesic.IsGeodesicOn g (fun t => He (t, p.2))
      (fun t => fderiv ℝ He (t, p.2) (1, 0)) {t | ((t, p.2) : ℝ × ℝ) ∈ We} := by
    intro p hp
    have hg0 := hCF.geo (c p) hp
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := hg0.pos t ht
      have hq : (t, p.2) ∈ We := ht
      rw [hfd _ hq]
      simpa using this
    · have := hg0.vel t ht
      have hq : (t, p.2) ∈ We := ht
      have hev : (fun t' : ℝ => fderiv ℝ H (t', σ₀ + p.2 • e) (1, 0)) =ᶠ[nhds t]
          (fun t' : ℝ => fderiv ℝ He (t', p.2) (1, 0)) := by
        have hcont : Continuous fun t' : ℝ => ((t', p.2) : ℝ × ℝ) := by fun_prop
        filter_upwards [hcont.continuousAt.eventually (hWeo.mem_nhds hq)] with t' ht'
        rw [hfd _ ht']; simp [hc]
      rw [hfd _ hq]
      simpa [hc] using this.congr_of_eventuallyEq hev.symm
  obtain ⟨δ, hδ, hW', P, hP⟩ := Lightlike.Geodesic.exists_isJacobiOn_local hg hWeo hHeC ht₀e
    (fun q hq => hCF.mem _ hq) hgeoe
  refine ⟨δ, hδ, fun t ht => by simpa [hWe, hc] using hW' t ht, P, ?_⟩
  refine Lightlike.Geodesic.IsJacobiOn.congr_eventually hP (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · exact Filter.Eventually.of_forall fun t' => by simp [hHe, hc]
  · have hq : ((t, (0 : ℝ)) : ℝ × ℝ) ∈ We := hW' t ht
    have hcont : Continuous fun t' : ℝ => ((t', (0 : ℝ)) : ℝ × ℝ) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually (hWeo.mem_nhds hq)] with t' ht'
    rw [hfd _ ht']; simp [hc]
  · have hq : ((t, (0 : ℝ)) : ℝ × ℝ) ∈ We := hW' t ht
    have hcont : Continuous fun t' : ℝ => ((t', (0 : ℝ)) : ℝ × ℝ) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually (hWeo.mem_nhds hq)] with t' ht'
    rw [hfd _ ht']; simp [hc]

end Lightlike.Penrose
