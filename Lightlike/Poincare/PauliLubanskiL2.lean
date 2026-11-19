import Lightlike.Poincare.GeneratorL2

/-!
# The Pauli–Lubanski combination of the `L²` generators

For a test wave function `ψ` in the chart (`ChartTest`), the momentum coordinates `p_σ ψ` are again test wave
functions (`ChartTest.mulP`), and the combination `½ ε^{μνρσ} M_{νρ} (p_σ ψ)` of the `L²` generators of the
one-parameter subgroups `γ_{νρ}` is the class of `Q ↦ plMat(Q) ψ(Q)` (`sum_genL2_mulP`): on test functions the
Pauli–Lubanski operator built from the `L²` derivatives acts as multiplication by the matrix function `plMat`, whose
Minkowski square is `−m² s(s+1)` up to the factor `i²` (`pauliLubanski_sq_generators`).

Supporting results for the Pauli–Lubanski operator on `L²`; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2 Filter Topology

namespace Lightlike.Poincare

noncomputable section

/-- The lowered momentum coordinate `p_σ` as a function of the chart. -/
def pChart (m : ℝ) (σ : Fin 4) (p : Fin 3 → ℝ) : ℝ := pLow (Real.sqrt (m ^ 2 + sqV p)) p σ

lemma contDiff_sqV : ContDiff ℝ 1 sqV := by
  unfold sqV
  have h : ∀ i : Fin 3, ContDiff ℝ 1 fun p : Fin 3 → ℝ => p i := fun i =>
    contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i
  exact (((h 0).pow 2).add ((h 1).pow 2)).add ((h 2).pow 2)

lemma contDiff_pChart {m : ℝ} (hm : 0 < m) (σ : Fin 4) : ContDiff ℝ 1 (pChart m σ) := by
  have hs : ContDiff ℝ 1 fun p : Fin 3 → ℝ => Real.sqrt (m ^ 2 + sqV p) :=
    (contDiff_const.add contDiff_sqV).sqrt fun p => by have := sqV_nonneg p; positivity
  unfold pChart
  fin_cases σ
  · simpa [pLow] using hs
  · simpa [pLow] using (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) (0 : Fin 3)).neg
  · simpa [pLow] using (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) (1 : Fin 3)).neg
  · simpa [pLow] using (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) (2 : Fin 3)).neg

lemma pChart_coordV {m : ℝ} (σ : Fin 4) (Q : MassShell m) : pChart m σ (coordV Q.1) = pCoord σ Q := by
  rw [pChart, pCoord, coord0_eq_sqrt]

namespace ChartTest

variable {m : ℝ} {n : ℕ} (F : ChartTest n)

/-- The test wave function `p_σ ψ`. -/
def mulP (hm : 0 < m) (σ : Fin 4) : ChartTest n where
  φ := fun p => ((pChart m σ p : ℝ) : ℂ) • F.φ p
  contDiff := by
    have h1 : ContDiff ℝ 1 fun p => ((pChart m σ p : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_pChart hm σ)
    exact h1.smul F.contDiff
  hasCompactSupport := HasCompactSupport.smul_left (f := fun p => ((pChart m σ p : ℝ) : ℂ)) F.hasCompactSupport

lemma mulP_ψ (hm : 0 < m) (σ : Fin 4) : (F.mulP hm σ).ψ m = fun Q => ((pCoord σ Q : ℝ) : ℂ) • F.ψ m Q := by
  funext Q
  simp only [ψ, mulP, pChart_coordV]

/-- **The generator of `p_σ ψ`**: `M (p_σ ψ) = (d p_σ)(M p) ψ + p_σ M ψ`. -/
lemma genFun_mulP (hm : 0 < m) (σ : Fin 4) (ν ρ : Fin 4) (Q : MassShell m) :
    (F.mulP hm σ).genFun hm (lorGen ν ρ) Q =
      ((pLow (coord0 (moveVel Q.1 (lorGen ν ρ))) (coordV (moveVel Q.1 (lorGen ν ρ))) σ : ℝ) : ℂ) • F.ψ m Q +
        ((pCoord σ Q : ℝ) : ℂ) • F.genFun hm (lorGen ν ρ) Q := by
  have h1 := hasDerivAt_inducedAct_curve hm n (isCurveAt_lorCurve ν ρ) Q ((F.mulP hm σ).chartSmoothAt Q)
  have h2 := hasDerivAt_inducedAct_curve_mul hm n (isCurveAt_lorCurve ν ρ) Q (F.chartSmoothAt Q) σ
  have e : (fun t => inducedAct hm (spinRep n) (lorCurve ν ρ t) ((F.mulP hm σ).ψ m) Q) =
      fun t => inducedAct hm (spinRep n) (lorCurve ν ρ t) (fun Q => ((pCoord σ Q : ℝ) : ℂ) • F.ψ m Q) Q := by
    rw [F.mulP_ψ hm σ]
  rw [e] at h1
  exact h1.unique h2

/-- **The Pauli–Lubanski combination of the generators on test functions**, pointwise:
`½ ε^{μνρσ} M_{νρ} (p_σ ψ)(Q) = plMat(Q) ψ(Q)`. -/
lemma sum_genFun_mulP (hm : 0 < m) (μ : Fin 4) (Q : MassShell m) :
    ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ : ℝ) : ℂ) • (F.mulP hm σ).genFun hm (lorGen ν ρ) Q =
      plMat hm n Q μ *ᵥ F.ψ m Q := by
  have hMP := hasDerivAt_pauliLubanski_MP hm n lorCurve isCurveAt_lorCurve Q (F.chartSmoothAt Q) μ
  have hsum : HasDerivAt (fun t => ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ : ℝ) : ℂ) •
      inducedAct hm (spinRep n) (lorCurve ν ρ t) (fun Q => ((pCoord σ Q : ℝ) : ℂ) • F.ψ m Q) Q)
      (∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ : ℝ) : ℂ) • (F.mulP hm σ).genFun hm (lorGen ν ρ) Q) 0 := by
    refine HasDerivAt.fun_sum fun ν _ => HasDerivAt.fun_sum fun ρ _ => HasDerivAt.fun_sum fun σ _ => ?_
    have h := hasDerivAt_inducedAct_curve hm n (isCurveAt_lorCurve ν ρ) Q ((F.mulP hm σ).chartSmoothAt Q)
    have e : (fun t => inducedAct hm (spinRep n) (lorCurve ν ρ t) ((F.mulP hm σ).ψ m) Q) =
        fun t => inducedAct hm (spinRep n) (lorCurve ν ρ t) (fun Q => ((pCoord σ Q : ℝ) : ℂ) • F.ψ m Q) Q := by
      rw [F.mulP_ψ hm σ]
    rw [e] at h
    exact h.const_smul (((1 / 2 * levi μ ν ρ σ : ℝ) : ℂ))
  exact hsum.unique hMP

end ChartTest

end

end Lightlike.Poincare
