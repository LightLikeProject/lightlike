import Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.KMS

/-!
# Model-level KMS statement at inverse temperature `2π`

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

Momentum model: `ℋ = L²(ℝ, dk)`, `Δ = e^{-2π k}` (multiplication), `J g(k) = conj g(-k)`.
Then `ξ ∈ H(Δ, J)`, i.e. `J Δ^{1/2} ξ = ξ`, reads `conj ξ(-k) = e^{-π k} ξ(k)` almost everywhere.
For two such vectors `ξ, η` the function `φ = conj ξ · η` (the matrix element
`⟪ξ, Δ^{-i z} η⟫` is `laplace φ (-2π i z)` up to the choice of convention) is integrable together
with `φ e^{-2π k}`, and satisfies `φ(k) e^{-2π k} = conj φ(-k)`.

This is a model statement: the identification of this model with the wedge subspace of a
Wightman theory is *not* proved here.

## Main results

* `bw_relation_phi` — the relation for `φ = conj ξ · η`.
* `kms_model` — continuity on the closed strip, holomorphy inside, boundary relation.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

namespace Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

variable {ξ η : ℝ → ℂ}

/-- The matrix-element density `φ = conj ξ · η`. -/
noncomputable def matrixDensity (ξ η : ℝ → ℂ) : ℝ → ℂ := fun k => (starRingEnd ℂ) (ξ k) * η k

/-- The Bisognano–Wichmann relation `conj ξ(-k) = e^{-π k} ξ(k)` (a.e.) in the momentum model. -/
def BWRel (ξ : ℝ → ℂ) : Prop :=
  ∀ᵐ k : ℝ, (starRingEnd ℂ) (ξ (-k)) = (Real.exp (-π * k) : ℂ) * ξ k

/-- Reflection and conjugation preserve `L²`. -/
lemma memLp_conj_neg (hξ : MemLp ξ 2) : MemLp (fun k => (starRingEnd ℂ) (ξ (-k))) 2 := by
  have h := (hξ.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))).star
  exact h

/-- Integrability of `φ`. -/
lemma integrable_matrixDensity (hξ : MemLp ξ 2) (hη : MemLp η 2) :
    Integrable (matrixDensity ξ η) := by
  have := (hξ.star).integrable_mul hη
  exact this

/-- **The relation `φ(k) e^{-2π k} = conj φ(-k)` for `φ = conj ξ · η`.** -/
theorem bw_relation_phi (hξ : BWRel ξ) (hη : BWRel η) :
    ∀ᵐ k : ℝ, matrixDensity ξ η k * (Real.exp (-(2 * π) * k) : ℂ)
      = (starRingEnd ℂ) (matrixDensity ξ η (-k)) := by
  filter_upwards [hξ, hη] with k h1 h2
  have h1' : ξ (-k) = (Real.exp (-π * k) : ℂ) * (starRingEnd ℂ) (ξ k) := by
    have := congrArg (starRingEnd ℂ) h1
    rwa [map_mul, Complex.conj_conj, Complex.conj_ofReal] at this
  unfold matrixDensity
  rw [map_mul, Complex.conj_conj, h1', h2]
  have : (Real.exp (-(2 * π) * k) : ℂ) = (Real.exp (-π * k) : ℂ) * (Real.exp (-π * k) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  rw [this]; ring

/-- Integrability of `φ e^{-2π k}`. -/
lemma integrable_matrixDensity_exp (hξ : MemLp ξ 2) (hη : MemLp η 2) (rξ : BWRel ξ)
    (rη : BWRel η) :
    Integrable (fun k : ℝ => matrixDensity ξ η k * (Real.exp (-(2 * π) * k) : ℂ)) := by
  have h1 : Integrable (fun k : ℝ => (starRingEnd ℂ) (matrixDensity ξ η (-k))) := by
    have := ((memLp_conj_neg hξ).star).integrable_mul (memLp_conj_neg hη)
    refine this.congr (Filter.Eventually.of_forall fun k => ?_)
    simp [matrixDensity]
  exact h1.congr ((bw_relation_phi rξ rη).mono fun k hk => hk.symm)

/-- **KMS statement at `β = 2π` in the momentum model.** For `ξ, η ∈ L²(ℝ)` satisfying the
Bisognano–Wichmann relation, `F(w) = ∫ conj ξ(k) η(k) e^{w k} dk` is continuous on
`-2π ≤ Re w ≤ 0`, holomorphic on `-2π < Re w < 0`, and its two boundary lines are related by
`F(-2π i t - 2π) = conj F(-2π i t)`. -/
theorem kms_model (hξ : MemLp ξ 2) (hη : MemLp η 2) (rξ : BWRel ξ) (rη : BWRel η) :
    ContinuousOn (laplace (matrixDensity ξ η)) {w : ℂ | -(2 * π) ≤ w.re ∧ w.re ≤ 0}
    ∧ (∀ w : ℂ, -(2 * π) < w.re → w.re < 0 →
        DifferentiableAt ℂ (laplace (matrixDensity ξ η)) w)
    ∧ ∀ t : ℝ, laplace (matrixDensity ξ η) (-(2 * π * Complex.I * t) - 2 * π)
        = (starRingEnd ℂ) (laplace (matrixDensity ξ η) (-(2 * π * Complex.I * t))) := by
  have h0 := integrable_matrixDensity hξ hη
  have h1 := integrable_matrixDensity_exp hξ hη rξ rη
  exact ⟨laplace_continuousOn h0 h1, fun w a b => laplace_differentiableAt h0 h1 a b,
    laplace_sub_two_pi (bw_relation_phi rξ rη)⟩

end Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.BWRel := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.BWRel
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.bw_relation_phi := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.bw_relation_phi
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.integrable_matrixDensity := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.integrable_matrixDensity
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.integrable_matrixDensity_exp := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.integrable_matrixDensity_exp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.kms_model := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.kms_model
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.matrixDensity := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.matrixDensity
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.memLp_conj_neg := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.memLp_conj_neg
