import Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.Strip

/-!
# The KMS boundary relation for the Laplace transform

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

In the momentum model, `Δ^{it} = e^{-2π i t k}` acts by multiplication on `L²(ℝ, dk)` and
`J g(k) = conj g(-k)`. A vector `ξ` of the standard subspace satisfies the relation
`conj ξ(-k) = e^{-π k} ξ(k)`. For two such vectors, `φ = conj ξ · η` satisfies
`φ(k) e^{-2π k} = conj φ(-k)`; this file shows that such a `φ` has Laplace transform with
`laplace φ (w - 2π) = conj (laplace φ w)` on the imaginary axis, i.e. the two boundary values of the
strip function `F(z) = laplace φ (-2π i z)` at `Im z = 0` and `Im z = -1` are complex conjugate.
This is the (model-level) KMS boundary relation at inverse temperature `2π`.

## Main results

* `laplace_sub_two_pi` — the boundary relation.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

namespace Lightlike.Rows.G1_054

variable {φ : ℝ → ℂ}

/-- Reflection and conjugation of the Laplace transform:
`∫ conj φ(-k) e^{w k} dk = conj (laplace φ (-conj w))`. -/
lemma integral_conj_neg (φ : ℝ → ℂ) (w : ℂ) :
    ∫ k : ℝ, (starRingEnd ℂ) (φ (-k)) * cexp (w * k)
      = (starRingEnd ℂ) (laplace φ (-(starRingEnd ℂ) w)) := by
  have h1 : ∫ k : ℝ, (starRingEnd ℂ) (φ (-k)) * cexp (w * k)
      = ∫ k : ℝ, (starRingEnd ℂ) (φ k) * cexp (w * ((-k : ℝ) : ℂ)) := by
    have := integral_neg_eq_self
      (fun k : ℝ => (starRingEnd ℂ) (φ k) * cexp (w * ((-k : ℝ) : ℂ))) volume
    simpa using this
  rw [h1, laplace, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.ofReal_neg]
  congr 2
  simp

/-- **KMS boundary relation (model level).** If `φ(k) e^{-2π k} = conj φ(-k)` almost everywhere,
then `laplace φ (-2π i t - 2π) = conj (laplace φ (-2π i t))` for every real `t`. -/
theorem laplace_sub_two_pi
    (h : ∀ᵐ k : ℝ, φ k * (Real.exp (-(2 * π) * k) : ℂ) = (starRingEnd ℂ) (φ (-k)))
    (t : ℝ) :
    laplace φ (-(2 * π * Complex.I * t) - 2 * π)
      = (starRingEnd ℂ) (laplace φ (-(2 * π * Complex.I * t))) := by
  set w : ℂ := -(2 * π * Complex.I * t) with hw
  have hexp : ∀ k : ℝ, cexp ((w - 2 * π) * k) = cexp (w * k) * (Real.exp (-(2 * π) * k) : ℂ) := by
    intro k
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast; ring
  have h1 : laplace φ (w - 2 * π)
      = ∫ k : ℝ, (starRingEnd ℂ) (φ (-k)) * cexp (w * k) := by
    unfold laplace
    refine integral_congr_ae ?_
    filter_upwards [h] with k hk
    rw [hexp, ← hk]; ring
  rw [h1, integral_conj_neg]
  congr 2
  simp only [hw, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

end Lightlike.Rows.G1_054
