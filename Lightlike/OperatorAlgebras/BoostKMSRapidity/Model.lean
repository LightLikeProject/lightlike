import Lightlike.OperatorAlgebras.BoostKMSRapidity.LaplaceStrip
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Bisognano-Wichmann standard subspace in the rapidity picture (G1-056)

Hilbert space `L²(ℝ, dx)`; the modular operator is `Δ = e^{-2πx}` (multiplication), so the modular
group `Δ^{it}` is multiplication by `e^{-2πitx}`, i.e. the boost group (translation in rapidity,
dilation in the Mellin picture) run at parameter `2π`; the modular conjugation is `Jψ(x) = conj ψ(-x)`.
The standard subspace is `H = ker(1 - JΔ^{1/2})`, i.e.
`ψ ∈ H ⟺ ψ, e^{-πx}ψ ∈ L²  and  ψ(x) = e^{πx} conj ψ(-x)` (`InH`).

For `ξ, η ∈ H` we show that `g = conj ξ · η` satisfies the integrability hypotheses of
`LaplaceStrip` (`integrable_corr`, `integrable_corr'`) and the **KMS boundary identity**
`laplace g (t - i) = conj (laplace g t)` (`laplace_corr_boundary`).

Supporting lemmas; no catalogue entry.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace Lightlike.BisognanoWichmann

/-- Membership in the standard subspace `H = ker (1 - J Δ^{1/2})` of the model. -/
def InH (ψ : ℝ → ℂ) : Prop :=
  MemLp ψ 2 volume ∧ MemLp (fun x => ((Real.exp (-(π * x)) : ℝ) : ℂ) * ψ x) 2 volume ∧
    ∀ᵐ x : ℝ, ψ x = ((Real.exp (π * x) : ℝ) : ℂ) * conj (ψ (-x))

/-- The correlation density `conj ξ · η`; `⟨ξ, Δ^{it} η⟩ = laplace (corr ξ η) t`. -/
def corr (ξ η : ℝ → ℂ) (x : ℝ) : ℂ := conj (ξ x) * η x

lemma integrable_corr {ξ η : ℝ → ℂ} (hξ : InH ξ) (hη : InH η) : Integrable (corr ξ η) := by
  have := (hξ.1.star).integrable_mul hη.1
  exact this

lemma integrable_corr' {ξ η : ℝ → ℂ} (hξ : InH ξ) (hη : InH η) :
    Integrable fun x => Real.exp (-(2 * π * x)) • corr ξ η x := by
  have := (hξ.2.1.star).integrable_mul hη.2.1
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, Pi.star_apply, corr, Complex.star_def, Complex.real_smul, map_mul,
    Complex.conj_ofReal]
  have : ((Real.exp (-(2 * π * x)) : ℝ) : ℂ) =
      ((Real.exp (-(π * x)) : ℝ) : ℂ) * ((Real.exp (-(π * x)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
  rw [this]; ring

/-- Pointwise form of the KMS boundary identity. -/
lemma corr_boundary_pt {ξ η : ℝ → ℂ} (t x : ℝ)
    (h1 : ξ x = ((Real.exp (π * x) : ℝ) : ℂ) * conj (ξ (-x)))
    (h2 : η x = ((Real.exp (π * x) : ℝ) : ℂ) * conj (η (-x))) :
    corr ξ η x * kern x (t - I) =
      (fun y : ℝ => ξ y * conj (η y) * cexp (2 * π * I * y * t)) (-x) := by
  have e1 : kern x (t - I) = ((Real.exp (-(2 * π * x)) : ℝ) : ℂ) * cexp (-(2 * π * I * x) * t) := by
    rw [kern, Complex.ofReal_exp, ← Complex.exp_add]; congr 1
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have e2 : ((Real.exp (π * x) : ℝ) : ℂ) * ((Real.exp (π * x) : ℝ) : ℂ) *
      ((Real.exp (-(2 * π * x)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    have : π * x + π * x + -(2 * π * x) = 0 := by ring
    rw [this]; simp
  rw [corr, e1]
  simp only [h1, h2, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have e3 : cexp (2 * π * I * ((-x : ℝ) : ℂ) * t) = cexp (-(2 * π * I * x) * t) := by
    congr 1; push_cast; ring
  rw [e3]
  linear_combination (ξ (-x) * conj (η (-x)) * cexp (-(2 * π * I * x) * t)) * e2

/-- **KMS boundary identity**: for `ξ, η ∈ H`, `⟨ξ, Δ^{i(t - i)} η⟩ = ⟨Δ^{it} η, ξ⟩ = conj ⟨ξ, Δ^{it} η⟩`. -/
theorem laplace_corr_boundary {ξ η : ℝ → ℂ} (hξ : InH ξ) (hη : InH η) (t : ℝ) :
    laplace (corr ξ η) (t - I) = conj (laplace (corr ξ η) t) := by
  set h : ℝ → ℂ := fun y => ξ y * conj (η y) * cexp (2 * π * I * y * t) with hh
  have hae : ∀ᵐ x : ℝ, corr ξ η x * kern x (t - I) = h (-x) := by
    filter_upwards [hξ.2.2, hη.2.2] with x h1 h2 using corr_boundary_pt t x h1 h2
  have L : laplace (corr ξ η) (t - I) = ∫ x, h (-x) := integral_congr_ae hae
  have R : conj (laplace (corr ξ η) t) = ∫ x, h x := by
    rw [laplace, ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [corr, kern, hh, map_mul, Complex.conj_conj]
    rw [← Complex.exp_conj]; simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]
    congr 2; ring_nf
  rw [L, R]
  exact integral_neg_eq_self h volume

end Lightlike.BisognanoWichmann
