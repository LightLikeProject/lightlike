import Lightlike.Rows.G1_047.Green

/-!
# Energy of a rectangle dominates the Bogomolny boundary term (CO24)

`bogoEnergy` is the energy density `½B² + |D₁φ|² + |D₂φ|² + (λ/4)(|φ|²−v²)²` at critical coupling
`λ = 2e²` of a configuration `(φ, A₁, A₂)`. Combined with the pointwise bound of `Density.lean`
and Green's theorem of `Green.lean`, the energy in any rectangle is at least `±` the boundary
integral of `W` (`box_energy_ge_plus/minus` give the bound against `∫∫ bogoTerm`, and
`box_integral_bogoTerm` identifies the latter with the boundary integral).

## Main results

* `bogoEnergy`: the energy density of a configuration.
* `integral2_mono`: monotonicity of iterated interval integrals of continuous functions.
* `box_energy_ge_plus`, `box_energy_ge_minus`: `±∫∫ bogoTerm ≤ ∫∫ bogoEnergy`.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex MeasureTheory Set

/-- The energy density at critical coupling `λ = 2e²` of the configuration `(φ, A₁, A₂)`. -/
def bogoEnergy (e v : ℝ) (A₁ A₂ : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  energyDensity (2 * e ^ 2) v (fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1)) (φ p)
    (covD e (A₁ p) (fderiv ℝ φ p (1, 0)) (φ p))
    (covD e (A₂ p) (fderiv ℝ φ p (0, 1)) (φ p))

/-- The pointwise bound `e v² B + curlJ ≤ density`, in terms of `bogoTerm`, `bogoEnergy`. -/
theorem bogoTerm_le_bogoEnergy (e v : ℝ) (A₁ A₂ : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    bogoTerm e v A₁ A₂ φ p ≤ bogoEnergy e v A₁ A₂ φ p :=
  energyDensity_ge_plus _ _ _ _ _ _

/-- The pointwise bound `−(e v² B + curlJ) ≤ density`. -/
theorem neg_bogoTerm_le_bogoEnergy (e v : ℝ) (A₁ A₂ : ℝ × ℝ → ℝ) (φ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    -bogoTerm e v A₁ A₂ φ p ≤ bogoEnergy e v A₁ A₂ φ p :=
  energyDensity_ge_minus _ _ _ _ _ _

/-- Monotonicity of iterated interval integrals of continuous functions on `ℝ × ℝ`. -/
theorem integral2_mono {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ p, f p ≤ g p) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, f (x, y)) ≤ ∫ x in a..b, ∫ y in c..d, g (x, y) := by
  have hf' : Continuous fun x => ∫ y in c..d, f (x, y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x y => f (x, y)) hf c d
  have hg' : Continuous fun x => ∫ y in c..d, g (x, y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x y => g (x, y)) hg c d
  refine intervalIntegral.integral_mono_on hab (hf'.intervalIntegrable _ _)
    (hg'.intervalIntegrable _ _) fun x _ => ?_
  refine intervalIntegral.integral_mono_on hcd
    ((hf.comp (Continuous.prodMk_right x)).intervalIntegrable _ _)
    ((hg.comp (Continuous.prodMk_right x)).intervalIntegrable _ _) fun y _ => hfg _

/-- The Bogomolny integrand and the energy density are continuous for `φ ∈ C²`, `A_j ∈ C¹`. -/
theorem continuous_bogo {e v : ℝ} {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂) :
    Continuous (bogoTerm e v A₁ A₂ φ) ∧ Continuous (bogoEnergy e v A₁ A₂ φ) := by
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have h1 : Continuous fun p => fderiv ℝ A₁ p := hA₁.continuous_fderiv one_ne_zero
  have h2 : Continuous fun p => fderiv ℝ A₂ p := hA₂.continuous_fderiv one_ne_zero
  have hφc : Continuous φ := hφ.continuous
  have hB : Continuous fun p => fderiv ℝ A₂ p (1, 0) - fderiv ℝ A₁ p (0, 1) :=
    (h2.clm_apply continuous_const).sub (h1.clm_apply continuous_const)
  have hD₁ : Continuous fun p => covD e (A₁ p) (fderiv ℝ φ p (1, 0)) (φ p) := by
    unfold covD
    have := hA₁.continuous
    fun_prop
  have hD₂ : Continuous fun p => covD e (A₂ p) (fderiv ℝ φ p (0, 1)) (φ p) := by
    unfold covD
    have := hA₂.continuous
    fun_prop
  constructor
  · unfold bogoTerm curlJ
    fun_prop
  · unfold bogoEnergy energyDensity
    fun_prop

/-- **Energy dominates the boundary term (upper sign).** For a rectangle,
`∫∫ (e v² B + curlJ) ≤ ∫∫ energy density`, at critical coupling. -/
theorem box_energy_ge_plus (e v : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    (∫ x in a₁..b₁, ∫ y in a₂..b₂, bogoTerm e v A₁ A₂ φ (x, y)) ≤
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, bogoEnergy e v A₁ A₂ φ (x, y) :=
  integral2_mono (continuous_bogo hφ hA₁ hA₂).1 (continuous_bogo hφ hA₁ hA₂).2
    (bogoTerm_le_bogoEnergy e v A₁ A₂ φ) h₁ h₂

/-- **Energy dominates the boundary term (lower sign).**
`−∫∫ (e v² B + curlJ) ≤ ∫∫ energy density`, at critical coupling. -/
theorem box_energy_ge_minus (e v : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    -(∫ x in a₁..b₁, ∫ y in a₂..b₂, bogoTerm e v A₁ A₂ φ (x, y)) ≤
      ∫ x in a₁..b₁, ∫ y in a₂..b₂, bogoEnergy e v A₁ A₂ φ (x, y) := by
  have hc := continuous_bogo (e := e) (v := v) hφ hA₁ hA₂
  have := integral2_mono (f := fun p => -bogoTerm e v A₁ A₂ φ p) hc.1.neg hc.2
    (neg_bogoTerm_le_bogoEnergy e v A₁ A₂ φ) h₁ h₂
  simpa [intervalIntegral.integral_neg] using this

end Lightlike.Vortex
