import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Gauge invariance of the Bardeen potentials (G1-030, CO4)

Scalar sector of linear perturbations of a spatially flat FLRW universe in conformal time `η`, with the
metric `ds² = a(η)² [ -(1 + 2A) dη² + 2 ∂ᵢB dη dxⁱ + ((1 - 2ψ) δᵢⱼ + 2 ∂ᵢ∂ⱼE) dxⁱ dxʲ ]`
(Baumann, *TASI Lectures on Inflation*, Section 9.2.3, gauge-invariant variables; the sign conventions of the
potentials below are fixed here and are not claimed to be those of a displayed equation of that paper).

Only time derivatives enter the gauge transformation of `(A, B, ψ, E)` and the Bardeen potentials, so everything is
stated for functions of `η` at one fixed comoving point; the statement for fields on `ℝ × ℝ³` is the same
statement applied at each point.

Under `xᵘ ↦ xᵘ + ξᵘ`, `ξ⁰ = T`, `ξⁱ = ∂ⁱL`, the perturbation changes by minus the Lie derivative of the
background `a² η_{μν}`, which gives `gauge`:
`A ↦ A - T' - 𝓗 T`, `B ↦ B + T - L'`, `ψ ↦ ψ + 𝓗 T`, `E ↦ E - L`, with `𝓗 = a'/a`.
The Bardeen potentials are `Φ = A + 𝓗 σ + σ'` and `Ψ = ψ - 𝓗 σ` with the shear `σ = B - E'`.
-/

namespace Lightlike
namespace Cosmology
namespace Perturbation

/-- The scalar part `(A, B, ψ, E)` of a metric perturbation of spatially flat FLRW in conformal time, at one
comoving point: lapse `A`, shift potential `B`, curvature perturbation `ψ`, and shear potential `E`. -/
@[ext]
structure ScalarPert where
  /-- The lapse perturbation `A` (`δg₀₀ = -2 a² A`). -/
  A : ℝ → ℝ
  /-- The shift potential `B` (`δg₀ᵢ = a² ∂ᵢB`). -/
  B : ℝ → ℝ
  /-- The curvature perturbation `ψ` (the trace part of `δgᵢⱼ = a² (-2ψ δᵢⱼ + 2 ∂ᵢ∂ⱼE)`). -/
  psi : ℝ → ℝ
  /-- The spatial shear potential `E`. -/
  E : ℝ → ℝ

/-- The conformal Hubble rate `𝓗 = a'/a` of a scale factor `a` of conformal time. -/
noncomputable def hubble (a : ℝ → ℝ) (η : ℝ) : ℝ := deriv a η / a η

/-- The gauge transformation of a scalar perturbation by the generator `ξ⁰ = T`, `ξⁱ = ∂ⁱL`. -/
noncomputable def gauge (a T L : ℝ → ℝ) (p : ScalarPert) : ScalarPert where
  A := fun η => p.A η - deriv T η - hubble a η * T η
  B := fun η => p.B η + T η - deriv L η
  psi := fun η => p.psi η + hubble a η * T η
  E := fun η => p.E η - L η

/-- The shear `σ = B - E'` of a scalar perturbation. -/
noncomputable def shear (p : ScalarPert) : ℝ → ℝ := fun η => p.B η - deriv p.E η

/-- The Bardeen potential `Φ = A + 𝓗 σ + σ'`. -/
noncomputable def bardeenPhi (a : ℝ → ℝ) (p : ScalarPert) (η : ℝ) : ℝ :=
  p.A η + hubble a η * shear p η + deriv (shear p) η

/-- The Bardeen potential `Ψ = ψ - 𝓗 σ`. -/
noncomputable def bardeenPsi (a : ℝ → ℝ) (p : ScalarPert) (η : ℝ) : ℝ :=
  p.psi η - hubble a η * shear p η

/-- Under a gauge transformation the shear shifts by the time generator: `σ ↦ σ + T`. -/
theorem shear_gauge {a T L : ℝ → ℝ} {p : ScalarPert} (hE : Differentiable ℝ p.E)
    (hL : Differentiable ℝ L) : shear (gauge a T L p) = fun η => shear p η + T η := by
  funext η
  have h : deriv (fun y => p.E y - L y) η = deriv p.E η - deriv L η := deriv_sub (hE η) (hL η)
  simp only [shear, gauge, h]
  ring

/-- **The Bardeen potential `Ψ` is gauge invariant.** -/
theorem bardeenPsi_gauge {a T L : ℝ → ℝ} {p : ScalarPert} (hE : Differentiable ℝ p.E)
    (hL : Differentiable ℝ L) (η : ℝ) :
    bardeenPsi a (gauge a T L p) η = bardeenPsi a p η := by
  have hs := congrFun (shear_gauge (a := a) (T := T) hE hL (p := p)) η
  simp only [bardeenPsi]
  rw [hs]
  simp only [gauge]
  ring

/-- **The Bardeen potential `Φ` is gauge invariant**, for a differentiable shift potential and a twice
differentiable shear potential and a differentiable time generator. -/
theorem bardeenPhi_gauge {a T L : ℝ → ℝ} {p : ScalarPert} (hB : Differentiable ℝ p.B)
    (hE : Differentiable ℝ p.E) (hE' : Differentiable ℝ (deriv p.E)) (hT : Differentiable ℝ T)
    (hL : Differentiable ℝ L) (η : ℝ) :
    bardeenPhi a (gauge a T L p) η = bardeenPhi a p η := by
  have hs := shear_gauge (a := a) (T := T) hE hL (p := p)
  have hσ : Differentiable ℝ (shear p) := hB.sub hE'
  have hd : deriv (fun y => shear p y + T y) η = deriv (shear p) η + deriv T η :=
    deriv_add (hσ η) (hT η)
  simp only [bardeenPhi, hs]
  simp only [gauge, hd]
  ring

/-- **A pure-gauge perturbation has vanishing Bardeen potentials**: the gauge transform of the zero
perturbation (the unperturbed universe) has `Φ = Ψ = 0`. -/
theorem bardeen_pureGauge {a T L : ℝ → ℝ} (hT : Differentiable ℝ T) (hL : Differentiable ℝ L)
    (η : ℝ) :
    bardeenPhi a (gauge a T L ⟨0, 0, 0, 0⟩) η = 0 ∧ bardeenPsi a (gauge a T L ⟨0, 0, 0, 0⟩) η = 0 := by
  have h0 : Differentiable ℝ (0 : ℝ → ℝ) := differentiable_const 0
  have hz : deriv (0 : ℝ → ℝ) = 0 := funext fun x => deriv_const x (0 : ℝ)
  have hd0 : Differentiable ℝ (deriv (0 : ℝ → ℝ)) := by
    rw [hz]
    exact h0
  have hsh : shear (⟨0, 0, 0, 0⟩ : ScalarPert) = 0 := by
    funext η
    simp [shear, hz]
  refine ⟨?_, ?_⟩
  · rw [bardeenPhi_gauge (p := ⟨0, 0, 0, 0⟩) h0 h0 hd0 hT hL]
    simp [bardeenPhi, hsh, hz]
  · rw [bardeenPsi_gauge (p := ⟨0, 0, 0, 0⟩) h0 hL]
    simp [bardeenPsi, hsh]

/-- **Newtonian gauge.** The gauge transformation with `T = -σ`, `L = E` removes the shift and the shear
potential and leaves exactly the Bardeen potentials as lapse and curvature perturbation. -/
theorem gauge_newtonian (a : ℝ → ℝ) (p : ScalarPert) :
    gauge a (fun η => - shear p η) p.E p
      = ⟨bardeenPhi a p, fun _ => 0, bardeenPsi a p, fun _ => 0⟩ := by
  have hd : deriv (fun η => - shear p η) = fun η => - deriv (shear p) η :=
    funext fun η => deriv.neg (f := shear p)
  have h1 : (fun η => p.A η - deriv (fun η => - shear p η) η - hubble a η * - shear p η)
      = bardeenPhi a p := by
    funext η
    simp only [hd, bardeenPhi]
    ring
  have h2 : (fun η => p.B η + - shear p η - deriv p.E η) = fun _ => 0 := by
    funext η
    simp only [shear]
    ring
  have h3 : (fun η => p.psi η + hubble a η * - shear p η) = bardeenPsi a p := by
    funext η
    simp only [bardeenPsi]
    ring
  have h4 : (fun η => p.E η - p.E η) = fun _ => 0 := by
    funext η
    ring
  simp only [gauge]
  rw [h1, h2, h3, h4]

/-- **Converse (pure gauge).** If both Bardeen potentials vanish identically then the perturbation is the
gauge transform of the zero perturbation, with the generator `T = σ`, `L = -E`. -/
theorem eq_gauge_zero_of_bardeen_eq_zero {a : ℝ → ℝ} {p : ScalarPert}
    (hΦ : bardeenPhi a p = 0) (hΨ : bardeenPsi a p = 0) :
    p = gauge a (shear p) (fun η => - p.E η) ⟨0, 0, 0, 0⟩ := by
  have hd : deriv (fun η => - p.E η) = fun η => - deriv p.E η := funext fun η => deriv.neg (f := p.E)
  ext η
  · have := congrFun hΦ η
    simp only [bardeenPhi, Pi.zero_apply] at this
    simp only [gauge, Pi.zero_apply]
    linarith
  · simp only [gauge, hd, shear, Pi.zero_apply]
    ring
  · have := congrFun hΨ η
    simp only [bardeenPsi, Pi.zero_apply] at this
    simp only [gauge, Pi.zero_apply]
    linarith
  · simp only [gauge, Pi.zero_apply]
    ring

/-- **Characterisation of pure gauge.** For a perturbation with differentiable `B`, `E`, `E'`, both Bardeen
potentials vanish identically iff the perturbation is the gauge transform of the zero perturbation by
differentiable generators `T`, `L`. -/
theorem bardeen_eq_zero_iff_pureGauge {a : ℝ → ℝ} {p : ScalarPert} (hB : Differentiable ℝ p.B)
    (hE : Differentiable ℝ p.E) (hE' : Differentiable ℝ (deriv p.E)) :
    (bardeenPhi a p = 0 ∧ bardeenPsi a p = 0) ↔
      ∃ T L : ℝ → ℝ, Differentiable ℝ T ∧ Differentiable ℝ L ∧
        p = gauge a T L ⟨0, 0, 0, 0⟩ := by
  constructor
  · rintro ⟨hΦ, hΨ⟩
    exact ⟨shear p, fun η => - p.E η, hB.sub hE', hE.neg,
      eq_gauge_zero_of_bardeen_eq_zero hΦ hΨ⟩
  · rintro ⟨T, L, hT, hL, hp⟩
    subst hp
    exact ⟨funext fun η => (bardeen_pureGauge hT hL η).1, funext fun η => (bardeen_pureGauge hT hL η).2⟩

end Perturbation
end Cosmology
end Lightlike
