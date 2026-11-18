import Lightlike.Asymptotics.Tauberian.FourierExchange

/-!
# The heavy-operator bound of Hartman–Keller–Stoica

Section 3 of Mukhametzhanov–Zhiboedov (arXiv:1904.06359), equations (3.1)–(3.6): for a positive
measure `ρ` with a modular invariant partition function `Z(β) = ∫ e^{-β(Δ - c/12)} dρ(Δ)`, the heavy
part `Z_H` (operators with `Δ ≥ Δ_H > c/12`) satisfies, for `β' < β`,
`(1 - e^{-κ}) Z_H(β) ≤ e^{-κ} (Z_L(β) - Z_L(β'))`, `κ = (β - β') (Δ_H - c/12)` (`heavy_le`).
-/

open MeasureTheory Set

noncomputable section

namespace Lightlike.Tauberian

/-- The partition function restricted to a set of dimensions:
`∫_S e^{-β (Δ - c/12)} dρ(Δ)`. -/
def partZ (ρ : Measure ℝ) (c β : ℝ) (S : Set ℝ) : ℝ := ∫ x in S, Real.exp (-β * (x - c / 12)) ∂ρ

/-- **The HKS bound** (MZ (3.3)–(3.4)). `Z = Z_L + Z_H` is modular invariant between `β` and `β'`
(`Z_L(β) + Z_H(β) = Z_L(β') + Z_H(β')`), `0 < β' < β` and `Δ_H > c/12`. -/
theorem heavy_le (ρ : Measure ℝ) (c β β' ΔH : ℝ) (hβ' : 0 < β') (hββ' : β' < β)
    (hint : ∀ b : ℝ, 0 < b → Integrable (fun x : ℝ => Real.exp (-b * (x - c / 12))) ρ)
    (hmod : partZ ρ c β (Iio ΔH) + partZ ρ c β (Ici ΔH) = partZ ρ c β' (Iio ΔH) + partZ ρ c β' (Ici ΔH)) :
    (1 - Real.exp (-((β - β') * (ΔH - c / 12)))) * partZ ρ c β (Ici ΔH) ≤
      Real.exp (-((β - β') * (ΔH - c / 12))) * (partZ ρ c β (Iio ΔH) - partZ ρ c β' (Iio ΔH)) := by
  have h1 : partZ ρ c β (Ici ΔH) ≤ Real.exp (-((β - β') * (ΔH - c / 12))) * partZ ρ c β' (Ici ΔH) := by
    unfold partZ
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((hint β (by linarith)).integrableOn)
      (((hint β' hβ').integrableOn).const_mul _) measurableSet_Ici fun x hx => ?_
    have hx' : ΔH ≤ x := hx
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  nlinarith [h1, hmod]

end Lightlike.Tauberian
