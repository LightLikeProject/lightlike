import Lightlike.OperatorAlgebras.BoostKMSRapidity.Model

/-!
# The KMS property of the boost flow on the Bisognano-Wichmann subspace (G1-056)

In the rapidity picture on `L²(ℝ)` the boost flow at parameter `2π` is `(V_t ψ)(x) = e^{-2πitx} ψ(x)`
(`flow`). We show that `V_t` preserves the standard subspace `H` (`InH_flow`) and that for `ξ, η ∈ H`
the function `t ↦ ⟨ξ, V_t η⟩` extends continuously to the closed strip `-1 ≤ Im z ≤ 0`,
holomorphically inside, with boundary value `⟨V_t η, ξ⟩` on `Im z = -1`
(`StripKMS`, `strip_kms`): the KMS condition at `β = 2π` for the boost, in the form of
Brunetti-Guido-Longo (the modular group of `H` is the flow `V`).

Supporting lemmas; the catalogue entry is `strip_kms` once the failure checks are in.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace Lightlike.BisognanoWichmann

/-- The boost flow at parameter `2π`: `(V_t ψ)(x) = e^{-2πitx} ψ(x)`. -/
def flow (t : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := fun x => kern x (t : ℂ) * ψ x

/-- The (conjugate-linear in the first slot) pairing `⟨f, g⟩ = ∫ conj f · g` on `L²(ℝ)`. -/
def ip (f g : ℝ → ℂ) : ℂ := ∫ x, conj (f x) * g x

lemma norm_kern_real (x t : ℝ) : ‖kern x (t : ℂ)‖ = 1 := by
  rw [norm_kern]; simp

/-- The boost flow preserves the standard subspace `H`. -/
theorem InH_flow {η : ℝ → ℂ} (hη : InH η) (t : ℝ) : InH (flow t η) := by
  obtain ⟨h1, h2, h3⟩ := hη
  refine ⟨?_, ?_, ?_⟩
  · refine h1.congr_norm (((continuous_kern_x (t : ℂ)).aestronglyMeasurable).mul h1.aestronglyMeasurable) ?_
    exact Eventually.of_forall fun x => by simp [flow, norm_kern_real]
  · have hm : AEStronglyMeasurable (fun x : ℝ => ((Real.exp (-(π * x)) : ℝ) : ℂ) * flow t η x)
        volume :=
      (by fun_prop : Continuous fun x : ℝ => ((Real.exp (-(π * x)) : ℝ) : ℂ)).aestronglyMeasurable.mul
        (((continuous_kern_x (t : ℂ)).aestronglyMeasurable).mul h1.aestronglyMeasurable)
    refine h2.congr_norm hm (Eventually.of_forall fun x => ?_)
    simp [flow, norm_kern_real]
  · filter_upwards [h3] with x hx
    have hk : conj (kern (-x) (t : ℂ)) = kern x (t : ℂ) := by
      rw [kern, ← Complex.exp_conj]
      simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      congr 1; push_cast; ring
    simp only [flow, map_mul, hk]
    rw [hx]
    ring

lemma laplace_corr_real (ξ η : ℝ → ℂ) (t : ℝ) :
    laplace (corr ξ η) (t : ℂ) = ip ξ (flow t η) := by
  unfold laplace ip
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [corr, flow]; ring

lemma conj_laplace_corr_real (ξ η : ℝ → ℂ) (t : ℝ) :
    conj (laplace (corr ξ η) (t : ℂ)) = ip (flow t η) ξ := by
  unfold laplace ip
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [corr, flow, map_mul, Complex.conj_conj]; ring

/-- The **strip KMS condition** for a pair of vectors `ξ, η` under the boost flow `V`: the function
`t ↦ ⟨ξ, V_t η⟩` extends to a function continuous on the closed strip `-1 ≤ Im z ≤ 0`,
holomorphic on the open strip, whose value at `t - i` is `⟨V_t η, ξ⟩`. -/
def StripKMS (ξ η : ℝ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, ContinuousOn F {z : ℂ | -1 ≤ z.im ∧ z.im ≤ 0} ∧
    DifferentiableOn ℂ F {z : ℂ | -1 < z.im ∧ z.im < 0} ∧
    (∀ t : ℝ, F (t : ℂ) = ip ξ (flow t η)) ∧
    ∀ t : ℝ, F ((t : ℂ) - I) = ip (flow t η) ξ

/-- **KMS for the boost on the Bisognano-Wichmann subspace** (model): for all `ξ, η ∈ H`, the boost
flow `V_t = Δ^{it}` (with `Δ = e^{-2πx}`, boost parameter `2π`) satisfies the strip KMS condition,
and it preserves `H`. -/
theorem strip_kms {ξ η : ℝ → ℂ} (hξ : InH ξ) (hη : InH η) : StripKMS ξ η := by
  refine ⟨laplace (corr ξ η),
    continuousOn_laplace (integrable_corr hξ hη) (integrable_corr' hξ hη),
    differentiableOn_laplace (integrable_corr hξ hη) (integrable_corr' hξ hη),
    laplace_corr_real ξ η, fun t => ?_⟩
  rw [laplace_corr_boundary hξ hη t, conj_laplace_corr_real]

end Lightlike.BisognanoWichmann
