import Lightlike.OperatorAlgebras.KMSInfiniteDimensions.KMSStrip

/-!
# The KMS condition for a state and a flow, in infinite dimensions

Row G1-053.  For a state `ω` on an algebra `A` and a one-parameter flow `τ : ℝ → A → A`, the KMS
condition at inverse temperature `β > 0` (Bratteli-Robinson, Definition 5.3.1; Panangaden,
Definition 5.8) asks, for all `a b`, for a function `F`, continuous and bounded on the closed strip
`0 ≤ Im z ≤ β`, analytic inside, with boundary values `F(t) = ω(a τᵗ(b))` and
`F(t + iβ) = ω(τᵗ(b) a)`.

We prove that `F` is unique (`IsKMSFunctional.eq_of_agree`), and that a state that is KMS for the
trivial flow is a trace (`IsKMSFunctional.tracial_of_trivial_flow`): this is the mechanism by which a
wrong flow, such as a rotation in place of a boost, fails the KMS condition.
-/

open Complex Set

namespace Lightlike.OperatorAlgebras.KMSInfiniteDimensions

variable {A : Type*} [Mul A]

/-- The **KMS condition** for the state `ω` and the flow `τ` at inverse temperature `β`: for all
`a b` there is a function `F` on the closed strip `0 ≤ Im z ≤ β`, continuous and bounded there,
analytic in the open strip, with `F(t) = ω(a τᵗ(b))` and `F(t + iβ) = ω(τᵗ(b) a)`. -/
def IsKMSFunctional (ω : A → ℂ) (τ : ℝ → A → A) (β : ℝ) : Prop :=
  ∀ a b : A, ∃ F : ℂ → ℂ, ContinuousOn F (strip β) ∧ DifferentiableOn ℂ F (openStrip β) ∧
    (∃ C : ℝ, ∀ z ∈ strip β, ‖F z‖ ≤ C) ∧ (∀ t : ℝ, F t = ω (a * τ t b)) ∧
    ∀ t : ℝ, F (t + I * β) = ω (τ t b * a)

namespace IsKMSFunctional

/-- **Uniqueness of the KMS function**: two admissible functions that agree on the real line agree on
the whole closed strip. -/
theorem eq_of_agree {β : ℝ} (hβ : 0 < β) {F G : ℂ → ℂ}
    (hFc : ContinuousOn F (strip β)) (hFd : DifferentiableOn ℂ F (openStrip β))
    (hFb : ∃ C : ℝ, ∀ z ∈ strip β, ‖F z‖ ≤ C)
    (hGc : ContinuousOn G (strip β)) (hGd : DifferentiableOn ℂ G (openStrip β))
    (hGb : ∃ C : ℝ, ∀ z ∈ strip β, ‖G z‖ ≤ C) (h : ∀ t : ℝ, F t = G t) :
    ∀ z ∈ strip β, F z = G z := by
  obtain ⟨C₁, h₁⟩ := hFb
  obtain ⟨C₂, h₂⟩ := hGb
  have key := eq_zero_of_real_zero (F := fun z => F z - G z) hβ (hFc.sub hGc) (hFd.sub hGd)
    ⟨C₁ + C₂, fun z hz => (norm_sub_le _ _).trans (add_le_add (h₁ z hz) (h₂ z hz))⟩
    (fun t => by simp [h t])
  intro z hz
  exact sub_eq_zero.mp (key z hz)

/-- **A state that is KMS (`β > 0`) for the trivial flow is a trace**: `ω(a b) = ω(b a)`.
The function `F` is constant on the real line, hence constant on the strip, and its two boundary
values are `ω(a b)` and `ω(b a)`. -/
theorem tracial_of_trivial_flow {ω : A → ℂ} {β : ℝ} (hβ : 0 < β)
    (h : IsKMSFunctional ω (fun _ => id) β) (a b : A) : ω (a * b) = ω (b * a) := by
  obtain ⟨F, hc, hd, hb, h0, h1⟩ := h a b
  have key := eq_of_agree hβ hc hd hb (G := fun _ => ω (a * b)) continuousOn_const
    (differentiableOn_const _) ⟨‖ω (a * b)‖, fun _ _ => le_rfl⟩
    (fun t => by simpa using h0 t)
  have hmem : ((0 : ℝ) + I * β : ℂ) ∈ strip β := by simp [strip, hβ.le]
  have := key _ hmem
  rw [h1 0] at this
  simpa using this.symm

end IsKMSFunctional

end Lightlike.OperatorAlgebras.KMSInfiniteDimensions

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.IsKMSFunctional := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.IsKMSFunctional
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.IsKMSFunctional.eq_of_agree := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.IsKMSFunctional.eq_of_agree
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.IsKMSFunctional.tracial_of_trivial_flow := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.IsKMSFunctional.tracial_of_trivial_flow
