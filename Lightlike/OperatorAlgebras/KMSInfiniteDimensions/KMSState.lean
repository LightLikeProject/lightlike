import Lightlike.OperatorAlgebras.GibbsKMS

/-!
# The KMS condition for a state and a flow, in the strip form

J. Panangaden, *Energy Full Counting Statistics and Return to Equilibrium*, arXiv:2110.01678 (source key
`panangaden-2021`), Definition 5.8, p. 46 and Proposition 5.9, p. 47: a state `ω` is `(τ, β)`-KMS if for all `A`, `B`
there is a function `F_{A,B}`, bounded and continuous on the closed strip `0 ≤ Im z ≤ β` and analytic inside, with
`F_{A,B}(t) = ω(A τᵗ(B))` and `F_{A,B}(t + iβ) = ω(τᵗ(B) A)`.

* `IsKMSState τ ω β`: this condition, for a flow `τ : ℝ → A → A` on any type `A` with a product and a functional
  `ω : A → ℂ`; it does not use the finite-dimensional trace of `FiniteKMS.lean`;
* `isKMSState_gibbs`: the Gibbs state of `GibbsKMS.lean` (a Hilbert basis and real eigenvalues, `∑ e^{-βλₙ} < ∞`) is
  `(τ, β)`-KMS for `τᵗ(A) = e^{itH} A e^{-itH}`.
-/

namespace Lightlike.OperatorAlgebras.KMSInfiniteDimensions

open Lightlike.OperatorAlgebras.GibbsKMS

/-- **The `β`-KMS condition in the strip form** (Panangaden, Definition 5.8, p. 46): for all `a`, `b` there is a function
`F`, bounded and continuous on the closed strip `0 ≤ Im z ≤ β` and analytic on the open strip, with
`F(t) = ω(a τᵗ(b))` and `F(t + iβ) = ω(τᵗ(b) a)` for real `t`. -/
def IsKMSState {A : Type*} [Mul A] (τ : ℝ → A → A) (ω : A → ℂ) (β : ℝ) : Prop :=
  ∀ a b : A, ∃ F : ℂ → ℂ, ContinuousOn F (strip β) ∧ DifferentiableOn ℂ F (openStrip β) ∧
    (∃ C : ℝ, ∀ z ∈ strip β, ‖F z‖ ≤ C) ∧ (∀ t : ℝ, F t = ω (a * τ t b)) ∧
    ∀ t : ℝ, F (t + Complex.I * β) = ω (τ t b * a)

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The Gibbs state is `(τ, β)`-KMS** (Panangaden, Proposition 5.4 and 5.9, pp. 43, 47): for a Hilbert basis `b` and real
eigenvalues `ev` with `∑ₙ e^{-β evₙ} < ∞` and `β > 0`, the state `ω(A) = tr(e^{-βH} A)/Z` satisfies `IsKMSState` for
`τᵗ(A) = e^{itH} A e^{-itH}`. -/
theorem isKMSState_gibbs (b : HilbertBasis ι ℂ H) (ev : ι → ℝ) {β : ℝ} (hβ : 0 < β)
    (hZ : Summable fun n => Real.exp (-(β * ev n))) :
    IsKMSState (dyn b ev) (gibbs b ev β) β := fun A B =>
  ⟨kmsFun b ev β A B, continuousOn_kmsFun b ev hβ hZ A B, differentiableOn_kmsFun b ev hβ hZ A B,
    ⟨_, fun _ hz => norm_kmsFun_le b ev hβ hZ A B hz⟩, fun t => kmsFun_ofReal b ev hβ hZ A B t,
    fun t => kmsFun_add_I_mul b ev hβ hZ A B t⟩

end Lightlike.OperatorAlgebras.KMSInfiniteDimensions

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.IsKMSState := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.IsKMSState
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_053.isKMSState_gibbs := _root_.Lightlike.OperatorAlgebras.KMSInfiniteDimensions.isKMSState_gibbs
