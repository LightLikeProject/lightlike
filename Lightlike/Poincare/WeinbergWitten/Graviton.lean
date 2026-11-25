import Lightlike.Poincare.ConeSourceMeasure
import Lightlike.Poincare.MasslessGenerators
import Lightlike.Poincare.OneParticleContinuity

/-!
# Gravitons as massless helicity ±2 representations of the Poincaré group

Row G3-253 (target T-PG3). The massless one-particle representation of integer helicity `h` is the induced
representation `poincareCone (2h)` on `L²(d³p / 2|p|)` of the forward light cone (`Lightlike/Poincare`). We name it
`helicityRep h`; the photon is `h = ±1` and the graviton `h = ±2`.

## Main statements

* `helicityRep_mul`, `helicityRep_one`: the group law of `ℝ⁴ ⋊ SL(2,ℂ)`.
* `helicityRep_surjective`: every `V(a, A)` is a unitary operator (an onto linear isometry).
* `helicityRep_irreducible`: the representation is irreducible, for every `h`.
* `helicityAct_rot_helicity`: the rotation by `θ` about the momentum acts at the standard momentum by `e^{i h θ}`.

## Limits

The existence of a graviton as a representation is the content; the Weinberg–Witten statement is in the sibling
files of this folder.
-/

open MeasureTheory Lightlike.Poincare Lightlike.Lorentz

namespace Lightlike.Poincare.WeinbergWitten

noncomputable section

/-- The one-particle Hilbert space `L²(d³p / 2|p|)` of the forward light cone. -/
abbrev OneParticle : Type := Lp ℂ 2 coneSourceMeasure

/-- **The massless one-particle representation of helicity `h ∈ ℤ`** of `ℝ⁴ ⋊ SL(2,ℂ)`: `V(a, A) = T(a) U(A)` with
the helicity character `A ↦ (A₀₀)^{2h}` of the little group. Photons: `h = ±1`; gravitons: `h = ±2`. -/
def helicityRep (h : ℤ) (a : Transl) (A : SL2C) : OneParticle →ₗᵢ[ℂ] OneParticle :=
  poincareCone (2 * h) measurePreserving_coneSourceMeasure a A

/-- The photon representations (helicity `±1`) and the graviton representations (helicity `±2`). -/
abbrev gravitonRep (ε : ℤˣ) := helicityRep (2 * ε)

/-- **The group law**: `V(a, A) V(b, B) = V(a + A b, A B)`. -/
theorem helicityRep_mul (h : ℤ) (a b : Transl) (A B : SL2C) (f : OneParticle) :
    helicityRep h a A (helicityRep h b B f) = helicityRep h (a + translAct A b) (A * B) f :=
  poincareCone_mul _ _ a b A B f

/-- The identity acts trivially. -/
theorem helicityRep_one (h : ℤ) (f : OneParticle) : helicityRep h 0 1 f = f :=
  poincareCone_one _ _ f

/-- **Unitarity**: every `V(a, A)` is onto, hence (being an isometry) a unitary operator of the one-particle space. -/
theorem helicityRep_surjective (h : ℤ) (a : Transl) (A : SL2C) : Function.Surjective (helicityRep h a A) := by
  intro g
  refine ⟨helicityRep h (-translAct A⁻¹ a) A⁻¹ g, ?_⟩
  rw [helicityRep_mul, translAct_neg, ← translAct_mul, mul_inv_cancel, translAct_one, add_neg_cancel,
    helicityRep_one]

/-- `V(a, A)` as a unitary operator of the one-particle space. -/
def helicityRepE (h : ℤ) (a : Transl) (A : SL2C) : OneParticle ≃ₗᵢ[ℂ] OneParticle :=
  LinearIsometryEquiv.ofSurjective (helicityRep h a A) (helicityRep_surjective h a A)

/-- **Irreducibility**: a closed subspace of the one-particle space invariant under every `V(a, A)` is `0` or
everything. -/
theorem helicityRep_irreducible (h : ℤ) (K : Submodule ℂ OneParticle) (hK : IsClosed (K : Set OneParticle))
    (hinv : ∀ a A, ∀ f ∈ K, helicityRep h a A f ∈ K) : K = ⊥ ∨ K = ⊤ := by
  refine irreducible_massless_coneSourceMeasure (2 * h) K hK (fun a f hf => ?_) (fun A f hf => ?_)
  · have := hinv a 1 f hf
    simpa [helicityRep, poincareCone, helL2_one] using this
  · have := hinv 0 A f hf
    simpa [helicityRep, poincareCone, translCone_zero] using this

/-- **Helicity `h`**: the rotation by `θ` about the momentum acts on the states of the standard momentum `K` by
`e^{i h θ}`; the translations of the little group act trivially (`hasDerivAt_helicityAct_trans`, finite helicity). -/
theorem helicityAct_rot_helicity (h : ℤ) (θ : ℝ) (ψ : LightCone → ℂ) :
    helicityAct (2 * h) (coneRot θ) ψ coneBase = Complex.exp (Complex.I * (h * θ)) * ψ coneBase := by
  rw [helicityAct_base _ (coneRot_mem θ)]
  congr 1
  simp only [coneRot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

end

end Lightlike.Poincare.WeinbergWitten

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.OneParticle := _root_.Lightlike.Poincare.WeinbergWitten.OneParticle
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.gravitonRep := _root_.Lightlike.Poincare.WeinbergWitten.gravitonRep
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.helicityAct_rot_helicity := _root_.Lightlike.Poincare.WeinbergWitten.helicityAct_rot_helicity
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.helicityRep := _root_.Lightlike.Poincare.WeinbergWitten.helicityRep
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.helicityRepE := _root_.Lightlike.Poincare.WeinbergWitten.helicityRepE
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.helicityRep_irreducible := _root_.Lightlike.Poincare.WeinbergWitten.helicityRep_irreducible
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.helicityRep_mul := _root_.Lightlike.Poincare.WeinbergWitten.helicityRep_mul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.helicityRep_one := _root_.Lightlike.Poincare.WeinbergWitten.helicityRep_one
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_253.helicityRep_surjective := _root_.Lightlike.Poincare.WeinbergWitten.helicityRep_surjective
