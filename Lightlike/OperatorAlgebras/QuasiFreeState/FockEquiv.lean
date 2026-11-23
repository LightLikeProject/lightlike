import Lightlike.OperatorAlgebras.QuasiFreeState.Fock
import Lightlike.OperatorAlgebras.FockExists

/-!
# A quasi-free state whose covariance is the real part of a complex inner product is pure

Let `(V, ω, η)` be a symplectic space with a covariance, and suppose there is a surjective additive map `e : V →+ h` onto a
complex inner product space with `ω(a, b) = Im ⟨e a, e b⟩` and `η(a, b) = Re ⟨e a, e b⟩`. Then the Gram kernel of the
quasi-free state is the Gram kernel of the Fock vectors (`qfKer_eq_fockGram`), so the GNS space of the quasi-free
state is unitarily equivalent to the Fock space with the Weyl unitaries matching (`exists_unitary_qf_fock`). The
Fock representation is irreducible (`commutant_scalar`), hence so is the GNS representation, and the quasi-free state
is pure (`isPureState_qfState_of_equiv`).

This is the sufficiency half of the purity criterion `η = Re⟨·,·⟩`, `ω = Im⟨·,·⟩` for a complex structure `J` on `V`
(`ω(a, b) = -η(a, J b)`); the necessity half is not proved here. The conventions are those of Dereziński,
arXiv:math-ph/0511030, eq. (70) (`(Ψ|W(y)Ψ) = exp(-¼ yηy)`) and Theorem 39 (`η + iω` positive in the sense `|ω| ≤ ...`),
which this file reads only for the convention; the criterion itself is the Fock-vacuum purity of
`isPureState_fock`, and no comparison with a published statement of the criterion is claimed.
-/

open scoped InnerProductSpace ComplexConjugate

universe u v

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (ω η : LinearMap.BilinForm ℝ V)
  {h : Type v} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- **The Gram kernel of the quasi-free state is the Fock Gram function**, transported along `e`. -/
theorem qfKer_eq_fockGram (e : V →+ h) (hω : ∀ a b, ω a b = symp h (e a) (e b))
    (hη : ∀ a b, η a b = (⟪e a, e b⟫_ℂ).re) (f g : V) :
    qfKer ω η f g = fockGram (e f) (e g) := by
  have hsub : e (g - f) = e g - e f := map_sub e g f
  have hηn : η (g - f) (g - f) = ‖e g - e f‖ ^ 2 := by
    rw [hη, hsub, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hsy : symp h (-(e f)) (e g) = -ω f g := by
    rw [hω, symp, symp, inner_neg_left]
    simp
  simp only [qfKer, Matrix.of_apply, fockGram]
  rw [hηn, hsy, show -(e f) + e g = e g - e f by abel]
  congr 1
  · congr 1; push_cast; ring
  · rw [Complex.ofReal_exp]; congr 1; push_cast; ring

variable [Fact (qfKerM ω η).PosSemidef]

/-- **The GNS space of the quasi-free state is the Fock space**: a unitary `U` with `U (kq f) = W(e f) Ω` that
intertwines the Weyl unitaries, `U W(g) = W(e g) U`. -/
theorem exists_unitary_qf_fock (hω₀ : ∀ a b, ω a b = -ω b a) (e : V →+ h) (he : Function.Surjective e)
    (hω : ∀ a b, ω a b = symp h (e a) (e b)) (hη : ∀ a b, η a b = (⟪e a, e b⟫_ℂ).re) :
    ∃ U : QFSpace ω η ≃ₗᵢ[ℂ] FockSpace h, ∀ g ψ, U (qfW ω η hω₀ g ψ) = (fockRepOf h).W (e g) (U ψ) := by
  set R := fockRepOf h with hR
  let Φ₂ : (V →₀ ℂ) →ₗ[ℂ] FockSpace h :=
    Finsupp.linearCombination ℂ fun f : V => R.W (e f) R.Ω
  have hd₂ : Dense ((LinearMap.range Φ₂ : Submodule ℂ (FockSpace h)) : Set (FockSpace h)) := by
    have hr : LinearMap.range Φ₂ = Submodule.span ℂ (Set.range fun f : V => R.W (e f) R.Ω) :=
      Finsupp.range_linearCombination _
    have hrange : Set.range (fun f : V => R.W (e f) R.Ω) = Set.range (fun f : h => R.W f R.Ω) := by
      ext x
      constructor
      · rintro ⟨f, rfl⟩; exact ⟨e f, rfl⟩
      · rintro ⟨f, rfl⟩
        obtain ⟨g, rfl⟩ := he f
        exact ⟨g, rfl⟩
    rw [hr, hrange, Submodule.dense_iff_topologicalClosure_eq_top]
    exact R.cyclic
  obtain ⟨U, hU⟩ := exists_unitary_of_gram_eq (Φ₁ := qfPhi ω η) (Φ₂ := Φ₂)
    (fun x y => by
      simp only [qfPhi_single, Φ₂, Finsupp.linearCombination_single, one_smul]
      rw [inner_kq ω η hω₀, R.inner_W_Ω, qfKer_eq_fockGram ω η e hω hη])
    (by
      rw [show LinearMap.range (qfPhi ω η) = Submodule.span ℂ (Set.range (kq ω η)) from
        Finsupp.range_linearCombination _]
      have := qfVac_cyclic ω η hω₀
      simpa [qfW_vac] using this)
    hd₂
  refine ⟨U, fun g ψ => ?_⟩
  have key : ∀ c, Φ₂ (qfTau ω g c) = R.W (e g) (Φ₂ c) := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single f s =>
      have h1 : (Finsupp.single f s : V →₀ ℂ) = s • Finsupp.single f 1 := by simp
      rw [h1, map_smul, map_smul, map_smul, map_smul, qfTau_single, map_smul]
      simp only [Φ₂, Finsupp.linearCombination_single, one_smul]
      rw [R.weyl, qfPhase, hω, map_add, add_comm (e f) (e g)]
  have hc1 : Continuous fun x : QFSpace ω η => U (qfW ω η hω₀ g x) :=
    U.continuous.comp (qfW ω η hω₀ g).continuous
  have hc2 : Continuous fun x : QFSpace ω η => R.W (e g) (U x) :=
    (R.W (e g)).continuous.comp U.continuous
  have := Continuous.ext_on (dense_range_qfPhi ω η) hc1 hc2 (fun x hx => by
    obtain ⟨c, rfl⟩ := hx
    simp only [qfW_phi, hU, key])
  exact congrFun this ψ

/-- **A quasi-free state whose covariance is the real part of a complex inner product is pure**: if
`ω = Im⟨e ·, e ·⟩` and `η = Re⟨e ·, e ·⟩` for a surjective additive map `e` onto a complex inner product space, then the
GNS representation of `ω_η` is irreducible and `ω_η` is a pure state (sufficiency half of the purity criterion). -/
theorem isPureState_qfState_of_equiv (hω₀ : ∀ a b, ω a b = -ω b a) (e : V →+ h) (he : Function.Surjective e)
    (hω : ∀ a b, ω a b = symp h (e a) (e b)) (hη : ∀ a b, η a b = (⟪e a, e b⟫_ℂ).re) :
    IsPureState (qfState ω η hω₀) := by
  obtain ⟨U, hU⟩ := exists_unitary_qf_fock ω η hω₀ e he hω hη
  refine isPureState_qfState ω η hω₀ fun T hT => ?_
  set R := fockRepOf h with hR
  let C : FockSpace h →L[ℂ] FockSpace h :=
    (U : QFSpace ω η →L[ℂ] FockSpace h).comp (T.comp (U.symm : FockSpace h →L[ℂ] QFSpace ω η))
  have hC : ∀ f ψ, C (R.W f ψ) = R.W f (C ψ) := by
    intro f ψ
    obtain ⟨g, rfl⟩ := he f
    have h1 : U.symm (R.W (e g) ψ) = qfW ω η hω₀ g (U.symm ψ) := by
      apply U.injective
      rw [hU]; simp
    have h2 : T (qfW ω η hω₀ g (U.symm ψ)) = qfW ω η hω₀ g (T (U.symm ψ)) := by
      have := congrArg (fun S => S (U.symm ψ)) (hT g)
      simpa [qfOp] using this
    show U (T (U.symm (R.W (e g) ψ))) = R.W (e g) (U (T (U.symm ψ)))
    rw [h1, h2, hU]
  obtain ⟨c, hc⟩ := commutant_scalar R C hC
  refine ⟨c, ContinuousLinearMap.ext fun x => ?_⟩
  have := hc (U x)
  change U (T (U.symm (U x))) = c • U x at this
  have h3 := congrArg U.symm this
  rw [LinearIsometryEquiv.symm_apply_apply, map_smul, LinearIsometryEquiv.symm_apply_apply] at h3
  exact h3

end Lightlike.OperatorAlgebras.QuasiFreeState
