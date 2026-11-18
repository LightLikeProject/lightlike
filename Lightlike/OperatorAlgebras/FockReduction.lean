import Lightlike.OperatorAlgebras.FockExists
import Lightlike.OperatorAlgebras.GramUnitary

/-!
# The cyclic-vector reduction of Shale's criterion

Helper lemmas for `T-OP2-P5` (`Tasks/OP/T_OP2_P5.lean`): a Bogoliubov transformation `T` is implemented in a
Fock representation iff there is a vector `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)` for all `f`.

`⇒`: `Ψ = U⁻¹ Ω`. `⇐`: the vectors `W f Ψ` and `W (T f) Ω` have the same Gram matrix (the transformation preserves
the symplectic form), `Ψ` is cyclic by the irreducibility (`fockRep_cyclic`), and the Gram unitary
(`exists_unitary_of_gram_eq`) intertwines the Weyl operators.
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **`⇒`**: an implementing unitary gives a vector with Gaussian characteristic function. -/
lemma gaussian_vector_of_implements (R : FockRep h K) (T : Bogoliubov h)
    (hT : Implements R.toCCRRep T) :
    ∃ Ψ : K, ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ)) := by
  obtain ⟨U, hU⟩ := hT
  refine ⟨U.symm R.Ω, fun f => ?_⟩
  have h1 : R.W f (U.symm R.Ω) = U.symm (R.W (T.toEquiv f) R.Ω) := by
    apply U.injective
    rw [hU, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [h1, LinearIsometryEquiv.inner_map_map, R.vacuum_expectation]

lemma symp_neg_left (f g : h) : symp h (-f) g = -symp h f g := by simp [symp, inner_neg_left]

/-- **The Gram matrix of the vectors `W f Ψ`** equals that of `W (T f) Ω`, given the Gaussian characteristic
function of `Ψ`. -/
lemma gram_gaussian_vector (R : FockRep h K) (T : Bogoliubov h) {Ψ : K}
    (hΨ : ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ))) (f g : h) :
    ⟪R.W f Ψ, R.W g Ψ⟫_ℂ = ⟪R.W (T.toEquiv f) R.Ω, R.W (T.toEquiv g) R.Ω⟫_ℂ := by
  rw [R.inner_W_Ω]
  have h1 : ⟪R.W f Ψ, R.W g Ψ⟫_ℂ = ⟪Ψ, R.W (-f) (R.W g Ψ)⟫_ℂ := by
    rw [← (R.W (-f)).inner_map_map, R.toCCRRep.W_neg_W]
  rw [h1, R.weyl, inner_smul_right, hΨ]
  unfold fockGram
  have e1 : T.toEquiv (-f + g) = -T.toEquiv f + T.toEquiv g := by
    rw [map_add, map_neg]
  have e2 : symp h (-T.toEquiv f) (T.toEquiv g) = symp h (-f) g := by
    rw [symp_neg_left, symp_neg_left, T.symp_map]
  rw [e1, e2]

end Lightlike.OperatorAlgebras
