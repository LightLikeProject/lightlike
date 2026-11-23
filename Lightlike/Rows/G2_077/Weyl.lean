import Lightlike.Rows.G2_077.Fock2
import Lightlike.OperatorAlgebras.FockExists

/-!
# Weyl unitaries of the Sorkin–Johnston state

On the Fock space over the one-particle space `h = oneParticle Δ` we define the Weyl unitaries
`sjW Δ f = W (K f)` for `f : ι → ℝ`.  They satisfy the Weyl relation
`sjW f ∘ sjW g = exp(-i (fᵀ Δ g)/2) • sjW (f + g)` (`sjW_weyl`) and the vacuum expectation is
`exp(-qform Δ f / 2)` (`sjW_expectation`).
-/

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder InnerProductSpace Matrix

namespace Lightlike.Rows.G2_077

open Lightlike.OperatorAlgebras

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-particle vector `K f` as an element of the one-particle space `oneParticle Δ`. -/
noncomputable def kvH (Δ : Matrix ι ι ℝ) (f : ι → ℝ) : oneParticle Δ :=
  ⟨kv Δ f, kv_mem_range Δ f⟩

lemma kvH_add (Δ : Matrix ι ι ℝ) (f g : ι → ℝ) : kvH Δ (f + g) = kvH Δ f + kvH Δ g :=
  Subtype.ext (kv_add Δ f g)

/-- The Weyl unitary `W(K f)` of the Sorkin–Johnston state, in the Fock representation over
`oneParticle Δ`. -/
noncomputable def sjW (Δ : Matrix ι ι ℝ) (f : ι → ℝ) :
    FockSpace (oneParticle Δ) ≃ₗᵢ[ℂ] FockSpace (oneParticle Δ) :=
  (fockRepOf (oneParticle Δ)).W (kvH Δ f)

/-- **Weyl relation** for `sjW`. -/
theorem sjW_weyl {Δ : Matrix ι ι ℝ} (h : Δ.transpose = -Δ) (f g : ι → ℝ)
    (ψ : FockSpace (oneParticle Δ)) :
    sjW Δ f (sjW Δ g ψ) =
      Complex.exp (-(Complex.I * ((f ⬝ᵥ Δ.mulVec g) / 2 : ℝ))) • sjW Δ (f + g) ψ := by
  unfold sjW
  rw [(fockRepOf (oneParticle Δ)).weyl, ← kvH_add]
  have : symp (oneParticle Δ) (kvH Δ f) (kvH Δ g) = f ⬝ᵥ Δ.mulVec g := by
    rw [symp]
    have := inner_kv_im h f g
    simpa [kvH] using this
  rw [this]

/-- **Vacuum expectation**: `⟪Ω, sjW f Ω⟫ = exp(-qform Δ f / 2)`. -/
theorem sjW_expectation (Δ : Matrix ι ι ℝ) (f : ι → ℝ) :
    ⟪(fockRepOf (oneParticle Δ)).Ω, sjW Δ f (fockRepOf (oneParticle Δ)).Ω⟫_ℂ =
      Complex.exp (-(qform Δ f / 2 : ℝ)) := by
  unfold sjW
  rw [(fockRepOf (oneParticle Δ)).vacuum_expectation]
  have : ‖kvH Δ f‖ ^ 2 = 2 * qform Δ f := by
    rw [← norm_kv_sq Δ f]; rfl
  have h2 : ‖kvH Δ f‖ ^ 2 / 4 = qform Δ f / 2 := by rw [this]; ring
  rw [h2]

end Lightlike.Rows.G2_077
