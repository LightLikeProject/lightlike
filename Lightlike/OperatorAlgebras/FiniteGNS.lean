import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
/-!
# The GNS representation of a faithful state on a matrix algebra

Jakšić, Ogata, Pautrat and Pillet, arXiv:1106.3786, Exercise 2.15, p. 61 (read): for a state `ν` on `O = B(K)`, the GNS space `H_ν`
carries the inner product `(ξ|η)_ν = tr(η ν ξ*)`, `π_ν(A) ξ = A ξ` is a representation, the vector `η_ν` is cyclic and
`ν(A) = (η_ν|π_ν(A) η_ν)`. For a faithful `ν` (`ν` positive definite), `H_ν` is the space of all matrices and `η_ν = 1`.

Here `GNSMat ν` is `Matrix n n ℂ` with Mathlib's inner product `⟪ξ, η⟫ = tr(η ν ξᴴ)` (`Matrix.toMatrixInnerProductSpace`), `gnsRep ν A`
is left multiplication by `A`, and `gnsVec ν = 1`: `gnsRep_star` (a `*`-representation), `inner_gnsVec_gnsRep` (`ν(A) = tr(ν A)`),
`gnsRep_gnsVec_surjective` (cyclic).
-/

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The GNS space of a faithful state `ν` on `Matrix n n ℂ`: a type synonym of `Matrix n n ℂ`. -/
def GNSMat (_ν : Matrix n n ℂ) : Type _ := Matrix n n ℂ

namespace GNSMat

variable (ν : Matrix n n ℂ) [hν : Fact ν.PosDef]

noncomputable instance : NormedAddCommGroup (GNSMat ν) := ν.toMatrixNormedAddCommGroup hν.out

noncomputable instance : InnerProductSpace ℂ (GNSMat ν) := ν.toMatrixInnerProductSpace hν.out.posSemidef

instance : FiniteDimensional ℂ (GNSMat ν) := inferInstanceAs (FiniteDimensional ℂ (Matrix n n ℂ))

/-- The identification of `Matrix n n ℂ` with the GNS space. -/
def toGNS : Matrix n n ℂ ≃ₗ[ℂ] GNSMat ν := LinearEquiv.refl ℂ _

/-- **The GNS inner product** (Exercise 2.15): `⟪ξ, η⟫ = tr(η ν ξᴴ)`. -/
lemma inner_toGNS (ξ η : Matrix n n ℂ) : ⟪toGNS ν ξ, toGNS ν η⟫_ℂ = (η * ν * ξᴴ).trace := rfl

end GNSMat

open GNSMat

variable (ν : Matrix n n ℂ) [Fact ν.PosDef]

/-- **The GNS representation** `π_ν(A) ξ = A ξ`. -/
noncomputable def gnsRep (A : Matrix n n ℂ) : GNSMat ν →ₗ[ℂ] GNSMat ν where
  toFun ξ := toGNS ν (A * (toGNS ν).symm ξ)
  map_add' ξ η := by simp [Matrix.mul_add]
  map_smul' c ξ := by simp [Matrix.mul_smul]

lemma gnsRep_toGNS (A ξ : Matrix n n ℂ) : gnsRep ν A (toGNS ν ξ) = toGNS ν (A * ξ) := rfl

/-- `π_ν` is multiplicative and unital. -/
lemma gnsRep_mul (A B : Matrix n n ℂ) : gnsRep ν (A * B) = gnsRep ν A ∘ₗ gnsRep ν B := by
  ext ξ
  show toGNS ν (A * B * (toGNS ν).symm ξ) = toGNS ν (A * (B * (toGNS ν).symm ξ))
  rw [Matrix.mul_assoc]

lemma gnsRep_one : gnsRep ν 1 = LinearMap.id := by
  ext ξ
  show toGNS ν (1 * (toGNS ν).symm ξ) = ξ
  rw [Matrix.one_mul]
  rfl

/-- **`π_ν` is a `*`-representation**: `⟪π(A) ξ, η⟫ = ⟪ξ, π(Aᴴ) η⟫`. -/
lemma gnsRep_star (A ξ η : Matrix n n ℂ) :
    ⟪gnsRep ν A (toGNS ν ξ), toGNS ν η⟫_ℂ = ⟪toGNS ν ξ, gnsRep ν Aᴴ (toGNS ν η)⟫_ℂ := by
  rw [gnsRep_toGNS, gnsRep_toGNS, inner_toGNS, inner_toGNS, conjTranspose_mul, ← Matrix.mul_assoc,
    trace_mul_comm (η * ν * ξᴴ) Aᴴ]
  simp only [Matrix.mul_assoc]

/-- The cyclic vector `η_ν = 1`. -/
def gnsVec : GNSMat ν := toGNS ν 1

/-- **The state is the vector state of `η_ν`** (Exercise 2.15 (2)): `⟪η_ν, π_ν(A) η_ν⟫ = tr(ν A)`. -/
theorem inner_gnsVec_gnsRep (A : Matrix n n ℂ) : ⟪gnsVec ν, gnsRep ν A (gnsVec ν)⟫_ℂ = (ν * A).trace := by
  rw [gnsVec, gnsRep_toGNS, inner_toGNS, conjTranspose_one, Matrix.mul_one, Matrix.mul_one, trace_mul_comm]

/-- **`η_ν` is cyclic** (Exercise 2.15 (2)): every vector is `π_ν(A) η_ν` for some `A`. -/
theorem gnsRep_gnsVec_surjective : Function.Surjective fun A : Matrix n n ℂ => gnsRep ν A (gnsVec ν) := by
  intro ξ
  refine ⟨(toGNS ν).symm ξ, ?_⟩
  show toGNS ν ((toGNS ν).symm ξ * 1) = ξ
  rw [Matrix.mul_one]
  exact (toGNS ν).apply_symm_apply ξ

end Lightlike.OperatorAlgebras
