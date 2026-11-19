import Lightlike.NCG.FiniteSpectralTriple
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The two-point space `ℂ ⊕ ℂ` on `ℂ²`

The algebra `ℂ² = ℂ ⊕ ℂ` acts on `H = ℂ²` diagonally, `π(a) = diag(a₀, a₁)`, and `J` is the complex conjugation. Then
`J π(b) J = π(b̄)`, and for an operator `D` with matrix `(Dᵢⱼ)` the first-order condition `[[D, π(a)], J π(b) J] = 0`
holds for all `a`, `b` exactly when `D` is diagonal: `[[D, π(a)], π(c)]ᵢⱼ = Dᵢⱼ (aⱼ - aᵢ)(cⱼ - cᵢ)`. So the
off-diagonal `D = σₓ`, which would join the two points, is rejected (Paschke-Sitarz, arXiv:q-alg/9612029, Lemma 6,
p. 5: `Dᵢⱼ,ₖₗ = 0` unless `i = k` or `j = l`; here `H = H₀₀ ⊕ H₁₁`).

* `diagStar`, `pi2`, `conjJ`, `conjJ_pi2_conjJ`;
* `firstOrder_iff`: the first-order condition for `(pi2, conjJ, D)` holds iff `D₀₁ = D₁₀ = 0`;
* `not_firstOrder_sigmaX`.
-/

open Matrix WithLp

namespace Lightlike.NCG.TwoPoint

/-- The Hilbert space `ℂ²`. -/
abbrev H2 := EuclideanSpace ℂ (Fin 2)

/-- `diag : ℂ² → M₂(ℂ)` as a `*`-algebra homomorphism. -/
noncomputable def diagStar : (Fin 2 → ℂ) →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  { Matrix.diagonalAlgHom (R := ℂ) with
    map_star' := fun a => by
      show diagonal (star a) = star (diagonal a)
      rw [star_eq_conjTranspose, diagonal_conjTranspose] }

/-- **The diagonal representation** `π(a) = diag(a₀, a₁)` of `ℂ²` on `ℂ²`. -/
noncomputable def pi2 : (Fin 2 → ℂ) →⋆ₐ[ℂ] (H2 →L[ℂ] H2) :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).toStarAlgHom.comp diagStar

lemma pi2_eq (a : Fin 2 → ℂ) : pi2 a = Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diagonal a) := rfl

lemma injective_pi2 : Function.Injective pi2 := fun a b h => by
  rw [pi2_eq, pi2_eq] at h
  exact diagonal_injective ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).injective h)

/-- **The complex conjugation** `J x = x̄` on `ℂ²`, an antilinear map. -/
noncomputable def conjJ : H2 →ₗ⋆[ℂ] H2 where
  toFun x := toLp 2 (fun i => star (x i))
  map_add' x y := by
    ext i
    simp [star_add]
  map_smul' c x := by
    ext i
    simp [mul_comm]

lemma conjJ_apply (x : H2) (i : Fin 2) : conjJ x i = star (x i) := rfl

/-- `J π(b) J = π(b̄)`. -/
lemma conjJ_pi2_conjJ (b : Fin 2 → ℂ) (x : H2) : conjJ (pi2 b (conjJ x)) = pi2 (star b) x := by
  ext i
  simp [conjJ_apply, pi2_eq, mulVec_diagonal]

/-- The commutator `[[D, diag a], diag c]` of matrices. -/
def dcomm (D : Matrix (Fin 2) (Fin 2) ℂ) (a c : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (D * diagonal a - diagonal a * D) * diagonal c - diagonal c * (D * diagonal a - diagonal a * D)

/-- `[[D, diag a], diag c] = 0` for all `a`, `c` iff `D` is diagonal. -/
lemma dcomm_eq_zero_iff (D : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ a c, dcomm D a c = 0) ↔ D 0 1 = 0 ∧ D 1 0 = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun (h ![1, 0] ![1, 0]) 0) 1
    have h10 := congrFun (congrFun (h ![1, 0] ![1, 0]) 1) 0
    simp [dcomm, mul_apply, Fin.sum_univ_two, sub_mul, mul_sub] at h01 h10
    exact ⟨by linear_combination h01, by linear_combination h10⟩
  · rintro ⟨h01, h10⟩ a c
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dcomm, mul_apply, Fin.sum_univ_two, h01, h10] <;> ring

/-- **The first-order condition on the two-point space** (`π = pi2`, `J = conjJ`): it holds iff `D` is diagonal. -/
theorem firstOrder_iff (D : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ a b x, FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) D) (pi2 a)
        (conjJ (pi2 b (conjJ x))) =
      conjJ (pi2 b (conjJ (FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) D) (pi2 a) x)))) ↔
      D 0 1 = 0 ∧ D 1 0 = 0 := by
  rw [← dcomm_eq_zero_iff]
  have key : ∀ a c, FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) D) (pi2 a) * pi2 c -
      pi2 c * FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) D) (pi2 a) =
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (dcomm D a c) := by
    intro a c
    simp only [FiniteSpectralTriple.comm, pi2_eq, dcomm, map_sub, map_mul]
  simp only [conjJ_pi2_conjJ]
  constructor
  · intro h a c
    have h0 : FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) D) (pi2 a) * pi2 c -
        pi2 c * FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) D) (pi2 a) = 0 := by
      ext1 x
      have := h a (star c) x
      rw [star_star] at this
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, this,
        sub_self]
    rw [key] at h0
    exact (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).injective (h0.trans (map_zero _).symm)
  · intro h a b x
    have hk := key a (star b)
    rw [h, map_zero] at hk
    have := congrArg (fun T : H2 →L[ℂ] H2 => T x) hk
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] at this
    exact sub_eq_zero.mp this

/-- **The two-point space as a finite spectral triple** `(ℂ², ℂ², D)` for a self-adjoint `D`. -/
noncomputable def twoPoint (D : H2 →L[ℂ] H2) (hD : IsSelfAdjoint D) : FiniteSpectralTriple (Fin 2 → ℂ) H2 where
  π := { (pi2 : (Fin 2 → ℂ) →ₐ[ℂ] (H2 →L[ℂ] H2)).restrictScalars ℝ with map_star' := pi2.map_star' }
  injective_π := injective_pi2
  D := D
  isSelfAdjoint_D := hD

/-- `σₓ = [[0, 1], [1, 0]]`. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- **`D = σₓ` violates the first-order condition** on the two-point space with `J` the complex conjugation. -/
theorem not_firstOrder_sigmaX :
    ¬ ∀ a b x, FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) sigmaX) (pi2 a)
        (conjJ (pi2 b (conjJ x))) =
      conjJ (pi2 b (conjJ (FiniteSpectralTriple.comm (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) sigmaX)
        (pi2 a) x))) := by
  rw [firstOrder_iff]
  simp [sigmaX]

end Lightlike.NCG.TwoPoint
