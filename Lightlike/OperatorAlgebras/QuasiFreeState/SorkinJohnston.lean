import Lightlike.OperatorAlgebras.QuasiFreeState.PauliJordan
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The Sorkin-Johnston state of a finite causal set is pure (CS7)

For a finite causal set `(C, ≺)` with causal matrix `C_xy = 1` if `x ≺ y` and `0` otherwise, and a retarded propagator
`K_R = a C` (Johnston, arXiv:0909.0944, eq. (16), the massless case in `M²`, `a = 1/2`; here `a` is any real number), the
Pauli-Jordan matrix is `iΔ` with `Δ = K_R - K_Aᵀ`, `K_A = K_Rᵀ` (eq. (10)): `Δ = a (C - Cᵀ)`, real and antisymmetric. The
field operators satisfy `[φ_x, φ_y] = i Δ_xy` (eq. (22)); the Sorkin-Johnston two-point function is `Q = Pos(iΔ)`
(eq. (20); `iΔ = Q - Qᵀ`, `Im Q = Δ/2`), so its real part is `η/2` for the covariance `η = |iΔ| = (-Δ²)^{1/2}` and the state
is the quasi-free state with `ω = Δ`, `η = |iΔ|` in the conventions of `QuasiFreeState` (two-point function
`½ (η + iω)`).

Results: `|iΔ|` exists for every real antisymmetric matrix (`exists_pjData`, the positive square root of `-D²` by the
continuous functional calculus, which commutes with `D`), and the Sorkin-Johnston state of every finite causal set is
pure (`isPureState_causalSet`), by `isPureState_pauliJordan`.

Not claimed: the coefficient `a` of the four-dimensional retarded matrix `K_R = a L (1 - a b L)⁻¹` (with the link
matrix `L`) and the massive two-dimensional case, which are other antisymmetric matrices and are covered by
`isPureState_pauliJordan` once `Δ = K_R - K_Rᵀ` is given. The second source named in the milestone line,
arXiv:1205.7062, is a different paper (an eigenvalue-statistics paper); the Afshordi-Aslanbeigi-Sorkin paper was not read.
-/

set_option linter.unusedSectionVars false

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Matrix

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **`|iD|` exists**: for a real antisymmetric `D` there is a symmetric positive semidefinite `H` with `H² = -D²`
commuting with `D` (the positive square root of `-D² = Dᵀ D`). -/
theorem exists_pjData (D : Matrix ι ι ℝ) (hD : Dᵀ = -D) : ∃ H, PJData D H := by
  have hA : (0 : Matrix ι ι ℝ) ≤ -(D * D) := by
    rw [Matrix.nonneg_iff_posSemidef]
    have := Matrix.posSemidef_conjTranspose_mul_self D
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, hD, neg_mul] at this
  refine ⟨CFC.sqrt (-(D * D)), hD, (CFC.sqrt_nonneg _).posSemidef, CFC.sqrt_mul_sqrt_self _ hA, ?_⟩
  have hc : Commute (-(D * D)) D := by
    simp [Commute, SemiconjBy, mul_assoc]
  have h2 : Commute (CFC.sqrt (-(D * D))) D := by
    rw [CFC.sqrt_eq_real_sqrt _ hA, cfcₙ_eq_cfc (f := Real.sqrt) Real.continuous_sqrt.continuousOn Real.sqrt_zero]
    exact hc.cfc_real _
  exact h2

section CausalSet

variable (α : Type u) [PartialOrder α] [Fintype α] [DecidableEq α] [DecidableRel ((· < ·) : α → α → Prop)]

/-- **The causal matrix** `C_xy = 1` if `x ≺ y` and `0` otherwise (Johnston, arXiv:0909.0944, eq. (1)). -/
def causalMatrix : Matrix α α ℝ := Matrix.of fun x y => if x < y then 1 else 0

/-- **The Pauli-Jordan matrix** `Δ = K_R - K_Rᵀ` for the retarded propagator `K_R = a C` (arXiv:0909.0944, eqs. (10)
and (16), the massless case in `M²` for `a = 1/2`). -/
def pauliJordanMatrix (a : ℝ) : Matrix α α ℝ := a • (causalMatrix α - (causalMatrix α)ᵀ)

/-- The Pauli-Jordan matrix is antisymmetric. -/
lemma pauliJordanMatrix_anti (a : ℝ) : (pauliJordanMatrix α a)ᵀ = -pauliJordanMatrix α a := by
  simp [pauliJordanMatrix, Matrix.transpose_sub, Matrix.transpose_smul, smul_sub, neg_sub]

/-- **The Sorkin-Johnston state of a finite causal set is pure** (CS7): for every finite causal set and every
coefficient `a` of the retarded matrix `K_R = a C`, there is `H = |iΔ|` (symmetric, positive semidefinite, `H² = -Δ²`,
commuting with `Δ`) such that the quasi-free state with `ω = Δ`, `η = H` (two-point function `Pos(iΔ) = ½ (H + iΔ)`) is
pure. -/
theorem isPureState_causalSet (a : ℝ) :
    ∃ H : Matrix α α ℝ, ∃ h : PJData (pauliJordanMatrix α a) H,
      haveI : Fact (qfKerM (pjOmega (pauliJordanMatrix α a)) (pjEta H)).PosSemidef :=
        qfFact _ _ (pj_omega_antisymm h) (pj_isCovariance h)
      IsPureState (qfState (pjOmega (pauliJordanMatrix α a)) (pjEta H) (pj_omega_antisymm h)) := by
  obtain ⟨H, h⟩ := exists_pjData (pauliJordanMatrix α a) (pauliJordanMatrix_anti α a)
  exact ⟨H, h, isPureState_pauliJordan h⟩

end CausalSet

end Lightlike.OperatorAlgebras.QuasiFreeState
