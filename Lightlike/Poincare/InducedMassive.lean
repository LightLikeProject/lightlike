module

public import Lightlike.Poincare.WignerRotation

/-!
# The induced massive representations: the group law

For `m > 0` and a unitary matrix representation `D` of `SU(2)` (for instance the spin representation
`Lightlike.SU2.spinRep n` of spin `n/2`), the universal cover `SL(2,ℂ)` of the restricted Lorentz group acts on wave
functions `ψ : MassShell m → ℂ^ι` by `(U(A) ψ)(P) = D(W(A, A⁻¹ • P)) ψ(A⁻¹ • P)` with the Wigner rotation `W`
(`inducedAct`); this is an action (`inducedAct_mul`, `inducedAct_one`) because of the cocycle identity. The
translations act by the phases `e^{i⟨P, X⟩}` of the Minkowski pairing `⟨P, X⟩ = (det(P + X) − det P − det X)/2`
(`transAct`), and `U(A) T(X) = T(A • X) U(A)` (`inducedAct_transAct`): the relation of the semidirect product
`ℝ^{1,3} ⋊ SL(2,ℂ)`. Unitarity on `L²` of the invariant measure on the mass shell is a separate step.

**Difference from the source (kind: representation).** Bekaert–Boulanger write the standard boost, the little
group and the Wigner rotation for `Λ ∈ SO(D−1,1)↑` acting on `ℝ^{D−1,1}` (§3.1, equations (10)–(13); §3.2); here
they are stated for the universal cover `SL(2,ℂ) ≅ Spin(3,1)` acting on Hermitian `2 × 2` momenta, which is how
§1.1 (page 3) says the representations are meant ("a single (or double) valued representation of `SO(D−1,1)↑` is
meant to be a genuine representation of `Spin(D−1,1)`"). The `SO(3,1)↑` form is not derived from this file.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1, equation (13) (page 10 of v2): `U(Λ) Ψ_{p,σ} = (N(p)/N(Λp)) Σ_{σ'} D_{σ'σ}(W(Λ,p)) Ψ_{Λp,σ'}`;
  here in the wave-function form, without the normalisation `N`.
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz

namespace Lightlike.Poincare

/-! ## The induced action on wave functions -/

/-- The Wigner rotation as an element of `SU(2)`. -/
def wignerSU2 {m : ℝ} (hm : 0 < m) (A : SL2C) (P : MassShell m) : Lightlike.SU2 :=
  ⟨(wigner hm A P : Matrix (Fin 2) (Fin 2) ℂ), wigner_mem_specialUnitaryGroup hm A P⟩

lemma wignerSU2_mul {m : ℝ} (hm : 0 < m) (A' A : SL2C) (P : MassShell m) :
    wignerSU2 hm (A' * A) P = wignerSU2 hm A' (shellAct A P) * wignerSU2 hm A P := by
  apply Subtype.ext
  simp only [wignerSU2, wigner_mul hm A' A P]
  rfl

/-- **The induced massive action** of `SL(2,ℂ)` on wave functions `ψ : MassShell m → ℂ^ι`, for a unitary
representation `D` of `SU(2)`: `(U(A) ψ)(P) = D(W(A, A⁻¹ • P)) ψ(A⁻¹ • P)`. -/
def inducedAct {m : ℝ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Lightlike.SU2 →* Matrix.unitaryGroup ι ℂ) (A : SL2C) (ψ : MassShell m → ι → ℂ) :
    MassShell m → ι → ℂ :=
  fun P => ((D (wignerSU2 hm A (shellAct A⁻¹ P)) : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ
    ψ (shellAct A⁻¹ P)

/-- **The induced action is an action** (cocycle identity). -/
theorem inducedAct_mul {m : ℝ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Lightlike.SU2 →* Matrix.unitaryGroup ι ℂ) (A' A : SL2C) (ψ : MassShell m → ι → ℂ) :
    inducedAct hm D (A' * A) ψ = inducedAct hm D A' (inducedAct hm D A ψ) := by
  funext P
  simp only [inducedAct]
  have h1 : shellAct (A' * A)⁻¹ P = shellAct A⁻¹ (shellAct A'⁻¹ P) := by
    rw [_root_.mul_inv_rev, shellAct_mul]
  have h2 : shellAct A (shellAct A⁻¹ (shellAct A'⁻¹ P)) = shellAct A'⁻¹ P := by
    rw [← shellAct_mul, mul_inv_cancel, shellAct_one]
  rw [h1, wignerSU2_mul, h2, map_mul, Matrix.mulVec_mulVec]
  rfl

lemma wigner_one {m : ℝ} (hm : 0 < m) (Q : MassShell m) : wigner hm 1 Q = 1 := by
  rw [wigner, shellAct_one, mul_one, inv_mul_cancel]

lemma wignerSU2_one {m : ℝ} (hm : 0 < m) (Q : MassShell m) : wignerSU2 hm 1 Q = 1 := by
  apply Subtype.ext
  simp [wignerSU2, wigner_one]

theorem inducedAct_one {m : ℝ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Lightlike.SU2 →* Matrix.unitaryGroup ι ℂ) (ψ : MassShell m → ι → ℂ) :
    inducedAct hm D 1 ψ = ψ := by
  funext P
  simp only [inducedAct, wignerSU2_one, map_one, inv_one, shellAct_one]
  simp

/-! ## Translations -/

/-- The Minkowski pairing of Hermitian matrices, by polarisation of the determinant:
`⟨P, X⟩ = (det(P + X) − det P − det X)/2`. For `P = p⁰ + p·σ`, `X = x⁰ + x·σ` it is `p⁰x⁰ − p·x`. -/
def mink (P X : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ((P + X).det - P.det - X.det) / 2

lemma actP_add (A : SL2C) (P X : Matrix (Fin 2) (Fin 2) ℂ) : actP A (P + X) = actP A P + actP A X := by
  simp [actP, Matrix.mul_add, Matrix.add_mul]

/-- The pairing is `SL(2,ℂ)`-invariant. -/
lemma mink_actP (A : SL2C) (P X : Matrix (Fin 2) (Fin 2) ℂ) : mink (actP A P) (actP A X) = mink P X := by
  simp only [mink, ← actP_add, det_actP]

/-- The translations act by the phases `e^{i⟨P, X⟩}`. -/
def transAct {m : ℝ} {ι : Type} (X : Matrix (Fin 2) (Fin 2) ℂ) (ψ : MassShell m → ι → ℂ) :
    MassShell m → ι → ℂ :=
  fun P => Complex.exp (Complex.I * mink P.1 X) • ψ P

/-- **Covariance**: `U(A) T(X) U(A)⁻¹ = T(A • X)`, the semidirect-product relation of the Poincaré group. -/
theorem inducedAct_transAct {m : ℝ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Lightlike.SU2 →* Matrix.unitaryGroup ι ℂ) (A : SL2C) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : MassShell m → ι → ℂ) :
    inducedAct hm D A (transAct X ψ) = transAct (actP A X) (inducedAct hm D A ψ) := by
  funext P
  simp only [inducedAct, transAct, Matrix.mulVec_smul]
  congr 2
  have h : actP A (shellAct A⁻¹ P).1 = P.1 := by
    show actP A (actP A⁻¹ P.1) = P.1
    rw [← actP_mul, mul_inv_cancel, actP_one]
  rw [← mink_actP A, h]

end Lightlike.Poincare
