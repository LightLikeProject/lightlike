import Lightlike.OperatorAlgebras.VonNeumannDecomp

/-!
# The boundary form of the adjoint of a closed symmetric operator

For `y = x + p + q` and `y' = x' + p' + q'` in `D(A†)` (`x, x' ∈ D(A)`, `p, p' ∈ N_i`, `q, q' ∈ N_{-i}`):
`⟪A† y, y'⟫ - ⟪y, A† y'⟫ = 2 i (⟪q, q'⟫ - ⟪p, p'⟫)` (`boundary_form`). A library lemma (not in the source read), used for the self-adjoint
extensions `A_U`.
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- `⟪φ, A x⟫ = z̄ ⟪φ, x⟫` for `φ ∈ N_z`. -/
lemma inner_deficiency_apply (hA : ClosedSymm A) {z : ℂ} {φ : H} (hφ : φ ∈ deficiencySpace A z) (x : A.domain) :
    ⟪φ, (A x : H)⟫_ℂ = (starRingEnd ℂ) z * ⟪φ, (x : H)⟫_ℂ := by
  obtain ⟨hd, he⟩ := hφ
  have hfa := LinearPMap.adjoint_isFormalAdjoint hA.dense ⟨φ, hd⟩ x
  rw [← hfa, he, inner_smul_left]

/-- `⟪A x, φ⟫ = z ⟪x, φ⟫` for `φ ∈ N_z`. -/
lemma inner_apply_deficiency (hA : ClosedSymm A) {z : ℂ} {φ : H} (hφ : φ ∈ deficiencySpace A z) (x : A.domain) :
    ⟪(A x : H), φ⟫_ℂ = z * ⟪(x : H), φ⟫_ℂ := by
  rw [← inner_conj_symm, inner_deficiency_apply hA hφ x, map_mul, Complex.conj_conj, inner_conj_symm]

/-- `A† (x + p + q) = A x + i p - i q`. -/
lemma adjoint_decomp (hA : ClosedSymm A) (y : (A†).domain) (x : A.domain) {p q : H}
    (hp : p ∈ deficiencySpace A Complex.I) (hq : q ∈ deficiencySpace A (-Complex.I)) (hy : (y : H) = x + p + q) :
    (A† y : H) = A x + Complex.I • p - Complex.I • q := by
  obtain ⟨hpd, hpe⟩ := hp
  obtain ⟨hqd, hqe⟩ := hq
  have hxd : (x : H) ∈ (A†).domain := hA.le_adjoint.1 x.2
  have hAx : (A† ⟨(x : H), hxd⟩ : H) = A x := (hA.le_adjoint.2 (x := x) (y := ⟨(x : H), hxd⟩) rfl).symm
  have e1 : y = ⟨(x : H), hxd⟩ + ⟨p, hpd⟩ + ⟨q, hqd⟩ := Subtype.ext hy
  rw [e1, LinearPMap.map_add, LinearPMap.map_add, hAx, hpe, hqe, neg_smul,
    ← sub_eq_add_neg]

/-- **The boundary form**: `⟪A† y, y'⟫ - ⟪y, A† y'⟫ = 2 i (⟪q, q'⟫ - ⟪p, p'⟫)` for `y = x + p + q`, `y' = x' + p' + q'`. -/
theorem boundary_form (hA : ClosedSymm A) (y y' : (A†).domain) (x x' : A.domain) {p q p' q' : H}
    (hp : p ∈ deficiencySpace A Complex.I) (hq : q ∈ deficiencySpace A (-Complex.I))
    (hp' : p' ∈ deficiencySpace A Complex.I) (hq' : q' ∈ deficiencySpace A (-Complex.I))
    (hy : (y : H) = x + p + q) (hy' : (y' : H) = x' + p' + q') :
    ⟪(A† y : H), (y' : H)⟫_ℂ - ⟪(y : H), (A† y' : H)⟫_ℂ = 2 * Complex.I * (⟪q, q'⟫_ℂ - ⟪p, p'⟫_ℂ) := by
  rw [adjoint_decomp hA y x hp hq hy, adjoint_decomp hA y' x' hp' hq' hy', hy, hy']
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [hA.symm x x', inner_apply_deficiency hA hp' x, inner_apply_deficiency hA hq' x,
    inner_deficiency_apply hA hp x', inner_deficiency_apply hA hq x']
  simp only [Complex.conj_I, map_neg, neg_neg]
  ring

end Lightlike.OperatorAlgebras
