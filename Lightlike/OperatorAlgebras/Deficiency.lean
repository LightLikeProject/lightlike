import Lightlike.OperatorAlgebras.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Deficiency indices

For an operator `A : H →ₗ.[ℂ] H` with dense domain the deficiency spaces are the kernels of `A† - z` at
`z = ± i`, in terms of Mathlib's adjoint `A†`; `deficiencySpace A z = {ψ ∈ dom A† | A† ψ = z ψ}` and the
deficiency indices are their dimensions (`deficiencyDim`, a cardinal, so that no junk value appears for an
infinite dimension). For an operator without dense domain Mathlib's adjoint is the zero map, so the
deficiency indices are meaningful only for densely defined operators.

Trust check: a self-adjoint operator has no eigenvalue off the real axis, so both deficiency indices are
`0` (`deficiencyDim_of_isSelfAdjoint`).
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The deficiency space** of `A` at `z`: the vectors `ψ` of the domain of the adjoint `A†` with
`A† ψ = z ψ`. -/
def deficiencySpace (A : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H where
  carrier := {ψ | ∃ h : ψ ∈ (A†).domain, (A†) ⟨ψ, h⟩ = z • ψ}
  add_mem' := by
    rintro a b ⟨ha, hae⟩ ⟨hb, hbe⟩
    refine ⟨(A†).domain.add_mem ha hb, ?_⟩
    have : (⟨a + b, (A†).domain.add_mem ha hb⟩ : (A†).domain) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    change (A†).toFun ⟨a + b, _⟩ = _
    rw [this, (A†).toFun.map_add]
    change (A†) ⟨a, ha⟩ + (A†) ⟨b, hb⟩ = _
    rw [hae, hbe, smul_add]
  zero_mem' := ⟨(A†).domain.zero_mem, by
    have : (⟨0, (A†).domain.zero_mem⟩ : (A†).domain) = 0 := rfl
    change (A†).toFun ⟨0, _⟩ = _
    rw [this, (A†).toFun.map_zero, smul_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha, hae⟩
    refine ⟨(A†).domain.smul_mem c ha, ?_⟩
    have : (⟨c • a, (A†).domain.smul_mem c ha⟩ : (A†).domain) = c • ⟨a, ha⟩ := rfl
    change (A†).toFun ⟨c • a, _⟩ = _
    rw [this, (A†).toFun.map_smul]
    change c • (A†) ⟨a, ha⟩ = _
    rw [hae, smul_comm]

/-- **A deficiency index** of `A` at `z`: the dimension (a cardinal) of the deficiency space. The
deficiency indices of the milestone are `deficiencyDim A I` and `deficiencyDim A (-I)`. -/
noncomputable def deficiencyDim (A : H →ₗ.[ℂ] H) (z : ℂ) : Cardinal :=
  Module.rank ℂ (deficiencySpace A z)

omit [CompleteSpace H] in
/-- Equal partial maps agree on vectors that agree. -/
private lemma pmap_congr {B C : H →ₗ.[ℂ] H} (h : B = C) (x : B.domain) (y : C.domain)
    (hxy : (x : H) = y) : B x = C y := by
  subst h
  congr
  exact Subtype.ext hxy

/-- **Trust check**: a self-adjoint operator has no deficiency at a non-real `z`. -/
theorem deficiencySpace_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : deficiencySpace A z = ⊥ := by
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hAA : A† = A := hA
  have hform : A.IsFormalAdjoint A := by
    have := LinearPMap.adjoint_isFormalAdjoint hdense
    rwa [hAA] at this
  rw [Submodule.eq_bot_iff]
  rintro ψ ⟨h, he⟩
  have hd : ψ ∈ A.domain := hAA ▸ h
  have e1 : A ⟨ψ, hd⟩ = z • ψ := by
    rw [← he]
    exact (pmap_congr hAA ⟨ψ, h⟩ ⟨ψ, hd⟩ rfl).symm
  have h2 := hform ⟨ψ, hd⟩ ⟨ψ, hd⟩
  rw [e1, inner_smul_left, inner_smul_right] at h2
  have h3 : (starRingEnd ℂ z - z) * (⟪ψ, ψ⟫_ℂ) = 0 := by rw [sub_mul, h2]; ring
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exfalso
    apply hz
    have := congrArg Complex.im h4
    simp at this
    linarith
  · exact inner_self_eq_zero.mp h4

/-- **Trust check**: both deficiency indices of a self-adjoint operator are `0`. -/
theorem deficiencyDim_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : deficiencyDim A z = 0 := by
  unfold deficiencyDim
  rw [deficiencySpace_of_isSelfAdjoint hA hz]
  exact rank_bot ℂ H

end Lightlike.OperatorAlgebras
