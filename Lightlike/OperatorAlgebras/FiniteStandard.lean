import Lightlike.OperatorAlgebras.FiniteGNS
import Mathlib.Analysis.InnerProductSpace.StandardSubspace

/-!
# The standard subspace of a faithful state on a matrix algebra

R. Longo, "Lectures on Conformal Nets, Part I", Section 2.1, p. 21-22 (read): a closed real subspace `H` of a complex Hilbert space is
standard if it is cyclic (`H + iH` dense) and separating (`H ∩ iH = 0`); for a standard subspace the Tomita operator is
`S : ξ + iη ↦ ξ - iη`, and conversely (Lemma 2.1.1) the fixed points `ker(1 - S)` of a closed densely defined anti-linear involution `S`
form a standard subspace.

Here, in the GNS space of a faithful state `ν` on `Matrix n n ℂ` (`GNSMat ν`, cyclic vector `η_ν = 1`), Tomita's operator is
`S (A η_ν) = A* η_ν`, i.e. `ξ ↦ ξ*` (`tomitaS`), an anti-linear involution, and its fixed points, the self-adjoint matrices, form a
standard subspace in Mathlib's sense (`hermStandardSubspace`, `mem_hermStandardSubspace_iff`).
-/

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace Lightlike.OperatorAlgebras

open GNSMat

variable {n : Type*} [Fintype n] [DecidableEq n] (ν : Matrix n n ℂ) [Fact ν.PosDef]

/-- **Tomita's operator** on the GNS space: `S (A η_ν) = A* η_ν`, i.e. `ξ ↦ ξ*`. -/
noncomputable def tomitaS (ξ : GNSMat ν) : GNSMat ν := toGNS ν ((toGNS ν).symm ξ)ᴴ

lemma tomitaS_gnsRep (A : Matrix n n ℂ) : tomitaS ν (gnsRep ν A (gnsVec ν)) = gnsRep ν Aᴴ (gnsVec ν) := by
  simp [tomitaS, gnsVec, gnsRep_toGNS]

/-- `S` is an involution. -/
lemma tomitaS_tomitaS (ξ : GNSMat ν) : tomitaS ν (tomitaS ν ξ) = ξ := by
  simp [tomitaS]

lemma tomitaS_add (ξ η : GNSMat ν) : tomitaS ν (ξ + η) = tomitaS ν ξ + tomitaS ν η := by
  simp [tomitaS, conjTranspose_add]

lemma tomitaS_sub (ξ η : GNSMat ν) : tomitaS ν (ξ - η) = tomitaS ν ξ - tomitaS ν η := by
  simp [tomitaS, conjTranspose_sub]

/-- `S` is anti-linear. -/
lemma tomitaS_smul (c : ℂ) (ξ : GNSMat ν) : tomitaS ν (c • ξ) = (starRingEnd ℂ) c • tomitaS ν ξ := by
  simp [tomitaS, conjTranspose_smul]

/-- The self-adjoint vectors `A η_ν`, `A = A*`: the fixed points of `S`, a real subspace. -/
noncomputable def hermSubmodule : Submodule ℝ (GNSMat ν) where
  carrier := {ξ | tomitaS ν ξ = ξ}
  add_mem' {ξ η} hξ hη := by
    simp only [Set.mem_setOf_eq, tomitaS] at hξ hη ⊢
    rw [map_add, conjTranspose_add, map_add, hξ, hη]
  zero_mem' := by simp [tomitaS]
  smul_mem' r ξ hξ := by
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rw [show r • ξ = (r : ℂ) • ξ from (RCLike.real_smul_eq_coe_smul r ξ), tomitaS_smul, hξ, Complex.conj_ofReal]

lemma mem_hermSubmodule_iff (ξ : GNSMat ν) : ξ ∈ hermSubmodule ν ↔ tomitaS ν ξ = ξ := Iff.rfl

/-- The real subspace of self-adjoint vectors is closed (it is finite-dimensional). -/
noncomputable def hermClosed : ClosedSubmodule ℝ (GNSMat ν) :=
  ⟨hermSubmodule ν, (hermSubmodule ν).closed_of_finiteDimensional⟩

lemma tomitaS_I_smul (ξ : GNSMat ν) (hξ : tomitaS ν ξ = ξ) : tomitaS ν (Complex.I • ξ) = -(Complex.I • ξ) := by
  rw [tomitaS_smul, hξ, Complex.conj_I, neg_smul]

/-- **The self-adjoint vectors form a standard subspace** (Longo, Section 2.1 and Lemma 2.1.1, pp. 21-22): `H ∩ iH = 0` and
`H + iH` is the whole GNS space, through `ξ = (ξ + S ξ)/2 + i (ξ - S ξ)/(2i)` (eq. (2.1.2)). -/
noncomputable def hermStandardSubspace : StandardSubspace (GNSMat ν) where
  toClosedSubmodule := hermClosed ν
  IsSeparating := by
    refine eq_bot_iff.mpr fun ξ hξ => ?_
    obtain ⟨h1, h2⟩ := ClosedSubmodule.mem_inf.mp hξ
    have hS : tomitaS ν ξ = ξ := h1
    rw [ClosedSubmodule.mem_mapEquiv_iff, scalarSMulCLE_symm_apply] at h2
    have h3 : tomitaS ν ((-Complex.I) • ξ) = (-Complex.I) • ξ := h2
    rw [tomitaS_smul, hS, map_neg, Complex.conj_I, neg_neg] at h3
    have h4 : (Complex.I - -Complex.I) • ξ = 0 := by rw [sub_smul, h3, sub_self]
    have hne : Complex.I - -Complex.I ≠ 0 := by
      rw [sub_neg_eq_add, ← two_mul]; exact mul_ne_zero two_ne_zero Complex.I_ne_zero
    rw [(smul_eq_zero.mp h4).resolve_left hne]
    exact zero_mem _
  IsCyclic := by
    refine eq_top_iff.mpr fun ξ _ => ?_
    rw [ClosedSubmodule.mem_sup]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    refine subset_closure (Submodule.mem_sup.mpr ⟨(1 / 2 : ℂ) • (ξ + tomitaS ν ξ), ?_,
      (1 / 2 : ℂ) • (ξ - tomitaS ν ξ), ?_, ?_⟩)
    · show tomitaS ν _ = _
      rw [tomitaS_smul, tomitaS_add, tomitaS_tomitaS, hhalf, add_comm]
    · show _ ∈ (hermClosed ν).mulI
      rw [ClosedSubmodule.mem_mapEquiv_iff, scalarSMulCLE_symm_apply]
      show tomitaS ν ((-Complex.I) • _) = (-Complex.I) • _
      rw [tomitaS_smul, tomitaS_smul, tomitaS_sub, tomitaS_tomitaS, hhalf, map_neg, Complex.conj_I, smul_smul,
        smul_smul]
      rw [show -(-Complex.I) * (1 / 2 : ℂ) = (-Complex.I * (1 / 2)) * (-1) by ring, mul_smul, neg_one_smul, neg_sub]
    · rw [← smul_add]
      rw [show ξ + tomitaS ν ξ + (ξ - tomitaS ν ξ) = (2 : ℂ) • ξ by rw [two_smul]; abel, smul_smul]
      norm_num

/-- **The standard subspace is the fixed-point set of Tomita's operator** (Longo, Lemma 2.1.1, p. 22: `H = ker(1 - S)`). -/
lemma mem_hermStandardSubspace_iff (ξ : GNSMat ν) :
    ξ ∈ (hermStandardSubspace ν).toClosedSubmodule ↔ tomitaS ν ξ = ξ := Iff.rfl

end Lightlike.OperatorAlgebras
