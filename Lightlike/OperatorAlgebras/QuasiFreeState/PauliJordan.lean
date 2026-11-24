import Lightlike.OperatorAlgebras.QuasiFreeState.ComplexStructure
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The Sorkin-Johnston state is pure: from `|iΔ|` to a complex structure

Let `Δ` be a real antisymmetric matrix (the Pauli-Jordan matrix of a finite causal set, with `iΔ` Hermitian, is such a
matrix up to the normalisation of the retarded Green function, which is not used here) and let `H = |iΔ| = (-Δ²)^{1/2}`
be its absolute value: `H` is real symmetric positive semidefinite, `H H = -Δ Δ`, and `H` commutes with `Δ` (it is a
function of `Δ²`). The Sorkin-Johnston two-point function `Pos(iΔ) = ½ (H + iΔ)` is the quasi-free state of the CCR
`[φ(x), φ(y)] = i xᵀΔ y` with covariance `η(x, y) = xᵀ H y` (conventions of `QuasiFreeState`: `ω_η(W(φ)) =
exp(-¼ η(φ, φ))`, two-point function `½ (η + iω)`; Dereziński, arXiv:math-ph/0511030, eq. (70) and Theorem 39 (1)).

`H` need not be positive definite (`Δ` has a kernel when the number of points is odd), so the complex structure lives on
`R = range H`, where `H` is invertible, and `V = ℝⁿ = R ⊕ ker H = R ⊕ ker Δ`. We prove:
* `J = -(H|_R)⁻¹ Δ|_R` satisfies `J² = -1` on `R`, `η(Jx, Jy) = η(x, y)`, `ω(x, y) = -η(x, Jy)` (`pjStructure`);
* hence (`isPureState_qfState_pauliJordan`) the quasi-free state `ω_η` on `ℝⁿ` is pure.
-/

set_option linter.unusedSectionVars false

open scoped Matrix

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Matrix

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The hypotheses on the Pauli-Jordan matrix `D` and its absolute value `H`: `D` antisymmetric, `H` symmetric and
positive semidefinite, `H H = -D D`, and `H D = D H`. -/
structure PJData (D H : Matrix ι ι ℝ) : Prop where
  /-- `D` is antisymmetric. -/
  anti : Dᵀ = -D
  /-- `H` is positive semidefinite. -/
  psd : H.PosSemidef
  /-- `H² = -D²`, so `H = |iD|`. -/
  sq : H * H = -(D * D)
  /-- `H` commutes with `D`. -/
  comm : H * D = D * H

/-- Transposing a matrix across a dot product. -/
lemma dot_mulVec_transpose (M : Matrix ι ι ℝ) (x y : ι → ℝ) : (M *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Mᵀ *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

variable {D H : Matrix ι ι ℝ}

namespace PJData

variable (h : PJData D H)
include h

/-- `H` is symmetric. -/
lemma symm : Hᵀ = H := h.psd.isHermitian.eq

/-- `H` is self-adjoint for the dot product. -/
lemma dot_H (x y : ι → ℝ) : (H *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (H *ᵥ y) := by
  rw [dot_mulVec_transpose, h.symm]

/-- `D` is anti-self-adjoint for the dot product. -/
lemma dot_D (x y : ι → ℝ) : (D *ᵥ x) ⬝ᵥ y = -(x ⬝ᵥ (D *ᵥ y)) := by
  rw [dot_mulVec_transpose, h.anti, Matrix.neg_mulVec, dotProduct_neg]

/-- `|D x|² = |H x|²`. -/
lemma dot_self_D_eq (x : ι → ℝ) : (D *ᵥ x) ⬝ᵥ (D *ᵥ x) = (H *ᵥ x) ⬝ᵥ (H *ᵥ x) := by
  rw [h.dot_D, h.dot_H, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.sq, Matrix.neg_mulVec, dotProduct_neg]

/-- `ker H = ker D`. -/
lemma H_eq_zero_iff (x : ι → ℝ) : H *ᵥ x = 0 ↔ D *ᵥ x = 0 := by
  have := h.dot_self_D_eq x
  constructor
  · intro hx
    rw [hx, dotProduct_zero] at this
    exact dotProduct_self_eq_zero.1 this
  · intro hx
    rw [hx, dotProduct_zero] at this
    exact dotProduct_self_eq_zero.1 this.symm

/-- `H` is injective on its range. -/
lemma eq_zero_of_mem_range (x : ι → ℝ) (hx : x ∈ LinearMap.range H.mulVecLin) (h0 : H *ᵥ x = 0) :
    x = 0 := by
  obtain ⟨w, rfl⟩ := hx
  have h1 : H *ᵥ (H *ᵥ w) = 0 := by simpa using h0
  have h2 : (H *ᵥ w) ⬝ᵥ (H *ᵥ w) = 0 := by
    rw [h.dot_H, h1, dotProduct_zero]
  simpa using dotProduct_self_eq_zero.1 h2

/-- `ℝⁿ = range H ⊕ ker H`. -/
lemma isCompl : IsCompl (LinearMap.range H.mulVecLin) (LinearMap.ker H.mulVecLin) := by
  rw [Submodule.isCompl_iff_disjoint]
  · rw [Submodule.disjoint_def]
    intro x hx hk
    exact h.eq_zero_of_mem_range x hx hk
  · have := LinearMap.finrank_range_add_finrank_ker (H.mulVecLin)
    simp only [Module.finrank_fintype_fun_eq_card] at this ⊢
    omega

/-- The subspace `R = range H` on which `H` is invertible. -/
abbrev Rsp (H : Matrix ι ι ℝ) : Submodule ℝ (ι → ℝ) := LinearMap.range H.mulVecLin

/-- `D` maps `R` into `R` (it commutes with `H`). -/
lemma D_mem (x : ι → ℝ) (hx : x ∈ Rsp H) : D *ᵥ x ∈ Rsp H := by
  obtain ⟨w, rfl⟩ := hx
  refine ⟨D *ᵥ w, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [h.comm]

/-- `H D x = D H x`. -/
lemma H_D (x : ι → ℝ) : H *ᵥ (D *ᵥ x) = D *ᵥ (H *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.comm]

/-- `H H x = -D D x`. -/
lemma H_H (x : ι → ℝ) : H *ᵥ (H *ᵥ x) = -(D *ᵥ (D *ᵥ x)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.sq, Matrix.neg_mulVec]

end PJData

open PJData

/-- `H` restricted to `R`. -/
noncomputable def Hr (H : Matrix ι ι ℝ) : Rsp H →ₗ[ℝ] Rsp H :=
  H.mulVecLin.restrict (fun x _ => LinearMap.mem_range_self _ x)

/-- `D` restricted to `R`. -/
noncomputable def Dr (h : PJData D H) : Rsp H →ₗ[ℝ] Rsp H :=
  D.mulVecLin.restrict (fun x hx => h.D_mem x hx)

/-- The value of `Hr`. -/
lemma Hr_apply (x : Rsp H) : ((Hr H x : Rsp H) : ι → ℝ) = H *ᵥ (x : ι → ℝ) := rfl

/-- The value of `Dr`. -/
lemma Dr_apply (h : PJData D H) (x : Rsp H) : ((Dr h x : Rsp H) : ι → ℝ) = D *ᵥ (x : ι → ℝ) := rfl

/-- `H|_R` is injective. -/
lemma Hr_injective (h : PJData D H) : Function.Injective (Hr H) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  apply Subtype.ext
  exact h.eq_zero_of_mem_range _ x.2 (by simpa [Hr_apply] using congrArg Subtype.val hx)

/-- `H|_R` is an automorphism of `R`. -/
noncomputable def Hequiv (h : PJData D H) : Rsp H ≃ₗ[ℝ] Rsp H :=
  LinearEquiv.ofBijective (Hr H) ⟨Hr_injective h, LinearMap.injective_iff_surjective.1 (Hr_injective h)⟩

/-- **The complex structure** `J = -(H|_R)⁻¹ D|_R` on `R`. -/
noncomputable def Jr (h : PJData D H) : Rsp H →ₗ[ℝ] Rsp H :=
  -((Hequiv h).symm.toLinearMap ∘ₗ Dr h)

/-- `H J r = -D r`. -/
lemma H_Jr (h : PJData D H) (r : Rsp H) :
    H *ᵥ ((Jr h r : Rsp H) : ι → ℝ) = -(D *ᵥ (r : ι → ℝ)) := by
  have h1 : Hr H (Jr h r) = -(Dr h r) := by
    have : Hr H ((Hequiv h).symm (Dr h r)) = Dr h r := (Hequiv h).apply_symm_apply (Dr h r)
    simp only [Jr, LinearMap.neg_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_neg]
    exact congrArg Neg.neg this
  have h2 := congrArg Subtype.val h1
  simpa [Hr_apply, Dr_apply] using h2

/-- The antisymmetric form `x ⬝ D y` on `ℝⁿ`. -/
noncomputable def pjOmega (D : Matrix ι ι ℝ) : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' D

/-- The covariance `x ⬝ H y` on `ℝⁿ`. -/
noncomputable def pjEta (H : Matrix ι ι ℝ) : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' H

/-- The value of `pjOmega`. -/
lemma pjOmega_apply (D : Matrix ι ι ℝ) (x y : ι → ℝ) : pjOmega D x y = x ⬝ᵥ (D *ᵥ y) :=
  Matrix.toBilin'_apply' D x y

/-- The value of `pjEta`. -/
lemma pjEta_apply (H : Matrix ι ι ℝ) (x y : ι → ℝ) : pjEta H x y = x ⬝ᵥ (H *ᵥ y) :=
  Matrix.toBilin'_apply' H x y

/-- `D J x = H x` on `R`. -/
lemma D_Jr (h : PJData D H) (x : Rsp H) : D *ᵥ ((Jr h x : Rsp H) : ι → ℝ) = H *ᵥ (x : ι → ℝ) := by
  set y : ι → ℝ := ((Jr h x : Rsp H) : ι → ℝ) with hy
  have hyR : y ∈ Rsp H := (Jr h x).2
  have hw : (D *ᵥ y - H *ᵥ (x : ι → ℝ)) ∈ Rsp H :=
    Submodule.sub_mem _ (h.D_mem y hyR) (LinearMap.mem_range_self _ _)
  have h0 : H *ᵥ (D *ᵥ y - H *ᵥ (x : ι → ℝ)) = 0 := by
    rw [Matrix.mulVec_sub, h.H_D, H_Jr h x, Matrix.mulVec_neg, h.H_H x]
    abel
  exact sub_eq_zero.1 (h.eq_zero_of_mem_range _ hw h0)

/-- `J² = -1` on `R`. -/
lemma Jr_sq (h : PJData D H) (x : Rsp H) : Jr h (Jr h x) = -x := by
  set y := Jr h x with hy
  set z := Jr h y with hz
  have hzR : ((z : Rsp H) : ι → ℝ) + (x : ι → ℝ) ∈ Rsp H := Submodule.add_mem _ z.2 x.2
  have h1 : H *ᵥ (((z : Rsp H) : ι → ℝ) + (x : ι → ℝ)) ∈ Rsp H := LinearMap.mem_range_self _ _
  have h0 : H *ᵥ (H *ᵥ (((z : Rsp H) : ι → ℝ) + (x : ι → ℝ))) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, H_Jr h y, Matrix.mulVec_neg, h.H_D, H_Jr h x,
      Matrix.mulVec_neg, h.H_H x]
    simp
  have h2 := h.eq_zero_of_mem_range _ h1 h0
  have h3 := h.eq_zero_of_mem_range _ hzR h2
  apply Subtype.ext
  simpa [add_eq_zero_iff_eq_neg] using h3

/-- **The Pauli-Jordan complex structure** on `R = range H`: `J² = -1`, `η` is `J`-invariant and positive definite and
`ω(x, y) = -η(x, J y)`, for `ω = x ⬝ D y` and `η = x ⬝ H y` restricted to `R`. -/
noncomputable def pjStructure (h : PJData D H) :
    CompatibleComplexStructure ((pjOmega D).compl₁₂ (Rsp H).subtype (Rsp H).subtype)
      ((pjEta H).compl₁₂ (Rsp H).subtype (Rsp H).subtype) where
  J := Jr h
  J_sq := Jr_sq h
  symm x y := by
    simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, pjEta_apply]
    rw [← h.dot_H, dotProduct_comm]
  eta_J x y := by
    simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, pjEta_apply]
    rw [H_Jr h y, dotProduct_neg, ← h.dot_D, D_Jr h x, h.dot_H]
  eta_pos x hx := by
    simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, pjEta_apply]
    have hnn : 0 ≤ (x : ι → ℝ) ⬝ᵥ (H *ᵥ (x : ι → ℝ)) := by
      simpa using h.psd.dotProduct_mulVec_nonneg (x : ι → ℝ)
    refine lt_of_le_of_ne hnn fun h0 => hx ?_
    have h1 : H *ᵥ (x : ι → ℝ) = 0 := by
      rw [← h.psd.dotProduct_mulVec_zero_iff]; simpa using h0.symm
    exact Subtype.ext (h.eq_zero_of_mem_range _ x.2 h1)
  omega_eq x y := by
    simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, pjEta_apply, pjOmega_apply]
    rw [H_Jr h y]; simp

/-- The projection of `ℝⁿ = R ⊕ ker H` onto `R`. -/
noncomputable def pjProj (h : PJData D H) : (ι → ℝ) →ₗ[ℝ] Rsp H :=
  Submodule.projectionOnto _ _ h.isCompl

/-- `x = P x + k` with `k ∈ ker H = ker D`. -/
lemma exists_ker_add (h : PJData D H) (x : ι → ℝ) :
    ∃ k : ι → ℝ, D *ᵥ k = 0 ∧ x = ((pjProj h x : Rsp H) : ι → ℝ) + k := by
  refine ⟨x - ((pjProj h x : Rsp H) : ι → ℝ), ?_, by abel⟩
  have hk : x - ((pjProj h x : Rsp H) : ι → ℝ) ∈ LinearMap.ker H.mulVecLin := by
    rw [← Submodule.ker_projectionOnto h.isCompl]
    rw [LinearMap.mem_ker, map_sub]
    change pjProj h x - pjProj h ((pjProj h x : Rsp H) : ι → ℝ) = 0
    have : pjProj h ((pjProj h x : Rsp H) : ι → ℝ) = pjProj h x :=
      Submodule.projectionOnto_apply_left h.isCompl (pjProj h x)
    rw [this, sub_self]
  exact (h.H_eq_zero_iff _).1 (by simpa using hk)

/-- `P` is onto `R` (it is the identity on `R`). -/
lemma pjProj_surjective (h : PJData D H) : Function.Surjective (pjProj h) := fun r =>
  ⟨(r : ι → ℝ), Submodule.projectionOnto_apply_left h.isCompl r⟩

/-- `ω` and `η` factor through the projection. -/
lemma pj_forms (h : PJData D H) (a b : ι → ℝ) :
    pjOmega D a b = ((pjOmega D).compl₁₂ (Rsp H).subtype (Rsp H).subtype) (pjProj h a) (pjProj h b) ∧
    pjEta H a b = ((pjEta H).compl₁₂ (Rsp H).subtype (Rsp H).subtype) (pjProj h a) (pjProj h b) := by
  obtain ⟨k, hk, hka⟩ := exists_ker_add h a
  obtain ⟨l, hl, hlb⟩ := exists_ker_add h b
  have hk' : H *ᵥ k = 0 := (h.H_eq_zero_iff k).2 hk
  have hl' : H *ᵥ l = 0 := (h.H_eq_zero_iff l).2 hl
  simp only [LinearMap.compl₁₂_apply, Submodule.subtype_apply, pjOmega_apply, pjEta_apply]
  set pa := ((pjProj h a : Rsp H) : ι → ℝ)
  set pb := ((pjProj h b : Rsp H) : ι → ℝ)
  have h1 : k ⬝ᵥ (D *ᵥ pb) = 0 := by
    have := h.dot_D k pb
    rw [hk, zero_dotProduct] at this
    linarith
  have h2 : k ⬝ᵥ (H *ᵥ pb) = 0 := by
    have := h.dot_H k pb
    rw [hk', zero_dotProduct] at this
    exact this.symm
  constructor
  · rw [hka, hlb, Matrix.mulVec_add, hl, add_zero, add_dotProduct, h1, add_zero]
  · rw [hka, hlb, Matrix.mulVec_add, hl', add_zero, add_dotProduct, h2, add_zero]

/-- The covariance `(pjOmega D, pjEta H)` satisfies the covariance inequality. -/
lemma pj_isCovariance (h : PJData D H) : IsCovariance (pjOmega D) (pjEta H) := by
  have S := (pjStructure h).isCovariance
  refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [(pj_forms h a b).2, (pj_forms h b a).2]; exact S.symm _ _
  · rw [(pj_forms h a a).2]; exact S.nonneg _
  · rw [(pj_forms h a b).1, (pj_forms h a a).2, (pj_forms h b b).2]; exact S.sq_le _ _

/-- `ω` is antisymmetric. -/
lemma pj_omega_antisymm (h : PJData D H) (a b : ι → ℝ) : pjOmega D a b = -pjOmega D b a := by
  rw [pjOmega_apply, pjOmega_apply, dotProduct_comm, h.dot_D]

/-- **The Sorkin-Johnston state is pure** (CS7, sufficiency; the positive part of the Pauli-Jordan matrix defines a
pure quasi-free state): for `D` antisymmetric and `H = |iD|` (symmetric, positive semidefinite, `H² = -D²`, commuting
with `D`), the quasi-free state of the CCR `ω(x, y) = x ⬝ D y` with covariance `η(x, y) = x ⬝ H y` on `ℝⁿ` is pure. -/
theorem isPureState_qfState_pauliJordan [Fact (qfKerM (pjOmega D) (pjEta H)).PosSemidef] (h : PJData D H) :
    IsPureState (qfState (pjOmega D) (pjEta H) (pj_omega_antisymm h)) := by
  exact isPureState_qfState_of_complexStructure_retract (pjStructure h) (pjProj h).toAddMonoidHom
    (pjProj_surjective h) (fun a b => (pj_forms h a b).1) (fun a b => (pj_forms h a b).2)

/-- **The Sorkin-Johnston state is pure**, without a separate positivity hypothesis: the Gram kernel is positive
semidefinite by `pj_isCovariance`. -/
theorem isPureState_pauliJordan (h : PJData D H) :
    haveI : Fact (qfKerM (pjOmega D) (pjEta H)).PosSemidef :=
      qfFact _ _ (pj_omega_antisymm h) (pj_isCovariance h)
    IsPureState (qfState (pjOmega D) (pjEta H) (pj_omega_antisymm h)) :=
  haveI : Fact (qfKerM (pjOmega D) (pjEta H)).PosSemidef :=
    qfFact _ _ (pj_omega_antisymm h) (pj_isCovariance h)
  isPureState_qfState_pauliJordan h

end Lightlike.OperatorAlgebras.QuasiFreeState
