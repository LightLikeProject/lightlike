import Lightlike.OperatorAlgebras.VonNeumann

/-!
# Von Neumann's decomposition of the adjoint's domain

For a closed symmetric densely defined `A`: every vector of the domain of `A†` is `x + p + q` with `x ∈ D(A)`, `p ∈ N_i`, `q ∈ N_{-i}`
(`exists_decomp`), and the decomposition is unique (`decomp_eq_zero`). This decomposition is not stated in the source read for von Neumann's
theorem (Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Section 4): it is a lemma of the library.
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- A vector of a deficiency space lies in the domain of the adjoint, where the adjoint acts as the scalar. -/
lemma deficiency_adjoint {z : ℂ} {p : H} (hp : p ∈ deficiencySpace A z) :
    ∃ h : p ∈ (A†).domain, (A† ⟨p, h⟩ : H) = z • p := hp

/-- **`N_{z̄}` is orthogonal to the range of `A - z`**. -/
lemma inner_deficiency_shift (hA : ClosedSymm A) {z : ℂ} {p : H} (hp : p ∈ deficiencySpace A ((starRingEnd ℂ) z))
    (x : A.domain) : ⟪p, shiftMap A z x⟫_ℂ = 0 := by
  obtain ⟨hpd, hpe⟩ := hp
  have hfa := LinearPMap.adjoint_isFormalAdjoint hA.dense ⟨p, hpd⟩ x
  rw [shiftMap_apply, inner_sub_right, inner_smul_right, ← hfa, hpe, inner_smul_left, Complex.conj_conj, sub_self]

/-- **The orthogonal complement of the range of `A - z` lies in `N_{z̄}`**. -/
lemma orthogonal_range_le_deficiency (hA : ClosedSymm A) (z : ℂ) :
    (LinearMap.range (shiftMap A z))ᗮ ≤ deficiencySpace A ((starRingEnd ℂ) z) := by
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  refine mem_deficiencySpace_of_forall hA.dense _ _ fun x => ?_
  have h0 := hy (shiftMap A z x) (LinearMap.mem_range_self _ x)
  rw [shiftMap_apply, inner_sub_left, inner_smul_left, sub_eq_zero] at h0
  rw [inner_smul_left, ← inner_conj_symm (𝕜 := ℂ) y (A x : H), h0, map_mul, starRingEnd_self_apply,
    ← inner_conj_symm (𝕜 := ℂ) y (x : H)]

/-- **Von Neumann's decomposition, existence**: every `y ∈ D(A†)` is `x + p + q` with `x ∈ D(A)`, `p ∈ N_i`, `q ∈ N_{-i}`. -/
theorem exists_decomp (hA : ClosedSymm A) (y : (A†).domain) :
    ∃ (x : A.domain) (p q : H), p ∈ deficiencySpace A Complex.I ∧ q ∈ deficiencySpace A (-Complex.I) ∧
      (y : H) = x + p + q := by
  set R := LinearMap.range (shiftMap A (-Complex.I)) with hR
  have hcl : IsClosed (R : Set H) := cs_range_shiftMap_closed hA (z := -Complex.I) (by simp)
  haveI : CompleteSpace R := hcl.completeSpace_coe
  obtain ⟨r, hr, φ, hφ, hv⟩ := R.exists_add_mem_mem_orthogonal ((A† y : H) + Complex.I • (y : H))
  obtain ⟨x, rfl⟩ := hr
  have hφN : φ ∈ deficiencySpace A Complex.I := by
    have := orthogonal_range_le_deficiency hA (-Complex.I) hφ
    simpa using this
  set p : H := (2 * Complex.I)⁻¹ • φ with hpdef
  have hp : p ∈ deficiencySpace A Complex.I := Submodule.smul_mem _ _ hφN
  refine ⟨x, p, (y : H) - x - p, hp, ?_, by abel⟩
  obtain ⟨hpd, hpe⟩ := hp
  have hxd : (x : H) ∈ (A†).domain := hA.le_adjoint.1 x.2
  have hAx : (A† ⟨(x : H), hxd⟩ : H) = A x := (hA.le_adjoint.2 (x := x) (y := ⟨(x : H), hxd⟩) rfl).symm
  have hqd : (y : H) - x - p ∈ (A†).domain := (A†).domain.sub_mem ((A†).domain.sub_mem y.2 hxd) hpd
  refine ⟨hqd, ?_⟩
  have e1 : (⟨(y : H) - x - p, hqd⟩ : (A†).domain) = y - ⟨(x : H), hxd⟩ - ⟨p, hpd⟩ := rfl
  rw [e1, LinearPMap.map_sub, LinearPMap.map_sub, hAx, hpe]
  rw [shiftMap_apply] at hv
  have hφ2 : φ = (2 * Complex.I) • p := by
    rw [hpdef, smul_smul, mul_inv_cancel₀ (by simp), one_smul]
  have hAy : (A† y : H) = A x + Complex.I • (x : H) + (2 * Complex.I) • p - Complex.I • (y : H) := by
    rw [← hφ2]
    rw [eq_sub_iff_add_eq, hv]
    module
  rw [hAy]
  module

/-- **Von Neumann's decomposition, uniqueness**: `x + p + q = 0` with `x ∈ D(A)`, `p ∈ N_i`, `q ∈ N_{-i}` forces `x = p = q = 0`. -/
theorem decomp_eq_zero (hA : ClosedSymm A) (x : A.domain) {p q : H} (hp : p ∈ deficiencySpace A Complex.I)
    (hq : q ∈ deficiencySpace A (-Complex.I)) (h : (x : H) + p + q = 0) : (x : H) = 0 ∧ p = 0 ∧ q = 0 := by
  have hp' := hp
  have hq' := hq
  obtain ⟨hpd, hpe⟩ := hp
  obtain ⟨hqd, hqe⟩ := hq
  have hxeq : (x : H) = -p - q := by rw [← sub_eq_zero, ← h]; abel
  have hxd : (x : H) ∈ (A†).domain := hA.le_adjoint.1 x.2
  have hAx : (A x : H) = A† ⟨(x : H), hxd⟩ := hA.le_adjoint.2 (x := x) (y := ⟨(x : H), hxd⟩) rfl
  have e1 : (⟨(x : H), hxd⟩ : (A†).domain) = -⟨p, hpd⟩ - ⟨q, hqd⟩ := Subtype.ext hxeq
  rw [e1, LinearPMap.map_sub, LinearPMap.map_neg, hpe, hqe] at hAx
  have hs1 : shiftMap A Complex.I x = (2 * Complex.I) • q := by
    rw [shiftMap_apply, hAx, hxeq]; module
  have hs2 : shiftMap A (-Complex.I) x = (-(2 * Complex.I)) • p := by
    rw [shiftMap_apply, hAx, hxeq]; module
  have hq0 : q = 0 := by
    have h0 := inner_deficiency_shift hA (z := Complex.I) (by simpa using hq') x
    rw [hs1, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
    have : (2 * Complex.I) ≠ 0 := by simp
    have h3 : ((‖q‖ : ℂ) ^ 2) = 0 := (mul_eq_zero.mp h0).resolve_left this
    have h4 : ‖q‖ ^ 2 = 0 := by exact_mod_cast h3
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4)
  have hp0 : p = 0 := by
    have h0 := inner_deficiency_shift hA (z := -Complex.I) (by simpa using hp') x
    rw [hs2, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
    have : (-(2 * Complex.I)) ≠ 0 := by simp
    have h3 : ((‖p‖ : ℂ) ^ 2) = 0 := (mul_eq_zero.mp h0).resolve_left this
    have h4 : ‖p‖ ^ 2 = 0 := by exact_mod_cast h3
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4)
  refine ⟨?_, hp0, hq0⟩
  rw [hxeq, hp0, hq0]; simp

end Lightlike.OperatorAlgebras
