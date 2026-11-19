import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The real form of an antiunitary involution

For an antiunitary involution `J` on a complex inner product space `V` (`⟪J x, J y⟫ = ⟪y, x⟫`, `J² = 1`), the fixed
vectors `V_ℝ = {v | J v = v}` form a real subspace on which the inner product is real, and `V = V_ℝ ⊕ i V_ℝ`:
`v = (v + J v)/2 + i ((v - J v)/(2 i))`. This is the step "choose an orthonormal basis such that `Lᵢᵢ ψᵖ = ψᵖ`" in
T. Krajewski, arXiv:hep-th/9701081, Section 3.2, p. 13.

* `fixedSub J`, `mem_fixedSub`;
* `inner_re_of_mem_fixedSub`: `⟪u, v⟫` is real on `V_ℝ`;
* `fixed_add_I_mul_fixed`: every `v` is `u + i w` with `u, w ∈ V_ℝ`;
* `fixed_inter_I_fixed`: `u + i w = 0` with `u, w ∈ V_ℝ` forces `u = w = 0`;
* `fixedPairMap`, `finrank_fixedSub`: `dim_ℝ V_ℝ = dim_ℂ V`;
* `exists_orthonormalBasis_fixed`: an orthonormal basis of `J`-fixed vectors.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.NCG

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- **The fixed vectors** `V_ℝ = {v | J v = v}` of an antilinear map, a real subspace. -/
def fixedSub (J : V →ₗ⋆[ℂ] V) : Submodule ℝ V where
  carrier := {v | J v = v}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
    rw [hx, hy]
  zero_mem' := map_zero J
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [show c • x = (c : ℂ) • x from (RCLike.real_smul_eq_coe_smul c x), LinearMap.map_smulₛₗ, hx,
      Complex.conj_ofReal]

lemma mem_fixedSub {J : V →ₗ⋆[ℂ] V} {v : V} : v ∈ fixedSub J ↔ J v = v := Iff.rfl

variable {J : V →ₗ⋆[ℂ] V}

/-- **The inner product is real on `V_ℝ`**: `⟪u, v⟫ = ⟪J u, J v⟫ = conj ⟪u, v⟫`. -/
lemma inner_re_of_mem_fixedSub (hJ : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪y, x⟫_ℂ) {u v : V} (hu : u ∈ fixedSub J)
    (hv : v ∈ fixedSub J) : ((⟪u, v⟫_ℂ).re : ℂ) = ⟪u, v⟫_ℂ := by
  have h := hJ u v
  rw [mem_fixedSub.1 hu, mem_fixedSub.1 hv] at h
  exact Complex.conj_eq_iff_re.1 ((inner_conj_symm v u).trans h.symm)

/-- **`v = u + i w`** with `u = (v + J v)/2` and `w = (v - J v)/(2 i)` fixed by `J`. -/
lemma fixed_add_I_mul_fixed (hJJ : ∀ x, J (J x) = x) (v : V) :
    ∃ u ∈ fixedSub J, ∃ w ∈ fixedSub J, v = u + Complex.I • w := by
  refine ⟨(1 / 2 : ℂ) • (v + J v), ?_, (1 / (2 * Complex.I)) • (v - J v), ?_, ?_⟩
  · rw [mem_fixedSub, LinearMap.map_smulₛₗ, map_add, hJJ, add_comm (J v)]
    congr 1
    simp [map_div₀, map_ofNat]
  · rw [mem_fixedSub, LinearMap.map_smulₛₗ, map_sub, hJJ]
    rw [show (starRingEnd ℂ) (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) by
      simp [map_ofNat, Complex.conj_I]]
    rw [neg_smul, ← smul_neg, neg_sub]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, smul_sub, smul_add, add_add_sub_cancel,
      ← add_smul]
    norm_num

/-- **`V_ℝ ∩ i V_ℝ = 0`**: `u + i w = 0` with `u, w` fixed forces `u = w = 0`. -/
lemma fixed_inter_I_fixed {u w : V} (hu : u ∈ fixedSub J) (hw : w ∈ fixedSub J) (h : u + Complex.I • w = 0) :
    u = 0 ∧ w = 0 := by
  have h2 := congrArg J h
  rw [map_add, LinearMap.map_smulₛₗ, mem_fixedSub.1 hu, mem_fixedSub.1 hw, Complex.conj_I, map_zero] at h2
  have hw0 : (2 * Complex.I) • w = 0 := by
    have := sub_eq_zero.2 (h.trans h2.symm)
    rw [show u + Complex.I • w - (u + -Complex.I • w) = (2 * Complex.I) • w by
      rw [neg_smul, sub_add_eq_sub_sub, add_sub_cancel_left, sub_neg_eq_add, ← two_smul ℂ, smul_smul]] at this
    exact this
  have hw' : w = 0 := (smul_eq_zero.1 hw0).resolve_left (by simp [Complex.I_ne_zero])
  refine ⟨?_, hw'⟩
  rw [hw', smul_zero, add_zero] at h
  exact h

/-- The real-linear map `V_ℝ × V_ℝ → V`, `(u, w) ↦ u + i w`. -/
def fixedPairMap (J : V →ₗ⋆[ℂ] V) : (fixedSub J × fixedSub J) →ₗ[ℝ] V where
  toFun p := (p.1 : V) + Complex.I • (p.2 : V)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
    rw [smul_comm c Complex.I]

lemma fixedPairMap_bijective (hJJ : ∀ x, J (J x) = x) : Function.Bijective (fixedPairMap J) := by
  refine ⟨fun p q hpq => ?_, fun v => ?_⟩
  · have h : ((p.1 : V) - q.1) + Complex.I • ((p.2 : V) - q.2) = 0 := by
      have := sub_eq_zero.2 hpq
      simp only [fixedPairMap, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [smul_sub]
      rw [← this]
      abel
    obtain ⟨h1, h2⟩ := fixed_inter_I_fixed (Submodule.sub_mem _ p.1.2 q.1.2) (Submodule.sub_mem _ p.2.2 q.2.2) h
    exact Prod.ext (Subtype.ext (sub_eq_zero.1 h1)) (Subtype.ext (sub_eq_zero.1 h2))
  · obtain ⟨u, hu, w, hw, rfl⟩ := fixed_add_I_mul_fixed hJJ v
    exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩

/-- **`dim_ℝ V_ℝ = dim_ℂ V`.** -/
theorem finrank_fixedSub [FiniteDimensional ℂ V] (hJJ : ∀ x, J (J x) = x) :
    Module.finrank ℝ (fixedSub J) = Module.finrank ℂ V := by
  have h := (LinearEquiv.ofBijective _ (fixedPairMap_bijective hJJ)).finrank_eq
  rw [Module.finrank_prod, finrank_real_of_complex] at h
  omega

/-- **An orthonormal basis of `J`-fixed vectors** for an antiunitary involution `J` (Krajewski, Section 3.2, p. 13:
"we can choose an orthonormal basis such that `Lᵢᵢ ψᵢᵢᵖ = e^{iφ} ψᵢᵢᵖ`", and then the phases disappear): an orthonormal
basis of the real form `V_ℝ` for the real inner product `re ⟪·, ·⟫`, which is `⟪·, ·⟫` there. -/
theorem exists_orthonormalBasis_fixed [FiniteDimensional ℂ V] (hJ : ∀ x y, ⟪J x, J y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hJJ : ∀ x, J (J x) = x) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V, ∀ k, J (b k) = b k := by
  let _ : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  have hd : Module.finrank ℝ (fixedSub J) = Module.finrank ℂ V := finrank_fixedSub hJJ
  let e := stdOrthonormalBasis ℝ (fixedSub J)
  let v : Fin (Module.finrank ℂ V) → V := fun k => (e (Fin.cast hd.symm k) : V)
  have hmem : ∀ k, v k ∈ fixedSub J := fun k => (e (Fin.cast hd.symm k)).2
  have hon : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro k l
    have h1 := (orthonormal_iff_ite.1 e.orthonormal) (Fin.cast hd.symm k) (Fin.cast hd.symm l)
    rw [Submodule.coe_inner, real_inner_eq_re_inner, RCLike.re_to_complex] at h1
    rw [← inner_re_of_mem_fixedSub hJ (hmem k) (hmem l)]
    show (((⟪(e (Fin.cast hd.symm k) : V), (e (Fin.cast hd.symm l) : V)⟫_ℂ).re : ℝ) : ℂ) = _
    rw [h1]
    by_cases hkl : k = l
    · subst hkl; simp
    · rw [if_neg (fun h => hkl (Fin.cast_injective _ h)), if_neg hkl, Complex.ofReal_zero]
  refine ⟨OrthonormalBasis.mk hon ?_, fun k => ?_⟩
  · exact (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge
  · rw [OrthonormalBasis.coe_mk]
    exact hmem k

end Lightlike.NCG
