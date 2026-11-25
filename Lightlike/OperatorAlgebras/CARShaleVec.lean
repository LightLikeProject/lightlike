import Lightlike.OperatorAlgebras.CARShale

/-!
# Transformed ladder operators of an arbitrary vector

For a real-linear `R` preserving `Re⟪·,·⟫`, the transformed annihilation and creation operators of a vector `v` are
`annV v = (φ(R v) + i φ(R (i v)))/2` and `creV v = (φ(R v) - i φ(R (i v)))/2`. They satisfy the CAR
`{annV u, creV v} = ⟪u, v⟫` (`annV_creV_anticomm`), `annV` is conjugate-linear and `creV` linear in `v`, and `creV v` is
the adjoint of `annV v`. In terms of the Fock operators, `annV v = a*(β v) + a(α v)` and `creV v = a*(α v) + a(β v)`
with `α, β` the linear and antilinear parts of `R`. The families `annR j`, `creR j` of `CARShale.lean` are the
case `v = b j`.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CARShale

variable {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  (B : HilbertBasis (Finset ι) ℂ Γ) {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  (b : HilbertBasis ι ℂ Z) (R : Z →ₗ[ℝ] Z)

/-- The transformed annihilation operator of a vector. -/
noncomputable def annV (v : Z) : Γ →L[ℂ] Γ :=
  (1 / 2 : ℂ) • (fockField B b (R v) + Complex.I • fockField B b (R (Complex.I • v)))

/-- The transformed creation operator of a vector. -/
noncomputable def creV (v : Z) : Γ →L[ℂ] Γ :=
  (1 / 2 : ℂ) • (fockField B b (R v) - Complex.I • fockField B b (R (Complex.I • v)))

/-- `annR j` is `annV (b j)`. -/
lemma annR_eq_annV (j : ι) : annR B b R j = annV B b R (b j) := rfl

/-- `creR j` is `creV (b j)`. -/
lemma creR_eq_creV (j : ι) : creR B b R j = creV B b R (b j) := rfl

variable (hR : ∀ w w', (⟪R w, R w'⟫_ℂ).re = (⟪w, w'⟫_ℂ).re)
include hR

/-- The anticommutator of the fields of two transformed vectors. -/
lemma field_anticomm_R (u v : Z) :
    fockField B b (R u) * fockField B b (R v) + fockField B b (R v) * fockField B b (R u) =
      ((2 * (⟪u, v⟫_ℂ).re : ℝ) : ℂ) • (1 : Γ →L[ℂ] Γ) := by
  rw [fockField_anticomm, hR]

omit hR in
/-- Auxiliary lemma `re_inner_I_right` for the fermionic Shale theorem. -/
lemma re_inner_I_right (u v : Z) : (⟪u, Complex.I • v⟫_ℂ).re = -(⟪u, v⟫_ℂ).im := by
  rw [inner_smul_right]; simp

omit hR in
/-- Auxiliary lemma `re_inner_I_left` for the fermionic Shale theorem. -/
lemma re_inner_I_left (u v : Z) : (⟪Complex.I • u, v⟫_ℂ).re = (⟪u, v⟫_ℂ).im := by
  rw [inner_smul_left]; simp

omit hR in
/-- Auxiliary lemma `re_inner_I_I` for the fermionic Shale theorem. -/
lemma re_inner_I_I (u v : Z) : (⟪Complex.I • u, Complex.I • v⟫_ℂ).re = (⟪u, v⟫_ℂ).re := by
  rw [inner_smul_left, inner_smul_right]; simp

/-- **The CAR for the transformed operators of two vectors**: `{annV u, creV v} = ⟪u, v⟫`. -/
theorem annV_creV_anticomm (u v : Z) :
    annV B b R u * creV B b R v + creV B b R v * annV B b R u = ⟪u, v⟫_ℂ • (1 : Γ →L[ℂ] Γ) := by
  have h1 := field_anticomm_R B b R hR u v
  have h2 := field_anticomm_R B b R hR u (Complex.I • v)
  have h3 := field_anticomm_R B b R hR (Complex.I • u) v
  have h4 := field_anticomm_R B b R hR (Complex.I • u) (Complex.I • v)
  rw [re_inner_I_right] at h2
  rw [re_inner_I_left] at h3
  rw [re_inner_I_I] at h4
  simp only [annV, creV, smul_mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul]
  have hz : ⟪u, v⟫_ℂ = ((⟪u, v⟫_ℂ).re : ℂ) + ((⟪u, v⟫_ℂ).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  rw [hz]
  linear_combination (norm := (match_scalars <;> (push_cast; ring_nf; try simp only [Complex.I_sq]; try ring)))
    (1 / 4 : ℂ) • h1 - (Complex.I / 4) • h2 + (Complex.I / 4) • h3 + (1 / 4 : ℂ) • h4

/-- `{creV u, creV v} = 0`. -/
theorem creV_anticomm (u v : Z) :
    creV B b R u * creV B b R v + creV B b R v * creV B b R u = 0 := by
  have h1 := field_anticomm_R B b R hR u v
  have h2 := field_anticomm_R B b R hR u (Complex.I • v)
  have h3 := field_anticomm_R B b R hR (Complex.I • u) v
  have h4 := field_anticomm_R B b R hR (Complex.I • u) (Complex.I • v)
  rw [re_inner_I_right] at h2
  rw [re_inner_I_left] at h3
  rw [re_inner_I_I] at h4
  simp only [creV, smul_mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul]
  linear_combination (norm := (match_scalars <;> (push_cast; ring_nf; try simp only [Complex.I_sq]; try ring)))
    (1 / 4 : ℂ) • h1 - (Complex.I / 4) • h2 - (Complex.I / 4) • h3 - (1 / 4 : ℂ) • h4

/-- `{annV u, annV v} = 0`. -/
theorem annV_anticomm (u v : Z) :
    annV B b R u * annV B b R v + annV B b R v * annV B b R u = 0 := by
  have h1 := field_anticomm_R B b R hR u v
  have h2 := field_anticomm_R B b R hR u (Complex.I • v)
  have h3 := field_anticomm_R B b R hR (Complex.I • u) v
  have h4 := field_anticomm_R B b R hR (Complex.I • u) (Complex.I • v)
  rw [re_inner_I_right] at h2
  rw [re_inner_I_left] at h3
  rw [re_inner_I_I] at h4
  simp only [annV, smul_mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    smul_add, smul_sub, smul_smul]
  linear_combination (norm := (match_scalars <;> (push_cast; ring_nf; try simp only [Complex.I_sq]; try ring)))
    (1 / 4 : ℂ) • h1 + (Complex.I / 4) • h2 + (Complex.I / 4) • h3 - (1 / 4 : ℂ) • h4

omit hR in
/-- `creV v` is the adjoint of `annV v`. -/
lemma inner_annV_creV (v : Z) (x y : Γ) : ⟪annV B b R v x, y⟫_ℂ = ⟪x, creV B b R v y⟫_ℂ := by
  simp only [annV, creV, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
    inner_field B b]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp [Complex.conj_I, h2]
  ring

omit hR in
/-- `R (c v) = Re c · R v + Im c · R (i v)`. -/
lemma R_smul (c : ℂ) (v : Z) : R (c • v) = c.re • R v + c.im • R (Complex.I • v) := by
  have he : c • v = c.re • v + c.im • (Complex.I • v) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [he, map_add, map_smul, map_smul]

omit hR in
/-- `annV` is additive. -/
lemma annV_add (u v : Z) : annV B b R (u + v) = annV B b R u + annV B b R v := by
  have h1 : Complex.I • (u + v) = Complex.I • u + Complex.I • v := smul_add _ _ _
  simp only [annV, h1, map_add, fockField_add B b]; module

omit hR in
/-- `creV` is additive. -/
lemma creV_add (u v : Z) : creV B b R (u + v) = creV B b R u + creV B b R v := by
  have h1 : Complex.I • (u + v) = Complex.I • u + Complex.I • v := smul_add _ _ _
  simp only [creV, h1, map_add, fockField_add B b]; module

omit hR in
/-- `annV` is conjugate-linear. -/
lemma annV_smul (c : ℂ) (v : Z) : annV B b R (c • v) = (starRingEnd ℂ c) • annV B b R v := by
  have h2 : Complex.I • (c • v) = (Complex.I * c) • v := smul_smul _ _ _
  simp only [annV]
  rw [h2, R_smul R c v, R_smul R (Complex.I * c) v]
  simp only [fockField_add B b, fockField_real_smul B b]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  have hc : starRingEnd ℂ c = (c.re : ℂ) - c.im * Complex.I := by apply Complex.ext <;> simp
  rw [hc]
  linear_combination (norm := (match_scalars <;> (push_cast; ring_nf; try simp only [Complex.I_sq]; try ring)))

omit hR in
/-- `creV` is linear. -/
lemma creV_smul (c : ℂ) (v : Z) : creV B b R (c • v) = c • creV B b R v := by
  have h2 : Complex.I • (c • v) = (Complex.I * c) • v := smul_smul _ _ _
  simp only [creV]
  rw [h2, R_smul R c v, R_smul R (Complex.I * c) v]
  simp only [fockField_add B b, fockField_real_smul B b]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  conv_rhs => rw [← Complex.re_add_im c]
  linear_combination (norm := (match_scalars <;> (push_cast; ring_nf; try simp only [Complex.I_sq]; try ring)))

/-- The vector `annV v Ω` is continuous in `v`. -/
lemma continuous_annV_apply (Ω : Γ) : Continuous fun v : Z => annV B b R v Ω := by
  have hR' := continuous_R R hR
  have h1 : Continuous fun v : Z => fockField B b (R v) Ω :=
    ((continuous_fockField B b).comp hR').clm_apply continuous_const
  have h2 : Continuous fun v : Z => fockField B b (R (Complex.I • v)) Ω :=
    ((continuous_fockField B b).comp (hR'.comp (continuous_const_smul Complex.I))).clm_apply continuous_const
  have := (h1.add (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)
  convert this using 2
  simp [annV]

/-- **A vector killed by the transformed annihilation operators of a Hilbert basis is killed by all of them.** -/
theorem annV_kill_of_basis {κ : Type*} (e : HilbertBasis κ ℂ Z) (Ω : Γ) (h : ∀ k, annV B b R (e k) Ω = 0) (v : Z) :
    annV B b R v Ω = 0 := by
  let T : Submodule ℂ Z :=
    { carrier := {v | annV B b R v Ω = 0}
      add_mem' := fun {u v} hu hv => by
        show annV B b R (u + v) Ω = 0
        rw [annV_add B b R, ContinuousLinearMap.add_apply, show annV B b R u Ω = 0 from hu,
          show annV B b R v Ω = 0 from hv, add_zero]
      zero_mem' := by
        show annV B b R 0 Ω = 0
        have := annV_smul B b R 0 0
        simpa using congrArg (fun f => f Ω) this
      smul_mem' := fun c v hv => by
        show annV B b R (c • v) Ω = 0
        rw [annV_smul B b R, ContinuousLinearMap.smul_apply, show annV B b R v Ω = 0 from hv, smul_zero] }
  have hcl : IsClosed (T : Set Z) := isClosed_eq (continuous_annV_apply B b R hR Ω) continuous_const
  have hsub : Submodule.span ℂ (Set.range e) ≤ T := by
    rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact h k
  have hd : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤ := e.dense_span
  have : (T : Set Z) = Set.univ := by
    have h1 : closure (Submodule.span ℂ (Set.range e) : Set Z) ⊆ T := hcl.closure_subset_iff.2 hsub
    rw [← Submodule.topologicalClosure_coe, hd] at h1
    exact Set.eq_univ_of_univ_subset h1
  have hv : v ∈ (T : Set Z) := by rw [this]; trivial
  exact hv

end Lightlike.OperatorAlgebras.CARShale
