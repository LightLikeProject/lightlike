import Lightlike.NCG.QuaternionMatrix
import Lightlike.NCG.FiniteSpectralTriple

/-!
# Complexifying a real representation of the quaternions

Every complex `2 × 2` matrix is a unique complex combination of `ι(1), ι(i), ι(j), ι(k)` (`ι = quatToMat`), with
coordinates `quatCoord M = ((M₀₀ + M₁₁)/2, i(M₁₁ - M₀₀)/2, (M₀₁ - M₁₀)/2, -i(M₀₁ + M₁₀)/2)`. So a real-linear map
`ρ` on `ℍ` extends complex-linearly to `ρ_ℂ(M) = ∑ₖ quatCoord M k • ρ(bₖ)` on `M₂(ℂ) = ℍ ⊗_ℝ ℂ`.

* `quatBasis`, `quatCoord`, `quat_decomp`, `quatCoord_quatToMat`, `quat_eq_sum`;
* `complexify`, `complexify_quatToMat`: `ρ_ℂ ∘ ι = ρ`;
* `quatCoord_add`, `quatCoord_smul`, `complexifyL`, `complexify_mul`: `ρ_ℂ` is complex-linear and multiplicative;
* `complexify_mul_of`, `complexify_sum`: the bimodule form `ρ₁_ℂ(M) ρ₂_ℂ(N) = ρ₃_ℂ(MN)` and linearity in the coefficients.
-/

open Matrix
open scoped Quaternion

namespace Lightlike.NCG

/-- The real basis `1, i, j, k` of `ℍ`. -/
def quatBasis : Fin 4 → ℍ[ℝ] := ![1, qI, qJ, qK]

/-- The coordinates of `M ∈ M₂(ℂ)` in the complex basis `ι(1), ι(i), ι(j), ι(k)`. -/
noncomputable def quatCoord (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℂ :=
  ![(M 0 0 + M 1 1) / 2, Complex.I * (M 1 1 - M 0 0) / 2, (M 0 1 - M 1 0) / 2,
    -(Complex.I * (M 0 1 + M 1 0)) / 2]

/-- **`M = ∑ₖ quatCoord M k • ι(bₖ)`.** -/
theorem quat_decomp (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = ∑ k, quatCoord M k • quatToMat (quatBasis k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, quatCoord, quatBasis, quatToMat_apply, qI, qJ, qK, Complex.ext_iff] <;>
    (try constructor) <;> ring

/-- **The coordinates of `ι(q)`** are the real components of `q`. -/
lemma quatCoord_quatToMat (q : ℍ[ℝ]) :
    quatCoord (quatToMat q) = ![(q.re : ℂ), (q.imI : ℂ), (q.imJ : ℂ), (q.imK : ℂ)] := by
  ext k
  fin_cases k <;> simp [quatCoord, quatToMat_apply, Complex.ext_iff] <;> (try constructor) <;> ring

/-- `q = re + imI i + imJ j + imK k`. -/
lemma quat_eq_sum (q : ℍ[ℝ]) : q = ∑ k, (![q.re, q.imI, q.imJ, q.imK] k) • quatBasis k := by
  ext <;> simp [Fin.sum_univ_four, quatBasis, qI, qJ, qK]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The complexification** `ρ_ℂ(M) = ∑ₖ quatCoord M k • ρ(bₖ)` of a real-linear map `ρ : ℍ → End(H)`. -/
noncomputable def complexify (ρ : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (M : Matrix (Fin 2) (Fin 2) ℂ) : H →L[ℂ] H :=
  ∑ k, quatCoord M k • ρ (quatBasis k)

/-- **`ρ_ℂ(ι(q)) = ρ(q)`.** -/
lemma complexify_quatToMat (ρ : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (q : ℍ[ℝ]) : complexify ρ (quatToMat q) = ρ q := by
  rw [complexify, quatCoord_quatToMat]
  conv_rhs => rw [quat_eq_sum q, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  have hk : (![(q.re : ℂ), (q.imI : ℂ), (q.imJ : ℂ), (q.imK : ℂ)] k) =
      ((![q.re, q.imI, q.imJ, q.imK] k : ℝ) : ℂ) := by
    fin_cases k <;> rfl
  rw [hk]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

lemma quatCoord_add (M N : Matrix (Fin 2) (Fin 2) ℂ) : quatCoord (M + N) = quatCoord M + quatCoord N := by
  ext k
  fin_cases k <;> simp [quatCoord] <;> ring

lemma quatCoord_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : quatCoord (c • M) = c • quatCoord M := by
  ext k
  fin_cases k <;> simp [quatCoord] <;> ring

/-- `ρ_ℂ` as a complex-linear map. -/
noncomputable def complexifyL (ρ : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := complexify ρ
  map_add' M N := by
    simp only [complexify, quatCoord_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [complexify, quatCoord_smul, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

lemma complexifyL_apply (ρ : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    complexifyL ρ M = complexify ρ M := rfl

/-- **`ρ_ℂ` is multiplicative** for a multiplicative `ρ`: `ℍ ⊗_ℝ ℂ ≅ M₂(ℂ)` turns a real `*`-representation of `ℍ` into
a complex representation of `M₂(ℂ)`. -/
theorem complexify_mul (ρ : ℍ[ℝ] →ₐ[ℝ] (H →L[ℂ] H)) (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    complexify ρ.toLinearMap (M * N) = complexify ρ.toLinearMap M * complexify ρ.toLinearMap N := by
  have hMN : M * N = ∑ k, ∑ l, (quatCoord M k * quatCoord N l) • quatToMat (quatBasis k * quatBasis l) := by
    conv_lhs => rw [quat_decomp M, quat_decomp N]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, map_mul]
  rw [← complexifyL_apply, hMN, map_sum]
  simp only [map_sum, map_smul, complexifyL_apply, complexify_quatToMat, AlgHom.toLinearMap_apply]
  rw [complexify, complexify, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [AlgHom.toLinearMap_apply, map_mul, smul_mul_smul_comm]

/-- **The bimodule form**: if `ρ₁(p) ρ₂(q) = ρ₃(pq)` for all quaternions, then `ρ₁_ℂ(M) ρ₂_ℂ(N) = ρ₃_ℂ(MN)`. For
`ρ₁ = π ∘ E_αβ`, `ρ₂ = π ∘ E_βγ`, `ρ₃ = π ∘ E_αγ` this gives the matrix units of `M₂ₙ(ℂ)` from a representation of
`Mₙ(ℍ)`. -/
theorem complexify_mul_of (ρ₁ ρ₂ ρ₃ : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (h : ∀ p q, ρ₁ p * ρ₂ q = ρ₃ (p * q))
    (M N : Matrix (Fin 2) (Fin 2) ℂ) : complexify ρ₁ M * complexify ρ₂ N = complexify ρ₃ (M * N) := by
  have hMN : M * N = ∑ k, ∑ l, (quatCoord M k * quatCoord N l) • quatToMat (quatBasis k * quatBasis l) := by
    conv_lhs => rw [quat_decomp M, quat_decomp N]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, map_mul]
  rw [show complexify ρ₃ (M * N) = complexifyL ρ₃ (M * N) from rfl, hMN, map_sum]
  simp only [map_sum, map_smul, complexifyL_apply, complexify_quatToMat]
  rw [complexify, complexify, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [smul_mul_smul_comm, h]

/-- **`ρ_ℂ` is linear in the coefficients**: `ρ_ℂ(∑ⱼ cⱼ ι(qⱼ)) = ∑ⱼ cⱼ ρ(qⱼ)`. -/
lemma complexify_sum {κ : Type*} [Fintype κ] (ρ : ℍ[ℝ] →ₗ[ℝ] (H →L[ℂ] H)) (c : κ → ℂ) (q : κ → ℍ[ℝ]) :
    complexify ρ (∑ j, c j • quatToMat (q j)) = ∑ j, c j • ρ (q j) := by
  rw [show complexify ρ (∑ j, c j • quatToMat (q j)) = complexifyL ρ (∑ j, c j • quatToMat (q j)) from rfl, map_sum]
  simp only [map_smul, complexifyL_apply, complexify_quatToMat]

end Lightlike.NCG
