import Lightlike.Asymptotics.EPRL.EprlCoherentVertex

/-!
# The EPRL map, fusion coefficients and node tensor for `γ > 1`

For `γ > 1` the simplicity constraint selects the lowest irreducible component `k = j⁺ - j⁻` of
`V_{j⁺} ⊗ V_{j⁻}` (Engle–Pereira–Rovelli–Livine, arXiv:0711.0146, Section III, eq. (27); Barrett–Dowdall–
Fairbairn–Gomes–Hellmann, arXiv:0902.1170, Section 3.4, Figure 4 and eqs. (17)–(19)). This file copies
the `γ < 1` definitions of `Fusion.lean` and `Vertex.lean` with the lowest Clebsch–Gordan component
`eprlMapLow` in place of the highest one, for doubled spins `n`, `m` with `m ≤ n` and the `SU(2)` spin
`k = n - m` on every leg.

## Main results

* `eprlMapLow`, `eprlMapLow_isometry`, `eprlMapLow_equivariant`: the map and its basic properties
  (from `cgz`).
* `eprlPairLow`, `eprlPairLow_equivariant`: the map on two legs.
* `eprlLiftLow`, `eprlIntertwinerLow`, `fusionLow`, `eprlIntertwinerLow_ivec`: the lift, the projection
  to Spin(4) intertwiners and the fusion coefficients.
* `eprlNodeLow`, `eprlNodeLow_eq_eprlIntertwinerLow`: the node tensor and its bridge to the matrix
  form, with the signs of the two incoming legs (as for `γ < 1`).

## References

* J. Engle, R. Pereira, C. Rovelli, E. Livine, *Nucl. Phys. B* 799 (2008) 136, arXiv:0711.0146,
  Section III, eq. (27).
* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4.
-/

open Matrix Finset
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

/-- **The EPRL map for `γ > 1`**: the lowest Clebsch–Gordan component
`V_{(n-m)/2} → V_{n/2} ⊗ V_{m/2}` (EPRL, arXiv:0711.0146, Section III, eq. (27): `k = j⁺ - j⁻`). -/
noncomputable def eprlMapLow (n m : ℕ) : Matrix (Idx n m) (Fin (n - m + 1)) ℂ := cgz n m (n - m)

theorem tri_sub {n m : ℕ} (h : m ≤ n) : Pentagon.Tri n m (n - m) := by
  rw [tri_iff_exists]
  exact ⟨m, h, le_rfl, by omega⟩

/-- `Y_low` is an isometry. -/
theorem eprlMapLow_isometry {n m : ℕ} (h : m ≤ n) : (eprlMapLow n m)ᴴ * eprlMapLow n m = 1 :=
  cgz_isometry (tri_sub h)

/-- `Y_low` is `SU(2)`-equivariant. -/
theorem eprlMapLow_equivariant {n m : ℕ} (h : m ≤ n) (g : SU2) :
    (spinMat n g ⊗ₖ spinMat m g) * eprlMapLow n m = eprlMapLow n m * spinMat (n - m) g :=
  cgz_equivariant (tri_sub h) g

/-- The pair map for `γ > 1`, `Y₁ ⊗ Y₂` with the target regrouped by `shuffle`. -/
noncomputable def eprlPairLow (n₁ m₁ n₂ m₂ : ℕ) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx (n₁ - m₁) (n₂ - m₂)) ℂ :=
  (eprlMapLow n₁ m₁ ⊗ₖ eprlMapLow n₂ m₂).submatrix (shuffle n₁ m₁ n₂ m₂).symm id

/-- `Y₁ ⊗ Y₂` is equivariant for the diagonal `SU(2)`. -/
theorem eprlPairLow_equivariant {n₁ m₁ n₂ m₂ : ℕ} (h₁ : m₁ ≤ n₁) (h₂ : m₂ ≤ n₂) (g : SU2) :
    (pairMat n₁ n₂ g ⊗ₖ pairMat m₁ m₂ g) * eprlPairLow n₁ m₁ n₂ m₂ =
      eprlPairLow n₁ m₁ n₂ m₂ * pairMat (n₁ - m₁) (n₂ - m₂) g := by
  have h := spin4Mat_kronecker n₁ n₂ m₁ m₂ (g, g)
  have h' : pairMat n₁ n₂ g ⊗ₖ pairMat m₁ m₂ g = (spin4Mat n₁ m₁ (g, g) ⊗ₖ
      spin4Mat n₂ m₂ (g, g)).submatrix (shuffle n₁ m₁ n₂ m₂).symm (shuffle n₁ m₁ n₂ m₂).symm := by
    rw [h, submatrix_submatrix]
    simp
  rw [h', eprlPairLow, submatrix_mul_equiv, ← mul_kronecker_mul]
  simp only [spin4Mat]
  rw [eprlMapLow_equivariant h₁, eprlMapLow_equivariant h₂, mul_kronecker_mul]
  ext P c
  simp [mul_apply, submatrix_apply]

section Node

variable (n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ)

/-- The EPRL map for `γ > 1` before projection, `T ↦ (Y₁ ⊗ Y₂) T (Y₃ ⊗ Y₄)ᴴ`. -/
noncomputable def eprlLiftLow
    (T : Matrix (Idx (n₁ - m₁) (n₂ - m₂)) (Idx (n₃ - m₃) (n₄ - m₄)) ℂ) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ :=
  eprlPairLow n₁ m₁ n₂ m₂ * T * (eprlPairLow n₃ m₃ n₄ m₄)ᴴ

/-- **The EPRL map on 4-valent intertwiners for `γ > 1`**, `Φ(T) = P (Y₁ ⊗ Y₂) T (Y₃ ⊗ Y₄)ᴴ`. -/
noncomputable def eprlIntertwinerLow
    (T : Matrix (Idx (n₁ - m₁) (n₂ - m₂)) (Idx (n₃ - m₃) (n₄ - m₄)) ℂ) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ :=
  projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (eprlLiftLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T)

/-- **The fusion coefficients for `γ > 1`**,
`f(z; x, y) = ⟨ι⁺_x ⊗ ι⁻_y, (Y₁ ⊗ Y₂) ι_z (Y₃ ⊗ Y₄)ᴴ⟩`, with `ι_z` the `SU(2)` intertwiner of the
spins `n - m`. -/
noncomputable def fusionLow (z x y : ℕ) : ℂ :=
  hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ x y)
    (eprlLiftLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄
      (ivec (n₁ - m₁) (n₂ - m₂) (n₃ - m₃) (n₄ - m₄) z))

/-- `Φ(ι_z) = Σ_{x,y} f(z; x, y) ι⁺_x ⊗ ι⁻_y` for `γ > 1`. -/
theorem eprlIntertwinerLow_ivec (z : ℕ) :
    eprlIntertwinerLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (ivec (n₁ - m₁) (n₂ - m₂) (n₃ - m₃) (n₄ - m₄) z) =
      ∑ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
        fusionLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z p.1 p.2 • ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2 :=
  rfl

end Node

/-- **The EPRL node tensor for `γ > 1`** of the `SU(2)` intertwiner `ι_z` of spins `n - m`:
`Σ_{x,y} f(z; x, y) ι⁺_x ⊗ ι⁻_y` as a function of the projections. -/
noncomputable def eprlNodeLow (n m : Fin 4 → ℕ) (z : ℕ) (μ ν : Fin 4 → ℤ) : ℂ :=
  ∑ p ∈ nodeChannel4 n m, fusionLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) z p.1 p.2 *
    (fourJNode n p.1 μ * fourJNode m p.2 ν)

/-- **The node tensor for `γ > 1` is `Φ(ι_z)`**, with the signs of the invariant forms of the two
incoming legs (as for `γ < 1`: `fourJ_eq_ivec` does not depend on the EPRL map). -/
theorem eprlNodeLow_eq_eprlIntertwinerLow {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ} (z : ℕ)
    (P : Idx n₁ n₂ × Idx m₁ m₂) (Q : Idx n₃ n₄ × Idx m₃ m₄) :
    eprlNodeLow ![n₁, n₂, n₃, n₄] ![m₁, m₂, m₃, m₄] z
        ![(n₁ : ℤ) - 2 * (P.1.1 : ℕ), (n₂ : ℤ) - 2 * (P.1.2 : ℕ), 2 * (Q.1.1 : ℕ) - n₃,
          2 * (Q.1.2 : ℕ) - n₄]
        ![(m₁ : ℤ) - 2 * (P.2.1 : ℕ), (m₂ : ℤ) - 2 * (P.2.2 : ℕ), 2 * (Q.2.1 : ℕ) - m₃,
          2 * (Q.2.2 : ℕ) - m₄] =
      (-1 : ℂ) ^ (n₂ + n₄ + (P.1.1 : ℕ) + P.1.2) * (-1 : ℂ) ^ (m₂ + m₄ + (P.2.1 : ℕ) + P.2.2) *
        eprlIntertwinerLow n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄
          (ivec (n₁ - m₁) (n₂ - m₂) (n₃ - m₃) (n₄ - m₄) z) P Q := by
  rw [eprlIntertwinerLow_ivec, Matrix.sum_apply, Finset.mul_sum]
  simp only [eprlNodeLow, nodeChannel4, fourJNode, Matrix.cons_val]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hx, hy⟩ := mem_product.mp hp
  rw [fourJ_eq_ivec hx P.1 Q.1, fourJ_eq_ivec hy P.2 Q.2]
  simp only [Matrix.smul_apply, ivec4, kroneckerMap_apply, smul_eq_mul]
  ring

end Lightlike.Asymptotics.EPRL
