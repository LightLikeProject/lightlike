import Lightlike.Cosmology.BianchiClassification.Basic

/-!
# Every alternating bilinear bracket on `ℝ³` has Bianchi form

An alternating bilinear map `B : ℝ³ × ℝ³ → ℝ³` factors through the cross product,
`B x y = M (x × y)`, and splitting `M` into symmetric and antisymmetric parts gives
`B = bracket n a` with `n` symmetric.  If `B` satisfies the Jacobi identity then `n a = 0`.

## Main results

* `Lightlike.Rows.G1_039.exists_bracket_eq`: an alternating bilinear `B` equals `bracket n a`
  for some symmetric `n` and some `a`.
* `Lightlike.Rows.G1_039.exists_bracket_eq_of_jacobi`: if moreover `B` satisfies Jacobi, then
  `n a = 0`.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Rows.G1_039

/-- The space `ℝ³`. -/
abbrev V3 : Type := Fin 3 → ℝ

/-- Alternating bilinear maps are antisymmetric. -/
theorem alt_antisymm (B : V3 →ₗ[ℝ] V3 →ₗ[ℝ] V3) (hB : ∀ x, B x x = 0) (x y : V3) :
    B y x = - B x y := by
  have h := hB (x + y)
  simp only [map_add, LinearMap.add_apply, hB x, hB y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h)

/-- An alternating bilinear map is determined by its values on the basis pairs. -/
theorem alt_apply (B : V3 →ₗ[ℝ] V3 →ₗ[ℝ] V3) (hB : ∀ x, B x x = 0) (x y : V3) :
    B x y = (x 1 * y 2 - x 2 * y 1) • B (Pi.single 1 1) (Pi.single 2 1) +
      (x 2 * y 0 - x 0 * y 2) • B (Pi.single 2 1) (Pi.single 0 1) +
      (x 0 * y 1 - x 1 * y 0) • B (Pi.single 0 1) (Pi.single 1 1) := by
  have hx : x = x 0 • (Pi.single 0 1 : V3) + x 1 • (Pi.single 1 1 : V3) +
      x 2 • (Pi.single 2 1 : V3) := by
    ext i; fin_cases i <;> simp
  have hy : y = y 0 • (Pi.single 0 1 : V3) + y 1 • (Pi.single 1 1 : V3) +
      y 2 • (Pi.single 2 1 : V3) := by
    ext i; fin_cases i <;> simp
  have a10 := alt_antisymm B hB (Pi.single 0 1) (Pi.single 1 1)
  have a20 := alt_antisymm B hB (Pi.single 2 1) (Pi.single 0 1)
  have a21 := alt_antisymm B hB (Pi.single 1 1) (Pi.single 2 1)
  have z0 := hB (Pi.single 0 1)
  have z1 := hB (Pi.single 1 1)
  have z2 := hB (Pi.single 2 1)
  conv_lhs => rw [hx, hy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, z0, z1, z2, smul_zero,
    a10, a20, a21]
  module

/-- An alternating bilinear bracket on `ℝ³` is `bracket n a` for a symmetric matrix `n` and a
vector `a` (splitting `B x y = M (x × y)` into symmetric and antisymmetric parts of `M`). -/
theorem exists_bracket_eq (B : V3 →ₗ[ℝ] V3 →ₗ[ℝ] V3) (hB : ∀ x, B x x = 0) :
    ∃ (n : Matrix (Fin 3) (Fin 3) ℝ) (a : V3), n.IsSymm ∧ ∀ x y, B x y = bracket n a x y := by
  set M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j =>
    (![B (Pi.single 1 1) (Pi.single 2 1), B (Pi.single 2 1) (Pi.single 0 1),
      B (Pi.single 0 1) (Pi.single 1 1)] j : V3) i with hM
  refine ⟨(1 / 2 : ℝ) • (M + M.transpose),
    ![(M 1 2 - M 2 1) / 2, (M 2 0 - M 0 2) / 2, (M 0 1 - M 1 0) / 2], ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  · intro x y
    rw [alt_apply B hB x y]
    ext i
    fin_cases i <;>
    simp [bracket, hM, crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- If moreover the bracket satisfies the Jacobi identity, then `n a = 0`. -/
theorem exists_bracket_eq_of_jacobi (B : V3 →ₗ[ℝ] V3 →ₗ[ℝ] V3) (hB : ∀ x, B x x = 0)
    (hJ : ∀ x y z, B (B x y) z + B (B y z) x + B (B z x) y = 0) :
    ∃ (n : Matrix (Fin 3) (Fin 3) ℝ) (a : V3), n.IsSymm ∧ n.mulVec a = 0 ∧
      ∀ x y, B x y = bracket n a x y := by
  obtain ⟨n, a, hn, h⟩ := exists_bracket_eq B hB
  refine ⟨n, a, hn, ?_, h⟩
  rw [← jacobi_bracket_iff n hn a]
  intro x y z
  simpa [jacobi, ← h] using hJ x y z

end Lightlike.Rows.G1_039
