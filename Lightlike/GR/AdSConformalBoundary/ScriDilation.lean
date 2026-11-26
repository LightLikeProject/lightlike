import Lightlike.GR.AdSConformalBoundary.ScriLimit

/-!
# The dilation acts on null infinity

The fifth layer of GE7 m1. The dilation `x ↦ c x` (`c > 0`) acts on the retarded time and direction of a point of
Minkowski space by `(u, n) ↦ (c u, n)`:

* `scriDil c`: the map `(u, n) ↦ (c u, n)` on `ℝ × (Fin 3 → ℝ)`;
* `scriCoord_smul`: `scriCoord (c • x) = scriDil c (scriCoord x)` for `c > 0`;
* `scriDil_scriAct`: the dilation and the Poincaré action are compatible,
  `scriDil c (scriAct Λ a p) = scriAct Λ (c • a) (scriDil c p)`: with the Poincaré group it generates the similarity
  group of Minkowski space acting on null infinity (the dilation scales the retarded time, the Lorentz group the
  direction, the translations shift the retarded time).
-/

open Matrix

noncomputable section

namespace Lightlike

/-- The dilation `(u, n) ↦ (c u, n)` of null infinity. -/
def scriDil (c : ℝ) (p : ℝ × (Fin 3 → ℝ)) : ℝ × (Fin 3 → ℝ) := (c * p.1, p.2)

theorem scriDil_one (p : ℝ × (Fin 3 → ℝ)) : scriDil 1 p = p := by simp [scriDil]

theorem scriDil_mul (c d : ℝ) (p : ℝ × (Fin 3 → ℝ)) : scriDil c (scriDil d p) = scriDil (c * d) p := by
  simp [scriDil, mul_assoc]

/-- The norm of a scaled vector. -/
theorem eNorm_smul {c : ℝ} (hc : 0 ≤ c) (w : Fin 3 → ℝ) : eNorm (c • w) = c * eNorm w := by
  simp only [eNorm, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **The dilation acts on the retarded time and the direction by `(u, n) ↦ (c u, n)`.** -/
theorem scriCoord_smul {c : ℝ} (hc : 0 < c) (x : Fin 4 → ℝ) :
    scriCoord (c • x) = scriDil c (scriCoord x) := by
  have hn : eNorm (fun i => (c • x) i.succ) = c * eNorm (fun i => x i.succ) := by
    exact eNorm_smul hc.le (fun i => x i.succ)
  simp only [scriCoord, scriDil, hn]
  refine Prod.ext ?_ ?_
  · simp only [Pi.smul_apply, smul_eq_mul]; ring
  · ext i
    simp only [Pi.smul_apply, smul_eq_mul, mul_inv]
    by_cases h : eNorm (fun i => x i.succ) = 0
    · simp [h]
    · field_simp

/-- The dilation commutes with the Poincaré action, the translation being scaled. -/
theorem scriDil_scriAct (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 4 → ℝ) (c : ℝ) (p : ℝ × (Fin 3 → ℝ)) :
    scriDil c (scriAct Λ a p) = scriAct Λ (c • a) (scriDil c p) := by
  simp only [scriDil, scriAct, Pi.smul_apply, smul_eq_mul]
  refine Prod.ext ?_ rfl
  show c * (p.1 / nullDirFactor Λ p.2 + a 0 - ∑ i, nullDirMap Λ p.2 i * a i.succ) =
    c * p.1 / nullDirFactor Λ p.2 + c * a 0 - ∑ i, nullDirMap Λ p.2 i * (c * a i.succ)
  have : ∑ i : Fin 3, nullDirMap Λ p.2 i * (c * a i.succ) = c * ∑ i, nullDirMap Λ p.2 i * a i.succ := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [this]; ring

end Lightlike
