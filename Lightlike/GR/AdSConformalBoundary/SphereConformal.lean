import Lightlike.GR.AdSConformalBoundary.ScriAction

/-!
# A Lorentz transformation acts conformally on the sphere of null directions

The third layer of GE7 m1. The direction map `n ↦ n' = nullDirMap Λ n` of `NullDirection.lean` has the differential
`nullDirDeriv Λ n v` at a unit vector `n` in the direction `v`, and for a vector `v` tangent to the sphere
(`n · v = 0`) it multiplies lengths by `K⁻¹`, `K = nullDirFactor Λ n`:

* `hasDerivAt_nullDirMap`: `d/dt n'(n + t v)` at `t = 0` is `nullDirDeriv Λ n v`
  (`(R K - w D) / K²`, with `w = Λ (1, n)`, `(D, R) = Λ (0, v)`);
* `sum_sq_nullDirDeriv`: for a unit `n` and `n · v = 0`, `|dn'(v)|² = |v|² / K²`: the map is conformal on the
  round sphere, with conformal factor `K⁻²` on the metric (the proof uses only that `Λ` preserves the Minkowski
  product of `(1, n)` and `(0, v)` and the Minkowski square of `(0, v)`).

Together with `scriAct` (the action on the retarded time), this is the conformal action of the Lorentz group on the
degenerate metric `0 du² + dΩ²` of future null infinity.
-/

open Matrix

noncomputable section

namespace Lightlike

/-- The Minkowski product in coordinates: `-x₀ y₀ + Σ xᵢ yᵢ`. -/
theorem minkDot_eq (x y : Fin 4 → ℝ) :
    x ⬝ᵥ (eta 4 *ᵥ y) = -(x 0 * y 0) + ∑ i : Fin 3, x i.succ * y i.succ := by
  simp [eta, mulVec_diagonal, dotProduct, Fin.sum_univ_succ, etaDiag]

/-- The tangent vector `(0, v)`. -/
def tanVec (v : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.cons 0 v

/-- The differential of the direction map at `n` in the direction `v`. -/
def nullDirDeriv (Λ : Matrix (Fin 4) (Fin 4) ℝ) (n v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i =>
  ((Λ *ᵥ tanVec v) i.succ * (Λ *ᵥ nullVec n) 0 - (Λ *ᵥ nullVec n) i.succ * (Λ *ᵥ tanVec v) 0) /
    (Λ *ᵥ nullVec n) 0 ^ 2

theorem nullVec_add_smul (n v : Fin 3 → ℝ) (t : ℝ) : nullVec (n + t • v) = nullVec n + t • tanVec v := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [nullVec, tanVec]

/-- The differential of the direction map: `d/dt n'(n + t v)` at `t = 0`. -/
theorem hasDerivAt_nullDirMap {Λ : Matrix (Fin 4) (Fin 4) ℝ} {n : Fin 3 → ℝ}
    (hK : nullDirFactor Λ n ≠ 0) (v : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => nullDirMap Λ (n + t • v) i) (nullDirDeriv Λ n v i) 0 := by
  have hcomp : ∀ (t : ℝ) (j : Fin 4), (Λ *ᵥ nullVec (n + t • v)) j =
      (Λ *ᵥ nullVec n) j + t * (Λ *ᵥ tanVec v) j := by
    intro t j
    simp [nullVec_add_smul, mulVec_add, mulVec_smul]
  have hnum : HasDerivAt (fun t : ℝ => (Λ *ᵥ nullVec n) i.succ + t * (Λ *ᵥ tanVec v) i.succ)
      ((Λ *ᵥ tanVec v) i.succ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Λ *ᵥ tanVec v) i.succ)).const_add
      ((Λ *ᵥ nullVec n) i.succ)
  have hden : HasDerivAt (fun t : ℝ => (Λ *ᵥ nullVec n) 0 + t * (Λ *ᵥ tanVec v) 0)
      ((Λ *ᵥ tanVec v) 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Λ *ᵥ tanVec v) 0)).const_add
      ((Λ *ᵥ nullVec n) 0)
  have hK' : (Λ *ᵥ nullVec n) 0 + 0 * (Λ *ᵥ tanVec v) 0 ≠ 0 := by simpa [nullDirFactor] using hK
  have h := hnum.div hden hK'
  have hfun : (fun t : ℝ => nullDirMap Λ (n + t • v) i) = fun t =>
      ((Λ *ᵥ nullVec n) i.succ + t * (Λ *ᵥ tanVec v) i.succ) /
        ((Λ *ᵥ nullVec n) 0 + t * (Λ *ᵥ tanVec v) 0) := by
    ext t
    simp only [nullDirMap, nullDirFactor, hcomp]
  rw [hfun]
  convert h using 1
  simp [nullDirDeriv]

/-- **Conformality on the sphere**: for a unit `n` and `v` tangent to the sphere, `|dn'(v)|² = |v|² / K²`. -/
theorem sum_sq_nullDirDeriv {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hL : Λᵀ * eta 4 * Λ = eta 4)
    (h0 : 0 < Λ 0 0) {n v : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) (hv : ∑ i, n i * v i = 0) :
    ∑ i, nullDirDeriv Λ n v i ^ 2 = (∑ i, v i ^ 2) / nullDirFactor Λ n ^ 2 := by
  set w := Λ *ᵥ nullVec n with hw
  set q := Λ *ᵥ tanVec v with hq
  have hK : 0 < w 0 := nullDirFactor_pos hL h0 hn
  -- the three invariants
  have h1 : minkSq w = 0 := by
    rw [hw, minkSq_mulVec hL]; exact minkSq_nullVec hn
  have h2 : minkSq q = ∑ i, v i ^ 2 := by
    rw [hq, minkSq_mulVec hL]; simp [minkSq, tanVec]
  have h3 : w ⬝ᵥ (eta 4 *ᵥ q) = 0 := by
    rw [hw, hq, minkDot_mulVec hL, minkDot_eq]; simp [nullVec, tanVec, hv]
  rw [minkDot_eq] at h3
  simp only [minkSq] at h1 h2
  have hA : ∑ i : Fin 3, w i.succ ^ 2 = w 0 ^ 2 := by linarith
  have hB : ∑ i : Fin 3, w i.succ * q i.succ = w 0 * q 0 := by linarith
  have hC : ∑ i : Fin 3, q i.succ ^ 2 = q 0 ^ 2 + ∑ i, v i ^ 2 := by linarith
  have hexp : ∑ i : Fin 3, (q i.succ * w 0 - w i.succ * q 0) ^ 2 = w 0 ^ 2 * ∑ i, v i ^ 2 := by
    have : ∀ i : Fin 3, (q i.succ * w 0 - w i.succ * q 0) ^ 2 =
        w 0 ^ 2 * q i.succ ^ 2 - 2 * w 0 * q 0 * (w i.succ * q i.succ) + q 0 ^ 2 * w i.succ ^ 2 := by
      intro i; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hA, hB, hC]
    ring
  have hKf : nullDirFactor Λ n = w 0 := rfl
  rw [hKf]
  simp only [nullDirDeriv, div_pow, ← Finset.sum_div, ← hw, ← hq]
  rw [hexp]
  field_simp

/-- Non-vacuity: the boost `boostX` at the direction `e₁` sends the tangent vector `e₂` to `e₂ / 2`, so lengths
are divided by `K = 2`. -/
theorem nullDirDeriv_boostX : nullDirDeriv boostX ![1, 0, 0] ![0, 1, 0] = ![0, 1 / 2, 0] := by
  ext i
  fin_cases i
  · simp [nullDirDeriv, nullVec, tanVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [nullDirDeriv, nullVec, tanVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]
    norm_num
  · simp [nullDirDeriv, nullVec, tanVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]

end Lightlike
