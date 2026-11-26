import Lightlike.GR.AdSConformalBoundary.NullDirection

/-!
# The Poincaré group acts on future null infinity

The second layer of GE7 m1. A point of future null infinity of Minkowski space is a retarded time `u` and a direction
`n` of the unit sphere (`scriPoint` of `ScriPlus.lean` in the compactified chart); in Cartesian coordinates a point
`x = (t, x⃗)` has retarded time `u = t - n · x⃗` along the null direction `(1, n)`. A Poincaré transformation
`x ↦ Λ x + a` with `Λ (1, n) = K (1, n')` (`NullDirection.lean`) sends `(u, n)` to
`(u / K + a₀ - n' · a⃗, n')`:

* `scriAct Λ a`: this map on `ℝ × (Fin 3 → ℝ)`; the retarded time is divided by the factor `K = nullDirFactor Λ n`,
  the direction moves by `nullDirMap Λ n`, and the translation adds `-(1, n') · a` (the Minkowski product);
* `scriAct_one`: the identity acts as the identity;
* `nullDirFactor_mul`, `nullDirMap_mul`: the cocycle rule for the product of two Lorentz matrices;
* `scriAct_comp`: `scriAct Λ₁ a₁ ∘ scriAct Λ₂ a₂ = scriAct (Λ₁ Λ₂) (Λ₁ a₂ + a₁)`, the group law of the Poincaré group.

The conformal factor on the sphere and the relation to the compactified chart are the next layers.
-/

open Matrix

noncomputable section

namespace Lightlike

/-- A Lorentz matrix preserving the time orientation: `Λᵀ η Λ = η` and `Λ₀₀ > 0`. -/
structure IsOrthochronous (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  lorentz : Λᵀ * eta 4 * Λ = eta 4
  pos : 0 < Λ 0 0

/-- The identity is orthochronous. -/
theorem IsOrthochronous.one : IsOrthochronous (1 : Matrix (Fin 4) (Fin 4) ℝ) :=
  ⟨by simp, by simp⟩

/-- The action of `x ↦ Λ x + a` on a point `(u, n)` of future null infinity. -/
def scriAct (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 4 → ℝ) (p : ℝ × (Fin 3 → ℝ)) :
    ℝ × (Fin 3 → ℝ) :=
  (p.1 / nullDirFactor Λ p.2 + a 0 - ∑ i : Fin 3, nullDirMap Λ p.2 i * a i.succ, nullDirMap Λ p.2)

theorem scriAct_one (p : ℝ × (Fin 3 → ℝ)) : scriAct 1 0 p = p := by
  simp [scriAct, nullDirFactor_one, nullDirMap_one]

theorem scriAct_snd (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 4 → ℝ) (p : ℝ × (Fin 3 → ℝ)) :
    (scriAct Λ a p).2 = nullDirMap Λ p.2 := rfl

/-- The retarded time of the image is `u / K - (1, n') · a` (Minkowski product). -/
theorem scriAct_fst (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 4 → ℝ) (p : ℝ × (Fin 3 → ℝ)) :
    (scriAct Λ a p).1 = p.1 / nullDirFactor Λ p.2 - nullVec (nullDirMap Λ p.2) ⬝ᵥ (eta 4 *ᵥ a) := by
  simp only [scriAct, nullVec_dot]
  ring

/-- The cocycle rule for the factor: `K(Λ₁Λ₂, n) = K(Λ₂, n) K(Λ₁, n₂')`. -/
theorem mulVec_mul_nullVec {Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ} (h₁ : IsOrthochronous Λ₁)
    (h₂ : IsOrthochronous Λ₂) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    (Λ₁ * Λ₂) *ᵥ nullVec n =
      (nullDirFactor Λ₂ n * nullDirFactor Λ₁ (nullDirMap Λ₂ n)) •
        nullVec (nullDirMap Λ₁ (nullDirMap Λ₂ n)) := by
  have hn' := sum_sq_nullDirMap h₂.lorentz h₂.pos hn
  rw [← mulVec_mulVec, mulVec_nullVec_eq h₂.lorentz h₂.pos hn, mulVec_smul,
    mulVec_nullVec_eq h₁.lorentz h₁.pos hn', smul_smul]

/-- The factor of a product: `K(Λ₁Λ₂, n) = K(Λ₂, n) K(Λ₁, n₂')`. -/
theorem nullDirFactor_mul {Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ} (h₁ : IsOrthochronous Λ₁)
    (h₂ : IsOrthochronous Λ₂) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    nullDirFactor (Λ₁ * Λ₂) n = nullDirFactor Λ₂ n * nullDirFactor Λ₁ (nullDirMap Λ₂ n) := by
  have := congrFun (mulVec_mul_nullVec h₁ h₂ hn) 0
  simpa [nullDirFactor, nullVec] using this

/-- The direction of a product: `(Λ₁Λ₂) n = Λ₁ (Λ₂ n)`. -/
theorem nullDirMap_mul {Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ} (h₁ : IsOrthochronous Λ₁)
    (h₂ : IsOrthochronous Λ₂) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    nullDirMap (Λ₁ * Λ₂) n = nullDirMap Λ₁ (nullDirMap Λ₂ n) := by
  have hK : 0 < nullDirFactor Λ₂ n * nullDirFactor Λ₁ (nullDirMap Λ₂ n) :=
    mul_pos (nullDirFactor_pos h₂.lorentz h₂.pos hn)
      (nullDirFactor_pos h₁.lorentz h₁.pos (sum_sq_nullDirMap h₂.lorentz h₂.pos hn))
  ext i
  have hv := congrFun (mulVec_mul_nullVec h₁ h₂ hn) i.succ
  simp only [nullVec, Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hv
  show ((Λ₁ * Λ₂) *ᵥ nullVec n) i.succ / nullDirFactor (Λ₁ * Λ₂) n = _
  rw [nullVec, hv, nullDirFactor_mul h₁ h₂ hn]
  exact mul_div_cancel_left₀ _ hK.ne'

/-- **The group law**: acting by `Λ₂, a₂` and then by `Λ₁, a₁` is acting by `Λ₁ Λ₂, Λ₁ a₂ + a₁`. -/
theorem scriAct_comp {Λ₁ Λ₂ : Matrix (Fin 4) (Fin 4) ℝ} (h₁ : IsOrthochronous Λ₁)
    (h₂ : IsOrthochronous Λ₂) (a₁ a₂ : Fin 4 → ℝ) {p : ℝ × (Fin 3 → ℝ)} (hn : ∑ i, p.2 i ^ 2 = 1) :
    scriAct Λ₁ a₁ (scriAct Λ₂ a₂ p) = scriAct (Λ₁ * Λ₂) (Λ₁ *ᵥ a₂ + a₁) p := by
  have hn' : ∑ i, nullDirMap Λ₂ p.2 i ^ 2 = 1 := sum_sq_nullDirMap h₂.lorentz h₂.pos hn
  have hK₂ := nullDirFactor_pos h₂.lorentz h₂.pos hn
  have hK₁ := nullDirFactor_pos h₁.lorentz h₁.pos hn'
  have hkey := minkDot_mulVec h₁.lorentz (nullVec (nullDirMap Λ₂ p.2)) a₂
  rw [mulVec_nullVec_eq h₁.lorentz h₁.pos hn', smul_dotProduct, smul_eq_mul] at hkey
  have hD : nullVec (nullDirMap Λ₁ (nullDirMap Λ₂ p.2)) ⬝ᵥ (eta 4 *ᵥ (Λ₁ *ᵥ a₂)) =
      (nullVec (nullDirMap Λ₂ p.2) ⬝ᵥ (eta 4 *ᵥ a₂)) / nullDirFactor Λ₁ (nullDirMap Λ₂ p.2) := by
    rw [← hkey]
    field_simp
  refine Prod.ext ?_ ?_
  · simp only [scriAct_fst, scriAct_snd, mulVec_add, dotProduct_add, nullDirFactor_mul h₁ h₂ hn,
      nullDirMap_mul h₁ h₂ hn]
    rw [hD]
    field_simp
    ring
  · simp only [scriAct]
    exact (nullDirMap_mul h₁ h₂ hn).symm

/-- Non-vacuity: the boost `boostX` sends the point `(u, e₁)` to `(u / 2, e₁)` (the Doppler factor `2`). -/
theorem scriAct_boostX (u : ℝ) : scriAct boostX 0 (u, ![1, 0, 0]) = (u / 2, ![1, 0, 0]) := by
  have hK : nullDirFactor boostX ![1, 0, 0] = 2 := nullDirFactor_boostX_pos
  have hn : nullDirMap boostX ![1, 0, 0] = ![1, 0, 0] := by
    ext i
    simp only [nullDirMap, hK]
    fin_cases i
    · simp [nullVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]
      norm_num
    · simp [nullVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]
    · simp [nullVec, boostX, mulVec, dotProduct, Fin.sum_univ_succ]
  simp [scriAct, hK, hn]

end Lightlike
