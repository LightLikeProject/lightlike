import Lightlike.GR.AdSConformalBoundary.NullCone

/-!
# The action of `SO(2,3)` on the boundary of anti-de Sitter space is a group action

The second layer of the action of the isometry group of anti-de Sitter space on its conformal boundary (GE7). A matrix
`Λ` with `Λᵀ η' Λ = η'` sends the null direction `(cos τ, sin τ, ω)` to `ρ (cos τ', sin τ', ω')`
(`mulVec_adsNullVec_eq`). The boundary point is the pair `(τ, ω)` with the angle `τ` modulo `2π`, so the group law is
stated on the null vectors `adsNullVec τ ω`, which only see the angle through `(cos τ, sin τ)`:

* `adsNullVec_eq_of_smul_eq`: `a X = b X'` with `a, b > 0` and both `X`, `X'` of the form `adsNullVec` forces `a = b` and
  `X = X'`;
* `adsLorentz_mul`: the product of two such matrices is again one;
* `adsNullFactor_mul`: `ρ_{ΛM}(p) = ρ_Λ(M p) ρ_M(p)`;
* `adsNullVec_mul`: `(ΛM) p = Λ (M p)`, as points of the boundary: the null vectors of the two images agree, so the angles
  agree modulo `2π` and the directions agree;
* `adsNullVec_one`: the identity matrix acts trivially.

Check on the concrete boost `adsBoost`: the factor law holds for `adsBoost` composed with itself
(`adsNullFactor_adsBoost_mul`).
-/

open Matrix

noncomputable section

namespace Lightlike

/-- The product of two matrices with `Λᵀ η' Λ = η'` is again one. -/
theorem adsLorentz_mul {Λ M : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta)
    (hM : Mᵀ * adsEta * M = adsEta) : (Λ * M)ᵀ * adsEta * (Λ * M) = adsEta := by
  calc (Λ * M)ᵀ * adsEta * (Λ * M) = Mᵀ * (Λᵀ * adsEta * Λ) * M := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = adsEta := by rw [hΛ, hM]

/-- Two positive multiples of null vectors of the form `adsNullVec` agree when the vectors agree. -/
theorem adsNullVec_eq_of_smul_eq {a b τ τ' : ℝ} {ω ω' : Fin 3 → ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a • adsNullVec τ ω = b • adsNullVec τ' ω') : a = b ∧ adsNullVec τ ω = adsNullVec τ' ω' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [adsNullVec, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hsq : a ^ 2 = b ^ 2 := by
    have e1 : (a * Real.cos τ) ^ 2 + (a * Real.sin τ) ^ 2 = a ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq τ]
    have e2 : (b * Real.cos τ') ^ 2 + (b * Real.sin τ') ^ 2 = b ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq τ']
    rw [← e1, ← e2, h0, h1]
  have hab : a = b := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  subst hab
  refine ⟨rfl, ?_⟩
  have := smul_right_injective (Fin 5 → ℝ) ha.ne' h
  exact this

/-- The factor law: `ρ_{ΛM}(p) = ρ_Λ(M p) ρ_M(p)`. -/
theorem adsNullFactor_mul {Λ M : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta)
    (hM : Mᵀ * adsEta * M = adsEta) (τ : ℝ) {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) :
    adsNullFactor (Λ * M) τ ω =
      adsNullFactor Λ (adsAngle M τ ω) (adsDir M τ ω) * adsNullFactor M τ ω ∧
    adsNullVec (adsAngle (Λ * M) τ ω) (adsDir (Λ * M) τ ω) =
      adsNullVec (adsAngle Λ (adsAngle M τ ω) (adsDir M τ ω)) (adsDir Λ (adsAngle M τ ω) (adsDir M τ ω)) := by
  have hω' := sum_sq_adsDir hM τ hω
  have hΛM := adsLorentz_mul hΛ hM
  have e1 := mulVec_adsNullVec_eq hΛM τ hω
  have e2 := mulVec_adsNullVec_eq hM τ hω
  have e3 := mulVec_adsNullVec_eq hΛ (adsAngle M τ ω) hω'
  have hM' : (Λ * M) *ᵥ adsNullVec τ ω = (adsNullFactor Λ (adsAngle M τ ω) (adsDir M τ ω) * adsNullFactor M τ ω) •
      adsNullVec (adsAngle Λ (adsAngle M τ ω) (adsDir M τ ω)) (adsDir Λ (adsAngle M τ ω) (adsDir M τ ω)) := by
    rw [← mulVec_mulVec, e2, mulVec_smul, e3, smul_smul, mul_comm]
  rw [e1] at hM'
  have := adsNullVec_eq_of_smul_eq (adsNullFactor_pos hΛM τ hω)
    (mul_pos (adsNullFactor_pos hΛ _ hω') (adsNullFactor_pos hM τ hω)) hM'
  exact this

/-- The group law on boundary points: `(ΛM) p = Λ (M p)`, the angle being read modulo `2π` through `(cos, sin)`. -/
theorem adsNullVec_mul {Λ M : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta)
    (hM : Mᵀ * adsEta * M = adsEta) (τ : ℝ) {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) :
    adsNullVec (adsAngle (Λ * M) τ ω) (adsDir (Λ * M) τ ω) =
      adsNullVec (adsAngle Λ (adsAngle M τ ω) (adsDir M τ ω)) (adsDir Λ (adsAngle M τ ω) (adsDir M τ ω)) :=
  (adsNullFactor_mul hΛ hM τ hω).2

/-- The identity acts trivially on boundary points. -/
theorem adsNullVec_one (τ : ℝ) {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) :
    adsNullVec (adsAngle 1 τ ω) (adsDir 1 τ ω) = adsNullVec τ ω := by
  have hΛ : (1 : Matrix (Fin 5) (Fin 5) ℝ)ᵀ * adsEta * 1 = adsEta := by simp
  have e := mulVec_adsNullVec_eq hΛ τ hω
  rw [one_mulVec, adsNullFactor_one, one_smul] at e
  exact e.symm

/-- Non-vacuity: the factor law for the boost `adsBoost` composed with itself. -/
theorem adsNullFactor_adsBoost_mul :
    adsNullFactor (adsBoost * adsBoost) 0 ![1, 0, 0] =
      adsNullFactor adsBoost (adsAngle adsBoost 0 ![1, 0, 0]) (adsDir adsBoost 0 ![1, 0, 0]) *
        adsNullFactor adsBoost 0 ![1, 0, 0] :=
  (adsNullFactor_mul adsBoost_lorentz adsBoost_lorentz 0 (by simp [Fin.sum_univ_three])).1

end Lightlike
