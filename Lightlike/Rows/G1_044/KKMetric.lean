import Lightlike.Spacetime.ConformalRicci

/-!
# The Kaluza-Klein metric on a circle: definition, entries and inverse (G1-044)

For a metric `g`, a one-form `A` and a positive function `φ` (the dilaton) on `ℝⁿ`, the five-dimensional
Kaluza-Klein metric on `ℝⁿ × ℝ = Fin (n+1) → ℝ` (the fifth coordinate is the last one) is
`ds² = g_{ab} dxᵃ dxᵇ + φ² (dy + A_a dxᵃ)²`, that is
`Ĝ_{ab} = g_{ab} + φ² A_a A_b`, `Ĝ_{a5} = φ² A_a`, `Ĝ_{55} = φ²`, all evaluated at the first `n` coordinates
(`kkMetric`); it does not depend on `y`.  Here we prove that its inverse is
`Ĝᵃᵇ = gᵃᵇ`, `Ĝᵃ⁵ = -Aᵃ`, `Ĝ⁵⁵ = φ⁻² + A_a Aᵃ` (`kkMetric_inv`).

Supporting file for the row G1-044 (Kaluza-Klein reduction, Overduin-Wesson 1997, Section 2).
-/

open Matrix

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ}

/-- The first `n` coordinates of a point of `ℝⁿ⁺¹`. -/
def proj (x : Fin (n + 1) → ℝ) : Fin n → ℝ := fun i => x i.castSucc

/-- The Kaluza-Klein metric `ds² = g + φ² (dy + A)²` on `ℝⁿ⁺¹` built from a metric `g`, a one-form `A` and a
dilaton `φ` on `ℝⁿ`; it does not depend on the last coordinate. -/
def kkMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
    (φ : (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => ℝ)
      (Fin.lastCases (motive := fun _ => ℝ) (φ (proj x) ^ 2) (fun b => φ (proj x) ^ 2 * A (proj x) b) j)
      (fun a => Fin.lastCases (motive := fun _ => ℝ) (φ (proj x) ^ 2 * A (proj x) a)
        (fun b => g (proj x) a b + φ (proj x) ^ 2 * A (proj x) a * A (proj x) b) j) i

section Entries

variable (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
  (φ : (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ)

@[simp] theorem kkMetric_cc (a b : Fin n) :
    kkMetric g A φ x a.castSucc b.castSucc =
      g (proj x) a b + φ (proj x) ^ 2 * A (proj x) a * A (proj x) b := by
  simp [kkMetric]

@[simp] theorem kkMetric_c5 (a : Fin n) :
    kkMetric g A φ x a.castSucc (Fin.last n) = φ (proj x) ^ 2 * A (proj x) a := by
  simp [kkMetric]

@[simp] theorem kkMetric_5c (b : Fin n) :
    kkMetric g A φ x (Fin.last n) b.castSucc = φ (proj x) ^ 2 * A (proj x) b := by
  simp [kkMetric]

@[simp] theorem kkMetric_55 : kkMetric g A φ x (Fin.last n) (Fin.last n) = φ (proj x) ^ 2 := by
  simp [kkMetric]

end Entries

/-- The explicit inverse of the Kaluza-Klein metric:
`Ĝᵃᵇ = gᵃᵇ`, `Ĝᵃ⁵ = -Aᵃ`, `Ĝ⁵⁵ = φ⁻² + A_a Aᵃ`. -/
def kkInv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
    (φ : (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    Fin.lastCases (motive := fun _ => ℝ)
      (Fin.lastCases (motive := fun _ => ℝ)
        ((φ (proj x))⁻¹ ^ 2 + ∑ c, ∑ d, A (proj x) c * (g (proj x))⁻¹ c d * A (proj x) d)
        (fun b => -∑ d, A (proj x) d * (g (proj x))⁻¹ d b) j)
      (fun a => Fin.lastCases (motive := fun _ => ℝ) (-∑ d, (g (proj x))⁻¹ a d * A (proj x) d)
        (fun b => (g (proj x))⁻¹ a b) j) i

section Inverse

variable (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
  (φ : (Fin n → ℝ) → ℝ) (x : Fin (n + 1) → ℝ)

@[simp] theorem kkInv_cc (a b : Fin n) :
    kkInv g A φ x a.castSucc b.castSucc = (g (proj x))⁻¹ a b := by
  simp [kkInv]

@[simp] theorem kkInv_c5 (a : Fin n) :
    kkInv g A φ x a.castSucc (Fin.last n) = -∑ d, (g (proj x))⁻¹ a d * A (proj x) d := by
  simp [kkInv]

@[simp] theorem kkInv_5c (b : Fin n) :
    kkInv g A φ x (Fin.last n) b.castSucc = -∑ d, A (proj x) d * (g (proj x))⁻¹ d b := by
  simp [kkInv]

@[simp] theorem kkInv_55 :
    kkInv g A φ x (Fin.last n) (Fin.last n) =
      (φ (proj x))⁻¹ ^ 2 + ∑ c, ∑ d, A (proj x) c * (g (proj x))⁻¹ c d * A (proj x) d := by
  simp [kkInv]

/-- **The inverse of the Kaluza-Klein metric**: `Ĝ · Ĝ⁻¹ = 1` for `Ĝ⁻¹ = kkInv`, when `g` is invertible and
the dilaton does not vanish at the point. -/
theorem kkMetric_mul_kkInv (hg : g (proj x) * (g (proj x))⁻¹ = 1) (hφ : φ (proj x) ≠ 0) :
    kkMetric g A φ x * kkInv g A φ x = 1 := by
  have hgi : ∀ c d, ∑ e, g (proj x) c e * (g (proj x))⁻¹ e d = if c = d then 1 else 0 := fun c d => by
    have := congrFun (congrFun hg c) d
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hs : φ (proj x) ^ 2 * (φ (proj x))⁻¹ ^ 2 = 1 := by field_simp
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply, kkMetric_cc, kkMetric_c5,
      kkMetric_5c, kkMetric_55, kkInv_cc, kkInv_c5, kkInv_5c, kkInv_55]
  · have e : ∑ x_1, φ (proj x) ^ 2 * A (proj x) x_1 * -∑ d, (g (proj x))⁻¹ x_1 d * A (proj x) d =
        -(φ (proj x) ^ 2 * ∑ c, ∑ d, A (proj x) c * (g (proj x))⁻¹ c d * A (proj x) d) := by
      simp only [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    rw [e]
    simp only [↓reduceIte]
    linear_combination hs
  · have e : ∑ x_1, φ (proj x) ^ 2 * A (proj x) x_1 * (g (proj x))⁻¹ x_1 b =
        φ (proj x) ^ 2 * ∑ d, A (proj x) d * (g (proj x))⁻¹ d b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    have hne : Fin.last n ≠ b.castSucc := (Fin.castSucc_lt_last b).ne'
    rw [e]
    simp only [hne, ↓reduceIte]
    ring
  · have e : ∑ x_1, (g (proj x) a x_1 + φ (proj x) ^ 2 * A (proj x) a * A (proj x) x_1) *
          -∑ d, (g (proj x))⁻¹ x_1 d * A (proj x) d =
        -A (proj x) a - φ (proj x) ^ 2 * A (proj x) a *
          ∑ c, ∑ d, A (proj x) c * (g (proj x))⁻¹ c d * A (proj x) d := by
      have h1 : ∑ x_1, g (proj x) a x_1 * ∑ d, (g (proj x))⁻¹ x_1 d * A (proj x) d = A (proj x) a := by
        have := congrFun (Matrix.mulVec_mulVec (A (proj x)) (g (proj x)) (g (proj x))⁻¹) a
        rw [hg, Matrix.one_mulVec] at this
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 : ∑ x_1, φ (proj x) ^ 2 * A (proj x) a * A (proj x) x_1 *
          ∑ d, (g (proj x))⁻¹ x_1 d * A (proj x) d =
          φ (proj x) ^ 2 * A (proj x) a *
            ∑ c, ∑ d, A (proj x) c * (g (proj x))⁻¹ c d * A (proj x) d := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
      simp only [add_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib, h1, h2]
      ring
    have hne : a.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last a).ne
    rw [e]
    simp only [hne, ↓reduceIte]
    linear_combination (A (proj x) a) * hs
  · have e : ∑ x_1, (g (proj x) a x_1 + φ (proj x) ^ 2 * A (proj x) a * A (proj x) x_1) *
          (g (proj x))⁻¹ x_1 b = (if a = b then 1 else 0) +
          φ (proj x) ^ 2 * A (proj x) a * ∑ d, A (proj x) d * (g (proj x))⁻¹ d b := by
      simp only [add_mul, Finset.sum_add_distrib, hgi, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [e]
    simp only [Fin.castSucc_inj]
    ring

/-- **The inverse of the Kaluza-Klein metric is `kkInv`**: `Ĝᵃᵇ = gᵃᵇ`, `Ĝᵃ⁵ = -Aᵃ`,
`Ĝ⁵⁵ = φ⁻² + A_a Aᵃ`. -/
theorem kkMetric_inv (hg : g (proj x) * (g (proj x))⁻¹ = 1) (hφ : φ (proj x) ≠ 0) :
    (kkMetric g A φ x)⁻¹ = kkInv g A φ x :=
  Matrix.inv_eq_right_inv (kkMetric_mul_kkInv g A φ x hg hφ)

end Inverse

end KK

end Lightlike
