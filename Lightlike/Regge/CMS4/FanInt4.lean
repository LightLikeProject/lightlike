import Lightlike.Regge.CMS4.Plucker4

/-!
# A closed positively oriented fan has angle sum in `2π ℤ` (dimension 4)

For a positive definite `G`, the plane quotient by the axis `(w₁, w₂)` with positive Gram
determinant and a chain of vectors `v 0, …, v n = v 0` with `det4 w₁ w₂ (v i) (v (i+1)) > 0`, the
sum of the fan angles is an integer multiple of `2π`. This is the stable form of `quad_fan4` and
`hex_fan4`: it survives a small perturbation of the vertices of the star, which is used to prove
the first-order cancellation.

## Main results

* `fan_int4`: closed positive chain gives an angle sum in `2π ℤ`.
-/

open Real Matrix
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3

variable {G : Matrix (Fin 4) (Fin 4) ℝ}

/-- **A closed positively oriented fan** has angle sum a multiple of `2π`. -/
theorem fan_int4 (hG : G.PosDef) {w₁ w₂ : Fin 4 → ℝ} (hD : 0 < gramW G w₁ w₂) (n : ℕ) (hn : 0 < n)
    (v : ℕ → Fin 4 → ℝ) (hpos : ∀ i < n, 0 < det4 w₁ w₂ (v i) (v (i + 1)))
    (hc : v n = v 0) :
    ∃ k : ℤ, ∑ i ∈ Finset.range n, fanAng4 G w₁ w₂ (v i) (v (i + 1)) = 2 * π * k := by
  have hp : ∀ i < n, 0 < bf2 G w₁ w₂ (v i) (v i) ∧ 0 < bf2 G w₁ w₂ (v (i + 1)) (v (i + 1)) :=
    fun i hi => bf2_pos_of_det4 hG hD (hpos i hi).ne'
  have ht : 0 < bf2 G w₁ w₂ (v 0) (v 0) := (hp 0 hn).1
  have hpos' : ∀ i ≤ n, 0 < bf2 G w₁ w₂ (v i) (v i) := by
    intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · exact (hp i h).1
    · have : i = n := by omega
      subst this
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact (hp j (by omega)).2
  set z : ℕ → ℂ := fun i => iota4 G w₁ w₂ (v 0) (v i) with hz
  have hz0 : ∀ i ≤ n, z i ≠ 0 := fun i hi => iota4_ne hG hD ht (hpos' i hi)
  have him : ∀ i < n, 0 < (starRingEnd ℂ (z i) * z (i + 1)).im := by
    intro i hi
    simp only [hz]
    rw [conj_iota_mul4 hG hD ht]
    simp only [zeta4]
    exact mul_pos (Real.sqrt_pos.2 (div_pos hG.det_pos hD)) (hpos i hi)
  obtain ⟨k, hk⟩ := fan_angle z hz0 him
  have h4 : z n = z 0 := by simp only [hz]; rw [hc]
  have h0 : Complex.arg (starRingEnd ℂ (z 0) * z n) = 0 := by
    rw [h4]
    have : starRingEnd ℂ (z 0) * z 0 = ((Complex.normSq (z 0) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.arg_ofReal_of_nonneg (Complex.normSq_nonneg _)]
  have hs : ∑ i ∈ Finset.range n, fanAng4 G w₁ w₂ (v i) (v (i + 1))
      = ∑ i ∈ Finset.range n, Complex.arg (starRingEnd ℂ (z i) * z (i + 1)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    simp only [hz]
    rw [conj_iota_mul4 hG hD ht, ← arccos_eq_arg4 hG hD (hpos i hi')]
    rfl
  refine ⟨k, ?_⟩
  rw [hs, hk, h0]
  ring

end Lightlike.Regge4
