import Lightlike.Asymptotics.Lorentzian.CriticalGradient

/-!
# Pauli algebra of the generators `genMat d` on a spinor

For `M = genMat d` (`½ Σ d_i σ_i`) and a spinor `ξ` with `m = spinVec ξ`: `⟨ξ, M ξ⟩ = ½ d·m`,
`M² = ¼ (d·d)`, and `‖M ξ‖²` in terms of `d` and `m` (`inner_genMat`, `spinAct_genMat_sq`,
`inner_genMat_genMat`); `Σ m_i² = 1` for a unit spinor. `srcValue_eval` evaluates the second
derivative of the source coefficient of the vertex action along a one-parameter orbit as a
polynomial in `α, β, m` with the projector `δ_ij - m_i m_j` (`projForm`) and the triple product
`m · (α × β)` (`tripleForm`). Used by `HessianNode.lean`.

## Main results

* `inner_genMat`, `spinAct_genMat_sq`, `inner_genMat_genMat`, `spinVec_sq_sum`: the Pauli identities.
* `srcValue_eval`: the value of the second variation of one source end.
-/

open Complex
open scoped ComplexConjugate Matrix

namespace Lightlike.Asymptotics.Lorentzian

theorem spinVec_cast_zero (ξ : Spinor) :
    (spinVec ξ 0 : ℂ) = conj (ξ 0) * ξ 1 + ξ 0 * conj (ξ 1) := by
  simp only [spinVec]
  apply Complex.ext <;> simp <;> ring

theorem spinVec_cast_one (ξ : Spinor) :
    (spinVec ξ 1 : ℂ) = -Complex.I * (conj (ξ 0) * ξ 1 - ξ 0 * conj (ξ 1)) := by
  simp only [spinVec]
  apply Complex.ext <;> simp <;> ring

theorem spinVec_cast_two (ξ : Spinor) :
    (spinVec ξ 2 : ℂ) = ξ 0 * conj (ξ 0) - ξ 1 * conj (ξ 1) := by
  simp only [spinVec]
  rw [Complex.mul_conj', Complex.mul_conj']
  push_cast
  ring

/-- `⟨ξ, ½ d·σ ξ⟩ = ½ d · m` with `m = spinVec ξ` (no normalisation needed). -/
theorem inner_genMat (d : Fin 3 → ℂ) (ξ : Spinor) :
    inner ℂ ξ (spinAct (genMat d) ξ) = (1 / 2 : ℂ) * ∑ i, d i * (spinVec ξ i : ℂ) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_three, RCLike.inner_apply,
    spinAct_zero_apply, spinAct_one_apply, genMat, spinVec_cast_zero, spinVec_cast_one,
    spinVec_cast_two]
  simp [Matrix.of_apply]
  ring

/-- `M² = ¼ (d·d) · 1` for `M = genMat d`. -/
theorem spinAct_genMat_sq (d : Fin 3 → ℂ) (ξ : Spinor) :
    spinAct (genMat d) (spinAct (genMat d) ξ) =
      ((d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2) / 4) • ξ := by
  ext i; fin_cases i <;> simp [genMat, Matrix.of_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- `⟨ξ, M ξ⟩`-type second-order quantity: `‖M ξ‖²` as a complex number
`¼ ((Σ conj d_i d_i) ⟨ξ,ξ⟩ + i (conj d × d) · m)`. -/
theorem inner_genMat_genMat (d : Fin 3 → ℂ) (ξ : Spinor) :
    inner ℂ (spinAct (genMat d) ξ) (spinAct (genMat d) ξ) =
      (1 / 4 : ℂ) * ((∑ i, conj (d i) * d i) * inner ℂ ξ ξ +
        Complex.I * ((spinVec ξ 0 : ℂ) * (conj (d 1) * d 2 - conj (d 2) * d 1) +
          (spinVec ξ 1 : ℂ) * (conj (d 2) * d 0 - conj (d 0) * d 2) +
          (spinVec ξ 2 : ℂ) * (conj (d 0) * d 1 - conj (d 1) * d 0))) := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_three, RCLike.inner_apply,
    spinAct_zero_apply, spinAct_one_apply, genMat, spinVec_cast_zero, spinVec_cast_one,
    spinVec_cast_two]
  simp [Matrix.of_apply, Complex.conj_I, map_ofNat, map_div₀]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- For a unit spinor, `Σ m_i² = 1`. -/
theorem spinVec_sq_sum (ξ : Spinor) (hξ : ‖ξ‖ = 1) : ∑ i, spinVec ξ i ^ 2 = 1 := by
  have h0 : ‖ξ‖ ^ 2 = ‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
  have h : ‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2 = 1 := by rw [← h0, hξ]; norm_num
  simp only [Fin.sum_univ_three, spinVec]
  have e1 : (2 * (conj (ξ 0) * ξ 1).re) ^ 2 + (2 * (conj (ξ 0) * ξ 1).im) ^ 2 =
      4 * (‖ξ 0‖ ^ 2 * ‖ξ 1‖ ^ 2) := by
    have : ‖conj (ξ 0) * ξ 1‖ ^ 2 = (conj (ξ 0) * ξ 1).re ^ 2 + (conj (ξ 0) * ξ 1).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [norm_mul, mul_pow, Complex.norm_conj] at this
    nlinarith
  nlinarith [e1, h]

/-- The projector `δ_ij - m_i m_j` as a bilinear form on `ℝ³`. -/
def projForm (m u v : Fin 3 → ℝ) : ℝ :=
  ∑ i, u i * v i - (∑ i, m i * u i) * (∑ i, m i * v i)

/-- The triple product `m · (u × v)`. -/
def tripleForm (m u v : Fin 3 → ℝ) : ℝ :=
  m 0 * (u 1 * v 2 - u 2 * v 1) + m 1 * (u 2 * v 0 - u 0 * v 2) + m 2 * (u 0 * v 1 - u 1 * v 0)

/-- **The second derivative of the source coefficient, evaluated** for `M = (genMat (β + iα))†`:
`n (⟨M²ξ,ξ⟩ - ⟨Mξ,ξ⟩²) - (n + 2ip)(‖Mξ‖² + Re⟨ξ,M²ξ⟩ - 2 Re⟨ξ,Mξ⟩²)` equals
`k (-½ (α,α) + i (α,β) - ½ (β,β)) - i p (β,β) + (k + i p) m·(α×β)` with `k = n/2` and `m = spinVec ξ`. -/
theorem srcValue_eval (n : ℕ) (p : ℝ) (α β : Fin 3 → ℝ) {ξ : Spinor} (hξ : ‖ξ‖ = 1) :
    let M := genMat (fun i => (β i : ℂ) - Complex.I * α i)
    (n : ℂ) * (inner ℂ (spinAct M (spinAct M ξ)) ξ - inner ℂ (spinAct M ξ) ξ ^ 2) -
        ((n : ℂ) + 2 * Complex.I * p) *
          ((‖spinAct M ξ‖ ^ 2 + (inner ℂ ξ (spinAct M (spinAct M ξ))).re -
            2 * (inner ℂ ξ (spinAct M ξ)).re ^ 2 : ℝ) : ℂ) =
      ((n : ℂ) / 2) * (-(1 / 2 : ℂ) * (projForm (spinVec ξ) α α : ℝ) +
          Complex.I * (projForm (spinVec ξ) α β : ℝ) - (1 / 2 : ℂ) * (projForm (spinVec ξ) β β : ℝ)) -
        Complex.I * p * (projForm (spinVec ξ) β β : ℝ) +
        ((n : ℂ) / 2 + Complex.I * p) * (tripleForm (spinVec ξ) α β : ℝ) := by
  intro M
  have hin : inner ℂ ξ ξ = 1 := by rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hm := spinVec_sq_sum ξ hξ
  have F1 := inner_genMat (fun i => (β i : ℂ) - Complex.I * α i) ξ
  have F2 := spinAct_genMat_sq (fun i => (β i : ℂ) - Complex.I * α i) ξ
  have F3 := inner_genMat_genMat (fun i => (β i : ℂ) - Complex.I * α i) ξ
  have hmc : (spinVec ξ 0 : ℂ) ^ 2 + (spinVec ξ 1 : ℂ) ^ 2 + (spinVec ξ 2 : ℂ) ^ 2 = 1 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hm
    simpa [Fin.sum_univ_three] using this
  -- the real parts and the norm
  have hu : inner ℂ ξ (spinAct M ξ) = (1 / 2 : ℂ) * ∑ i, ((β i : ℂ) - Complex.I * α i) * (spinVec ξ i : ℂ) := F1
  have hu' : inner ℂ (spinAct M ξ) ξ = (1 / 2 : ℂ) * ∑ i, ((β i : ℂ) + Complex.I * α i) * (spinVec ξ i : ℂ) := by
    rw [← inner_conj_symm, hu]
    simp [map_sum, Fin.sum_univ_three, map_ofNat, map_div₀]
  have hRu : (inner ℂ ξ (spinAct M ξ)).re = (1 / 2) * ∑ i, β i * spinVec ξ i := by
    rw [hu]; simp [Fin.sum_univ_three]
  have hs : inner ℂ ξ (spinAct M (spinAct M ξ)) =
      ((((β 0 : ℂ) - Complex.I * α 0) ^ 2 + ((β 1 : ℂ) - Complex.I * α 1) ^ 2 +
        ((β 2 : ℂ) - Complex.I * α 2) ^ 2) / 4) := by
    rw [F2, inner_smul_right, hin, mul_one]
  have hs' : inner ℂ (spinAct M (spinAct M ξ)) ξ =
      ((((β 0 : ℂ) + Complex.I * α 0) ^ 2 + ((β 1 : ℂ) + Complex.I * α 1) ^ 2 +
        ((β 2 : ℂ) + Complex.I * α 2) ^ 2) / 4) := by
    rw [← inner_conj_symm, hs]
    simp [map_ofNat, map_div₀]
  have hRs : (inner ℂ ξ (spinAct M (spinAct M ξ))).re =
      ((β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2) - (α 0 ^ 2 + α 1 ^ 2 + α 2 ^ 2)) / 4 := by
    rw [hs]; simp [pow_two]; ring
  have hN : ((‖spinAct M ξ‖ : ℝ) : ℂ) ^ 2 = (1 / 4 : ℂ) * ((∑ i, ((β i : ℂ) ^ 2 + (α i : ℂ) ^ 2)) +
      Complex.I * ((spinVec ξ 0 : ℂ) * (2 * Complex.I * (α 1 * β 2 - α 2 * β 1)) +
        (spinVec ξ 1 : ℂ) * (2 * Complex.I * (α 2 * β 0 - α 0 * β 2)) +
        (spinVec ξ 2 : ℂ) * (2 * Complex.I * (α 0 * β 1 - α 1 * β 0)))) := by
    have e : ((‖spinAct M ξ‖ : ℝ) : ℂ) ^ 2 = inner ℂ (spinAct M ξ) (spinAct M ξ) := by
      rw [inner_self_eq_norm_sq_to_K]; rfl
    rw [e]
    change inner ℂ (spinAct (genMat fun i => (β i : ℂ) - Complex.I * α i) ξ)
      (spinAct (genMat fun i => (β i : ℂ) - Complex.I * α i) ξ) = _
    rw [F3, hin]
    simp [Fin.sum_univ_three, Complex.conj_I]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hs', hu', hRs, hRu]
  push_cast
  rw [hN]
  simp only [projForm, tripleForm, Fin.sum_univ_three]
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, pow_two] <;> ring

end Lightlike.Asymptotics.Lorentzian
