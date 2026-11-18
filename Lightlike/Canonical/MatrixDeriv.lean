import Mathlib
import Lightlike.Gauge.MatrixInverse

/-!
# Derivatives of matrix expressions along lines

Jacobi's formula `d/dt det (A + t B) = det A tr (A⁻¹ B)`, the derivative of `√det`, and the derivative of the
kinetic term `(tr (HPHP) − c (tr HP)²)/√det H` of the Hamiltonian constraint along `(H + t L, P + t p)`.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The trace of a differentiable matrix path is differentiable with the trace of the derivative. -/
lemma hasDerivAt_trace {M : ℝ → Matrix (Fin d) (Fin d) ℝ} {M' : Matrix (Fin d) (Fin d) ℝ} {t : ℝ}
    (h : HasDerivAt M M' t) : HasDerivAt (fun s => (M s).trace) M'.trace t := by
  have hT : HasFDerivAt (fun A : Matrix (Fin d) (Fin d) ℝ => A.trace)
      (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin d) ℝ ℝ)) (M t) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin d) ℝ ℝ)).hasFDerivAt
  exact hT.comp_hasDerivAt t h

lemma hasDerivAt_linePath (H L : Matrix (Fin d) (Fin d) ℝ) :
    HasDerivAt (fun t : ℝ => H + t • L) L 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).smul_const L).const_add H
  refine HasDerivAt.congr_deriv this ?_
  simp

lemma hasDerivAt_mul_path {M N : ℝ → Matrix (Fin d) (Fin d) ℝ} {M' N' : Matrix (Fin d) (Fin d) ℝ}
    (hM : HasDerivAt M M' 0) (hN : HasDerivAt N N' 0) :
    HasDerivAt (fun t => M t * N t) (M' * N 0 + M 0 * N') 0 := hM.mul hN

end



/-- The derivative of `det (1 + t M)` at `t = 0` is `tr M`. -/
lemma hasDerivAt_det_one_add_smul (M : Matrix (Fin d) (Fin d) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) M.trace 0 := by
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ t : ℝ, (1 + t • M).det = 1 + M.trace * t + p.eval t * t ^ 2 :=
    ⟨_, fun t => Matrix.det_one_add_smul t M⟩
  have hfun : (fun t : ℝ => (1 + t • M).det) = fun t => 1 + M.trace * t + p.eval t * t ^ 2 := funext hp
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => M.trace * t) M.trace 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul M.trace
  have h2 : HasDerivAt (fun t : ℝ => p.eval t * t ^ 2) 0 0 := by
    have := (p.hasDerivAt (0 : ℝ)).mul (hasDerivAt_pow 2 (0 : ℝ))
    refine HasDerivAt.congr_deriv this ?_
    simp
  refine HasDerivAt.congr_deriv ((h1.const_add 1).add h2) ?_
  simp

/-- **Jacobi's formula** along a line: `d/dt det (A + t B) = det A · tr (A⁻¹ B)` at `t = 0`. -/
lemma hasDerivAt_det_add_smul (A B : Matrix (Fin d) (Fin d) ℝ) (hA : IsUnit A.det) :
    HasDerivAt (fun t : ℝ => (A + t • B).det) (A.det * (A⁻¹ * B).trace) 0 := by
  have e : ∀ t : ℝ, (A + t • B).det = A.det * (1 + t • (A⁻¹ * B)).det := by
    intro t
    have : A + t • B = A * (1 + t • (A⁻¹ * B)) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
        Matrix.one_mul]
    rw [this, Matrix.det_mul]
  simp only [e]
  exact (hasDerivAt_det_one_add_smul (A⁻¹ * B)).const_mul _


/-- The kinetic term of the Hamiltonian constraint, as a function of the matrices `H = h`, `P = π`. -/
def kinJ (c : ℝ) (H P : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ((H * P * H * P).trace - c * (H * P).trace ^ 2) / Real.sqrt H.det

/-- The derivative of `√det (H + t L)` at `t = 0`: `det H tr (H⁻¹ L)/(2 √det H)`. -/
lemma hasDerivAt_sqrt_det (H L : Matrix (Fin d) (Fin d) ℝ) (hH : 0 < H.det) :
    HasDerivAt (fun t : ℝ => Real.sqrt (H + t • L).det)
      (H.det * (H⁻¹ * L).trace / (2 * Real.sqrt H.det)) 0 := by
  have hdet := hasDerivAt_det_add_smul H L hH.ne'.isUnit
  have := hdet.sqrt (by simpa using hH.ne')
  simpa using this

/-- The derivative of `kinJ c` at `(H, P)` in the direction `(L, p)`:
`(q' √det H − q (det H tr (H⁻¹ L)/(2 √det H)))/det H` with `q = tr (HP HP) − c (tr HP)²` and
`q' = 2 tr (HP (LP + Hp)) − 2 c tr (HP) tr (LP + Hp)`. -/
def dkinJ (c : ℝ) (H P L p : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ((2 * ((H * P) * (L * P + H * p)).trace - c * (2 * (H * P).trace * (L * P + H * p).trace)) *
      Real.sqrt H.det - ((H * P * H * P).trace - c * (H * P).trace ^ 2) *
      (H.det * (H⁻¹ * L).trace / (2 * Real.sqrt H.det))) / Real.sqrt H.det ^ 2

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma hasDerivAt_kinJ (c : ℝ) (H P L p : Matrix (Fin d) (Fin d) ℝ) (hH : 0 < H.det) :
    HasDerivAt (fun t : ℝ => kinJ c (H + t • L) (P + t • p)) (dkinJ c H P L p) 0 := by
  have hA : HasDerivAt (fun t : ℝ => (H + t • L) * (P + t • p)) (L * P + H * p) 0 := by
    have := (hasDerivAt_linePath H L).mul (hasDerivAt_linePath P p)
    refine HasDerivAt.congr_deriv this ?_
    simp
  have hAA : HasDerivAt (fun t : ℝ => ((H + t • L) * (P + t • p)) * ((H + t • L) * (P + t • p)))
      ((L * P + H * p) * (H * P) + (H * P) * (L * P + H * p)) 0 := by
    have := hA.mul hA
    refine HasDerivAt.congr_deriv this ?_
    simp
  have htr1 := hasDerivAt_trace hAA
  have htr2 := hasDerivAt_trace hA
  have hq : HasDerivAt (fun t : ℝ => (((H + t • L) * (P + t • p)) * ((H + t • L) * (P + t • p))).trace
        - c * ((H + t • L) * (P + t • p)).trace ^ 2)
      (2 * ((H * P) * (L * P + H * p)).trace - c * (2 * (H * P).trace * (L * P + H * p).trace)) 0 := by
    have h2 := htr2.pow 2
    have := htr1.sub (h2.const_mul c)
    refine HasDerivAt.congr_deriv this ?_
    simp only [Matrix.trace_add, Nat.cast_ofNat, Matrix.trace_mul_comm (L * P + H * p) (H * P), zero_smul,
      add_zero]
    ring
  have hs := hasDerivAt_sqrt_det H L hH
  have hqs := hq.div hs (by simpa using (Real.sqrt_pos.mpr hH).ne')
  unfold kinJ
  convert hqs using 1
  · funext t
    simp [Matrix.mul_assoc]
  · unfold dkinJ
    simp [Matrix.mul_assoc]

end

end Lightlike.Canonical

end
