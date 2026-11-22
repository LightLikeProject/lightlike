import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Standard basis of an `sl₂`-triple of matrices with a primitive vector

Let `H, E, F` be complex `d × d` matrices forming an `sl₂`-triple (`IsSl2Triple`) and `m` a primitive
vector of weight `n ∈ ℕ`. This file shows that the vectors `ψ k = Fᵏ m` (`k ≤ n`) are linearly
independent eigenvectors of `H`, with `H ψ k = (n - 2k) ψ k`, `F ψ k = ψ (k+1)`,
`E ψ (k+1) = (k+1)(n-k) ψ k`, and `ψ (n+1) = 0`.

This is the first step of the classification of irreducible finite-dimensional `sl₂(ℂ)`-modules,
proved from Mathlib's `Mathlib.Algebra.Lie.Sl2` only.
-/

open Matrix Module LieModule

namespace SU2Spin

attribute [local instance 100] LieRing.ofAssociativeRing

variable {d : ℕ} {H E F : Matrix (Fin d) (Fin d) ℂ}

/-- The vectors `Fᵏ m`. -/
def fpow (F : Matrix (Fin d) (Fin d) ℂ) (m : Fin d → ℂ) (k : ℕ) : Fin d → ℂ :=
  ((F.mulVecLin) ^ k) m

@[simp] lemma fpow_zero (m : Fin d → ℂ) : fpow F m 0 = m := by simp [fpow]

lemma fpow_succ (m : Fin d → ℂ) (k : ℕ) : fpow F m (k + 1) = F *ᵥ fpow F m k := by
  simp [fpow, pow_succ', Module.End.mul_apply]

variable (t : IsSl2Triple H E F) {m : Fin d → ℂ} {n : ℕ}

lemma fpow_eq (k : ℕ) :
    fpow F m k = ((toEnd ℂ (Matrix (Fin d) (Fin d) ℂ) (Fin d → ℂ) F) ^ k) m := by
  rfl

include t

lemma mulVec_H_fpow (P : t.HasPrimitiveVectorWith m (n : ℂ)) (k : ℕ) :
    H *ᵥ fpow F m k = ((n : ℂ) - 2 * k) • fpow F m k := by
  have := P.lie_h_pow_toEnd_f k
  exact this

lemma mulVec_E_fpow_succ (P : t.HasPrimitiveVectorWith m (n : ℂ)) (k : ℕ) :
    E *ᵥ fpow F m (k + 1) = (((k : ℂ) + 1) * (n - k)) • fpow F m k := by
  have := P.lie_e_pow_succ_toEnd_f k
  exact this

lemma fpow_succ_eq_zero (P : t.HasPrimitiveVectorWith m (n : ℂ)) : fpow F m (n + 1) = 0 :=
  P.pow_toEnd_f_eq_zero_of_eq_nat rfl

lemma fpow_ne_zero (P : t.HasPrimitiveVectorWith m (n : ℂ)) {k : ℕ} (hk : k ≤ n) :
    fpow F m k ≠ 0 :=
  P.pow_toEnd_f_ne_zero_of_eq_nat rfl hk

lemma linearIndependent_fpow (P : t.HasPrimitiveVectorWith m (n : ℂ)) :
    LinearIndependent ℂ (fun k : Fin (n + 1) => fpow F m k) := by
  refine Module.End.eigenvectors_linearIndependent' H.mulVecLin
    (fun k : Fin (n + 1) => (n : ℂ) - 2 * (k : ℕ)) ?_ _ fun k => ?_
  · intro a b hab
    have : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := by
      have h2 := sub_right_injective hab
      simpa using h2
    exact Fin.ext (by exact_mod_cast this)
  · refine Module.End.hasEigenvector_iff.2 ⟨?_, fpow_ne_zero t P (by omega)⟩
    exact Module.End.mem_eigenspace_iff.2 (mulVec_H_fpow t P k)

end SU2Spin
