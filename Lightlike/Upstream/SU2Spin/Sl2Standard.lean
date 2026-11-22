import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Analysis.Complex.Polynomial.Basic
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

lemma mulVec_E_m (P : t.HasPrimitiveVectorWith m (n : ℂ)) : E *ᵥ m = 0 := by
  have := P.lie_e
  exact this

/-- The span of the vectors `Fᵏ m`, `k ≤ n`, is stable under `H`, `E` and `F`. -/
lemma span_fpow_invariant (P : t.HasPrimitiveVectorWith m (n : ℂ)) :
    (∀ v ∈ Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k), H *ᵥ v ∈
        Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k)) ∧
    (∀ v ∈ Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k), E *ᵥ v ∈
        Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k)) ∧
    (∀ v ∈ Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k), F *ᵥ v ∈
        Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k)) := by
  have hmem : ∀ k : ℕ, k ≤ n →
      fpow F m k ∈ Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k) :=
    fun k hk => Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [mulVec_H_fpow t P]
      exact Submodule.smul_mem _ _ (hmem k (by omega))
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      show E *ᵥ fpow F m k ∈ _
      rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | hpos
      · rw [h0, fpow_zero, mulVec_E_m t P]; exact Submodule.zero_mem _
      · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [hj, Nat.succ_eq_add_one, mulVec_E_fpow_succ t P]
        exact Submodule.smul_mem _ _ (hmem j (by omega))
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  · induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [← fpow_succ]
      by_cases hk : (k : ℕ) + 1 ≤ n
      · exact hmem _ hk
      · have : (k : ℕ) = n := by omega
        rw [this, fpow_succ_eq_zero t P]; exact Submodule.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

/-- An irreducible nonzero `sl₂`-module of matrices is spanned by `Fᵏ m`, `k ≤ n`, for a primitive
vector `m` of weight `n`. -/
lemma exists_primitive_span_eq_top (hd : 0 < d)
    (hirr : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ v ∈ W, H *ᵥ v ∈ W) → (∀ v ∈ W, E *ᵥ v ∈ W) →
      (∀ v ∈ W, F *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (n : ℕ) (m : Fin d → ℂ), t.HasPrimitiveVectorWith m (n : ℂ) ∧
      Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k) = ⊤ := by
  have : Nontrivial (Fin d → ℂ) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have : IsTriangularizable ℂ (Matrix (Fin d) (Fin d) ℂ) (Fin d → ℂ) :=
    instIsTriangularizableOfIsAlgClosed ℂ (Matrix (Fin d) (Fin d) ℂ) (Fin d → ℂ)
  obtain ⟨μ, m, hm, P⟩ := IsSl2Triple.exists_hasPrimitiveVectorWith (R := ℂ)
    (L := Matrix (Fin d) (Fin d) ℂ) (M := Fin d → ℂ) t
  obtain ⟨n, rfl⟩ := P.exists_nat
  obtain ⟨h1, h2, h3⟩ := span_fpow_invariant t P
  refine ⟨n, m, P, ?_⟩
  rcases hirr _ h1 h2 h3 with h | h
  · exfalso
    have : fpow F m 0 ∈ Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k) :=
      Submodule.subset_span ⟨0, rfl⟩
    rw [h] at this
    exact hm (by simpa using this)
  · exact h

end SU2Spin
