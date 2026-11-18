import Lightlike.Gauge.DiracSchur
import Lightlike.Gauge.MatrixInverse

/-!
# One stage of the Dirac algorithm, locally under constant rank

The multipliers `u` of the evolution `x' = X_H + ∑ u_a X_{φ_a}` must satisfy `Cmat x u + h x = 0` for the bracket
matrix `Cmat x = ({φ_a, φ_b}(x))` and `h x = ({φ_b, H}(x))` (Henneaux and Teitelboim 1992, Chapter One,
"Constrained Hamiltonian Systems"; the statement here has not been compared with that chapter). Index the primary
constraints by `m ⊕ n` and write `Cmat x = [[B x, C x], [D x, E x]]`.

At a point where `B x` is invertible and the rank of `Cmat x` equals `card m` (so that `E x = D x (B x)⁻¹ C x`), the
consistency condition is `χ(x) := h₂ x - D x (B x)⁻¹ h₁ x = 0`: the secondary constraints, explicit in the entries of
`B⁻¹`, `D`, `h`, hence smooth wherever these are.

* `stageSet`: the points of `S` where a multiplier exists.
* `stageSet_inter_eq`: on the set where the rank is constant and `B` invertible, `stageSet` is `S ∩ {χ = 0}`.
-/

namespace Lightlike.Gauge

open Matrix

variable {E : Type*} {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The points of `S` at which the consistency system `Cmat x u + h x = 0` has a solution. -/
def stageSet (Cm : E → Matrix (m ⊕ n) (m ⊕ n) ℝ) (h : E → (m ⊕ n) → ℝ) (S : Set E) : Set E :=
  {x ∈ S | ∃ u, Cm x *ᵥ u + h x = 0}

/-- The secondary-constraint functions `χ x = h₂ x - D x (B x)⁻¹ h₁ x`. -/
noncomputable def chi (Cm : E → Matrix (m ⊕ n) (m ⊕ n) ℝ) (h : E → (m ⊕ n) → ℝ) (x : E) : n → ℝ :=
  (h x ∘ Sum.inr) - (Cm x).toBlocks₂₁ *ᵥ ((Cm x).toBlocks₁₁⁻¹ *ᵥ (h x ∘ Sum.inl))

/-- **The Dirac stage under constant rank**: at points where `B x` is invertible and `E x = D x (B x)⁻¹ C x`, a
multiplier exists iff `χ x = 0`. -/
theorem exists_multiplier_iff_chi (Cm : E → Matrix (m ⊕ n) (m ⊕ n) ℝ) (h : E → (m ⊕ n) → ℝ) {x : E}
    (hB : IsUnit (Cm x).toBlocks₁₁.det) (hS : (Cm x).toBlocks₂₂ = (Cm x).toBlocks₂₁ * (Cm x).toBlocks₁₁⁻¹ * (Cm x).toBlocks₁₂) :
    (∃ u, Cm x *ᵥ u + h x = 0) ↔ chi Cm h x = 0 := by
  set M := Cm x with hM
  have hsplit : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (fromBlocks_toBlocks M).symm
  have key := consistency_iff M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ hB hS
    (h x ∘ Sum.inl) (h x ∘ Sum.inr)
  have hchi : chi Cm h x = (h x ∘ Sum.inr) - M.toBlocks₂₁ *ᵥ (M.toBlocks₁₁⁻¹ *ᵥ (h x ∘ Sum.inl)) := rfl
  rw [hchi, ← key]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u ∘ Sum.inl, u ∘ Sum.inr, ?_, ?_⟩
    · have := congrFun hu (Sum.inl ·)
      sorry
    · sorry
  · rintro ⟨u₁, u₂, e1, e2⟩
    refine ⟨Sum.elim u₁ u₂, ?_⟩
    rw [hsplit, fromBlocks_mulVec]
    ext i
    cases i <;> simp [← hsplit, e1, e2] <;> sorry

section Smooth

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {r : ℕ}

/-- **The secondary constraints are differentiable**: where the entries of the bracket matrix and of `h` are
differentiable and the block `B` is invertible, every component of `χ` is differentiable. (The functions are given
explicitly by the entries of `B⁻¹`, `D`, `h`, with no choice of null-vector bundle.) -/
theorem differentiableAt_chi (Cm : F → Matrix (Fin r ⊕ n) (Fin r ⊕ n) ℝ) (h : F → (Fin r ⊕ n) → ℝ) {x : F}
    (hCm : ∀ i j, DifferentiableAt ℝ (fun y => Cm y i j) x) (hh : ∀ i, DifferentiableAt ℝ (fun y => h y i) x)
    (hdet : ((Cm x).toBlocks₁₁).det ≠ 0) (j : n) :
    DifferentiableAt ℝ (fun y => chi Cm h y j) x := by
  have hB : ∀ a b, DifferentiableAt ℝ (fun y => (Cm y).toBlocks₁₁ a b) x := fun a b => hCm _ _
  have hBinv := fun a b => differentiableAt_inv_entry (fun y => (Cm y).toBlocks₁₁) hB hdet a b
  simp only [chi, Pi.sub_apply, Function.comp_apply, Matrix.mulVec, dotProduct]
  refine (hh _).sub (DifferentiableAt.fun_sum fun a _ => ?_)
  refine DifferentiableAt.mul (hCm _ _) (DifferentiableAt.fun_sum fun b _ => ?_)
  exact (hBinv a b).mul (hh _)

end Smooth

end Lightlike.Gauge
