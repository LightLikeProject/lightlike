import Lightlike.Gauge.DiracStage
import Lightlike.Gauge.Constraints
import Lightlike.Gauge.DiracAlgo

/-!
# The Dirac stage for Physlib's Poisson bracket

`DiracStage` treats a consistency system `Cm x u + h x = 0` for abstract functions `Cm`, `h`. Here `Cm` is the matrix of
Poisson brackets of the primary constraints (`bracketMatrix`) and `h b = {φ_b, H}`, the primary constraints being indexed by
`Fin r ⊕ Fin p ≃ Fin (r + p)` (an `r × r` block `B`, the rest `p`). The consistency conditions of Dirac (Wipf's lectures,
arXiv:hep-th/9312078, Section 3.3, eq. (3.24)) are
`{φ_b, H} + ∑_a {φ_b, φ_a} u_a = 0`; under an invertible block `B` and constant rank, they are solvable iff `χ = 0`.
-/

open ClassicalMechanics

namespace Lightlike.Gauge

open Matrix

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {r p : ℕ}

/-- The bracket matrix of the primary constraints, indexed by `Fin r ⊕ Fin p`. -/
noncomputable def bracketCm (φ : Fin (r + p) → X → X → ℝ) (x : X × X) : Matrix (Fin r ⊕ Fin p) (Fin r ⊕ Fin p) ℝ :=
  (bracketMatrix φ x.1 x.2).submatrix finSumFinEquiv finSumFinEquiv

/-- The vector `h_b = {φ_b, H}`, indexed by `Fin r ⊕ Fin p`. -/
noncomputable def bracketH (φ : Fin (r + p) → X → X → ℝ) (H : X → X → ℝ) (x : X × X) : Fin r ⊕ Fin p → ℝ :=
  fun b => poissonBracket (φ (finSumFinEquiv b)) H x.1 x.2

/-- The transported system: `(bracketCm u' + bracketH) i` is the consistency expression for the constraint `e i`. -/
theorem bracketCm_mulVec_add (φ : Fin (r + p) → X → X → ℝ) (H : X → X → ℝ) (x : X × X) (u : Fin (r + p) → ℝ)
    (i : Fin r ⊕ Fin p) :
    (bracketCm φ x *ᵥ (u ∘ finSumFinEquiv) + bracketH φ H x) i =
      poissonBracket (φ (finSumFinEquiv i)) H x.1 x.2 +
        ∑ a, bracketMatrix φ x.1 x.2 (finSumFinEquiv i) a * u a := by
  simp only [Pi.add_apply, bracketCm, bracketH, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
    Function.comp_apply]
  rw [Equiv.sum_comp finSumFinEquiv (fun a => bracketMatrix φ x.1 x.2 (finSumFinEquiv i) a * u a), add_comm]

/-- **The Dirac consistency system for Physlib's bracket is the abstract one**: a multiplier `u` solves
`{φ_b, H} + ∑_a {φ_b, φ_a} u_a = 0` for all `b` iff the transported vector solves `bracketCm u' + bracketH = 0`. -/
theorem poisson_consistency_iff (φ : Fin (r + p) → X → X → ℝ) (H : X → X → ℝ) (x : X × X) :
    (∃ u : Fin (r + p) → ℝ, ∀ b, poissonBracket (φ b) H x.1 x.2 +
        ∑ a, bracketMatrix φ x.1 x.2 b a * u a = 0) ↔
      ∃ u' : Fin r ⊕ Fin p → ℝ, bracketCm φ x *ᵥ u' + bracketH φ H x = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u ∘ finSumFinEquiv, funext fun i => ?_⟩
    rw [bracketCm_mulVec_add]; exact hu _
  · rintro ⟨u', hu'⟩
    refine ⟨u' ∘ finSumFinEquiv.symm, fun b => ?_⟩
    have := congrFun hu' (finSumFinEquiv.symm b)
    have h2 := bracketCm_mulVec_add φ H x (u' ∘ finSumFinEquiv.symm) (finSumFinEquiv.symm b)
    simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id, Equiv.apply_symm_apply] at h2
    rw [← h2]; exact this

/-- **Dirac's secondary constraints for Physlib's bracket**: where the block `B` of the bracket matrix of the primary
constraints is invertible and the rank is constant (`E = D B⁻¹ C`), the consistency conditions
`{φ_b, H} + ∑_a {φ_b, φ_a} u_a = 0` have a solution iff `χ x = 0`, `χ = h₂ - D B⁻¹ h₁` with `h_b = {φ_b, H}`. -/
theorem poisson_exists_multiplier_iff_chi (φ : Fin (r + p) → X → X → ℝ) (H : X → X → ℝ) {x : X × X}
    (hB : IsUnit (bracketCm φ x).toBlocks₁₁.det)
    (hS : (bracketCm φ x).toBlocks₂₂ =
      (bracketCm φ x).toBlocks₂₁ * (bracketCm φ x).toBlocks₁₁⁻¹ * (bracketCm φ x).toBlocks₁₂) :
    (∃ u : Fin (r + p) → ℝ, ∀ b, poissonBracket (φ b) H x.1 x.2 +
        ∑ a, bracketMatrix φ x.1 x.2 b a * u a = 0) ↔
      chi (fun y => bracketCm φ y) (fun y => bracketH φ H y) x = 0 := by
  rw [poisson_consistency_iff]
  exact exists_multiplier_iff_chi (fun y => bracketCm φ y) (fun y => bracketH φ H y) hB hS

/-- **Physlib's Poisson bracket as a bracket of functions on `X × X`**, the `br` of `DiracAlgo`. -/
noncomputable def physBr (f g : X × X → ℝ) (z : X × X) : ℝ :=
  poissonBracket (fun p q => f (p, q)) (fun p q => g (p, q)) z.1 z.2

/-- On the constraint functions, `physBr` is the matrix `bracketMatrix` of `Constraints.lean`. -/
theorem physBr_eq_bracketMatrix (φ : Fin (r + p) → X → X → ℝ) (a b : Fin (r + p)) (x : X × X) :
    physBr (fun z => φ a z.1 z.2) (fun z => φ b z.1 z.2) x = bracketMatrix φ x.1 x.2 a b := rfl

end Lightlike.Gauge
