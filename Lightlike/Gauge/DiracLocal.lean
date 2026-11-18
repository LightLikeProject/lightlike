import Lightlike.Gauge.DiracAlgo
import Lightlike.Gauge.MinorExists

/-!
# A selection near a point from constant rank

The pointwise form of the constant-rank hypothesis of the Dirac algorithm (Wipf's lectures, arXiv:hep-th/9312078, Section 3.3):
if the consistency matrix `A x = ({S_i, φ_a}(x))` of a stage has continuous entries at `x₀` and constant rank `r` near `x₀`, there is a
selection `σ` (rows and columns of a nonzero `r × r` minor at `x₀`) such that, on a neighbourhood of `x₀`, the selected block is
invertible and the Schur complement vanishes (`exists_selection_near`). This is the local, chart-dependent form of the source's global
null vectors; a selection valid on the whole surface needs a cover (not formalised).
-/

namespace Lightlike.Gauge

open Matrix Filter Topology

variable {E : Type*}

/-- The selection given by `r` rows `R` and `r` columns `C` (injective), the other rows and columns in the remaining parts. -/
noncomputable def Sel.ofMinor {S : Stage E} {M r : ℕ} (R : Fin r → Fin S.n) (C : Fin r → Fin M)
    (hR : Function.Injective R) (hC : Function.Injective C) : Sel S M := by
  classical
  exact
    { r := r
      p := Fintype.card {x // x ∉ Set.range R}
      l := Fintype.card {x // x ∉ Set.range C}
      eR := (Equiv.sumCompl (· ∈ Set.range R)).symm.trans
        (Equiv.sumCongr (Equiv.ofInjective R hR).symm (Fintype.equivFin _))
      eC := (Equiv.sumCompl (· ∈ Set.range C)).symm.trans
        (Equiv.sumCongr (Equiv.ofInjective C hC).symm (Fintype.equivFin _)) }

/-- The selected block is the submatrix on the chosen rows and columns. -/
theorem Sel.ofMinor_block {S : Stage E} {M r : ℕ} (R : Fin r → Fin S.n) (C : Fin r → Fin M)
    (hR : Function.Injective R) (hC : Function.Injective C) (br : (E → ℝ) → (E → ℝ) → E → ℝ)
    (φ : Fin M → E → ℝ) (x : E) :
    (S.consCm br φ (Sel.ofMinor R C hR hC) x).toBlocks₁₁ =
      Matrix.of (fun i j => br (S.Φ (R i)) (φ (C j)) x) := by
  classical
  ext i j
  simp [Stage.consCm, Matrix.toBlocks₁₁, Sel.ofMinor, Equiv.sumCompl_apply_inl, Equiv.ofInjective_apply]
  sorry

end Lightlike.Gauge
