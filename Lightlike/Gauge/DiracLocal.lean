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

/-- **A selection adapted to a point, from constant rank**: if the entries of the consistency matrix are continuous at `x₀` and
its rank is constant near `x₀`, some selection (rows and columns of a nonzero minor at `x₀`) has, on a neighbourhood of `x₀`, an
invertible block and a vanishing Schur complement. -/
theorem exists_selection_near [TopologicalSpace E] {M : ℕ} (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ)
    (S : Stage E) {x₀ : E}
    (hcont : ∀ i a, ContinuousAt (fun x => br (S.Φ i) (φ a) x) x₀) {r : ℕ}
    (hrank : ∀ᶠ x in 𝓝 x₀, (Matrix.of fun (i : Fin S.n) (a : Fin M) => br (S.Φ i) (φ a) x).rank = r) :
    ∃ σ : Sel S M, ∀ᶠ x in 𝓝 x₀,
      IsUnit (S.consCm br φ σ x).toBlocks₁₁.det ∧
        (S.consCm br φ σ x).toBlocks₂₂ =
          (S.consCm br φ σ x).toBlocks₂₁ * (S.consCm br φ σ x).toBlocks₁₁⁻¹ * (S.consCm br φ σ x).toBlocks₁₂ := by
  classical
  set A : E → Matrix (Fin S.n) (Fin M) ℝ := fun x => Matrix.of fun i a => br (S.Φ i) (φ a) x with hA
  obtain ⟨R, C, hR, hC, hunit⟩ := exists_isUnit_det_submatrix (A x₀)
  have hr0 : (A x₀).rank = r := hrank.self_of_nhds
  let σ : Sel S M := Sel.ofMinor R C hR hC
  refine ⟨σ, ?_⟩
  have hB : ∀ x, (S.consCm br φ σ x).toBlocks₁₁ = (A x).submatrix R C := fun x =>
    Sel.ofMinor_block R C hR hC br φ x
  have hinv : ∀ᶠ x in 𝓝 x₀, IsUnit (S.consCm br φ σ x).toBlocks₁₁.det := by
    refine eventually_isUnit_det (B := fun x => (S.consCm br φ σ x).toBlocks₁₁) (fun i j => ?_) ?_
    · simp only [hB, Matrix.submatrix_apply]; exact hcont _ _
    · simpa [hB] using hunit
  filter_upwards [hinv, hrank] with x hx hxr
  refine ⟨hx, ?_⟩
  have hsplit := fromBlocks_toBlocks (S.consCm br φ σ x)
  have hrk : (S.consCm br φ σ x).rank = r := by
    have : S.consCm br φ σ x = Matrix.reindex σ.eR σ.eC (A x) := rfl
    rw [this, Matrix.rank_reindex]; exact hxr
  have hle : (fromBlocks (S.consCm br φ σ x).toBlocks₁₁ (S.consCm br φ σ x).toBlocks₁₂
      (S.consCm br φ σ x).toBlocks₂₁ (S.consCm br φ σ x).toBlocks₂₂).rank ≤ Fintype.card (Fin σ.r) := by
    rw [hsplit, hrk, Fintype.card_fin]
    exact le_of_eq hr0.symm
  exact schur_eq_zero_of_rank_le_block _ _ _ _ hx hle

end Lightlike.Gauge
