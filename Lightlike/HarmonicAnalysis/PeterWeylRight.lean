import Lightlike.HarmonicAnalysis.PeterWeylEquivariant
import Lightlike.HarmonicAnalysis.PeterWeylClassFunctions

/-!
# Right translations on an isotypic component

For a Haar probability measure `μ` on a compact group `G` (right invariant by
`isMulRightInvariant_of_isProbabilityMeasure`), the right translation `(R_s f)(g) = f(g s)` acts on the
isotypic component of an irreducible `ρ`, under the isometry `U : T ↦ √(dim ρ) · tr(T ρ(·))` from the
Hilbert–Schmidt matrices, as left multiplication by `ρ(s)`: `R_s (U T) = U (ρ(s) T)`
(`rightTr_sum_hsFamily`). Together with the left translations (`exists_isotypic_isometry_equivariant`,
`L_s (U T) = U (T ρ(s⁻¹))`) this is the equivariance of `U` for both translations
(`exists_isotypic_isometry_biequivariant`).

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), §1, Theorem 1 and Proposition 8.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

open UnitaryMatrixRep

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [IsProbabilityMeasure μ]

/-- The right translation `ψ ↦ ψ(· s)` on `L²`, an isometry. -/
def rightTr (s : G) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => x * s) (measurePreserving_mul_right μ s)

/-- Right translation of a continuous function. -/
def rightC (s : G) (a : C(G, ℂ)) : C(G, ℂ) := a.comp ⟨fun x => x * s, by fun_prop⟩

lemma rightTr_toLp (s : G) (a : C(G, ℂ)) :
    rightTr μ s (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a) =
      ContinuousMap.toLp (E := ℂ) 2 μ ℂ (rightC s a) := by
  refine Lp.ext ?_
  have h1 := Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp (E := ℂ) 2 μ ℂ a)
    (measurePreserving_mul_right μ s)
  have h2 := (measurePreserving_mul_right μ s).quasiMeasurePreserving.ae_eq_comp
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) a)
  filter_upwards [h1, h2, ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) (rightC s a)]
    with x hx1 hx2 hx3
  rw [hx3]
  exact hx1.trans hx2

omit [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Right translation of a matrix coefficient: `ρ_{ji}(g s) = ∑ k, ρ(s)_{ki} ρ(g)_{jk}`. -/
lemma rightC_coeffFun (ρ : IrrRep G) (s : G) (j i : ρ.ι) :
    rightC s (coeffFun ρ j i) = ∑ k, ρ.ρ.mat s k i • coeffFun ρ j k := by
  ext g
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  show ρ.ρ.mat (g * s) j i = ∑ k, ρ.ρ.mat s k i * ρ.ρ.mat g j k
  rw [ρ.ρ.mat_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Right translation of the functions `√(dim ρ) · ρ_{ji}`. -/
theorem rightTr_hsFamily (ρ : IrrRep G) (s : G) (ij : ρ.ι × ρ.ι) :
    rightTr μ s (hsFamily μ ρ ij) = ∑ k, ρ.ρ.mat s k ij.1 • hsFamily μ ρ (k, ij.2) := by
  simp only [hsFamily, map_smul]
  rw [rightTr_toLp, rightC_coeffFun, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_comm]

/-- Right translation of `∑ T_{ij} · √(dim ρ) ρ_{ji}` replaces `T` by `ρ(s) T`. -/
theorem rightTr_sum_hsFamily (ρ : IrrRep G) (s : G) (T : ρ.ι × ρ.ι → ℂ) :
    rightTr μ s (∑ ij, T ij • hsFamily μ ρ ij) =
      ∑ ij : ρ.ι × ρ.ι, (∑ k, ρ.ρ.mat s ij.1 k * T (k, ij.2)) • hsFamily μ ρ ij := by
  simp only [map_sum, map_smul, rightTr_hsFamily, Fintype.sum_prod_type, Finset.smul_sum,
    Finset.sum_smul, smul_smul]
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

/-- **The isotypic component as a representation of `G × G`.** The isometry `U : T ↦ √(dim ρ) · tr(T ρ(·))`
from the Hilbert–Schmidt matrices onto the isotypic component of `ρ` intertwines both translations:
`L_s (U T) = U (T ρ(s⁻¹))` and `R_s (U T) = U (ρ(s) T)`. -/
theorem exists_isotypic_isometry_biequivariant (ρ : IrrRep G) :
    ∃ U : EuclideanSpace ℂ (ρ.ι × ρ.ι) ≃ₗᵢ[ℂ] isotypic μ (Quotient.mk (irrSetoid G) ρ),
      (∀ T : EuclideanSpace ℂ (ρ.ι × ρ.ι),
        ((U T : isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) = ∑ ij, T ij • hsFamily μ ρ ij) ∧
      (∀ (s : G) (T : EuclideanSpace ℂ (ρ.ι × ρ.ι)),
        leftTr μ s ((U T : isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) =
          ((U (WithLp.toLp 2 fun ij : ρ.ι × ρ.ι => ∑ k, T (ij.1, k) * ρ.ρ.mat s⁻¹ k ij.2) :
            isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ)) ∧
      ∀ (s : G) (T : EuclideanSpace ℂ (ρ.ι × ρ.ι)),
        rightTr μ s ((U T : isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) =
          ((U (WithLp.toLp 2 fun ij : ρ.ι × ρ.ι => ∑ k, ρ.ρ.mat s ij.1 k * T (k, ij.2)) :
            isotypic μ (Quotient.mk (irrSetoid G) ρ)) : Lp ℂ 2 μ) := by
  obtain ⟨U, hU, hleft⟩ := exists_isotypic_isometry_equivariant μ ρ
  refine ⟨U, hU, hleft, fun s T => ?_⟩
  rw [hU, hU, rightTr_sum_hsFamily]

end

end Lightlike.HarmonicAnalysis
