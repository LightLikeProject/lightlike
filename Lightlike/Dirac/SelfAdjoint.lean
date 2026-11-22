import Mathlib
import Lightlike.Dirac.Flat

/-!
# Formal self-adjointness of the flat Dirac operator and `∫ ‖D f‖² = ∫ ∑ ‖∂ᵢ f‖²`

For a Clifford module `V` over `Cl(ℝⁿ, -‖·‖²)` which is a real inner product space on which the
Clifford multiplications `γᵢ` are skew-adjoint (`IsSkewRep`), the Dirac operator `D = ∑ γᵢ ∂ᵢ` is
formally self-adjoint on compactly supported `C¹` functions (`integral_dirac_inner`), and
for compactly supported `C²` functions the integrated Lichnerowicz formula holds
(`integral_norm_dirac_sq`): `∫ ‖D f‖² = ∫ ∑ᵢ ‖∂ᵢ f‖²`, which says that `D²` and `∇*∇ = -Δ` have the same
quadratic form in flat space (`R = 0`). This is the flat ingredient of identifying `-∑ hessF i i`
with the adjoint `∇*∇`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); definitions only.
-/

open CliffordAlgebra InnerProductSpace MeasureTheory Laplacian

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Clifford multiplications by the basis vectors are skew-adjoint. -/
def IsSkewRep (ρ : CliffordRep n V) : Prop :=
  ∀ (i : Fin n) (w u : V), inner ℝ (gam ρ i w) u = -inner ℝ w (gam ρ i u)

/-- Integration by parts for `V`-valued compactly supported `C¹` functions, in direction `eᵢ`. -/
lemma integral_inner_fderiv {f g : E n → V} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (i : Fin n) :
    ∫ x, inner ℝ (f x) (fderiv ℝ g x (e i)) = -∫ x, inner ℝ (fderiv ℝ f x (e i)) (g x) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hgd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have h1 : Integrable (fun x => innerSL ℝ (fderiv ℝ f x (e i)) (g x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (innerSL ℝ).continuous₂.comp₂ ((hfd.clm_apply continuous_const)) hg.continuous
    · refine HasCompactSupport.intro hgc.isCompact fun x hx => ?_
      simp [image_eq_zero_of_notMem_tsupport hx]
  have h2 : Integrable (fun x => innerSL ℝ (f x) (fderiv ℝ g x (e i))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (innerSL ℝ).continuous₂.comp₂ hf.continuous ((hgd.clm_apply continuous_const))
    · refine HasCompactSupport.intro hfc.isCompact fun x hx => ?_
      simp [image_eq_zero_of_notMem_tsupport hx]
  have h3 : Integrable (fun x => innerSL ℝ (f x) (g x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (innerSL ℝ).continuous₂.comp₂ hf.continuous hg.continuous
    · refine HasCompactSupport.intro hfc.isCompact fun x hx => ?_
      simp [image_eq_zero_of_notMem_tsupport hx]
  have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := innerSL ℝ) (v := e i) (f := f) (g := g) h1 h2 h3
    (fun x _ => (hf.differentiable (by norm_num)) x) (fun x _ => (hg.differentiable (by norm_num)) x)
  exact this

/-- Compact support of the composite with a continuous linear map. -/
lemma hasCompactSupport_clm {g : E n → V} (hgc : HasCompactSupport g) (L : V →L[ℝ] V) :
    HasCompactSupport (fun x => L (g x)) :=
  hgc.comp_left (g := L) (map_zero L)

/-- **Formal self-adjointness of the flat Dirac operator.** For a skew Clifford module and
compactly supported `C¹` functions, `∫ ⟪D f, g⟫ = ∫ ⟪f, D g⟫`. -/
theorem integral_dirac_inner {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {f g : E n → V}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∫ x, inner ℝ (dirac ρ f x) (g x) = ∫ x, inner ℝ (f x) (dirac ρ g x) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hgd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  -- termwise
  have hterm : ∀ i : Fin n, ∫ x, inner ℝ (gam ρ i (fderiv ℝ f x (e i))) (g x) =
      ∫ x, inner ℝ (f x) (gam ρ i (fderiv ℝ g x (e i))) := by
    intro i
    have hgi : ContDiff ℝ 1 (fun x => gam ρ i (g x)) := (gam ρ i).contDiff.comp hg
    have hd : ∀ x, fderiv ℝ (fun x => gam ρ i (g x)) x (e i) = gam ρ i (fderiv ℝ g x (e i)) := by
      intro x
      have hh := (gam ρ i).hasFDerivAt.comp x ((hg.differentiable (by norm_num)) x).hasFDerivAt
      exact congrArg (fun L => L (e i)) hh.fderiv
    have := integral_inner_fderiv hf hgi hfc (hasCompactSupport_clm hgc (gam ρ i)) i
    simp only [hd] at this
    calc ∫ x, inner ℝ (gam ρ i (fderiv ℝ f x (e i))) (g x)
        = ∫ x, -inner ℝ (fderiv ℝ f x (e i)) (gam ρ i (g x)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact hρ i _ _
      _ = -∫ x, inner ℝ (fderiv ℝ f x (e i)) (gam ρ i (g x)) := integral_neg _
      _ = _ := by rw [← this]
  have hint : ∀ i : Fin n, Integrable (fun x => inner ℝ (gam ρ i (fderiv ℝ f x (e i))) (g x)) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (innerSL ℝ).continuous₂.comp₂
        ((gam ρ i).continuous.comp (hfd.clm_apply continuous_const)) hg.continuous
    · refine HasCompactSupport.intro hgc.isCompact fun x hx => ?_
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hint' : ∀ i : Fin n, Integrable (fun x => inner ℝ (f x) (gam ρ i (fderiv ℝ g x (e i)))) := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (innerSL ℝ).continuous₂.comp₂ hf.continuous
        ((gam ρ i).continuous.comp (hgd.clm_apply continuous_const))
    · refine HasCompactSupport.intro hfc.isCompact fun x hx => ?_
      simp [image_eq_zero_of_notMem_tsupport hx]
  simp only [dirac, sum_inner, inner_sum]
  rw [integral_finsetSum _ (fun i _ => hint i), integral_finsetSum _ (fun i _ => hint' i)]
  exact Finset.sum_congr rfl fun i _ => hterm i

end Lightlike.Dirac
