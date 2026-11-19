import Lightlike.Cosmology.FLRW
import Lightlike.Spacetime.EinsteinChart
import Lightlike.Spacetime.SchwarzschildManifold
import Lightlike.Spacetime.OpenEinstein
/-!
# FLRW spacetimes on the manifold layer, and Friedmann's equations

The coordinate FLRW metric `flrwMetric` of `Lightlike/Cosmology/FLRW.lean` is a Lorentzian coordinate metric on its chart domain
(`flrw_isLorentzian`), so it is a Lorentzian metric on the manifold `flrwOpen` (an open subset of `ℝ⁴`, `OpenCoordMetric.lean`):

* `flrwManifoldMetric`: the metric `-dt² + a(t)² dx² / (1 + k |x|²/4)²` on `flrwOpen hI k`;
* `flrwManifoldMetric_coordMetric` (**the bridge**): in every chart its components are `flrwMetric a k`;
* `flrwManifold_einstein_iff_friedmann`: for the Levi-Civita connection of this metric and the perfect-fluid source with the
  components `perfectFluid`, the Einstein equations `G + Λ g = 8πG T` (`EinsteinEquations.lean`) hold iff Friedmann's first and second
  equations hold at every `t ∈ I` (`flrw_einstein_iff_friedmann`, units `c = 1`).

**Differences from the cited statement** (Carroll, *Lecture Notes on General Relativity* (1997), eq. (8.36)): the comparison with the source
is pending, as for `flrw_einstein_iff_friedmann`. The manifold is the chart domain of the isotropic coordinates `(t, x)`, `t ∈ I`,
`1 + k |x|²/4 > 0`, not `I × Σ` for a complete space `Σ` of constant curvature: for `k > 0` it misses one point of the 3-sphere, for `k < 0` it
is the Poincaré ball; the fluid is comoving and `ρ, p` depend on `t` only, by assumption; signature `-+++`, coordinates `(t, x)` with index
`0` the time.
-/

open Matrix TopologicalSpace Manifold
open scoped ContDiff Manifold
noncomputable section
namespace Lightlike
namespace Cosmology

/-- The chart domain of the FLRW coordinates is open. -/
theorem isOpen_flrwDomain {I : Set ℝ} (hI : IsOpen I) (k : ℝ) : IsOpen (flrwDomain I k) := by
  have h1 : IsOpen {x : Fin 4 → ℝ | x 0 ∈ I} := hI.preimage (continuous_apply 0)
  have h2 : IsOpen {x : Fin 4 → ℝ | 0 < 1 + k * spatialNormSq x / 4} :=
    isOpen_lt continuous_const (by unfold spatialNormSq; fun_prop)
  exact h1.inter h2

/-- **FLRW is a Lorentzian coordinate metric** on its chart domain, for `a > 0` smooth on an open interval. -/
theorem flrw_isLorentzian {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I)
    (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ) : IsLorentzianCoordMetric (flrwMetric a k) (flrwDomain I k) := by
  have hU := isOpen_flrwDomain hI k
  have hDn : ∀ x ∈ flrwDomain I k, Dn k x ≠ 0 := fun x hx => (show 0 < Dn k x from hx.2).ne'
  refine ⟨?_, fun x hx => ?_⟩
  · refine isCoordMetric_diagonal (dF a k) hU ?_ ?_
    · intro i
      by_cases hi : i = 0
      · simp only [dF, hi, ite_true]; exact contDiffOn_const
      · simp only [dF, hi, ite_false]
        have hs : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => 1 + k * spatialNormSq y / 4) := by
          unfold spatialNormSq; fun_prop
        have ha0 : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => a (y 0)) (flrwDomain I k) :=
          ha.comp (by fun_prop : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 0)).contDiffOn (fun y hy => hy.1)
        exact (ha0.div hs.contDiffOn (fun y hy => hDn y hy)).pow 2
    · intro x hx i
      unfold dF; split_ifs
      · norm_num
      · exact pow_ne_zero 2 (div_ne_zero (hpos _ hx.1).ne' (hDn x hx))
  · refine ⟨Matrix.diagonal fun μ => if μ = 0 then 1 else a (x 0) / (1 + k * spatialNormSq x / 4), ?_, ?_⟩
    · rw [Matrix.det_diagonal]
      refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun μ _ => ?_)
      split_ifs
      · norm_num
      · exact div_ne_zero (hpos _ hx.1).ne' (hDn x hx)
    · unfold flrwMetric eta
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext μ
      by_cases h0 : μ = 0
      · simp [h0, etaDiag]
      · have : etaDiag μ = 1 := by
          unfold etaDiag
          have : (μ : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
          simp [this]
        simp [h0, this]; ring

variable {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ)

/-- The chart domain of the FLRW coordinates as an open subset of `ℝ⁴`. -/
def flrwOpen : Opens (Fin 4 → ℝ) := ⟨flrwDomain I k, isOpen_flrwDomain hI k⟩

include ha hpos in
/-- **FLRW as a Lorentzian metric on the manifold layer**: the metric `-dt² + a(t)² dx² / (1 + k |x|²/4)²` on the open set `flrwOpen`. -/
def flrwManifoldMetric : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) (flrwOpen hI k) 4 :=
  openMetric (flrwOpen hI k) (flrwMetric a k) (flrw_isLorentzian hI ha hpos k)

include ha hpos in
/-- **The bridge**: in every chart the components of `flrwManifoldMetric` are the coordinate FLRW metric `flrwMetric`. -/
theorem flrwManifoldMetric_coordMetric (x₀ : flrwOpen hI k) {y : Fin 4 → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).target) :
    (flrwManifoldMetric hI ha hpos k).coordMetric x₀ y = flrwMetric a k y :=
  openMetric_coordMetric (flrwOpen hI k) (flrwMetric a k) (flrw_isLorentzian hI ha hpos k) x₀ hy

include ha hpos in
/-- **Einstein's equations for FLRW with a perfect fluid on the manifold layer are Friedmann's equations**: for the Levi-Civita connection
of `flrwManifoldMetric` and the perfect-fluid source with components `perfectFluid`, `G + Λ g = 8πG T` holds iff Friedmann's first and
second equations hold at every `t ∈ I`. -/
theorem flrwManifold_einstein_iff_friedmann {ρ p : ℝ → ℝ} (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (flrwOpen hI k))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] (h : cov.IsLeviCivita (flrwManifoldMetric hI ha hpos k))
    (Λ Gn : ℝ) :
    (flrwManifoldMetric hI ha hpos k).EinsteinEq cov Λ (8 * Real.pi * Gn)
        (fun x v w => matForm (Matrix.of fun μ ν => perfectFluid ρ p (flrwMetric a k) μ ν x.1) v w) ↔
      ∀ t ∈ I, FirstFriedmann a ρ k Λ Gn t ∧ SecondFriedmann a ρ p Λ Gn t := by
  rw [← flrw_einstein_iff_friedmann hI ha hpos k Λ Gn]
  have := openMetric_einsteinEq_iff (flrwOpen hI k) (flrwMetric a k) (flrw_isLorentzian hI ha hpos k) cov h Λ
    (8 * Real.pi * Gn) (fun y => Matrix.of fun μ ν => perfectFluid ρ p (flrwMetric a k) μ ν y)
  refine this.trans ?_
  unfold IsEinsteinSolution
  exact ⟨fun H => ⟨(flrw_isLorentzian hI ha hpos k).1, fun x hx μ ν => H x hx μ ν⟩, fun H y hy μ ν => H.2 y hy μ ν⟩
end Cosmology
end Lightlike
