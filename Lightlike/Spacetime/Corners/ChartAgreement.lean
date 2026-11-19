import Lightlike.Spacetime.CurvatureSymmetries
import Lightlike.Spacetime.Corners.CurvatureSymmetries
import Lightlike.Spacetime.ChartConnection
import Lightlike.Spacetime.Corners.ChartConnection
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.RiemannSymmetryWithin
import Lightlike.Spacetime.CurvatureWithin
import Lightlike.GR.Einstein
import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.Corners.ChartCurvature
import Lightlike.Spacetime.Corners.Coordinates
import Lightlike.Spacetime.Corners.Curvature

/-!
# The curvature of a Levi-Civita connection in a chart agrees with the coordinate curvature

For a Levi-Civita connection `cov` of a Lorentzian metric `g` on a Hausdorff manifold modelled on `ℝⁿ`, in the
chart at `x₀`, at the point `φ⁻¹ y`:

* `riemann_coord_compW`: the components of `R(∂_μ, ∂_ν) ∂_σ` are the coordinate Riemann tensor
  `riemann (g.coordMetricW x₀)` of `Curvature.lean` (from `curvature_hatW`, `gamHat_coordW` and
  `mvfderiv_gamHat_coordW`: the Christoffel tensor of the connection against the trivialization is the Christoffel
  symbol of the coordinate metric);
* `ricciAt_coordW`: the intrinsic Ricci tensor (trace over a basis of the tangent space) is the coordinate
  `ricci`;
* `scalarCurvatureAt_coordW`: the intrinsic scalar curvature is the coordinate `scalarCurvature` (the trace of the
  Ricci tensor with `g` does not depend on the basis: `trace_raiseW`);
* `satisfiesEinstein_iff_chart_provedW`: the Einstein equations of `Connection.lean` hold iff the coordinate
  vacuum equations hold in every chart.

**Corners.** Everything is for any `ModelWithCorners I ℝ (Fin n → ℝ) H`; the coordinate Christoffel, Riemann, Ricci and scalar
curvature are those of `CurvatureWithin.lean`, with derivatives within `range I`, and the chart image is a set `IsCoordMetricW`
(relatively open in `range I`).

**Differences from the tasks.** `scalarCurvatureAt_coordW` is the statement of the task `T-GE1-P5` and
`satisfiesEinstein_iff_chart_provedW` that of `T-GE1-P6`, each with the added hypothesis
`[IsManifold I 2 M]` (needed by `curvatureAt_apply_proved`); the tasks stay open. The comparison
of the definitions with Carroll, *Spacetime and Geometry*, ch. 3, and Wald, *General Relativity*, is pending: the
sources were not read at the cited locations.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/ChartAgreement.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} (g : NondegMetric I M) (x : M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of `g` in a basis. -/
def gramBW (b : Module.Basis ι ℝ (TangentSpace I x)) : Matrix ι ι ℝ :=
  Matrix.of fun i j => g.g x (b i) (b j)

/-- The Gram matrix of a Lorentzian metric in a basis is invertible. -/
theorem gramB_isUnitW (b : Module.Basis ι ℝ (TangentSpace I x)) : IsUnit (gramBW g x b).det := by
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (g.bilinForm_nondegenerate x)
  have hmat : LinearMap.BilinForm.toMatrix b (g.g x).toBilinForm = gramBW g x b := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [← hmat]
  exact h.isUnit

/-- The coordinates of a tangent vector in any basis are `Σ g^{ij} g(u, e_j)`. -/
theorem coord_eq_sum_basisW (b : Module.Basis ι ℝ (TangentSpace I x)) (u : TangentSpace I x) (i : ι) :
    b.coord i u = ∑ j, (gramBW g x b)⁻¹ i j * g.g x u (b j) := by
  have hsym : (gramBW g x b).transpose = gramBW g x b := by
    ext i j; exact g.symm x _ _
  have hG := Matrix.nonsing_inv_mul _ (gramB_isUnitW g x b)
  have hexp : ∀ j, g.g x u (b j) = ∑ k, b.coord k u * gramBW g x b k j := by
    intro j
    conv_lhs => rw [← b.sum_repr u]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [gramBW, Module.Basis.coord_apply]
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 := congrFun (congrFun hG i)
  simp only [Matrix.mul_apply, Matrix.one_apply] at h2
  have : ∀ k, ∑ j, (gramBW g x b)⁻¹ i j * (b.coord k u * gramBW g x b k j) = b.coord k u * (if i = k then 1 else 0) := by
    intro k
    rw [← h2 k]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (congrFun hsym k) j
    simp only [Matrix.transpose_apply] at this
    rw [← this]; ring
  simp only [this]
  simp

/-- The endomorphism of a bilinear form `B` raised with `g`: `g(T u, w) = B(u, w)`. -/
def raiseW (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun u := sharp g x (LinearMap.toContinuousLinearMap (B u))
  map_add' u v := by
    rw [map_add, ← sharp_add]; congr 1
  map_smul' c u := by
    rw [map_smul, ← sharp_smul]; congr 1

/-- `g(T u, w) = B(u, w)`. -/
theorem g_raiseW (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (u w : TangentSpace I x) :
    g.g x (raiseW g x B u) w = B u w :=
  g_sharp g x _ w

/-- The trace of a bilinear form with respect to `g` does not depend on the basis. -/
theorem trace_raiseW (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (b : Module.Basis ι ℝ (TangentSpace I x)) :
    LinearMap.trace ℝ (TangentSpace I x) (raiseW g x B) =
      ∑ i, ∑ j, (gramBW g x b)⁻¹ i j * B (b i) (b j) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.toMatrix_apply, Matrix.diag]
  have := coord_eq_sum_basisW g x b (raiseW g x B (b i)) i
  rw [Module.Basis.coord_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g_raiseW]
end General

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
variable (cov : Connection I M) [LocallySmoothConnectionW cov] (x₀ : M)

/-- The components of the curvature at any point of the chart domain. -/
theorem hv_curvatureAtW {p : M} (hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet)
    (X₀ Y₀ Z₀ : TangentSpace I p) :
    hvW x₀ p (cov.curvatureAt p X₀ Y₀ Z₀) = RhatW cov x₀ p (hvW x₀ p X₀) (hvW x₀ p Y₀) (hvW x₀ p Z₀) := by
  have h2 := curvature_hatW cov x₀ hp (eventually_extendW p X₀) (eventually_extendW p Y₀)
    (eventually_extendW p Z₀)
  simp only [FiberBundle.extend_apply_self] at h2
  unfold Connection.curvatureAt
  dsimp only
  simp only [FiberBundle.extend_apply_self]
  exact h2

omit [LocallySmoothConnectionW cov] in
/-- The Christoffel tensor in the components of the trivialization is the Christoffel symbol of the coordinate
metric, for the Levi-Civita connection. -/
theorem gamHat_coordW (g : NondegMetric I M) (h : cov.IsLeviCivita g)
    {z : M} (hz : z ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet) (i j : Fin n) :
    gamHatW cov x₀ z (Pi.single j 1) (Pi.single i 1) =
      ∑ k, christoffelW (range I) (g.coordMetricW x₀) k i j (extChartAt I x₀ z) • (Pi.single k 1 : Fin n → ℝ) := by
  have hz' : extChartAt I x₀ z ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (by
      rw [extChartAt_source]; simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using hz)
  have hzs : z ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]; simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using hz
  have hcf : ∀ q ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet, ∀ k : Fin n,
      coordFieldW (I := I) x₀ k q = cfieldW (I := I) x₀ (Pi.single k 1) q := by
    intro q hq k
    unfold coordFieldW cfieldW
    rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTrivW (I := I) n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := k) hq]
    exact (show _ = coordBasisW x₀ hq k from rfl).trans (coordBasis_applyW x₀ hq k)
  have hev : (cfieldW (I := I) x₀ (Pi.single j 1 : Fin n → ℝ)) =ᶠ[nhds z] coordFieldW (I := I) x₀ j := by
    filter_upwards [(tTrivW (I := I) (E := Fin n → ℝ) x₀).open_baseSet.mem_nhds hz] with q hq
    exact (hcf q hq j).symm
  have hc1 : cov (cfieldW (I := I) x₀ (Pi.single j 1 : Fin n → ℝ)) z = cov (coordFieldW (I := I) x₀ j) z :=
    (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq
      ((contMDiffAt_cfieldW x₀ _ hz).mdifferentiableAt (by simp)) (mdiffAt_coordFieldW x₀ j hz)
      Filter.univ_mem hev
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hc2 : cov (coordFieldW (I := I) x₀ j) z = leviCivita g (coordFieldW (I := I) x₀ j) z :=
    leviCivita_unique g h hLC (mdiffAt_coordFieldW x₀ j hz)
  have hcf2 : cfieldW (I := I) x₀ (Pi.single i 1 : Fin n → ℝ) z = coordFieldW (I := I) x₀ i z := (hcf z hz i).symm
  rw [gamHat_eqW cov x₀ _ _ hz, hc1, hc2, hcf2]
  have key := leviCivita_coordFieldW g x₀ hz' i j
  rw [(extChartAt I x₀).left_inv hzs] at key
  rw [key]
  have hvc : ∀ u : TangentSpace I z,
      hvW x₀ z u = (tTrivW (I := I) (E := Fin n → ℝ) x₀).continuousLinearMapAt ℝ z u := fun u => by
    rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hz]
  show hvW x₀ z _ = _
  rw [hvc, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ← hvc, hcf z hz k]
  exact congrArg (fun v => _ • v) (hv_symmLW x₀ hz (Pi.single k 1))

/-- The derivative of `Γ̂` evaluated on two vectors is the derivative of the evaluation. -/
theorem mvfderiv_gamHat_applyW {p : M} (hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet)
    (u : TangentSpace I p) (a b : Fin n → ℝ) :
    (mvfderiv I (gamHatW cov x₀) p u) a b =
      mvfderiv I (fun z => gamHatW cov x₀ z a b) p u := by
  have hΓ := mdiffAt_gamHatW cov x₀ hp
  have h1 : MDifferentiableAt I 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (fun z => gamHatW cov x₀ z a) p :=
    hΓ.clm_apply mdifferentiableAt_const
  have e1 := mvfderiv_clm_applyW (E := Fin n → ℝ) (gamHatW cov x₀) (fun _ : M => a) p hΓ mdifferentiableAt_const u
  have e2 := mvfderiv_clm_applyW (E := Fin n → ℝ) (fun z => gamHatW cov x₀ z a) (fun _ : M => b) p h1
    mdifferentiableAt_const u
  rw [mvfderiv_const] at e1 e2
  simp only [zero_apply, map_zero, add_zero] at e1 e2
  rw [e2, e1]

/-- The derivative of `Γ̂` along `∂_μ` in the chart is `Σ_k ∂_μ Γᵏ_{νσ} e_k`, with the derivative taken within `range I`. -/
theorem mvfderiv_gamHat_coordW (g : NondegMetric I M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target) (μ ν σ : Fin n) :
    (mvfderiv I (gamHatW cov x₀) ((extChartAt I x₀).symm y)
      (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))) (Pi.single σ 1) (Pi.single ν 1) =
      ∑ k, pdW (range I) μ (fun y' => christoffelW (range I) (g.coordMetricW x₀) k ν σ y') y •
        (Pi.single k 1 : Fin n → ℝ) := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  have hp' : (extChartAt I x₀).symm y ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet := hp
  have hzs : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
  rw [mvfderiv_gamHat_applyW cov x₀ hp']
  set H : (Fin n → ℝ) → (Fin n → ℝ) := fun y' => ∑ k, christoffelW (range I) (g.coordMetricW x₀) k ν σ y' •
    (Pi.single k 1 : Fin n → ℝ) with hH
  have hgc := g.isCoordMetricW_coordMetric x₀
  have hd : ∀ k : Fin n, DifferentiableWithinAt ℝ
      (fun y' => christoffelW (range I) (g.coordMetricW x₀) k ν σ y') (range I) y := fun k =>
    differentiableWithinAt_of_contDiffOn hgc (hgc.contDiffOn_christoffel k ν σ) hy
  have hHd : DifferentiableWithinAt ℝ H (range I) y := by
    rw [hH]
    exact DifferentiableWithinAt.fun_sum fun k _ => (hd k).smul_const _
  have hΓ := mdiffAt_gamHatW cov x₀ hp'
  have hdiff : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ)
      (fun z => gamHatW cov x₀ z (Pi.single σ 1) (Pi.single ν 1)) ((extChartAt I x₀).symm y) :=
    (hΓ.clm_apply mdifferentiableAt_const).clm_apply mdifferentiableAt_const
  rw [mvfderiv_eq_chart_at (fun z => gamHatW cov x₀ z (Pi.single σ 1) (Pi.single ν 1)) x₀ _ hzs hdiff]
  rw [mfderiv_chart_coordFieldW x₀ μ hy, (extChartAt I x₀).right_inv hy]
  have hev : ((fun z => gamHatW cov x₀ z (Pi.single σ 1) (Pi.single ν 1)) ∘ (extChartAt I x₀).symm)
      =ᶠ[nhdsWithin y (range I)] H := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy] with w hw
    have hb : (extChartAt I x₀).symm w ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet :=
      symm_mem_chartTriv_baseSetW x₀ hw
    have := gamHat_coordW cov x₀ g h hb ν σ
    rw [(extChartAt I x₀).right_inv hw] at this
    exact this
  have hyr : y ∈ range I := extChartAt_target_subset_range x₀ hy
  rw [hev.fderivWithin_eq (hev.eq_of_nhdsWithin hyr)]
  rw [hH]
  have hdd : HasFDerivWithinAt (fun y' => ∑ k, christoffelW (range I) (g.coordMetricW x₀) k ν σ y' •
      (Pi.single k 1 : Fin n → ℝ)) (∑ k, (fderivWithin ℝ (fun y' => christoffelW (range I) (g.coordMetricW x₀) k ν σ y')
        (range I) y).smulRight (Pi.single k 1 : Fin n → ℝ)) (range I) y :=
    HasFDerivWithinAt.fun_sum fun k _ => ((hd k).hasFDerivWithinAt).smul_const _
  rw [hdd.fderivWithin (I.uniqueDiffOn y hyr)]
  simp [pdW]

/-- The components of the coordinate field `∂_k` are `e_k`. -/
theorem hv_coordFieldW (x₀ : M) {p : M} (hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet) (k : Fin n) :
    hvW x₀ p (coordFieldW (I := I) x₀ k p) = Pi.single k 1 := by
  have : coordFieldW (I := I) x₀ k p = cfieldW (I := I) x₀ (Pi.single k 1) p := by
    unfold coordFieldW cfieldW
    rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTrivW (I := I) n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := k) hp]
    exact (show _ = coordBasisW x₀ hp k from rfl).trans (coordBasis_applyW x₀ hp k)
  rw [this]
  exact hv_symmLW x₀ hp _

/-- `e⁻¹ (e_k)` is the coordinate field `∂_k` on the chart domain. -/
theorem symmL_eq_coordFieldW (x₀ : M) {p : M} (hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet) (k : Fin n) :
    (tTrivW (I := I) (E := Fin n → ℝ) x₀).symmL ℝ p (Pi.single k 1) = coordFieldW (I := I) x₀ k p := by
  unfold coordFieldW
  rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTrivW (I := I) n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := k) hp]
  exact ((show _ = coordBasisW x₀ hp k from rfl).trans (coordBasis_applyW x₀ hp k)).symm

/-- **The curvature in a chart is the coordinate Riemann tensor**: for the Levi-Civita connection, the `ρ`-component of the components of `R(∂_μ, ∂_ν) ∂_σ` at `φ⁻¹ y` is `riemannW (range I) (g.coordMetricW x₀) ρ σ μ ν y`. -/
theorem riemann_coord_compW (g : NondegMetric I M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target) (μ ν σ ρ : Fin n) :
    (hvW x₀ ((extChartAt I x₀).symm y)
      (cov.curvatureAt ((extChartAt I x₀).symm y)
        (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
        (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y))
        (coordFieldW (I := I) x₀ σ ((extChartAt I x₀).symm y)))) ρ =
      riemannW (range I) (g.coordMetricW x₀) ρ σ μ ν y := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  have hp' : (extChartAt I x₀).symm y ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet := hp
  rw [hv_curvatureAtW cov x₀ hp', hv_coordFieldW x₀ hp', hv_coordFieldW x₀ hp', hv_coordFieldW x₀ hp']
  unfold RhatW
  rw [symmL_eq_coordFieldW x₀ hp', symmL_eq_coordFieldW x₀ hp',
    mvfderiv_gamHat_coordW cov x₀ g h hy μ ν σ, mvfderiv_gamHat_coordW cov x₀ g h hy ν μ σ,
    gamHat_coordW cov x₀ g h hp' ν σ, gamHat_coordW cov x₀ g h hp' μ σ,
    (extChartAt I x₀).right_inv hy]
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  simp only [gamHat_coordW cov x₀ g h hp', (extChartAt I x₀).right_inv hy]
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp only [riemannW, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [mul_comm]
  ring

/-- `RhatW` is additive in its first argument. -/
theorem Rhat_add_leftW (p : M) (a a' b c : Fin n → ℝ) :
    RhatW cov x₀ p (a + a') b c = RhatW cov x₀ p a b c + RhatW cov x₀ p a' b c := by
  unfold RhatW
  simp only [map_add, add_apply]
  abel

/-- `RhatW` is homogeneous in its first argument. -/
theorem Rhat_smul_leftW (p : M) (r : ℝ) (a b c : Fin n → ℝ) :
    RhatW cov x₀ p (r • a) b c = r • RhatW cov x₀ p a b c := by
  unfold RhatW
  simp only [map_smul, smul_apply]
  module

/-- `RhatW` is additive in its second argument. -/
theorem Rhat_add_midW (p : M) (a b b' c : Fin n → ℝ) :
    RhatW cov x₀ p a (b + b') c = RhatW cov x₀ p a b c + RhatW cov x₀ p a b' c := by
  unfold RhatW
  simp only [map_add, add_apply]
  abel

/-- `RhatW` is homogeneous in its second argument. -/
theorem Rhat_smul_midW (p : M) (r : ℝ) (a b c : Fin n → ℝ) :
    RhatW cov x₀ p a (r • b) c = r • RhatW cov x₀ p a b c := by
  unfold RhatW
  simp only [map_smul, smul_apply]
  module

/-- `RhatW` is additive in its third argument. -/
theorem Rhat_add_rightW (p : M) (a b c c' : Fin n → ℝ) :
    RhatW cov x₀ p a b (c + c') = RhatW cov x₀ p a b c + RhatW cov x₀ p a b c' := by
  unfold RhatW
  simp only [map_add, add_apply]
  abel

/-- `RhatW` is homogeneous in its third argument. -/
theorem Rhat_smul_rightW (p : M) (r : ℝ) (a b c : Fin n → ℝ) :
    RhatW cov x₀ p a b (r • c) = r • RhatW cov x₀ p a b c := by
  unfold RhatW
  simp only [map_smul, smul_apply]
  module

/-- The curvature as a linear map in its first slot, in components. -/
def RhatFstW (p : M) (b c : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v := RhatW cov x₀ p v b c
  map_add' a a' := Rhat_add_leftW cov x₀ p a a' b c
  map_smul' r a := Rhat_smul_leftW cov x₀ p r a b c

/-- The Ricci tensor is the trace of the curvature in components. -/
theorem ricciAt_eq_traceW {p : M} (hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet)
    (Y Z : TangentSpace I p) :
    cov.ricciAt p Y Z = LinearMap.trace ℝ (Fin n → ℝ) (RhatFstW cov x₀ p (hvW x₀ p Y) (hvW x₀ p Z)) := by
  set hvC : TangentSpace I p →L[ℝ] (Fin n → ℝ) := (tTrivW (I := I) (E := Fin n → ℝ) x₀).continuousLinearMapAt ℝ p with hhv
  set sy : (Fin n → ℝ) →L[ℝ] TangentSpace I p := (tTrivW (I := I) (E := Fin n → ℝ) x₀).symmL ℝ p with hsy
  have hvc : ∀ u, hvW x₀ p u = hvC u := fun u => by
    rw [hhv, Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hp]
  have hcur : ∀ u : TangentSpace I p, cov.curvatureAt p u Y Z =
      sy (RhatFstW cov x₀ p (hvW x₀ p Y) (hvW x₀ p Z) (hvC u)) := fun u => by
    have h := hv_curvatureAtW cov x₀ hp u Y Z
    have := congrArg sy h
    rw [hsy, symmL_hvW x₀ hp] at this
    rw [this, hvc]; rfl
  set A : TangentSpace I p →ₗ[ℝ] TangentSpace I p :=
    (sy : (Fin n → ℝ) →ₗ[ℝ] _) ∘ₗ (RhatFstW cov x₀ p (hvW x₀ p Y) (hvW x₀ p Z)) ∘ₗ (hvC : _ →ₗ[ℝ] (Fin n → ℝ)) with hA
  have h1 : cov.ricciAt p Y Z = LinearMap.trace ℝ (TangentSpace I p) A := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (tbW p)]
    unfold Connection.ricciAt Matrix.trace
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.toMatrix_apply, Matrix.diag]
    exact congrArg ((tbW p).coord i) (hcur ((tbW p) i))
  rw [h1, hA, LinearMap.trace_comp_comm' ]
  have hid : (hvC : TangentSpace I p →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ (sy : (Fin n → ℝ) →ₗ[ℝ] _) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    show hvC (sy v) = v
    rw [← hvc]; exact hv_symmLW x₀ hp v
  rw [LinearMap.comp_assoc, hid, LinearMap.comp_id]

/-- **The Ricci tensor in a chart is the coordinate Ricci tensor**: `Ric(∂_ν, ∂_ζ) = ricciW (range I) (g.coordMetricW x₀) ζ ν y`. -/
theorem ricciAt_coordW (g : NondegMetric I M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target) (ν ζ : Fin n) :
    cov.ricciAt ((extChartAt I x₀).symm y)
      (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y))
      (coordFieldW (I := I) x₀ ζ ((extChartAt I x₀).symm y)) = ricciW (range I) (g.coordMetricW x₀) ζ ν y := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  have hp' : (extChartAt I x₀).symm y ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet := hp
  rw [ricciAt_eq_traceW cov x₀ hp', hv_coordFieldW x₀ hp', hv_coordFieldW x₀ hp',
    LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin n))]
  unfold ricciW Matrix.trace
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [LinearMap.toMatrix_apply, Matrix.diag, Pi.basisFun_repr, Pi.basisFun_apply]
  rw [← riemann_coord_compW cov x₀ g h hy ρ ν ζ ρ, hv_curvatureAtW cov x₀ hp', hv_coordFieldW x₀ hp',
    hv_coordFieldW x₀ hp', hv_coordFieldW x₀ hp']
  rfl

/-- The components are homogeneous on the chart domain. -/
theorem hv_smul'W (x₀ : M) {p : M} (hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet) (r : ℝ)
    (u : TangentSpace I p) : hvW x₀ p (r • u) = r • hvW x₀ p u :=
  ((tTrivW (I := I) (E := Fin n → ℝ) x₀).linear ℝ hp).map_smul _ _

/-- `RhatFstW` is additive in its second argument. -/
theorem RhatFst_add_midW (p : M) (b b' c : Fin n → ℝ) :
    RhatFstW cov x₀ p (b + b') c = RhatFstW cov x₀ p b c + RhatFstW cov x₀ p b' c :=
  LinearMap.ext fun v => Rhat_add_midW cov x₀ p v b b' c

/-- `RhatFstW` is homogeneous in its second argument. -/
theorem RhatFst_smul_midW (p : M) (r : ℝ) (b c : Fin n → ℝ) :
    RhatFstW cov x₀ p (r • b) c = r • RhatFstW cov x₀ p b c :=
  LinearMap.ext fun v => Rhat_smul_midW cov x₀ p r v b c

/-- `RhatFstW` is additive in its third argument. -/
theorem RhatFst_add_rightW (p : M) (b c c' : Fin n → ℝ) :
    RhatFstW cov x₀ p b (c + c') = RhatFstW cov x₀ p b c + RhatFstW cov x₀ p b c' :=
  LinearMap.ext fun v => Rhat_add_rightW cov x₀ p v b c c'

/-- `RhatFstW` is homogeneous in its third argument. -/
theorem RhatFst_smul_rightW (p : M) (r : ℝ) (b c : Fin n → ℝ) :
    RhatFstW cov x₀ p b (r • c) = r • RhatFstW cov x₀ p b c :=
  LinearMap.ext fun v => Rhat_smul_rightW cov x₀ p r v b c

/-- The Ricci tensor at a point of the chart domain, as a bilinear form. -/
def RicBW {p : M} (hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun Y Z => cov.ricciAt p Y Z)
    (fun Y Y' Z => by
      rw [ricciAt_eq_traceW cov x₀ hp, ricciAt_eq_traceW cov x₀ hp, ricciAt_eq_traceW cov x₀ hp, hv_addW x₀ hp,
        RhatFst_add_midW, map_add])
    (fun r Y Z => by
      rw [ricciAt_eq_traceW cov x₀ hp, ricciAt_eq_traceW cov x₀ hp, hv_smul'W x₀ hp, RhatFst_smul_midW, map_smul])
    (fun Y Z Z' => by
      rw [ricciAt_eq_traceW cov x₀ hp, ricciAt_eq_traceW cov x₀ hp, ricciAt_eq_traceW cov x₀ hp, hv_addW x₀ hp,
        RhatFst_add_rightW, map_add])
    (fun r Y Z => by
      rw [ricciAt_eq_traceW cov x₀ hp, ricciAt_eq_traceW cov x₀ hp, hv_smul'W x₀ hp, RhatFst_smul_rightW, map_smul])

/-- **The scalar curvature of a Levi-Civita connection is the coordinate scalar curvature** in a chart. -/
theorem scalarCurvatureAt_coordW (g : NondegMetric I M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target) :
    cov.scalarCurvatureAt g ((extChartAt I x₀).symm y) =
      scalarCurvatureW (range I) (g.coordMetricW x₀) y := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  have hp' : (extChartAt I x₀).symm y ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet := hp
  set p := (extChartAt I x₀).symm y with hpdef
  have h1 : cov.scalarCurvatureAt g p =
      ∑ i, ∑ j, (gramBW g p (tbW p))⁻¹ i j * RicBW cov x₀ hp' (tbW p i) (tbW p j) := rfl
  rw [h1, ← trace_raiseW g p (RicBW cov x₀ hp') (tbW p), trace_raiseW g p (RicBW cov x₀ hp') (coordBasisW x₀ hp)]
  have hG : gramBW g p (coordBasisW x₀ hp) = g.coordMetricW x₀ y := by
    ext i j
    exact (g.coordMetric_eqW x₀ hy i j).symm
  rw [hG]
  have hsym : ((g.coordMetricW x₀ y)⁻¹).transpose = (g.coordMetricW x₀ y)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, g.coordMetric_transposeW]
  unfold scalarCurvatureW
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
  have e1 : coordBasisW x₀ hp σ = coordFieldW (I := I) x₀ σ p := (coordField_applyW x₀ σ hy).symm
  have e2 : coordBasisW x₀ hp ν = coordFieldW (I := I) x₀ ν p := (coordField_applyW x₀ ν hy).symm
  have hr : RicBW cov x₀ hp' (coordBasisW x₀ hp σ) (coordBasisW x₀ hp ν) = ricciW (range I) (g.coordMetricW x₀) ν σ y := by
    rw [e1, e2]
    exact ricciAt_coordW cov x₀ g h hy σ ν
  have := congrFun (congrFun hsym ν) σ
  simp only [Matrix.transpose_apply] at this
  rw [hr, this]

/-- **The Einstein equations on a manifold are the coordinate Einstein equations in every chart.** -/
theorem satisfiesEinstein_iff_chart_provedW (g : NondegMetric I M)
    (h : cov.IsLeviCivita g) (Λ : ℝ) :
    g.SatisfiesEinstein cov Λ ↔
      ∀ x₀ : M, IsVacuumSolutionW (range I) Λ (g.coordMetricW x₀) (extChartAt I x₀).target := by
  constructor
  · rintro ⟨-, hE⟩ x₀
    refine ⟨g.isCoordMetricW_coordMetric x₀, fun y hy μ ν => ?_⟩
    have hp := symm_mem_chartTriv_baseSetW x₀ hy
    have e := hE _ (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
      (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y))
    have hs : cov.ricciAt ((extChartAt I x₀).symm y)
        (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
        (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y)) = ricciW (range I) (g.coordMetricW x₀) μ ν y := by
      rw [ricciAt_symm_provedW cov g h.1 h.2 _ _ _]
      exact ricciAt_coordW cov x₀ g h hy ν μ
    have hg : g.g ((extChartAt I x₀).symm y)
        (coordFieldW (I := I) x₀ μ ((extChartAt I x₀).symm y))
        (coordFieldW (I := I) x₀ ν ((extChartAt I x₀).symm y)) = g.coordMetricW x₀ y μ ν := by
      rw [coordField_applyW x₀ μ hy, coordField_applyW x₀ ν hy, g.coordMetric_eqW x₀ hy]
    rw [hs, scalarCurvatureAt_coordW cov x₀ g h hy, hg] at e
    unfold einsteinTensorW
    linarith
  · intro hvac
    refine ⟨h, fun p v w => ?_⟩
    set φ := extChartAt I p with hφ
    have hzs : p ∈ φ.source := mem_extChartAt_source p
    have hy : φ p ∈ φ.target := φ.map_source hzs
    have hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) p).baseSet := by
      simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using (mem_chart_source (Fin n → ℝ) p)
    have hvac' := (hvac p).2 (φ p) hy
    have hc : ∀ σ ν : Fin n, cov.ricciAt p (coordBasisW p hp σ) (coordBasisW p hp ν) -
        cov.scalarCurvatureAt g p / 2 * g.g p (coordBasisW p hp σ) (coordBasisW p hp ν) +
        Λ * g.g p (coordBasisW p hp σ) (coordBasisW p hp ν) = 0 := by
      intro σ ν
      have e := hvac' σ ν
      have hr := ricciAt_coordW cov p g h hy σ ν
      have hs := scalarCurvatureAt_coordW cov p g h hy
      have hg := g_coordFieldW g p σ ν hy
      rw [hφ, (extChartAt I p).left_inv hzs] at hr hs hg
      have hr' := ricciAt_coordW cov p g h hy ν σ
      rw [hφ, (extChartAt I p).left_inv hzs] at hr'
      have e1 : ∀ k, coordBasisW p hp k = coordFieldW p k p := fun k =>
        (coordBasis_applyW p hp k).trans (symmL_eq_coordFieldW p hp k)
      rw [e1 σ, e1 ν]
      have hsym := ricciAt_symm_provedW cov g h.1 h.2 p (coordFieldW p σ p) (coordFieldW p ν p)
      rw [hr, hs, hg]
      have hrs : ricciW (range I) (g.coordMetricW p) ν σ (φ p) = ricciW (range I) (g.coordMetricW p) σ ν (φ p) := by
        rw [← hr, hsym, hr']
      unfold einsteinTensorW at e
      linarith
    -- the bilinear form vanishes on the coordinate basis, hence everywhere
    set B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
      RicBW cov p hp - (cov.scalarCurvatureAt g p / 2 - Λ) • (g.g p).toBilinForm with hB
    have hB0 : B = 0 := by
      refine LinearMap.BilinForm.ext_basis (coordBasisW p hp) fun σ ν => ?_
      have := hc σ ν
      simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      show cov.ricciAt p _ _ - (cov.scalarCurvatureAt g p / 2 - Λ) * g.g p _ _ = 0
      linarith
    have := congrArg (fun B' => B' v w) hB0
    simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    show cov.ricciAt p v w - cov.scalarCurvatureAt g p / 2 * g.g p v w + Λ * g.g p v w = 0
    have h2 : (RicBW cov p hp) v w = cov.ricciAt p v w := rfl
    have h3 : ((g.g p).toBilinForm) v w = g.g p v w := rfl
    rw [h2, h3] at this
    linarith

end Lightlike
