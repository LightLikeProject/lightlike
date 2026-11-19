import Lightlike.Spacetime.CurvatureSymmetries
import Lightlike.Spacetime.ChartConnection
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.GR.Einstein

/-!
# The curvature of a Levi-Civita connection in a chart agrees with the coordinate curvature

For a Levi-Civita connection `cov` of a Lorentzian metric `g` on a Hausdorff manifold modelled on `ℝⁿ`, in the
chart at `x₀`, at the point `φ⁻¹ y`:

* `riemann_coord_comp`: the components of `R(∂_μ, ∂_ν) ∂_σ` are the coordinate Riemann tensor
  `riemann (g.coordMetric x₀)` of `Curvature.lean` (from `curvature_hat`, `gamHat_coord` and
  `mvfderiv_gamHat_coord`: the Christoffel tensor of the connection against the trivialization is the Christoffel
  symbol of the coordinate metric);
* `ricciAt_coord`: the intrinsic Ricci tensor (trace over a basis of the tangent space) is the coordinate
  `ricci`;
* `scalarCurvatureAt_coord`: the intrinsic scalar curvature is the coordinate `scalarCurvature` (the trace of the
  Ricci tensor with `g` does not depend on the basis: `trace_raise`);
* `satisfiesEinstein_iff_chart_proved`: the Einstein equations of `Connection.lean` hold iff the coordinate
  vacuum equations hold in every chart.

**Differences from the tasks.** `scalarCurvatureAt_coord` is the statement of the task `T-GE1-P5` and
`satisfiesEinstein_iff_chart_proved` that of `T-GE1-P6`, each with the added hypothesis
`[IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]` (needed by `curvatureAt_apply_proved`); the tasks stay open. The comparison
of the definitions with Carroll, *Spacetime and Geometry*, ch. 3, and Wald, *General Relativity*, is pending: the
sources were not read at the cited locations.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {n : ℕ} (g : NondegMetric 𝓘(ℝ, E) M) (x : M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of `g` in a basis. -/
def gramB (b : Module.Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) : Matrix ι ι ℝ :=
  Matrix.of fun i j => g.g x (b i) (b j)

/-- The Gram matrix of a Lorentzian metric in a basis is invertible. -/
theorem gramB_isUnit (b : Module.Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) : IsUnit (gramB g x b).det := by
  have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    (g.bilinForm_nondegenerate x)
  have hmat : LinearMap.BilinForm.toMatrix b (g.g x).toBilinForm = gramB g x b := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [← hmat]
  exact h.isUnit

/-- The coordinates of a tangent vector in any basis are `Σ g^{ij} g(u, e_j)`. -/
theorem coord_eq_sum_basis (b : Module.Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) (u : TangentSpace 𝓘(ℝ, E) x) (i : ι) :
    b.coord i u = ∑ j, (gramB g x b)⁻¹ i j * g.g x u (b j) := by
  have hsym : (gramB g x b).transpose = gramB g x b := by
    ext i j; exact g.symm x _ _
  have hG := Matrix.nonsing_inv_mul _ (gramB_isUnit g x b)
  have hexp : ∀ j, g.g x u (b j) = ∑ k, b.coord k u * gramB g x b k j := by
    intro j
    conv_lhs => rw [← b.sum_repr u]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [gramB, Module.Basis.coord_apply]
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 := congrFun (congrFun hG i)
  simp only [Matrix.mul_apply, Matrix.one_apply] at h2
  have : ∀ k, ∑ j, (gramB g x b)⁻¹ i j * (b.coord k u * gramB g x b k j) = b.coord k u * (if i = k then 1 else 0) := by
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
def raise (B : TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] ℝ) :
    TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x where
  toFun u := sharp g x (LinearMap.toContinuousLinearMap (B u))
  map_add' u v := by
    rw [map_add, ← sharp_add]; congr 1
  map_smul' c u := by
    rw [map_smul, ← sharp_smul]; congr 1

/-- `g(T u, w) = B(u, w)`. -/
theorem g_raise (B : TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] ℝ) (u w : TangentSpace 𝓘(ℝ, E) x) :
    g.g x (raise g x B u) w = B u w :=
  g_sharp g x _ w

/-- The trace of a bilinear form with respect to `g` does not depend on the basis. -/
theorem trace_raise (B : TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) x →ₗ[ℝ] ℝ)
    (b : Module.Basis ι ℝ (TangentSpace 𝓘(ℝ, E) x)) :
    LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, E) x) (raise g x B) =
      ∑ i, ∑ j, (gramB g x b)⁻¹ i j * B (b i) (b j) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.toMatrix_apply, Matrix.diag]
  have := coord_eq_sum_basis g x b (raise g x B (b i)) i
  rw [Module.Basis.coord_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g_raise]
end General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [LocallySmoothConnection cov] (x₀ : M)

/-- The components of the curvature at any point of the chart domain. -/
theorem hv_curvatureAt {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet)
    (X₀ Y₀ Z₀ : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    hv x₀ p (cov.curvatureAt p X₀ Y₀ Z₀) = Rhat cov x₀ p (hv x₀ p X₀) (hv x₀ p Y₀) (hv x₀ p Z₀) := by
  have h2 := curvature_hat cov x₀ hp (eventually_extend p X₀) (eventually_extend p Y₀)
    (eventually_extend p Z₀)
  simp only [FiberBundle.extend_apply_self] at h2
  unfold Connection.curvatureAt
  dsimp only
  simp only [FiberBundle.extend_apply_self]
  exact h2

omit [LocallySmoothConnection cov] in
/-- The Christoffel tensor in the components of the trivialization is the Christoffel symbol of the coordinate
metric, for the Levi-Civita connection. -/
theorem gamHat_coord (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
    {z : M} (hz : z ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (i j : Fin n) :
    gamHat cov x₀ z (Pi.single j 1) (Pi.single i 1) =
      ∑ k, christoffel (g.coordMetric x₀) k i j (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ z) • (Pi.single k 1 : Fin n → ℝ) := by
  have hz' : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ z ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source (by
      rw [extChartAt_source]; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hz)
  have hzs : z ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
    rw [extChartAt_source]; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hz
  have hcf : ∀ q ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet, ∀ k : Fin n,
      coordField x₀ k q = cfield x₀ (Pi.single k 1) q := by
    intro q hq k
    unfold coordField cfield
    rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTriv n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := k) hq]
    exact (show _ = coordBasis x₀ hq k from rfl).trans (coordBasis_apply x₀ hq k)
  have hev : (cfield x₀ (Pi.single j 1 : Fin n → ℝ)) =ᶠ[nhds z] coordField x₀ j := by
    filter_upwards [(tTriv (E := Fin n → ℝ) x₀).open_baseSet.mem_nhds hz] with q hq
    exact (hcf q hq j).symm
  have hc1 : cov (cfield x₀ (Pi.single j 1 : Fin n → ℝ)) z = cov (coordField x₀ j) z :=
    (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq
      ((contMDiffAt_cfield x₀ _ hz).mdifferentiableAt (by simp)) (mdiffAt_coordField x₀ j hz)
      Filter.univ_mem hev
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hc2 : cov (coordField x₀ j) z = leviCivita g (coordField x₀ j) z :=
    leviCivita_unique g h hLC (mdiffAt_coordField x₀ j hz)
  have hcf2 : cfield x₀ (Pi.single i 1 : Fin n → ℝ) z = coordField x₀ i z := (hcf z hz i).symm
  rw [gamHat_eq cov x₀ _ _ hz, hc1, hc2, hcf2]
  have key := leviCivita_coordField g x₀ hz' i j
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hzs] at key
  rw [key]
  have hvc : ∀ u : TangentSpace 𝓘(ℝ, Fin n → ℝ) z,
      hv x₀ z u = (tTriv (E := Fin n → ℝ) x₀).continuousLinearMapAt ℝ z u := fun u => by
    rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hz]
  show hv x₀ z _ = _
  rw [hvc, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, ← hvc, hcf z hz k]
  exact congrArg (fun v => _ • v) (hv_symmL x₀ hz (Pi.single k 1))

/-- The derivative of `Γ̂` evaluated on two vectors is the derivative of the evaluation. -/
theorem mvfderiv_gamHat_apply {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet)
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (a b : Fin n → ℝ) :
    (mvfderiv 𝓘(ℝ, Fin n → ℝ) (gamHat cov x₀) p u) a b =
      mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun z => gamHat cov x₀ z a b) p u := by
  have hΓ := mdiffAt_gamHat cov x₀ hp
  have h1 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (fun z => gamHat cov x₀ z a) p :=
    hΓ.clm_apply mdifferentiableAt_const
  have e1 := mvfderiv_clm_apply (E := Fin n → ℝ) (gamHat cov x₀) (fun _ : M => a) p hΓ mdifferentiableAt_const u
  have e2 := mvfderiv_clm_apply (E := Fin n → ℝ) (fun z => gamHat cov x₀ z a) (fun _ : M => b) p h1
    mdifferentiableAt_const u
  rw [mvfderiv_const] at e1 e2
  simp only [zero_apply, map_zero, add_zero] at e1 e2
  rw [e2, e1]

/-- The derivative of `Γ̂` along `∂_μ` in the chart is `Σ_k ∂_μ Γᵏ_{νσ} e_k`. -/
theorem mvfderiv_gamHat_coord (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (μ ν σ : Fin n) :
    (mvfderiv 𝓘(ℝ, Fin n → ℝ) (gamHat cov x₀) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))) (Pi.single σ 1) (Pi.single ν 1) =
      ∑ k, pd μ (fun y' => christoffel (g.coordMetric x₀) k ν σ y') y • (Pi.single k 1 : Fin n → ℝ) := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hp' : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := hp
  rw [mvfderiv_gamHat_apply cov x₀ hp']
  set H : (Fin n → ℝ) → (Fin n → ℝ) := fun y' => ∑ k, christoffel (g.coordMetric x₀) k ν σ y' • (Pi.single k 1 : Fin n → ℝ) with hH
  have hev : (fun z => gamHat cov x₀ z (Pi.single σ 1) (Pi.single ν 1)) =ᶠ[nhds ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)]
      H ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) := by
    filter_upwards [(tTriv (E := Fin n → ℝ) x₀).open_baseSet.mem_nhds hp'] with z hz
    exact gamHat_coord cov x₀ g h hz ν σ
  have hgc := g.isCoordMetric_coordMetric x₀
  have hd : ∀ k : Fin n, DifferentiableAt ℝ (fun y' => christoffel (g.coordMetric x₀) k ν σ y') y := fun k =>
    differentiableAt_of_contDiffOn (hgc.contDiffOn_christoffel k ν σ) hgc.isOpen hy
  have hHd : DifferentiableAt ℝ H y := by
    rw [hH]
    exact DifferentiableAt.fun_sum fun k _ => (hd k).smul_const _
  have hφd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀)
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) :=
    mdifferentiableAt_extChartAt (by simpa using hp')
  have hHm : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) H
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) := by
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy]
    exact mdifferentiableAt_iff_differentiableAt.2 hHd
  rw [mvfderiv_congr hev, mvfderiv_comp _ hHm hφd]
  simp only [ContinuousLinearMap.comp_apply]
  rw [mfderiv_chart_coordField x₀ μ hy, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy]
  rw [mvfderiv_eq_fderiv]
  show fderiv ℝ H y (Pi.single μ 1) = _
  rw [hH, fderiv_fun_sum (fun k _ => (hd k).smul_const _)]
  simp [pd, fderiv_smul_const (hd _)]

/-- The components of the coordinate field `∂_k` are `e_k`. -/
theorem hv_coordField (x₀ : M) {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (k : Fin n) :
    hv x₀ p (coordField x₀ k p) = Pi.single k 1 := by
  have : coordField x₀ k p = cfield x₀ (Pi.single k 1) p := by
    unfold coordField cfield
    rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTriv n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := k) hp]
    exact (show _ = coordBasis x₀ hp k from rfl).trans (coordBasis_apply x₀ hp k)
  rw [this]
  exact hv_symmL x₀ hp _

/-- `e⁻¹ (e_k)` is the coordinate field `∂_k` on the chart domain. -/
theorem symmL_eq_coordField (x₀ : M) {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (k : Fin n) :
    (tTriv (E := Fin n → ℝ) x₀).symmL ℝ p (Pi.single k 1) = coordField x₀ k p := by
  unfold coordField
  rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTriv n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := k) hp]
  exact ((show _ = coordBasis x₀ hp k from rfl).trans (coordBasis_apply x₀ hp k)).symm

/-- **The curvature in a chart is the coordinate Riemann tensor**: for the Levi-Civita connection, the `ρ`-component of the components of `R(∂_μ, ∂_ν) ∂_σ` at `φ⁻¹ y` is `riemann (g.coordMetric x₀) ρ σ μ ν y`. -/
theorem riemann_coord_comp (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (μ ν σ ρ : Fin n) :
    (hv x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      (cov.curvatureAt ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
        (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
        (coordField x₀ σ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)))) ρ =
      riemann (g.coordMetric x₀) ρ σ μ ν y := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hp' : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := hp
  rw [hv_curvatureAt cov x₀ hp', hv_coordField x₀ hp', hv_coordField x₀ hp', hv_coordField x₀ hp']
  unfold Rhat
  rw [symmL_eq_coordField x₀ hp', symmL_eq_coordField x₀ hp',
    mvfderiv_gamHat_coord cov x₀ g h hy μ ν σ, mvfderiv_gamHat_coord cov x₀ g h hy ν μ σ,
    gamHat_coord cov x₀ g h hp' ν σ, gamHat_coord cov x₀ g h hp' μ σ,
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy]
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  simp only [gamHat_coord cov x₀ g h hp', (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy]
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  simp only [riemann, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [mul_comm]
  ring

/-- `Rhat` is additive in its first argument. -/
theorem Rhat_add_left (p : M) (a a' b c : Fin n → ℝ) :
    Rhat cov x₀ p (a + a') b c = Rhat cov x₀ p a b c + Rhat cov x₀ p a' b c := by
  unfold Rhat
  simp only [map_add, add_apply]
  abel

/-- `Rhat` is homogeneous in its first argument. -/
theorem Rhat_smul_left (p : M) (r : ℝ) (a b c : Fin n → ℝ) :
    Rhat cov x₀ p (r • a) b c = r • Rhat cov x₀ p a b c := by
  unfold Rhat
  simp only [map_smul, smul_apply]
  module

/-- `Rhat` is additive in its second argument. -/
theorem Rhat_add_mid (p : M) (a b b' c : Fin n → ℝ) :
    Rhat cov x₀ p a (b + b') c = Rhat cov x₀ p a b c + Rhat cov x₀ p a b' c := by
  unfold Rhat
  simp only [map_add, add_apply]
  abel

/-- `Rhat` is homogeneous in its second argument. -/
theorem Rhat_smul_mid (p : M) (r : ℝ) (a b c : Fin n → ℝ) :
    Rhat cov x₀ p a (r • b) c = r • Rhat cov x₀ p a b c := by
  unfold Rhat
  simp only [map_smul, smul_apply]
  module

/-- `Rhat` is additive in its third argument. -/
theorem Rhat_add_right (p : M) (a b c c' : Fin n → ℝ) :
    Rhat cov x₀ p a b (c + c') = Rhat cov x₀ p a b c + Rhat cov x₀ p a b c' := by
  unfold Rhat
  simp only [map_add, add_apply]
  abel

/-- `Rhat` is homogeneous in its third argument. -/
theorem Rhat_smul_right (p : M) (r : ℝ) (a b c : Fin n → ℝ) :
    Rhat cov x₀ p a b (r • c) = r • Rhat cov x₀ p a b c := by
  unfold Rhat
  simp only [map_smul, smul_apply]
  module

/-- The curvature as a linear map in its first slot, in components. -/
def RhatFst (p : M) (b c : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v := Rhat cov x₀ p v b c
  map_add' a a' := Rhat_add_left cov x₀ p a a' b c
  map_smul' r a := Rhat_smul_left cov x₀ p r a b c

/-- The Ricci tensor is the trace of the curvature in components. -/
theorem ricciAt_eq_trace {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet)
    (Y Z : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    cov.ricciAt p Y Z = LinearMap.trace ℝ (Fin n → ℝ) (RhatFst cov x₀ p (hv x₀ p Y) (hv x₀ p Z)) := by
  set hvC : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →L[ℝ] (Fin n → ℝ) := (tTriv (E := Fin n → ℝ) x₀).continuousLinearMapAt ℝ p with hhv
  set sy : (Fin n → ℝ) →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p := (tTriv (E := Fin n → ℝ) x₀).symmL ℝ p with hsy
  have hvc : ∀ u, hv x₀ p u = hvC u := fun u => by
    rw [hhv, Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hp]
  have hcur : ∀ u : TangentSpace 𝓘(ℝ, Fin n → ℝ) p, cov.curvatureAt p u Y Z =
      sy (RhatFst cov x₀ p (hv x₀ p Y) (hv x₀ p Z) (hvC u)) := fun u => by
    have h := hv_curvatureAt cov x₀ hp u Y Z
    have := congrArg sy h
    rw [hsy, symmL_hv x₀ hp] at this
    rw [this, hvc]; rfl
  set A : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p :=
    (sy : (Fin n → ℝ) →ₗ[ℝ] _) ∘ₗ (RhatFst cov x₀ p (hv x₀ p Y) (hv x₀ p Z)) ∘ₗ (hvC : _ →ₗ[ℝ] (Fin n → ℝ)) with hA
  have h1 : cov.ricciAt p Y Z = LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) p) A := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (tb p)]
    unfold Connection.ricciAt Matrix.trace
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.toMatrix_apply, Matrix.diag]
    exact congrArg ((tb p).coord i) (hcur ((tb p) i))
  rw [h1, hA, LinearMap.trace_comp_comm' ]
  have hid : (hvC : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ (sy : (Fin n → ℝ) →ₗ[ℝ] _) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    show hvC (sy v) = v
    rw [← hvc]; exact hv_symmL x₀ hp v
  rw [LinearMap.comp_assoc, hid, LinearMap.comp_id]

/-- **The Ricci tensor in a chart is the coordinate Ricci tensor**: `Ric(∂_ν, ∂_ζ) = ricci (g.coordMetric x₀) ζ ν y`. -/
theorem ricciAt_coord (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (ν ζ : Fin n) :
    cov.ricciAt ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
      (coordField x₀ ζ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = ricci (g.coordMetric x₀) ζ ν y := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hp' : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := hp
  rw [ricciAt_eq_trace cov x₀ hp', hv_coordField x₀ hp', hv_coordField x₀ hp',
    LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin n))]
  unfold ricci Matrix.trace
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [LinearMap.toMatrix_apply, Matrix.diag, Pi.basisFun_repr, Pi.basisFun_apply]
  rw [← riemann_coord_comp cov x₀ g h hy ρ ν ζ ρ, hv_curvatureAt cov x₀ hp', hv_coordField x₀ hp',
    hv_coordField x₀ hp', hv_coordField x₀ hp']
  rfl

/-- The components are homogeneous on the chart domain. -/
theorem hv_smul' (x₀ : M) {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (r : ℝ)
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) : hv x₀ p (r • u) = r • hv x₀ p u :=
  ((tTriv (E := Fin n → ℝ) x₀).linear ℝ hp).map_smul _ _

/-- `RhatFst` is additive in its second argument. -/
theorem RhatFst_add_mid (p : M) (b b' c : Fin n → ℝ) :
    RhatFst cov x₀ p (b + b') c = RhatFst cov x₀ p b c + RhatFst cov x₀ p b' c :=
  LinearMap.ext fun v => Rhat_add_mid cov x₀ p v b b' c

/-- `RhatFst` is homogeneous in its second argument. -/
theorem RhatFst_smul_mid (p : M) (r : ℝ) (b c : Fin n → ℝ) :
    RhatFst cov x₀ p (r • b) c = r • RhatFst cov x₀ p b c :=
  LinearMap.ext fun v => Rhat_smul_mid cov x₀ p r v b c

/-- `RhatFst` is additive in its third argument. -/
theorem RhatFst_add_right (p : M) (b c c' : Fin n → ℝ) :
    RhatFst cov x₀ p b (c + c') = RhatFst cov x₀ p b c + RhatFst cov x₀ p b c' :=
  LinearMap.ext fun v => Rhat_add_right cov x₀ p v b c c'

/-- `RhatFst` is homogeneous in its third argument. -/
theorem RhatFst_smul_right (p : M) (r : ℝ) (b c : Fin n → ℝ) :
    RhatFst cov x₀ p b (r • c) = r • RhatFst cov x₀ p b c :=
  LinearMap.ext fun v => Rhat_smul_right cov x₀ p r v b c

/-- The Ricci tensor at a point of the chart domain, as a bilinear form. -/
def RicB {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) :
    TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun Y Z => cov.ricciAt p Y Z)
    (fun Y Y' Z => by
      rw [ricciAt_eq_trace cov x₀ hp, ricciAt_eq_trace cov x₀ hp, ricciAt_eq_trace cov x₀ hp, hv_add x₀ hp,
        RhatFst_add_mid, map_add])
    (fun r Y Z => by
      rw [ricciAt_eq_trace cov x₀ hp, ricciAt_eq_trace cov x₀ hp, hv_smul' x₀ hp, RhatFst_smul_mid, map_smul])
    (fun Y Z Z' => by
      rw [ricciAt_eq_trace cov x₀ hp, ricciAt_eq_trace cov x₀ hp, ricciAt_eq_trace cov x₀ hp, hv_add x₀ hp,
        RhatFst_add_right, map_add])
    (fun r Y Z => by
      rw [ricciAt_eq_trace cov x₀ hp, ricciAt_eq_trace cov x₀ hp, hv_smul' x₀ hp, RhatFst_smul_right, map_smul])

/-- **The scalar curvature of a Levi-Civita connection is the coordinate scalar curvature** in a chart. -/
theorem scalarCurvatureAt_coord (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : cov.IsLeviCivita g)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    cov.scalarCurvatureAt g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      scalarCurvature (g.coordMetric x₀) y := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hp' : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := hp
  set p := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y with hpdef
  have h1 : cov.scalarCurvatureAt g p =
      ∑ i, ∑ j, (gramB g p (tb p))⁻¹ i j * RicB cov x₀ hp' (tb p i) (tb p j) := rfl
  rw [h1, ← trace_raise g p (RicB cov x₀ hp') (tb p), trace_raise g p (RicB cov x₀ hp') (coordBasis x₀ hp)]
  have hG : gramB g p (coordBasis x₀ hp) = g.coordMetric x₀ y := by
    ext i j
    exact (g.coordMetric_eq x₀ hy i j).symm
  rw [hG]
  have hsym : ((g.coordMetric x₀ y)⁻¹).transpose = (g.coordMetric x₀ y)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, g.coordMetric_transpose]
  unfold scalarCurvature
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
  have e1 : coordBasis x₀ hp σ = coordField x₀ σ p := (coordField_apply x₀ σ hy).symm
  have e2 : coordBasis x₀ hp ν = coordField x₀ ν p := (coordField_apply x₀ ν hy).symm
  have hr : RicB cov x₀ hp' (coordBasis x₀ hp σ) (coordBasis x₀ hp ν) = ricci (g.coordMetric x₀) ν σ y := by
    rw [e1, e2]
    exact ricciAt_coord cov x₀ g h hy σ ν
  have := congrFun (congrFun hsym ν) σ
  simp only [Matrix.transpose_apply] at this
  rw [hr, this]

/-- **The Einstein equations on a manifold are the coordinate Einstein equations in every chart.** -/
theorem satisfiesEinstein_iff_chart_proved (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : cov.IsLeviCivita g) (Λ : ℝ) :
    g.SatisfiesEinstein cov Λ ↔
      ∀ x₀ : M, IsVacuumSolution Λ (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  constructor
  · rintro ⟨-, hE⟩ x₀
    refine ⟨g.isCoordMetric_coordMetric x₀, fun y hy μ ν => ?_⟩
    have hp := symm_mem_chartTriv_baseSet x₀ hy
    have e := hE _ (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
      (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
    have hs : cov.ricciAt ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
        (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = ricci (g.coordMetric x₀) μ ν y := by
      rw [ricciAt_symm_proved cov g h.1 h.2 _ _ _]
      exact ricciAt_coord cov x₀ g h hy ν μ
    have hg : g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ μ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
        (coordField x₀ ν ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = g.coordMetric x₀ y μ ν := by
      rw [coordField_apply x₀ μ hy, coordField_apply x₀ ν hy, g.coordMetric_eq x₀ hy]
    rw [hs, scalarCurvatureAt_coord cov x₀ g h hy, hg] at e
    unfold einsteinTensor
    linarith
  · intro hvac
    refine ⟨h, fun p v w => ?_⟩
    set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) p with hφ
    have hzs : p ∈ φ.source := mem_extChartAt_source p
    have hy : φ p ∈ φ.target := φ.map_source hzs
    have hp : p ∈ (tTriv (E := Fin n → ℝ) p).baseSet := by
      simpa [tTriv, TangentBundle.trivializationAt_baseSet] using (mem_chart_source (Fin n → ℝ) p)
    have hvac' := (hvac p).2 (φ p) hy
    have hc : ∀ σ ν : Fin n, cov.ricciAt p (coordBasis p hp σ) (coordBasis p hp ν) -
        cov.scalarCurvatureAt g p / 2 * g.g p (coordBasis p hp σ) (coordBasis p hp ν) +
        Λ * g.g p (coordBasis p hp σ) (coordBasis p hp ν) = 0 := by
      intro σ ν
      have e := hvac' σ ν
      have hr := ricciAt_coord cov p g h hy σ ν
      have hs := scalarCurvatureAt_coord cov p g h hy
      have hg := g_coordField g p σ ν hy
      rw [hφ, (extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hzs] at hr hs hg
      have hr' := ricciAt_coord cov p g h hy ν σ
      rw [hφ, (extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hzs] at hr'
      have e1 : ∀ k, coordBasis p hp k = coordField p k p := fun k =>
        (coordBasis_apply p hp k).trans (symmL_eq_coordField p hp k)
      rw [e1 σ, e1 ν]
      have hsym := ricciAt_symm_proved cov g h.1 h.2 p (coordField p σ p) (coordField p ν p)
      rw [hr, hs, hg]
      have hrs : ricci (g.coordMetric p) ν σ (φ p) = ricci (g.coordMetric p) σ ν (φ p) := by
        rw [← hr, hsym, hr']
      unfold einsteinTensor at e
      linarith
    -- the bilinear form vanishes on the coordinate basis, hence everywhere
    set B : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] ℝ :=
      RicB cov p hp - (cov.scalarCurvatureAt g p / 2 - Λ) • (g.g p).toBilinForm with hB
    have hB0 : B = 0 := by
      refine LinearMap.BilinForm.ext_basis (coordBasis p hp) fun σ ν => ?_
      have := hc σ ν
      simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
      show cov.ricciAt p _ _ - (cov.scalarCurvatureAt g p / 2 - Λ) * g.g p _ _ = 0
      linarith
    have := congrArg (fun B' => B' v w) hB0
    simp only [hB, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
    show cov.ricciAt p v w - cov.scalarCurvatureAt g p / 2 * g.g p v w + Λ * g.g p v w = 0
    have h2 : (RicB cov p hp) v w = cov.ricciAt p v w := rfl
    have h3 : ((g.g p).toBilinForm) v w = g.g p v w := rfl
    rw [h2, h3] at this
    linarith
end Lightlike
