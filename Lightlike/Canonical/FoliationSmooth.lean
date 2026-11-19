import Lightlike.Canonical.Foliation
import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The gradient and the unit normal of a time function are smooth

For a manifold modelled on `ℝⁿ` and a smooth function `τ`, the gradient `∇τ = (dτ)♯` is a smooth vector field
(`contMDiffAt_timeGrad`): in the chart at a point its components are `g^{ab} ∂_b τ`, the inverse of the coordinate metric
(`IsCoordMetric.contDiffOn_inv`) applied to the derivatives of `τ` along the coordinate fields
(`contMDiffAt_mvfderiv_cfield`). For a time function, the lapse and the unit normal `n = −N ∇τ` are then smooth
(`smoothNear_unitNormal`), which removes the smoothness hypothesis of `isUnitNormal` and `extrinsicCurvature_symm`
(`isUnitNormal_of_timeFunction`, `extrinsicCurvature_symm_of_timeFunction`).

**Source.** E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, Sec. 3.3.1, eqs. (3.4),
(3.5), p. 41 (the normal is built from the gradient of the smooth scalar field `t`).
-/

open Bundle Manifold Set Filter VectorField Matrix
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (τ : M → ℝ) (q : M)

/-- The derivatives `∂_c τ` of `τ` along the coordinate fields of the chart at `q`, at the point `φ⁻¹ y`. -/
def dTimeCoord (y : Fin n → ℝ) : Fin n → ℝ := fun c =>
  mvfderiv 𝓘(ℝ, Fin n → ℝ) τ ((extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm y)
    (Lightlike.cfield q (Pi.single c 1) ((extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm y))

/-- The components `g^{ab} ∂_b τ` of the gradient in the chart at `q`. -/
def timeGradCoord (y : Fin n → ℝ) : Fin n → ℝ := (g.coordMetric q y)⁻¹ *ᵥ dTimeCoord τ q y

variable {g τ q}

/-- **The gradient in the chart**: on the chart target, `∇τ` at `φ⁻¹ y` is the vector with components
`g^{ab} ∂_b τ`. -/
theorem timeGrad_eq_symmL {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) q).target) :
    timeGrad g τ ((extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm y) =
      (tTriv (E := Fin n → ℝ) q).symmL ℝ ((extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm y) (timeGradCoord g τ q y) := by
  set p := (extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm y with hpdef
  have hp := symm_mem_chartTriv_baseSet q hy
  set B := coordBasis q hp
  set G := g.coordMetric q y
  have hcb : ∀ c, B c = Lightlike.cfield q (Pi.single c 1) p := fun c => coordBasis_apply q hp c
  have hG : ∀ a c, G a c = g.g p (B a) (B c) := fun a c => g.coordMetric_eq q hy a c
  have hGt : Gᵀ = G := g.coordMetric_transpose q y
  have hGu : IsUnit G.det := g.coordMetric_isUnit_det q hy
  apply Lightlike.eq_of_g_eq g p
  intro u
  have hL : (g.g p (timeGrad g τ p)).toLinearMap =
      (g.g p ((tTriv (E := Fin n → ℝ) q).symmL ℝ p (timeGradCoord g τ q y))).toLinearMap := by
    refine B.ext fun c => ?_
    simp only [ContinuousLinearMap.coe_coe]
    rw [g_timeGrad]
    -- the right side: expand the components in the standard basis
    have hF : timeGradCoord g τ q y = ∑ a, timeGradCoord g τ q y a • (Pi.single a 1 : Fin n → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hF, map_sum]
    simp only [map_smul]
    have hcf : ∀ a, (tTriv (E := Fin n → ℝ) q).symmL ℝ p (Pi.single a 1) = B a := fun a => by
      rw [hcb]; rfl
    simp only [hcf, map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, ← hG]
    -- `Σ_a (G⁻¹ b)_a G_ac = b_c`
    have hm : ∑ a, timeGradCoord g τ q y a * G a c = (G *ᵥ timeGradCoord g τ q y) c := by
      simp only [mulVec, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show G a c = Gᵀ c a from rfl, hGt, mul_comm]
    rw [hm]
    unfold timeGradCoord
    rw [mulVec_mulVec, mul_nonsing_inv G hGu, one_mulVec]
    simp only [dTimeCoord, hcb]
    rfl
  exact congrArg (fun L : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] ℝ => L u) hL

/-- The chart components of the gradient field. -/
theorem hat_timeGrad {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) q).target) :
    hat q (timeGrad g τ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm y) = timeGradCoord g τ q y := by
  have hp := symm_mem_chartTriv_baseSet q hy
  show hv q _ (timeGrad g τ _) = _
  rw [timeGrad_eq_symmL hy, hv_symmL q hp]

variable (g) in
/-- **The gradient of a smooth function is a smooth vector field.** -/
theorem contMDiffAt_timeGrad (hτ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ τ) (q : M) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun p : M => (⟨p, timeGrad g τ p⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q := by
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) q with hφ
  have hq : q ∈ (tTriv (E := Fin n → ℝ) q).baseSet := mem_baseSet_trivializationAt _ _ q
  have hqs : q ∈ φ.source := mem_extChartAt_source q
  have hqt : φ q ∈ φ.target := mem_extChartAt_target q
  have htgt : φ.target ∈ 𝓝 (φ q) := (isOpen_extChartAt_target q).mem_nhds hqt
  rw [(tTriv (E := Fin n → ℝ) q).contMDiffAt_section_iff hq]
  -- smoothness of the components as a function of the chart coordinate
  have hsymm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ φ.symm (φ q) := by
    have := contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) q hqt
    simpa [hφ, contMDiffWithinAt_univ] using this
  have hb : ∀ c, ContDiffAt ℝ ∞ (fun y => dTimeCoord τ q y c) (φ q) := by
    intro c
    have h1 := contMDiffAt_mvfderiv_cfield q τ (Eventually.of_forall fun y => hτ.contMDiffAt)
      (Pi.single c 1)
    have h2 := h1.comp_of_eq hsymm (φ.left_inv hqs)
    exact contMDiffAt_iff_contDiffAt.1 h2
  have hinv : ∀ a c, ContDiffAt ℝ ∞ (fun y => (g.coordMetric q y)⁻¹ a c) (φ q) := fun a c =>
    ((g.isCoordMetric_coordMetric q).contDiffOn_inv a c).contDiffAt htgt
  have hF : ContDiffAt ℝ ∞ (timeGradCoord g τ q) (φ q) := by
    refine contDiffAt_pi.2 fun a => ?_
    simp only [timeGradCoord, mulVec, dotProduct]
    exact ContDiffAt.sum fun c _ => (hinv a c).mul (hb c)
  have hFm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (timeGradCoord g τ q ∘ φ) q :=
    (contMDiffAt_iff_contDiffAt.2 hF).comp q contMDiffAt_extChartAt
  refine hFm.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) q).mem_nhds hqs] with p hp
  have hy := φ.map_source hp
  have e := hat_timeGrad (g := g) (τ := τ) hy
  rw [φ.left_inv hp] at e
  show hat q (timeGrad g τ) p = timeGradCoord g τ q (φ p)
  exact e

/-- `g(∇τ, ∇τ)` is a smooth function. -/
theorem contMDiffAt_g_timeGrad (hτ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ τ) (q : M) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (fun p => g.g p (timeGrad g τ p) (timeGrad g τ p)) q :=
  Lightlike.contMDiffAt_gpair g (contMDiffAt_timeGrad g hτ q) (contMDiffAt_timeGrad g hτ q)

/-- **The unit normal of a time function is smooth.** -/
theorem contMDiffAt_unitNormal (h : IsTimeFunction g τ) (q : M) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun p : M => (⟨p, unitNormal g τ p⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q := by
  have hG := contMDiffAt_g_timeGrad (g := g) h.smooth q
  have hpos : 0 < -(g.g q (timeGrad g τ q) (timeGrad g τ q)) := neg_pos.2 (h.timelike q)
  have hsq : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun p => Real.sqrt (-(g.g p (timeGrad g τ p) (timeGrad g τ p)))) q := by
    have hneg := hG.neg
    exact (Real.contDiffAt_sqrt hpos.ne').contMDiffAt.comp q hneg
  have hN : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (fun p => -(lapse g τ p)) q := by
    have := hsq.inv₀ (Real.sqrt_pos.2 hpos).ne'
    exact this.neg
  exact hN.smul_section (contMDiffAt_timeGrad g h.smooth q)

/-- The unit normal of a time function is smooth near every point. -/
theorem smoothNear_unitNormal (h : IsTimeFunction g τ) (x₀ : M) : SmoothNear (unitNormal g τ) x₀ :=
  Eventually.of_forall fun q => contMDiffAt_unitNormal h q

variable [T2Space M]

/-- **The unit normal of a time function is a unit normal of its leaves**, without a smoothness hypothesis. -/
theorem isUnitNormal_of_timeFunction (h : IsTimeFunction g τ) (x₀ : M) :
    Hypersurface.IsUnitNormal g τ (unitNormal g τ) (-1) x₀ :=
  isUnitNormal h (smoothNear_unitNormal h x₀)

/-- **The extrinsic curvature of the leaves of a time function is symmetric** for the Levi-Civita connection. -/
theorem extrinsicCurvature_symm_of_timeFunction (h : IsTimeFunction g τ)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} (hc : cov.IsLeviCivita g) (x₀ : M)
    (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x₀) :
    extrinsicCurvature g τ cov x₀ u v = extrinsicCurvature g τ cov x₀ v u :=
  extrinsicCurvature_symm h hc (smoothNear_unitNormal h x₀) u v

end Lightlike.Canonical
