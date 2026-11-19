import Lightlike.Spacetime.NullHypersurfaceCoord
import Lightlike.Spacetime.RaychaudhuriManifold
import Lightlike.Spacetime.LeviCivitaSmooth

/-!
# Null hypersurfaces are ruled by null geodesics (G1-009)

For a smooth function `u` on a manifold with a metric `g`, the gradient `ℓ = ♯du` (`gradField`) has, in every chart, the
components `gradVec` of the coordinate metric and `u ∘ φ⁻¹` (`hv_gradField`). If the level sets of `u` are null near a
point (`g(ℓ, ℓ) = 0` there), `ℓ` is geodesic there for the Levi-Civita connection: `∇_ℓ ℓ = 0`
(`gradField_geodesic_of_null`), from the coordinate identity `∇_ℓ ℓ = ½ grad (ℓ · ℓ)`; with any normalization
`ℓ' = f ℓ`, `∇_{ℓ'} ℓ' = ⟨df, ℓ⟩ ℓ'` (`smul_gradField_of_null`, the source's (2.21)–(2.22) for `f = e^ρ`).

## References

* E. Gourgoulhon, J. L. Jaramillo, *A 3+1 perspective on null hypersurfaces and isolated horizons*,
  arXiv:gr-qc/0503113, section 2.5, eqs. (2.19)–(2.21), pp. 21–22.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter Matrix
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

section Gradient

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- The gradient `ℓ = ♯du` of a function `u`. -/
def gradField (u : M → ℝ) (p : M) : TangentSpace 𝓘(ℝ, Fin n → ℝ) p :=
  sharp g p (mvfderiv 𝓘(ℝ, Fin n → ℝ) u p)

/-- **The gradient in a chart**: its components are `gᵃᵇ ∂_b (u ∘ φ⁻¹)` for the coordinate metric. -/
theorem hv_gradField (x₀ : M) {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {u : M → ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) u p) :
    hv x₀ p (gradField g u p) =
      gradVec (g.coordMetric x₀) (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  set y := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p with hy
  set ũ := u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm with hũ
  set G := g.coordMetric x₀ y with hG
  set L := mvfderiv 𝓘(ℝ, Fin n → ℝ) u p with hLdef
  have hpb := mem_baseSet_of_mem_source x₀ hp
  have hyt : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp
  have hL : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p, L v = ∑ k, hv x₀ p v k * pd k ũ y := fun v => by
    rw [hLdef, mvfderiv_eq_chart₀ x₀ u hp hu v, mfderiv_extChartAt_apply' x₀ hp v]
    conv_lhs => rw [show hv x₀ p v = ∑ k, hv x₀ p v k • (Pi.single k 1 : Fin n → ℝ) by
      ext i; simp [Pi.single_apply]]
    simp only [map_sum, map_smul, smul_eq_mul, pd]
    rfl
  have hGs : Gᵀ = G := g.coordMetric_transpose x₀ y
  have hGw : G *ᵥ hv x₀ p (gradField g u p) = fun k => pd k ũ y := by
    funext k
    have h1 := g_sharp g p L (coordField x₀ k p)
    rw [g_hv' x₀ g hp, hv_coordField x₀ hpb k, hL, hv_coordField x₀ hpb k] at h1
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    rw [gradField, ← h1]
    conv_lhs => rw [← hGs]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hdet : IsUnit G.det := g.coordMetric_isUnit_det x₀ hyt
  rw [gradVec, ← hGw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- The square `g(ℓ, ℓ)` of the gradient in a chart is `gradSq`. -/
theorem g_gradField (x₀ : M) {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) {u : M → ℝ}
    (hu : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) u p) :
    g.g p (gradField g u p) (gradField g u p) =
      gradSq (g.coordMetric x₀) (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  have hyt := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp
  have hdet : IsUnit (g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p)).det := g.coordMetric_isUnit_det x₀ hyt
  rw [g_hv' x₀ g hp, hv_gradField g x₀ hp hu, gradSq, gradVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, dotProduct_comm]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- A smooth function read in a chart is smooth on the chart target. -/
theorem contDiffOn_comp_extChartAt_symm (x₀ : M) {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ u) :
    ContDiffOn ℝ ∞ (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
  contMDiffOn_iff_contDiffOn.1 (hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀))

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- The coordinate gradient of a function smooth on the chart target is smooth there. -/
theorem contDiffOn_gradVec (x₀ : M) {v : (Fin n → ℝ) → ℝ}
    (hv : ContDiffOn ℝ ∞ v (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    ContDiffOn ℝ ∞ (gradVec (g.coordMetric x₀) v) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have hgc := g.isCoordMetric_coordMetric x₀
  refine contDiffOn_pi.2 fun a => ?_
  have e : (fun y => gradVec (g.coordMetric x₀) v y a) =
      fun y => ∑ d, (g.coordMetric x₀ y)⁻¹ a d * pd d v y := by
    funext y; simp [gradVec, mulVec, dotProduct]
  rw [e]
  exact ContDiffOn.sum fun d _ => (hgc.contDiffOn_inv a d).mul (contDiffOn_pd hv hgc.isOpen d)

/-- **The gradient of a smooth function is a smooth vector field.** -/
theorem contMDiff_gradField {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, gradField g u q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) := by
  intro p
  have hpp := mem_baseSet_of_mem_source p (mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p)
  rw [(tTriv (E := Fin n → ℝ) p).contMDiffAt_section_iff hpp]
  have hy := mem_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p
  have hG := contDiffOn_gradVec g p (contDiffOn_comp_extChartAt_symm p hu)
  have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (gradVec (g.coordMetric p) (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm) ∘ extChartAt 𝓘(ℝ, Fin n → ℝ) p) p :=
    (hG.contDiffAt ((isOpen_extChartAt_target p).mem_nhds hy)).contMDiffAt.comp p (contMDiffAt_extChartAt (n := ∞))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds
    (mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p)] with q hq
  exact hv_gradField g p hq ((hu q).mdifferentiableAt (by simp))

/-- **The gradient of a function whose level sets are null near a point is geodesic there**: if `g(ℓ, ℓ) = 0` near
`p` for `ℓ = ♯du`, then `∇_ℓ ℓ = 0` at `p` for the Levi-Civita connection. The integral curves of `ℓ` are the null
generators of the null level sets, affinely parametrized. -/
theorem gradField_geodesic_of_null {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ u) {p : M}
    (hN : ∀ᶠ q in 𝓝 p, g.g q (gradField g u q) (gradField g u q) = 0) :
    leviCivita g (gradField g u) p (gradField g u p) = 0 := by
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  have hps := mem_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p
  have hpb := mem_baseSet_of_mem_source p hps
  have hyt := mem_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p
  have hgc := g.isCoordMetric_coordMetric p
  have hgs : ∀ z a b, g.coordMetric p z a b = g.coordMetric p z b a := fun z a b => by
    have := congrFun (congrFun (g.coordMetric_transpose p z) b) a
    simpa [Matrix.transpose_apply] using this
  have hũ := contDiffOn_comp_extChartAt_symm p hu
  have hV := (contMDiff_gradField g hu p).mdifferentiableAt (by simp)
  have key := hv_cov_eq' p (leviCivita g) g hLC hps hV (gradField g u p)
  -- the components of the gradient near the chart point
  have hcomp : chartComp p (gradField g u) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) p p)]
      gradVec (g.coordMetric p) (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds hyt] with z hz
    have hzs := (extChartAt 𝓘(ℝ, Fin n → ℝ) p).map_target hz
    show hv p _ (gradField g u _) = _
    rw [hv_gradField g p hzs ((hu _).mdifferentiableAt (by simp)), (extChartAt 𝓘(ℝ, Fin n → ℝ) p).right_inv hz]
  have hcov : covDMat (g.coordMetric p) (chartComp p (gradField g u)) (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) =
      covDMat (g.coordMetric p) (gradVec (g.coordMetric p) (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm))
        (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) := by
    ext a b
    simp only [covDMat, Matrix.of_apply, covD]
    have h1 : (fun z => chartComp p (gradField g u) z a) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) p p)]
        fun z => gradVec (g.coordMetric p) (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm) z a :=
      hcomp.mono fun z hz => by simp only [hz]
    unfold pd
    rw [h1.fderiv_eq, hcomp.eq_of_nhds]
  -- the square of the gradient vanishes near the chart point
  have hN' : gradSq (g.coordMetric p) (u ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) p p)]
      fun _ => 0 := by
    have hc : ContinuousAt (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) :=
      continuousAt_extChartAt_symm p
    have hN0 : ∀ᶠ q in 𝓝 ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) p p)),
        g.g q (gradField g u q) (gradField g u q) = 0 := by
      rwa [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv hps]
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds hyt, hc.eventually hN0]
      with z hz h0
    have hzs := (extChartAt 𝓘(ℝ, Fin n → ℝ) p).map_target hz
    have := g_gradField g p hzs ((hu _).mdifferentiableAt (by simp))
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).right_inv hz] at this
    rw [← this]
    exact h0
  rw [hcov, hv_gradField g p hps ((hu p).mdifferentiableAt (by simp)),
    gradVec_geodesic_of_null hgc hgs hũ hyt hN'] at key
  rw [← symmL_hv p hpb (leviCivita g (gradField g u) p (gradField g u p)), key, map_zero]

/-- **The null generators with any normalization** (Gourgoulhon–Jaramillo (2.21)): for `ℓ' = f ℓ` with `ℓ = ♯du` and
`g(ℓ, ℓ) = 0` near `p`, `∇_{ℓ'} ℓ' = κ ℓ'` at `p` with `κ = ⟨df, ℓ⟩`; for `f = e^ρ` this is the source's
`κ = ⟨dρ, ℓ'⟩` (2.22). -/
theorem smul_gradField_of_null {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ u) {p : M}
    (hN : ∀ᶠ q in 𝓝 p, g.g q (gradField g u q) (gradField g u q) = 0) {f : M → ℝ}
    (hf : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) f p) :
    leviCivita g (fun q => f q • gradField g u q) p (f p • gradField g u p) =
      mvfderiv 𝓘(ℝ, Fin n → ℝ) f p (gradField g u p) • (f p • gradField g u p) := by
  have hV := (contMDiff_gradField g hu p).mdifferentiableAt (by simp)
  have hL := (leviCivita g).isCovariantDerivativeOnUniv.leibniz (σ := gradField g u) (g := f) hV hf
  have e : (fun q => f q • gradField g u q) = f • gradField g u := rfl
  rw [e, hL]
  simp only [map_smul, _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    gradField_geodesic_of_null g hu hN, smul_zero, zero_add]
  rw [smul_smul, smul_smul, mul_comm]

end Gradient

end Lightlike
