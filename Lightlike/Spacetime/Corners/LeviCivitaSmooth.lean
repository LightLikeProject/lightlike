import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.RiemannSymmetryWithin
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.Corners.ChartCurvature
import Lightlike.Spacetime.Corners.Coordinates
import Lightlike.Spacetime.Corners.Curvature
/-!
# The Levi-Civita connection of a Lorentzian metric is smooth

`contMDiffCovariantDerivative_leviCivita`: for a `C²` manifold modelled on `Fin n → ℝ`, `leviCivita g`
(`LeviCivita.lean`) is a `C^∞` covariant derivative in Mathlib's sense (`ContMDiffCovariantDerivative`).

Proof. For a vector field `σ` smooth near `p`, the section `∇σ` of the bundle of endomorphisms is smooth at `p` iff its
components in the trivialization at `p` are (`contMDiffAt_clm_of_apply_inftyW`). Applied to `a`, these are
`D σ̂ (∂_a) + Γ̂(σ̂, a)` (`hat_covW`): the first term is the derivative of a smooth function along a coordinate field
(`contMDiffAt_mvfderiv_cfieldW`, by the chain rule in the fixed chart, `mvfderiv_chart_fixedW`), the second is smooth because
`Γ̂` is the Christoffel symbol of the coordinate metric (`gamHat_coordW`, which does not need smoothness of the connection)
and the coordinate metric is smooth (`contMDiffAt_gamHat_leviCivitaW`).

**Limits.** Manifolds with corners modelled on `Fin n → ℝ` (any `ModelWithCorners`, derivatives in the chart within `range I`) and `C²`; no Hausdorff hypothesis (the local smoothness `contMDiffAt_leviCivitaW` is proved in a chart). Mathlib's definition of a smooth
covariant derivative is used unchanged.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/LeviCivitaSmooth.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M]
variable (p : M)

/-- The derivative of the chart at `p` maps `e⁻¹ a` to `a`. -/
theorem mfderiv_chart_symmLW {y : M} (hy : y ∈ (tTrivW (I := I) (E := Fin n → ℝ) p).baseSet) (a : Fin n → ℝ) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I p) y
      ((tTrivW (I := I) (E := Fin n → ℝ) p).symmL ℝ y a) = a := by
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (I := I) (x₀ := p) (x := y)
  have hs : y ∈ (chartAt H p).source := by
    simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using hy
  rw [← h hs]
  exact (tTrivW (I := I) (E := Fin n → ℝ) p).continuousLinearMapAt_symmL hy a

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chain rule in a fixed chart centred at `p`, at a point `y` of its source: the derivative within `range I` of the
expression in the chart. -/
theorem mvfderiv_chart_fixedW (s : M → F) {y : M} (hy : y ∈ (extChartAt I p).source)
    (hs : MDifferentiableAt I 𝓘(ℝ, F) s y) (u : TangentSpace I y) :
    mvfderiv I s y u =
      fderivWithin ℝ (s ∘ (extChartAt I p).symm) (range I) (extChartAt I p y)
        (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I p) y u) :=
  mvfderiv_eq_chart_at s p y hy hs u

/-- The derivative of a smooth function along the coordinate field `cfieldW a` is smooth. -/
theorem contMDiffAt_mvfderiv_cfieldW (s : M → F)
    (hs : ∀ᶠ y in 𝓝 p, ContMDiffAt I 𝓘(ℝ, F) ∞ s y) (a : Fin n → ℝ) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => mvfderiv I s y (cfieldW (I := I) p a y)) p := by
  set φ := extChartAt I p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hsp : ContMDiffAt I 𝓘(ℝ, F) ∞ s p := hs.self_of_nhds
  have hsymm : ContMDiffWithinAt 𝓘(ℝ, Fin n → ℝ) I ∞ φ.symm (range I) (φ p) :=
    contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) p (mem_extChartAt_target p)
  have hφd : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ φ p := contMDiffAt_extChartAt
  have h1 : ContDiffWithinAt ℝ ∞ (s ∘ φ.symm) (range I) (φ p) := by
    have := hsp.comp_contMDiffWithinAt_of_eq hsymm (φ.left_inv hp)
    exact contMDiffWithinAt_iff_contDiffWithinAt.1 this
  have hpr : φ p ∈ range I := mem_range_self _
  have h2 : ContDiffWithinAt ℝ ∞ (fderivWithin ℝ (s ∘ φ.symm) (range I)) (range I) (φ p) :=
    h1.fderivWithin_right (m := ∞) I.uniqueDiffOn (by simp) hpr
  have h3 : ContDiffWithinAt ℝ ∞ (fun y => fderivWithin ℝ (s ∘ φ.symm) (range I) y a) (range I) (φ p) :=
    h2.clm_apply contDiffWithinAt_const
  have h3' : ContMDiffWithinAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞
      (fun y => fderivWithin ℝ (s ∘ φ.symm) (range I) y a) (range I) (φ p) :=
    contMDiffWithinAt_iff_contDiffWithinAt.2 h3
  have h4 := h3'.comp p (hφd.contMDiffWithinAt (s := Set.univ)) (fun z _ => ⟨_, rfl⟩)
  rw [contMDiffWithinAt_univ] at h4
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds hp,
    (tTrivW (I := I) (E := Fin n → ℝ) p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ p), hs] with y hy hyb hys
  have hmd : MDifferentiableAt I 𝓘(ℝ, F) s y := hys.mdifferentiableAt (by simp)
  rw [mvfderiv_chart_fixedW p s hy hmd]
  have : cfieldW (I := I) p a y = (tTrivW (I := I) (E := Fin n → ℝ) p).symmL ℝ y a := rfl
  rw [this, mfderiv_chart_symmLW p hyb]
  rfl

variable (g : NondegMetric I M)

/-- **The Christoffel tensor of the Levi-Civita connection applied to a smooth vector is smooth.** -/
theorem contMDiffAt_gamHat_leviCivitaW (v : M → Fin n → ℝ) (hvW : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ v p) (a : Fin n → ℝ) :
    ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (fun y => gamHatW (leviCivita g) p y (v y) a) p := by
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  set φ := extChartAt I p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hgc := g.isCoordMetricW_coordMetric p
  have hC : ∀ k i j : Fin n, ContMDiffAt I 𝓘(ℝ) ∞
      (fun y => christoffelW (range I) (g.coordMetricW p) k i j (φ y)) p := by
    intro k i j
    have h1 : ContDiffWithinAt ℝ ∞ (christoffelW (range I) (g.coordMetricW p) k i j) (range I) (φ p) :=
      ((hgc.contDiffOn_christoffel k i j).contDiffWithinAt (φ.map_source hp)).mono_of_mem_nhdsWithin
        (extChartAt_target_mem_nhdsWithin' hp)
    have h1' : ContMDiffWithinAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞
        (christoffelW (range I) (g.coordMetricW p) k i j) (range I) (φ p) :=
      contMDiffWithinAt_iff_contDiffWithinAt.2 h1
    have h4 := h1'.comp p (contMDiffAt_extChartAt (I := I) (x := p)).contMDiffWithinAt (s := Set.univ)
      (fun z _ => ⟨_, rfl⟩)
    rwa [contMDiffWithinAt_univ] at h4
  have hvj : ∀ j, ContMDiffAt I 𝓘(ℝ) ∞ (fun y => v y j) p := fun j =>
    (contMDiffAt_pi_space.1 hvW) j
  have hform : (fun y => gamHatW (leviCivita g) p y (v y) a) =ᶠ[𝓝 p]
      fun y => ∑ j, ∑ i, ∑ k, (a j * v y i * christoffelW (range I) (g.coordMetricW p) k j i (φ y)) • (Pi.single k 1 : Fin n → ℝ) := by
    filter_upwards [(tTrivW (I := I) (E := Fin n → ℝ) p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ p)] with y hy
    have hsv : v y = ∑ j, v y j • (Pi.single j 1 : Fin n → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    have hsa : a = ∑ i, a i • (Pi.single i 1 : Fin n → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hsv, hsa]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      gamHat_coordW (leviCivita g) p g hLC hy, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hform
  refine ContMDiffAt.sum fun j _ => ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun k _ => ?_
  exact ((contMDiffAt_const.mul (hvj i)).mul (hC k j i)).smul contMDiffAt_const

/-- `∇σ` of the Levi-Civita connection is smooth at `p` for a vector field smooth near `p`. -/
theorem contMDiffAt_leviCivitaW {σ : Π y : M, TangentSpace I y}
    (hσ : ∀ᶠ y in 𝓝 p, ContMDiffAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle I M)) y) :
    ContMDiffAt I (I.prod 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) ∞
      (fun y => (⟨y, leviCivita g σ y⟩ : TotalSpace ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) p := by
  have hp : p ∈ (tTrivW (I := I) (E := Fin n → ℝ) p).baseSet := mem_baseSet_trivializationAt _ _ p
  rw [(trivializationAt ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) p).contMDiffAt_section_iff (by simp [hom_trivializationAt_baseSet, hp, Trivial.trivialization])]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  refine contMDiffAt_clm_of_apply_inftyW fun a => ?_
  have hsm : ∀ᶠ y in 𝓝 p, ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (hatW p σ) y := by
    filter_upwards [hσ, (tTrivW (I := I) (E := Fin n → ℝ) p).open_baseSet.mem_nhds hp] with y hy hyb
    exact ((tTrivW (I := I) (E := Fin n → ℝ) p).contMDiffAt_section_iff hyb).1 hy
  have hA := contMDiffAt_mvfderiv_cfieldW p (hatW p σ) hsm a
  have hB := contMDiffAt_gamHat_leviCivitaW p g (hatW p σ) hsm.self_of_nhds a
  refine (hA.add hB).congr_of_eventuallyEq ?_
  filter_upwards [hσ, (tTrivW (I := I) (E := Fin n → ℝ) p).open_baseSet.mem_nhds hp] with y hy hyb
  have hmd : MDifferentiableAt I (I.prod 𝓘(ℝ, Fin n → ℝ)) (fun q : M => (⟨q, σ q⟩ : TangentBundle I M)) y :=
    hy.mdifferentiableAt (by simp)
  have hcl : ∀ u : TangentSpace I y, Trivialization.continuousLinearMapAt ℝ
      (trivializationAt (Fin n → ℝ) (TangentSpace I) p) y u = hvW p y u := fun u => by
    rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hyb]
  have := hat_covW (leviCivita g) p hyb hmd ((tTrivW (I := I) (E := Fin n → ℝ) p).symmL ℝ y a)
  simp only [ContinuousLinearMap.comp_apply]
  rw [hcl, this, hv_symmLW p hyb a]
  rfl

/-- **The Levi-Civita connection is locally smooth** on any `C²` manifold (no Hausdorff hypothesis). -/
instance (g : NondegMetric I M) : LocallySmoothConnectionW (leviCivita g) :=
  ⟨fun {σ x} hσ => contMDiffAt_leviCivitaW x g hσ⟩

end Lightlike
