import Lightlike.Spacetime.ChartAgreement
/-!
# The Levi-Civita connection of a Lorentzian metric is smooth

`contMDiffCovariantDerivative_leviCivita`: for a `C²` manifold modelled on `Fin n → ℝ`, `leviCivita g`
(`LeviCivita.lean`) is a `C^∞` covariant derivative in Mathlib's sense (`ContMDiffCovariantDerivative`).

Proof. For a vector field `σ` smooth near `p`, the section `∇σ` of the bundle of endomorphisms is smooth at `p` iff its
components in the trivialization at `p` are (`contMDiffAt_clm_of_apply_infty`). Applied to `a`, these are
`D σ̂ (∂_a) + Γ̂(σ̂, a)` (`hat_cov`): the first term is the derivative of a smooth function along a coordinate field
(`contMDiffAt_mvfderiv_cfield`, by the chain rule in the fixed chart, `mvfderiv_chart_fixed`), the second is smooth because
`Γ̂` is the Christoffel symbol of the coordinate metric (`gamHat_coord`, which does not need smoothness of the connection)
and the coordinate metric is smooth (`contMDiffAt_gamHat_leviCivita`).

**Limits.** Manifolds modelled on `Fin n → ℝ` without boundary and `C²`; no Hausdorff hypothesis (the local smoothness `contMDiffAt_leviCivita` is proved in a chart). Mathlib's definition of a smooth
covariant derivative is used unchanged.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
variable (p : M)

/-- The derivative of the chart at `p` maps `e⁻¹ a` to `a`. -/
theorem mfderiv_chart_symmL {y : M} (hy : y ∈ (tTriv (E := Fin n → ℝ) p).baseSet) (a : Fin n → ℝ) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) y
      ((tTriv (E := Fin n → ℝ) p).symmL ℝ y a) = a := by
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, Fin n → ℝ)) (x₀ := p) (x := y)
  have hs : y ∈ (chartAt (Fin n → ℝ) p).source := by
    simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hy
  rw [← h hs]
  exact (tTriv (E := Fin n → ℝ) p).continuousLinearMapAt_symmL hy a

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Chain rule in a fixed chart centred at `p`, at a point `y` of its source. -/
theorem mvfderiv_chart_fixed (s : M → F) {y : M} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source)
    (hs : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) s y) (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) s y u =
      fderiv ℝ (s ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) p y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) y u) := by
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) p with hφ
  have h1 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) φ y := mdifferentiableAt_extChartAt (by simpa [hφ, extChartAt_source] using hy)
  have h2 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) φ.symm (φ y) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := p) (φ.map_source hy)
    simpa [hφ, mdifferentiableWithinAt_univ] using this
  have h3 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) (s ∘ φ.symm) (φ y) := by
    refine MDifferentiableAt.comp (φ y) ?_ h2
    rw [φ.left_inv hy]; exact hs
  have heq : s =ᶠ[nhds y] (s ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds hy] with z hz
    simp [φ.left_inv hz]
  have hm : mvfderiv 𝓘(ℝ, Fin n → ℝ) s y = mvfderiv 𝓘(ℝ, Fin n → ℝ) ((s ∘ φ.symm) ∘ φ) y := mvfderiv_congr heq
  rw [hm, mvfderiv_comp y h3 h1]
  simp [mvfderiv_eq_fderiv]
  rfl

/-- The derivative of a smooth function along the coordinate field `cfield a` is smooth. -/
theorem contMDiffAt_mvfderiv_cfield (s : M → F)
    (hs : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞ s y) (a : Fin n → ℝ) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞ (fun y => mvfderiv 𝓘(ℝ, Fin n → ℝ) s y (cfield p a y)) p := by
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hsp : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞ s p := hs.self_of_nhds
  have hsymm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ φ.symm (φ p) := by
    have := contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) p (mem_extChartAt_target p)
    simpa [hφ, contMDiffWithinAt_univ] using this
  have hφd : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ φ p := contMDiffAt_extChartAt
  have h1 : ContDiffAt ℝ ∞ (s ∘ φ.symm) (φ p) := by
    have := hsp.comp_of_eq hsymm (φ.left_inv hp)
    exact contMDiffAt_iff_contDiffAt.1 this
  have h2 : ContDiffAt ℝ ∞ (fderiv ℝ (s ∘ φ.symm)) (φ p) := h1.fderiv_right (m := ∞) (by simp)
  have h3 : ContDiffAt ℝ ∞ (fun y => fderiv ℝ (s ∘ φ.symm) y a) (φ p) :=
    h2.clm_apply contDiffAt_const
  have h4 := (contMDiffAt_iff_contDiffAt.2 h3).comp_of_eq hφd rfl
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds hp,
    (tTriv (E := Fin n → ℝ) p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ p), hs] with y hy hyb hys
  have hmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) s y := hys.mdifferentiableAt (by simp)
  rw [mvfderiv_chart_fixed p s hy hmd]
  have : cfield p a y = (tTriv (E := Fin n → ℝ) p).symmL ℝ y a := rfl
  rw [this, mfderiv_chart_symmL p hyb]
  rfl

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- **The Christoffel tensor of the Levi-Civita connection applied to a smooth vector is smooth.** -/
theorem contMDiffAt_gamHat_leviCivita (v : M → Fin n → ℝ) (hv : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ v p) (a : Fin n → ℝ) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (fun y => gamHat (leviCivita g) p y (v y) a) p := by
  have hLC : (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hgc := g.isCoordMetric_coordMetric p
  have hC : ∀ k i j : Fin n, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (fun y => christoffel (g.coordMetric p) k i j (φ y)) p := by
    intro k i j
    have h1 : ContDiffAt ℝ ∞ (christoffel (g.coordMetric p) k i j) (φ p) :=
      (hgc.contDiffOn_christoffel k i j).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds (φ.map_source hp))
    exact (contMDiffAt_iff_contDiffAt.2 h1).comp_of_eq (contMDiffAt_extChartAt) rfl
  have hvj : ∀ j, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (fun y => v y j) p := fun j =>
    (contMDiffAt_pi_space.1 hv) j
  have hform : (fun y => gamHat (leviCivita g) p y (v y) a) =ᶠ[𝓝 p]
      fun y => ∑ j, ∑ i, ∑ k, (a j * v y i * christoffel (g.coordMetric p) k j i (φ y)) • (Pi.single k 1 : Fin n → ℝ) := by
    filter_upwards [(tTriv (E := Fin n → ℝ) p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ p)] with y hy
    have hsv : v y = ∑ j, v y j • (Pi.single j 1 : Fin n → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    have hsa : a = ∑ i, a i • (Pi.single i 1 : Fin n → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hsv, hsa]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      gamHat_coord (leviCivita g) p g hLC hy, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hform
  refine ContMDiffAt.sum fun j _ => ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun k _ => ?_
  exact ((contMDiffAt_const.mul (hvj i)).mul (hC k j i)).smul contMDiffAt_const

/-- A map into continuous linear maps is smooth if its values on every vector are (all orders). -/
theorem contMDiffAt_clm_of_apply_infty {G : M → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {p : M}
    (h : ∀ a : Fin n → ℝ, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (fun z => G z a) p) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ∞ G p := by
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) p with hφ
  have hp : p ∈ φ.source := mem_extChartAt_source p
  have hsymm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ φ.symm (φ p) := by
    have := contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) p (mem_extChartAt_target p)
    simpa [hφ, contMDiffWithinAt_univ] using this
  have hφd : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ φ p := contMDiffAt_extChartAt
  have h1 : ∀ a : Fin n → ℝ, ContDiffAt ℝ ∞ (fun y => G (φ.symm y) a) (φ p) := fun a => by
    have := (h a).comp_of_eq hsymm (φ.left_inv hp)
    exact contMDiffAt_iff_contDiffAt.1 this
  have h2 : ContDiffAt ℝ ∞ (fun y => G (φ.symm y)) (φ p) := by
    rw [← contDiffWithinAt_univ, contDiffWithinAt_clm_apply]
    exact fun a => (contDiffWithinAt_univ).2 (h1 a)
  have h3 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ∞ (fun y => G (φ.symm y)) (φ p) :=
    contMDiffAt_iff_contDiffAt.2 h2
  have h4 := h3.comp_of_eq hφd rfl
  refine h4.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) p).mem_nhds hp] with z hz
  simp [φ.left_inv hz]

/-- `∇σ` of the Levi-Civita connection is smooth at `p` for a vector field smooth near `p`. -/
theorem contMDiffAt_leviCivita {σ : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hσ : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) y) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) ∞
      (fun y => (⟨y, leviCivita g σ y⟩ : TotalSpace ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (fun y : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) y))) p := by
  have hp : p ∈ (tTriv (E := Fin n → ℝ) p).baseSet := mem_baseSet_trivializationAt _ _ p
  rw [(trivializationAt ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (fun y : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) y →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) y) p).contMDiffAt_section_iff (by simp [hom_trivializationAt_baseSet, hp, Trivial.trivialization])]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates]
  refine contMDiffAt_clm_of_apply_infty fun a => ?_
  have hsm : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (hat p σ) y := by
    filter_upwards [hσ, (tTriv (E := Fin n → ℝ) p).open_baseSet.mem_nhds hp] with y hy hyb
    exact ((tTriv (E := Fin n → ℝ) p).contMDiffAt_section_iff hyb).1 hy
  have hA := contMDiffAt_mvfderiv_cfield p (hat p σ) hsm a
  have hB := contMDiffAt_gamHat_leviCivita p g (hat p σ) hsm.self_of_nhds a
  refine (hA.add hB).congr_of_eventuallyEq ?_
  filter_upwards [hσ, (tTriv (E := Fin n → ℝ) p).open_baseSet.mem_nhds hp] with y hy hyb
  have hmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) y :=
    hy.mdifferentiableAt (by simp)
  have hcl : ∀ u : TangentSpace 𝓘(ℝ, Fin n → ℝ) y, Trivialization.continuousLinearMapAt ℝ
      (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) p) y u = hv p y u := fun u => by
    rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, ite_eq_left hyb]
  have := hat_cov (leviCivita g) p hyb hmd ((tTriv (E := Fin n → ℝ) p).symmL ℝ y a)
  simp only [ContinuousLinearMap.comp_apply]
  rw [hcl, this, hv_symmL p hyb a]
  rfl

/-- **The Levi-Civita connection of a Lorentzian metric is smooth** (a manifold modelled on `ℝⁿ`, `C²`; no Hausdorff hypothesis). -/
theorem contMDiffCovariantDerivative_leviCivita :
    CovariantDerivative.ContMDiffCovariantDerivative (leviCivita g) ∞ where
  contMDiff := ⟨fun {σ} hσ => fun p _ => by
    refine ContMDiffAt.contMDiffWithinAt ?_
    refine contMDiffAt_leviCivita p g ?_
    filter_upwards with y
    have := hσ y (mem_univ y)
    exact (this.contMDiffAt Filter.univ_mem).of_le (by simp)⟩

/-- **The Levi-Civita connection is locally smooth** on any `C²` manifold (no Hausdorff hypothesis). -/
instance (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) : LocallySmoothConnection (leviCivita g) :=
  ⟨fun {σ x} hσ => contMDiffAt_leviCivita x g hσ⟩

end Lightlike
