import Lightlike.Spacetime.RaychaudhuriCoord
import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.RaychaudhuriFocusing

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff Matrix Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

section ChartE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] (x₀ : N)

/-- The chain rule in the chart at `x₀`, at any point of its domain, for a vector-valued function. -/
theorem mvfderiv_eq_chart₀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : N → F) {p : N}
    (hp : p ∈ (extChartAt 𝓘(ℝ, E) x₀).source) (hf : MDiffAt f p) (u : TangentSpace 𝓘(ℝ, E) p) :
    mvfderiv 𝓘(ℝ, E) f p u =
      fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) x₀).symm) (extChartAt 𝓘(ℝ, E) x₀ p)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) p u) := by
  set φ := extChartAt 𝓘(ℝ, E) x₀ with hφ
  have h1 : MDiffAt φ p := mdifferentiableAt_extChartAt (by simpa [hφ] using hp)
  have h2 : MDiffAt φ.symm (φ p) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) (x := x₀) (φ.map_source hp)
    simpa [hφ, mdifferentiableWithinAt_univ] using this
  have h3 : MDiffAt (f ∘ φ.symm) (φ p) := by
    refine MDifferentiableAt.comp (φ p) ?_ h2
    rw [φ.left_inv hp]; exact hf
  have heq : f =ᶠ[nhds p] (f ∘ φ.symm) ∘ φ := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, E)) x₀).mem_nhds hp] with y hy
    simp [φ.left_inv hy]
  have hm : mvfderiv 𝓘(ℝ, E) f p = mvfderiv 𝓘(ℝ, E) ((f ∘ φ.symm) ∘ φ) p := mvfderiv_congr heq
  rw [hm, mvfderiv_comp p h3 h1]
  simp [mvfderiv_eq_fderiv]
  rfl

end ChartE

section Chart
variable (x₀ : M)

/-- The derivative of the chart is the trivialization: `dφ(u) = û`. -/
theorem mfderiv_extChartAt_apply {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀)
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) u = hv x₀ _ u := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have h3 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀) hy
  have h4 := mfderiv_extChartAt_symm_eq x₀ hy
  have h5 : mfderivWithin 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
      (range 𝓘(ℝ, Fin n → ℝ)) y = (chartTriv n x₀).symmL ℝ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
    rw [← h4]
    simp [mfderivWithin_univ]
    rfl
  rw [h5] at h3
  have := DFunLike.congr_fun h3 (hv x₀ _ u)
  have e : (chartTriv n x₀).symmL ℝ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (hv x₀ _ u) = u := symmL_hv x₀ hp u
  have h' : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀)
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      ((chartTriv n x₀).symmL ℝ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (hv x₀ _ u)) = hv x₀ _ u := this
  rw [e] at h'
  exact h'

/-- The components `v(y) = V̂(φ⁻¹ y)` of a vector field in the chart at `x₀`. -/
def chartComp (V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) : (Fin n → ℝ) → Fin n → ℝ :=
  fun y => hat x₀ V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)

/-- The components of a differentiable vector field are differentiable in the chart. -/
theorem differentiableAt_chartComp {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hV : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) :
    DifferentiableAt ℝ (chartComp x₀ V) y := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hmd := (mdiffAt_hat_iff x₀ V hp).1 hV
  have h2 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀) hy
    simpa [mdifferentiableWithinAt_univ] using this
  exact mdifferentiableAt_iff_differentiableAt.1 (hmd.comp y h2)

/-- A bilinear map in coordinates: `B x z = Σ_c Σ_b x_c z_b B(e_c, e_b)`. -/
theorem clm₂_apply_eq_sum (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (x z : Fin n → ℝ) :
    B x z = ∑ c, ∑ b, (x c * z b) • B (Pi.single c 1) (Pi.single b 1) := by
  conv_lhs => rw [show x = ∑ c, x c • Pi.single c (1 : ℝ) by ext i; simp [Pi.single_apply],
    show z = ∑ b, z b • Pi.single b (1 : ℝ) by ext i; simp [Pi.single_apply]]
  simp only [map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by
    rw [mul_comm]

/-- A linear map in coordinates: `ℓ w = Σ_b w_b ℓ(e_b)`. -/
theorem clm_apply_eq_sum' {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (ℓ : (Fin n → ℝ) →L[ℝ] F) (w : Fin n → ℝ) : ℓ w = ∑ b, w b • ℓ (Pi.single b 1) := by
  conv_lhs => rw [show w = ∑ b, w b • Pi.single b (1 : ℝ) by ext i; simp [Pi.single_apply]]
  simp [map_sum, map_smul]

variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- **The covariant derivative of a vector field in a chart**: the components of `∇_u V` at `φ⁻¹ y` are
`(∇_b vᵃ) uᵇ`, with `∇_b vᵃ = ∂_b vᵃ + Γᵃ_{bc} vᶜ` (`covD`) for the components `v` of `V` and the Christoffel symbols
of the coordinate metric, for the Levi-Civita connection. -/
theorem hv_cov_eq (h : cov.IsLeviCivita g) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hV : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) :
    hv x₀ _ (cov V _ u) = covDMat (g.coordMetric x₀) (chartComp x₀ V) y *ᵥ hv x₀ _ u := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hps : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_target hy
  have hmd := (mdiffAt_hat_iff x₀ V hp).1 hV
  have hd := differentiableAt_chartComp x₀ hy hV
  rw [hat_cov cov x₀ hp hV u, mvfderiv_eq_chart₀ x₀ (hat x₀ V) hps hmd u, mfderiv_extChartAt_apply x₀ hy u,
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy]
  have hcomp : hat x₀ V ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm = chartComp x₀ V := rfl
  have hvy : hat x₀ V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = chartComp x₀ V y := rfl
  rw [hcomp, hvy, clm₂_apply_eq_sum (gamHat cov x₀ _) (chartComp x₀ V y) (hv x₀ _ u)]
  simp only [gamHat_coord cov x₀ g h hp, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy]
  funext a
  have hpd : ∀ b, pd b (fun z => chartComp x₀ V z a) y = fderiv ℝ (chartComp x₀ V) y (Pi.single b 1) a := fun b => by
    have : HasFDerivAt (fun z => chartComp x₀ V z a)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) a).comp (fderiv ℝ (chartComp x₀ V) y)) y :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) a).hasFDerivAt.comp y hd.hasFDerivAt
    unfold pd; rw [this.fderiv]; rfl
  rw [clm_apply_eq_sum' (fderiv ℝ (chartComp x₀ V) y) (hv x₀ _ u)]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mulVec, dotProduct, covDMat, Matrix.of_apply, covD, ← hpd,
    add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

/-- The derivative of the chart at a point of its domain is the trivialization. -/
theorem mfderiv_extChartAt_apply' {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) p u = hv x₀ p u := by
  have key := mfderiv_extChartAt_apply x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hp)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hp] at key
  exact key u

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- **The trace in the chart**: an endomorphism of `T_p M` whose components are `M *ᵥ ·` has trace `tr M`. -/
theorem trace_eq_of_hv {p : M} (hp : p ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet)
    (A : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (Mx : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ u, hv x₀ p (A u) = Mx *ᵥ hv x₀ p u) :
    LinearMap.trace ℝ _ (A : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p) = Mx.trace := by
  set e := (tTriv (E := Fin n → ℝ) x₀).linearEquivAt ℝ p hp
  rw [← LinearMap.trace_conj' _ e]
  have : e.conj (A : TangentSpace 𝓘(ℝ, Fin n → ℝ) p →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) p) = Mx.toLin' := by
    refine LinearMap.ext fun w => ?_
    rw [LinearEquiv.conj_apply, Matrix.toLin'_apply]
    have h1 := hA (e.symm w)
    change e (A (e.symm w)) = Mx *ᵥ e (e.symm w) at h1
    rw [e.apply_symm_apply] at h1
    exact h1
  rw [this, Matrix.trace_toLin'_eq]

/-- **The Ricci tensor in the chart**: `Ric(Y, Y) = R_{st} Yˢ Yᵗ` with the coordinate Ricci tensor, for the
Levi-Civita connection. -/
theorem ricciAt_hv [LocallySmoothConnection cov] (h : cov.IsLeviCivita g) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (Y : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) :
    cov.ricciAt _ Y Y = ∑ s, ∑ t, ricci (g.coordMetric x₀) s t y * hv x₀ _ Y s * hv x₀ _ Y t := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hY : Y = ∑ s, hv x₀ _ Y s • coordField x₀ s ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
    conv_lhs => rw [← symmL_hv x₀ hp Y,
      show hv x₀ _ Y = ∑ s, hv x₀ _ Y s • Pi.single s (1 : ℝ) by ext i; simp [Pi.single_apply]]
    simp only [map_sum, map_smul, symmL_eq_coordField x₀ hp]
  have hR : cov.ricciAt _ Y Y = RicB cov x₀ hp Y Y := rfl
  rw [hR]
  conv_lhs => rw [hY]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hc : ∀ s t, RicB cov x₀ hp (coordField x₀ s ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
      (coordField x₀ t ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = ricci (g.coordMetric x₀) t s y :=
    fun s t => ricciAt_coord cov x₀ g h hy s t
  simp only [hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- A point of the chart domain is in the base set of the tangent trivialization. -/
theorem mem_baseSet_of_mem_source {q : M} (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    q ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := by
  have := symm_mem_chartTriv_baseSet x₀ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hq)
  rwa [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hq] at this

/-- The components of a smooth vector field are smooth in the chart. -/
theorem contDiffAt_chartComp {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hV : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) :
    ContDiffAt ℝ ∞ (chartComp x₀ V) y := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have h1 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (hat x₀ V) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) :=
    ((tTriv (E := Fin n → ℝ) x₀).contMDiffAt_section_iff hp).1 hV
  have h2 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y :=
    (contMDiffOn_extChartAt_symm x₀).contMDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hy)
  exact contMDiffAt_iff_contDiffAt.1 (h1.comp y h2)

/-- `hv_cov_eq` at a point of the chart domain. -/
theorem hv_cov_eq' (h : cov.IsLeviCivita g) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {q : M}
    (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hV : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q)
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) q) :
    hv x₀ q (cov V q u) =
      covDMat (g.coordMetric x₀) (chartComp x₀ V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ q) *ᵥ hv x₀ q u := by
  have key := hv_cov_eq x₀ cov g h (V := V) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hq)
    (by rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hq]; exact hV)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hq] at key
  exact key u

/-- `ricciAt_hv` at a point of the chart domain. -/
theorem ricciAt_hv' [LocallySmoothConnection cov] (h : cov.IsLeviCivita g) {q : M}
    (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (Y : TangentSpace 𝓘(ℝ, Fin n → ℝ) q) :
    cov.ricciAt q Y Y = ∑ s, ∑ t, ricci (g.coordMetric x₀) s t (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ q) *
      hv x₀ q Y s * hv x₀ q Y t := by
  have key := ricciAt_hv x₀ cov g h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hq)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hq] at key
  exact key Y

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- **The metric in components**: `g(u, w) = û ⬝ᵥ (g_{ij} ŵ)` at `φ⁻¹ y`. -/
theorem g_hv {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) :
    g.g _ u w = hv x₀ _ u ⬝ᵥ (g.coordMetric x₀ y *ᵥ hv x₀ _ w) := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hdec : ∀ z : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y),
      z = ∑ i, hv x₀ _ z i • coordBasis x₀ hp i := fun z => by
    conv_lhs => rw [← symmL_hv x₀ hp z,
      show hv x₀ _ z = ∑ i, hv x₀ _ z i • Pi.single i (1 : ℝ) by ext i; simp [Pi.single_apply]]
    simp only [map_sum, map_smul, coordBasis_apply]
  conv_lhs => rw [hdec u, hdec w]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    ← g.coordMetric_eq x₀ hy, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] in
/-- `g_hv` at a point of the chart domain. -/
theorem g_hv' {q : M} (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) q) :
    g.g q u w = hv x₀ q u ⬝ᵥ (g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ q) *ᵥ hv x₀ q w) := by
  have key := g_hv x₀ g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hq)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hq] at key
  exact key u w

/-- **Rotation-free in the chart**: if `g(∇_u V, w) = g(∇_w V, u)` at `x`, the coordinate rotation vanishes at `φ(x)`. -/
theorem rotation_chart_eq_zero (h : cov.IsLeviCivita g) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {x : M}
    (hV : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x)
    (hrot : ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, g.g x (cov V x u) w = g.g x (cov V x w) u) :
    rotation (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) = 0 := by
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hb := mem_baseSet_of_mem_source x hxs
  have hG := g.coordMetric_transpose x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)
  have key : ∀ a b, (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
      covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)) a b =
      (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
      covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)) b a := by
    intro a b
    have e := hrot ((tTriv (E := Fin n → ℝ) x).symmL ℝ x (Pi.single b 1))
      ((tTriv (E := Fin n → ℝ) x).symmL ℝ x (Pi.single a 1))
    rw [g_hv' x g hxs, g_hv' x g hxs, hv_cov_eq' x cov g h hxs hV, hv_cov_eq' x cov g h hxs hV, hv_symmL x hb,
      hv_symmL x hb] at e
    have hs : ∀ i j, g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) i j =
        g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) j i := fun i j => by
      conv_rhs => rw [← hG]
      rfl
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at e
    simp only [Matrix.mul_apply]
    rw [show (∑ c, g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) a c *
        covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) c b) =
        ∑ c, covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) c b *
          g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) c a from
      Finset.sum_congr rfl fun c _ => by rw [hs a c, mul_comm]]
    rw [e]
    exact Finset.sum_congr rfl fun c _ => by rw [hs b c, mul_comm]
  unfold rotation
  have hT : (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
      covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))ᵀ =
      g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
      covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    ext a b; exact key b a
  rw [hT, sub_self, smul_zero]

end Chart

/-- `IsCoordMetric` on a smaller open set. -/
theorem IsCoordMetric.of_subset {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U U' : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) (hU' : IsOpen U') (hsub : U' ⊆ U) : IsCoordMetric g U' where
  isOpen := hU'
  symm x hx := hg.symm x (hsub hx)
  isUnit_det x hx := hg.isUnit_det x (hsub hx)
  smooth i j := (hg.smooth i j).mono hsub

/-- `IsLorentzianCoordMetric` on a smaller open set. -/
theorem IsLorentzianCoordMetric.of_subset {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U U' : Set (Fin n → ℝ)}
    (hg : IsLorentzianCoordMetric g U) (hU' : IsOpen U') (hsub : U' ⊆ U) : IsLorentzianCoordMetric g U' :=
  ⟨hg.1.of_subset hU' hsub, fun y hy => hg.2 y (hsub hy)⟩

section Manifold
variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- The expansion `Θ = tr(∇V)` of a vector field, the trace of `u ↦ ∇_u V`. -/
def expansionM (V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (q : M) : ℝ :=
  LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) q)
    (cov V q : TangentSpace 𝓘(ℝ, Fin n → ℝ) q →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) q)

/-- `V(Θ)`, the derivative of the expansion along `V`, as a real number. -/
def expansionDeriv (V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (x : M) : ℝ :=
  mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (expansionM cov V) x (V x)

section Expansion
variable (h : cov.IsLeviCivita g) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
  (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
    (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
include h hV

/-- The expansion is the coordinate expansion of the components, on the chart domain. -/
theorem expansionM_eq (x₀ : M) {q : M} (hq : q ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    expansionM cov V q = expansion (g.coordMetric x₀) (chartComp x₀ V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ q) := by
  simp only [expansionM]
  rw [trace_eq_of_hv x₀ (mem_baseSet_of_mem_source x₀ hq) (cov V q) _
    (hv_cov_eq' x₀ cov g h hq ((hV q).mdifferentiableAt (by simp)))]
  simp [Matrix.trace, covDMat, expansion]

omit h in
/-- The components of a smooth field are smooth on the chart target. -/
theorem contDiffOn_chartComp (x₀ : M) (a : Fin n) :
    ContDiffOn ℝ ∞ (fun y => chartComp x₀ V y a) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := fun _ hy =>
  (contDiffAt_pi.1 (contDiffAt_chartComp x₀ hy (hV _)) a).contDiffWithinAt

/-- The expansion is differentiable. -/
theorem mdifferentiableAt_expansionM (x : M) : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (expansionM cov V) x := by
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hexp : DifferentiableAt ℝ (expansion (g.coordMetric x) (chartComp x V)) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    unfold expansion
    exact DifferentiableAt.fun_sum fun a _ => differentiableAt_covD (g.isCoordMetric_coordMetric x)
      (contDiffOn_chartComp hV x) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hxs) a a
  have hφ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x) x :=
    mdifferentiableAt_extChartAt (by simp)
  have hΘ : expansionM cov V =ᶠ[𝓝 x]
      (expansion (g.coordMetric x) (chartComp x V)) ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x) := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hxs] with q hq
    exact expansionM_eq cov g h hV x hq
  exact ((hexp.mdifferentiableAt).comp x hφ).congr_of_eventuallyEq hΘ

/-- **`V(Θ)` in the chart**: `V(Θ) = vᶜ ∂_c Θ` with the coordinate expansion of the components `v` at `φ(x)`. -/
theorem mfderiv_expansionM (x : M) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (expansionM cov V) x (V x) =
      ∑ c, chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) c *
        pd c (expansion (g.coordMetric x) (chartComp x V)) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hx0 : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) = x :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hxs
  have hc : (expansionM cov V ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)]
      expansion (g.coordMetric x) (chartComp x V) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hxs)] with y hy
    simp only [Function.comp_apply]
    rw [expansionM_eq cov g h hV x ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_target hy),
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).right_inv hy]
  have hvx : hv x x (V x) = chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    simp only [chartComp, hx0]; rfl
  rw [mfderiv_eq_chart (expansionM cov V) x x hxs (mdifferentiableAt_expansionM cov g h hV x) (V x), hc.fderiv_eq,
    mfderiv_extChartAt_apply' x hxs, hvx, clm_apply_eq_sum']
  simp only [smul_eq_mul]
  rfl

end Expansion

/-- **The Raychaudhuri identity on a manifold**: for the Levi-Civita connection of a metric of any signature and a smooth
vector field `V` that is geodesic near `x` (`∇_V V = 0`), `V(Θ) = -tr((∇V)²) - Ric(V, V)` at `x`, with `Θ = tr(∇V)`. -/
theorem raychaudhuri_manifold [LocallySmoothConnection cov] (h : cov.IsLeviCivita g)
    {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    {x : M} (hgeo : ∀ᶠ q in 𝓝 x, cov V q (V q) = 0) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (expansionM cov V) x (V x) =
      -LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
          ((cov V x).comp (cov V x) : TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x) -
        cov.ricciAt x (V x) (V x) := by
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hx0 : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) = x :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hxs
  have hy0 : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hxs
  have hmd : ∀ q, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q :=
    fun q => (hV q).mdifferentiableAt (by simp)
  -- a neighbourhood in the chart domain where `V` is geodesic
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1
    (hgeo.and ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hxs))
  set U := (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm ⁻¹' W with hU
  have hUo : IsOpen U :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hWo
  have hy0U : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ U := ⟨hy0, by simp only [mem_preimage, hx0]; exact hxW⟩
  have hgU : IsCoordMetric (g.coordMetric x) U := (g.isCoordMetric_coordMetric x).of_subset hUo inter_subset_left
  have hvU : ∀ a, ContDiffOn ℝ ∞ (fun y => chartComp x V y a) U := fun a y hy =>
    (contDiffAt_pi.1 (contDiffAt_chartComp x hy.1 (hV _)) a).contDiffWithinAt
  have hgeoU : ∀ y ∈ U, ∀ d, ∑ c, chartComp x V y c * covD (g.coordMetric x) (chartComp x V) d c y = 0 := by
    intro y hy d
    have hq := hWsub hy.2
    have e := hv_cov_eq x cov g h hy.1 (hmd _) (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y))
    have hvV : hv x _ (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) = chartComp x V y := rfl
    rw [hq.1, hvV] at e
    have e2 := congrFun e d
    have h0 : hv x ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y) (0 : TangentSpace 𝓘(ℝ, Fin n → ℝ) _) = 0 :=
      ((tTriv (E := Fin n → ℝ) x).linear ℝ (symm_mem_chartTriv_baseSet x hy.1)).map_zero
    rw [h0] at e2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, covDMat, Matrix.of_apply] at e2
    rw [e2]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have key := raychaudhuri_coord hgU hvU hgeoU hy0U
  -- the expansion is the coordinate expansion near `x`
  have hΘW : ∀ q ∈ W, expansionM cov V q =
      expansion (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x q) := by
    intro q hq
    have hqs := (hWsub hq).2
    simp only [expansionM]
    rw [trace_eq_of_hv x (mem_baseSet_of_mem_source x hqs) (cov V q) _ (hv_cov_eq' x cov g h hqs (hmd q))]
    simp [Matrix.trace, covDMat, expansion]
  have hΘ : expansionM cov V =ᶠ[𝓝 x]
      (expansion (g.coordMetric x) (chartComp x V)) ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x) := by
    filter_upwards [hWo.mem_nhds hxW] with q hq
    exact hΘW q hq
  have hexp : DifferentiableAt ℝ (expansion (g.coordMetric x) (chartComp x V)) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    unfold expansion
    exact DifferentiableAt.fun_sum fun a _ => differentiableAt_covD hgU hvU hy0U a a
  have hφ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x) x :=
    mdifferentiableAt_extChartAt (by simp)
  have hMD : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (expansionM cov V) x :=
    ((hexp.mdifferentiableAt).comp x hφ).congr_of_eventuallyEq hΘ
  have hc : (expansionM cov V ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) =ᶠ[𝓝 (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)]
      expansion (g.coordMetric x) (chartComp x V) := by
    filter_upwards [hUo.mem_nhds hy0U] with y hy
    simp only [Function.comp_apply]
    rw [hΘW _ hy.2, (extChartAt 𝓘(ℝ, Fin n → ℝ) x).right_inv hy.1]
  have hvx : hv x x (V x) = chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    simp only [chartComp, hx0]; rfl
  rw [mfderiv_eq_chart (expansionM cov V) x x hxs hMD (V x), hc.fderiv_eq, mfderiv_extChartAt_apply' x hxs, hvx,
    clm_apply_eq_sum']
  have htr2 : LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
      ((cov V x).comp (cov V x) : TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x) =
      ∑ a, ∑ b, covD (g.coordMetric x) (chartComp x V) a b (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
        covD (g.coordMetric x) (chartComp x V) b a (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    rw [trace_eq_of_hv x (mem_baseSet_of_mem_source x hxs) ((cov V x).comp (cov V x))
      (covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
        covDMat (g.coordMetric x) (chartComp x V) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)) (fun u => by
      rw [ContinuousLinearMap.comp_apply, hv_cov_eq' x cov g h hxs (hmd x), hv_cov_eq' x cov g h hxs (hmd x),
        Matrix.mulVec_mulVec])]
    simp [Matrix.trace, Matrix.mul_apply, covDMat]
  rw [htr2, ricciAt_hv' x cov g h hxs (V x), hvx]
  simp only [smul_eq_mul]
  exact key

/-- **The Raychaudhuri identity for the Levi-Civita connection** `leviCivita g` of a metric of any signature. -/
theorem raychaudhuri_leviCivita {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    {x : M} (hgeo : ∀ᶠ q in 𝓝 x, leviCivita g V q (V q) = 0) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (expansionM (leviCivita g) V) x (V x) =
      -LinearMap.trace ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
          ((leviCivita g V x).comp (leviCivita g V x) :
            TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x) -
        (leviCivita g).ricciAt x (V x) (V x) :=
  raychaudhuri_manifold (leviCivita g) g ⟨leviCivita_torsion g, leviCivita_compat g⟩ hV hgeo

/-- **The focusing inequality on a manifold** (Kar–SenGupta, after (16)): for a Lorentzian metric, its Levi-Civita
connection and a smooth unit (`g(V, V) = -1` near `x`) geodesic (`∇_V V = 0` near `x`) vector field that is rotation-free at
`x` (`g(∇_u V, w) = g(∇_w V, u)`) with `Ric(V, V) ≥ 0` at `x`: `V(Θ) ≤ -Θ²/(n-1)` at `x`. -/
theorem raychaudhuri_focusing_manifold_at (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    {x : M} (hgeo : ∀ᶠ q in 𝓝 x, cov V q (V q) = 0) (hnorm : ∀ᶠ q in 𝓝 x, gL.g q (V q) (V q) = -1) (hn : 1 < n)
    (hrot : ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, gL.g x (cov V x u) w = gL.g x (cov V x w) u)
    (hR : 0 ≤ cov.ricciAt x (V x) (V x)) :
    expansionDeriv cov V x ≤ -(expansionM cov V x) ^ 2 / (n - 1) := by
  set g := gL.toNondegMetric
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hx0 : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) = x :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hxs
  have hy0 : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hxs
  have hmd : ∀ q, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q :=
    fun q => (hV q).mdifferentiableAt (by simp)
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1
    ((hgeo.and hnorm).and ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hxs))
  set U := (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target ∩ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm ⁻¹' W with hU
  have hUo : IsOpen U :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hWo
  have hy0U : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ U := ⟨hy0, by simp only [mem_preimage, hx0]; exact hxW⟩
  have hgL : IsLorentzianCoordMetric (g.coordMetric x) U :=
    (gL.isLorentzianCoordMetric_coordMetric x).of_subset hUo inter_subset_left
  have hvU : ∀ a, ContDiffOn ℝ ∞ (fun y => chartComp x V y a) U := fun a =>
    (contDiffOn_chartComp hV x a).mono inter_subset_left
  have hgeoU : ∀ y ∈ U, ∀ d, ∑ c, chartComp x V y c * covD (g.coordMetric x) (chartComp x V) d c y = 0 := by
    intro y hy d
    have hq := hWsub hy.2
    have e := hv_cov_eq x cov g h hy.1 (hmd _) (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y))
    have hvV : hv x _ (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) = chartComp x V y := rfl
    rw [hq.1.1, hvV] at e
    have e2 := congrFun e d
    have h0 : hv x ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y) (0 : TangentSpace 𝓘(ℝ, Fin n → ℝ) _) = 0 :=
      ((tTriv (E := Fin n → ℝ) x).linear ℝ (symm_mem_chartTriv_baseSet x hy.1)).map_zero
    rw [h0] at e2
    simp only [Pi.zero_apply, Matrix.mulVec, dotProduct, covDMat, Matrix.of_apply] at e2
    rw [e2]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  have hnormU : ∀ y ∈ U, chartComp x V y ⬝ᵥ (g.coordMetric x y *ᵥ chartComp x V y) = -1 := by
    intro y hy
    have hq := hWsub hy.2
    have e := g_hv x g hy.1 (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y))
    have hc : chartComp x V y = hv x _ (V ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)) := rfl
    rw [hc, ← e]
    exact hq.1.2
  have hvx : hv x x (V x) = chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    simp only [chartComp, hx0]; rfl
  have hω := rotation_chart_eq_zero cov g h (hmd x) hrot
  have hRc : 0 ≤ ∑ s, ∑ t, ricci (g.coordMetric x) s t (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) *
      chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) s * chartComp x V (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) t := by
    rw [← hvx, ← ricciAt_hv' x cov g h hxs (V x)]; exact hR
  have key := raychaudhuri_focusing_at hvU hgeoU hnormU hgL hy0U hn hω hRc
  unfold expansionDeriv
  rw [mfderiv_expansionM cov g h hV x, expansionM_eq cov g h hV x hxs]
  exact key

set_option backward.isDefEq.respectTransparency false in
/-- **Geodesic focusing on a manifold** (Kar–SenGupta, after (16): zero rotation and `R_ab vᵃ vᵇ ≥ 0`): for a Lorentzian
metric with its Levi-Civita connection and a smooth vector field `V`, along an integral curve `γ` of `V` (`γ' = V(γ)`) on
`[0, L)` near which `V` is unit and geodesic, rotation-free with `Ric(V, V) ≥ 0` along `γ`, that starts converging
(`Θ(γ(0)) < 0`): `L ≤ (n-1)/|Θ(γ(0))|`, so the expansion cannot stay finite along `γ` beyond that parameter. -/
theorem raychaudhuri_focusing_manifold (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (hn : 1 < n) {γ : ℝ → M} {L : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u)
    (hR : ∀ s ∈ Ico 0 L, 0 ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s)))
    (h0 : expansionM cov V (γ 0) < 0) : L ≤ (n - 1) / |expansionM cov V (γ 0)| := by
  have hm : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  refine focusing (Θ := fun s => expansionM cov V (γ s)) (Θ' := fun s => expansionDeriv cov V (γ s)) hm ?_ ?_ h0
  · intro s hs
    have h1 := (mdifferentiableAt_expansionM cov gL.toNondegMetric h hV (γ s)).hasMFDerivAt
    show HasDerivAt (expansionM cov V ∘ γ) (expansionDeriv cov V (γ s)) s
    rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
    apply (h1.comp s (hγ s hs)).congr_mfderiv
    rw [ContinuousLinearMap.ext_iff]
    intro a
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul]
    rfl
  · intro s hs
    exact raychaudhuri_focusing_manifold_at cov gL h hV (hgeo s hs) (hnorm s hs) hn (hrot s hs) (hR s hs)

end Manifold

end Lightlike
