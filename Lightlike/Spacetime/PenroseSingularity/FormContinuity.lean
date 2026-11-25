import Lightlike.Spacetime.PenroseSingularity.FamilyTheta
import Lightlike.Spacetime.PenroseSingularity.SurfaceParam

/-!
# The fundamental forms of a parametrised surface in a chart (G1-012, step 3)

For a smooth parametrisation `xS` of a surface and a smooth vector field `k`, the matrices
`Q_ij = g(∂_i xS, ∂_j xS)` and `C_ij = g(∇_{∂_i xS} k, ∂_j xS)` are, in a fixed chart at `x₀ = xS 0`, given by
continuous expressions in `σ`; hence `tr (Q⁻¹ Cᵀ)` is continuous at `0` when `Q 0` is invertible.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The first fundamental form in a chart. -/
theorem Qx_eq_chart (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) {xS : (Fin m → ℝ) → M}
    {σ : Fin m → ℝ} (hxS : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ)
    (hsrc : xS σ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (a b : Fin m → ℝ) :
    g.g (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ a)
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ b) =
    gpairAt (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ))
      (fderiv ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ')) σ a)
      (fderiv ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ')) σ b) := by
  rw [g_eq_gpair g x₀ (xS σ) hsrc, fderiv_coord x₀ hxS hsrc a, fderiv_coord x₀ hxS hsrc b]

/-- The second fundamental form in a chart. -/
theorem Cx_eq_chart (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (x₀ : M) {xS : (Fin m → ℝ) → M}
    {k : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y} {σ : Fin m → ℝ}
    (hxS : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ)
    (hk : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (xS σ))
    (hb : xS σ ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (a b : Fin m → ℝ) :
    g.g (xS σ) (cov k (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ a))
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ b) =
    gpairAt (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ))
      (fderiv ℝ (fun σ' => hat (E := Fin n → ℝ) x₀ k (xS σ')) σ a +
        Lightlike.Geodesic.gammaApply (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ))
          (hat (E := Fin n → ℝ) x₀ k (xS σ))
          (fderiv ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ')) σ a))
      (fderiv ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ (xS σ')) σ b) := by
  have hsrc : xS σ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
    rw [extChartAt_source]; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hb
  rw [g_eq_gpair g x₀ (xS σ) hsrc, fderiv_coord x₀ hxS hsrc b]
  congr 1
  -- the components of `∇_a k`
  have hcov := hat_cov cov x₀ hb hk (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ a)
  have hhat : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) x₀ k) (xS σ) :=
    (mdiffAt_hat_iff x₀ k hb).1 hk
  have hfd := fderiv_comp_mfderiv hhat hxS a
  have hga := fderiv_coord x₀ hxS hsrc a
  have hGam := gamHat_eq_gammaApply g hLC x₀ hb (hat (E := Fin n → ℝ) x₀ k (xS σ))
    (hv (E := Fin n → ℝ) x₀ (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ a))
  show hv (E := Fin n → ℝ) x₀ (xS σ) _ = _
  rw [hcov, hGam, hfd, hga]
  rfl

/-- `gpairAt` is continuous in the point and the two vectors. -/
theorem continuousAt_gpairAt {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Lightlike.IsCoordMetric g U) {α : Type*} [TopologicalSpace α] {x u v : α → Fin n → ℝ} {a : α}
    (hx : ContinuousAt x a) (hu : ContinuousAt u a) (hv : ContinuousAt v a) (hxU : x a ∈ U) :
    ContinuousAt (fun s => gpairAt g (x s) (u s) (v s)) a := by
  unfold gpairAt
  have key : ∀ p q : Fin n, ContinuousAt (fun s => g (x s) p q * u s p * v s q) a := fun p q => by
    have hgc : ContinuousAt (fun z => g z p q) (x a) :=
      ((hg.smooth p q).continuousOn).continuousAt (hg.isOpen.mem_nhds hxU)
    exact ((hgc.comp hx).mul ((continuous_apply p).continuousAt.comp hu)).mul
      ((continuous_apply q).continuousAt.comp hv)
  exact tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => key p q

/-- `gammaApply` is continuous in the point and the two vectors. -/
theorem continuousAt_gammaApply {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Lightlike.IsCoordMetric g U) {α : Type*} [TopologicalSpace α] {x u v : α → Fin n → ℝ} {a : α}
    (hx : ContinuousAt x a) (hu : ContinuousAt u a) (hv : ContinuousAt v a) (hxU : x a ∈ U) :
    ContinuousAt (fun s => Lightlike.Geodesic.gammaApply g (x s) (u s) (v s)) a := by
  rw [continuousAt_pi]
  intro i
  unfold Lightlike.Geodesic.gammaApply
  have key : ∀ p q : Fin n, ContinuousAt (fun s => Lightlike.christoffel g i p q (x s) * u s p * v s q) a :=
    fun p q => by
      have hgc : ContinuousAt (fun z => Lightlike.christoffel g i p q z) (x a) :=
        ((hg.contDiffOn_christoffel i p q).continuousOn).continuousAt (hg.isOpen.mem_nhds hxU)
      exact ((hgc.comp hx).mul ((continuous_apply p).continuousAt.comp hu)).mul
        ((continuous_apply q).continuousAt.comp hv)
  exact tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => key p q

/-- **The entries of the fundamental forms are continuous at `0`.** -/
theorem continuousAt_forms (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) {xS : (Fin m → ℝ) → M} {Sg₀ : Set (Fin m → ℝ)}
    (hSo : IsOpen Sg₀) (h0 : (0 : Fin m → ℝ) ∈ Sg₀)
    (hsm : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ xS Sg₀)
    {k : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hk : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (a b : Fin m → ℝ) :
    ContinuousAt (fun σ => g.g (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ a)
        (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ b)) 0 ∧
    ContinuousAt (fun σ => g.g (xS σ)
        (cov k (xS σ) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ a))
        (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ b)) 0 := by
  classical
  set x₀ : M := xS 0 with hx₀
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ
  have hg : Lightlike.IsCoordMetric (g.coordMetric x₀) ψ.target :=
    g.toNondegMetric.isCoordMetric_coordMetric x₀
  have hsrc0 : x₀ ∈ ψ.source := mem_extChartAt_source x₀
  have hbs : ∀ y ∈ ψ.source, y ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet := fun y hy => by
    rw [extChartAt_source] at hy; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hy
  set O : Set (Fin m → ℝ) := Sg₀ ∩ xS ⁻¹' ψ.source with hO
  have hOo : IsOpen O := hsm.continuousOn.isOpen_inter_preimage hSo (isOpen_extChartAt_source x₀)
  have hO0 : (0 : Fin m → ℝ) ∈ O := ⟨h0, hsrc0⟩
  have hxd : ∀ σ ∈ O, MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ := fun σ hσ =>
    (hsm.contMDiffAt (hSo.mem_nhds hσ.1)).mdifferentiableAt (by simp)
  have hκ : ContDiffOn ℝ ∞ (fun σ => ψ (xS σ)) O := by
    have h1 : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (fun σ => ψ (xS σ)) O :=
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀)).comp (hsm.mono inter_subset_left)
        (fun σ hσ => by have h := hσ.2; rw [mem_preimage, hψ, extChartAt_source] at h; exact h)
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hkhat : ∀ y ∈ ψ.source, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
      (hat (E := Fin n → ℝ) x₀ k) y := fun y hy =>
    ((tTriv (E := Fin n → ℝ) x₀).contMDiffAt_section_iff (hbs y hy)).1 (hk.contMDiffAt)
  have hκh : ContDiffOn ℝ ∞ (fun σ => hat (E := Fin n → ℝ) x₀ k (xS σ)) O := by
    have h1 : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞
        (fun σ => hat (E := Fin n → ℝ) x₀ k (xS σ)) O := fun σ hσ =>
      ((hkhat _ hσ.2).comp σ (hsm.contMDiffAt (hSo.mem_nhds hσ.1))).contMDiffWithinAt
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hκc : ContinuousAt (fun σ => ψ (xS σ)) 0 := hκ.continuousOn.continuousAt (hOo.mem_nhds hO0)
  have hκhc : ContinuousAt (fun σ => hat (E := Fin n → ℝ) x₀ k (xS σ)) 0 :=
    hκh.continuousOn.continuousAt (hOo.mem_nhds hO0)
  have hdκ : ∀ v : Fin m → ℝ, ContinuousAt (fun σ => fderiv ℝ (fun σ' => ψ (xS σ')) σ v) 0 := fun v =>
    ((hκ.continuousOn_fderiv_of_isOpen hOo (by simp)).continuousAt (hOo.mem_nhds hO0)).clm_apply
      continuousAt_const
  have hdκh : ∀ v : Fin m → ℝ,
      ContinuousAt (fun σ => fderiv ℝ (fun σ' => hat (E := Fin n → ℝ) x₀ k (xS σ')) σ v) 0 := fun v =>
    ((hκh.continuousOn_fderiv_of_isOpen hOo (by simp)).continuousAt (hOo.mem_nhds hO0)).clm_apply
      continuousAt_const
  have hxU : ψ (xS 0) ∈ ψ.target := ψ.map_source hsrc0
  refine ⟨?_, ?_⟩
  · have hc := continuousAt_gpairAt hg hκc (hdκ a) (hdκ b) hxU
    refine hc.congr ?_
    filter_upwards [hOo.mem_nhds hO0] with σ hσ
    exact (Qx_eq_chart g x₀ (hxd σ hσ) hσ.2 a b).symm
  · have hu : ContinuousAt (fun σ => fderiv ℝ (fun σ' => hat (E := Fin n → ℝ) x₀ k (xS σ')) σ a +
        Lightlike.Geodesic.gammaApply (g.coordMetric x₀) (ψ (xS σ)) (hat (E := Fin n → ℝ) x₀ k (xS σ))
          (fderiv ℝ (fun σ' => ψ (xS σ')) σ a)) 0 :=
      (hdκh a).add (continuousAt_gammaApply hg hκc hκhc (hdκ a) hxU)
    have hc := continuousAt_gpairAt hg hκc hu (hdκ b) hxU
    refine hc.congr ?_
    filter_upwards [hOo.mem_nhds hO0] with σ hσ
    have hk' : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
        (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (xS σ) :=
      (hk.contMDiffAt).mdifferentiableAt (by simp)
    exact (Cx_eq_chart g hLC x₀ (hxd σ hσ) hk' (hbs _ hσ.2) a b).symm

end Lightlike.Penrose
