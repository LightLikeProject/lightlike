import Lightlike.Spacetime.PenroseSingularity.FamilyJacobi
import Lightlike.Spacetime.PenroseSingularity.JacobiRic

/-!
# The Gram matrix of a flow family (G1-012, step D3b wiring)

For a flow family `F (σ, t) = Γ (zS σ) t`, the matrix `Qg σ t = g(∂_{σ_i} F, ∂_{σ_j} F)` is an intrinsic
function of `t`. In a chart at `Γ (zS σ) t₀` it agrees with the Gram matrix `gramQ` of the chart Jacobi fields.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- The partial derivative of a two-variable map in the second variable. -/
theorem fderiv_slice_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {H : ℝ × E → F} {t : ℝ} {σ : E}
    (hH : DifferentiableAt ℝ H (t, σ)) (e : E) :
    fderiv ℝ (fun σ' => H (t, σ')) σ e = fderiv ℝ H (t, σ) (0, e) := by
  have hc : HasFDerivAt (fun σ' : E => ((t, σ') : ℝ × E))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) σ :=
    (hasFDerivAt_const t σ).prodMk (hasFDerivAt_id σ)
  have := hH.hasFDerivAt.comp σ hc
  show fderiv ℝ (H ∘ Prod.mk t) σ e = _
  rw [this.fderiv]
  simp

/-- The intrinsic Gram matrix of the `σ`-derivatives of the flow family. -/
def Qg (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
    (zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M) (σ : Fin m → ℝ) (t : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => g.g (Γ (zS σ) t)
    (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ (Pi.single i 1))
    (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') t) σ (Pi.single j 1))

variable {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)}

/-- **Chart data of the flow family at `(t, σ)`**: a chart family together with the identification of the
intrinsic Gram matrix with the chart Gram matrix. -/
theorem FlowFamily.exists_chart_gram (hF : FlowFamily g Γ zS Nz J Sg)
    (hk : ∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0) {σ : Fin m → ℝ} (hσ : σ ∈ Sg)
    {t : ℝ} (ht : t ∈ J) :
    ∃ W : Set (ℝ × (Fin m → ℝ)), (t, σ) ∈ W ∧
      ChartFamily (g.coordMetric (Γ (zS σ) t)) (extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t)).target
        (fun p : ℝ × (Fin m → ℝ) => extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) W ∧
      (∀ t', (t', σ) ∈ W →
        Qg g Γ zS σ t' = gramQ (g.coordMetric (Γ (zS σ) t))
          (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS σ) s))
          (fun i s => fderiv ℝ (fun p : ℝ × (Fin m → ℝ) =>
            extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) (s, σ) (0, Pi.single i 1)) t') ∧
      (∀ q ∈ W, q.2 ∈ Sg ∧ q.1 ∈ J ∧
        Γ (zS q.2) q.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t)).source ∧
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (Γ (zS σ) t) (phase (n := n) (Γ (zS q.2)) q.1)).2 =
          fderiv ℝ (fun p : ℝ × (Fin m → ℝ) =>
            extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) q (1, 0) ∧
        ∀ e : Fin m → ℝ, fderiv ℝ (fun p : ℝ × (Fin m → ℝ) =>
            extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) q (0, e) =
          (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (Γ (zS σ) t) ⟨Γ (zS q.2) q.1,
            mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') q.1) q.2 e⟩).2) := by
  obtain ⟨W, hW0, hCF, hvel⟩ := exists_chartFamily g (Γ (zS σ) t) hF.isOpen_J hF.isOpen_Sg hF.geo
    hF.smooth_flow hF.smooth_init hF.mem_Nz (hF.null_of_zero hk) ht hσ rfl
  have hid : ∀ q ∈ W, q.2 ∈ Sg ∧ q.1 ∈ J ∧
        Γ (zS q.2) q.1 ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t)).source ∧
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (Γ (zS σ) t) (phase (n := n) (Γ (zS q.2)) q.1)).2 =
          fderiv ℝ (fun p : ℝ × (Fin m → ℝ) =>
            extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) q (1, 0) ∧
        ∀ e : Fin m → ℝ, fderiv ℝ (fun p : ℝ × (Fin m → ℝ) =>
            extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) q (0, e) =
          (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (Γ (zS σ) t) ⟨Γ (zS q.2) q.1,
            mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') q.1) q.2 e⟩).2 := by
    intro q hq
    obtain ⟨hσS, hqJ, hsrc, hv⟩ := hvel q hq
    refine ⟨hσS, hqJ, hsrc, hv, fun e => ?_⟩
    have hmd := hF.mdifferentiableAt_slice hσS hqJ
    have hdiffH : DifferentiableAt ℝ (fun p : ℝ × (Fin m → ℝ) =>
        extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) q :=
      (hCF.smooth.contDiffAt (hCF.isOpen.mem_nhds hq)).differentiableAt (by simp)
    rw [← fderiv_slice_snd (H := fun p : ℝ × (Fin m → ℝ) =>
      extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) hdiffH e]
    exact fderiv_coord (Γ (zS σ) t) hmd hsrc e
  refine ⟨W, hW0, hCF, fun t' ht' => ?_, hid⟩
  obtain ⟨-, htJ, hsrc, -⟩ := hvel _ ht'
  have hmd := hF.mdifferentiableAt_slice hσ htJ
  have hdiffH : DifferentiableAt ℝ (fun p : ℝ × (Fin m → ℝ) =>
      extChartAt 𝓘(ℝ, Fin n → ℝ) (Γ (zS σ) t) (Γ (zS p.2) p.1)) (t', σ) :=
    (hCF.smooth.contDiffAt (hCF.isOpen.mem_nhds ht')).differentiableAt (by simp)
  ext i j
  simp only [Qg, gramQ, Matrix.of_apply]
  rw [g_eq_gpair g (Γ (zS σ) t) _ hsrc]
  have hi := fderiv_coord (Γ (zS σ) t) hmd hsrc (Pi.single i 1)
  have hj := fderiv_coord (Γ (zS σ) t) hmd hsrc (Pi.single j 1)
  rw [← hi, ← hj, fderiv_slice_snd hdiffH, fderiv_slice_snd hdiffH]

/-- **Focusing from pointwise local data**: `gram_focusing` where the curvature matrix `ρ` is only
supplied locally at each time (it is determined by `Q` and `C`). -/
theorem gram_focusing_local (hm : 0 < m) {T : ℝ} {Q C : ℝ → Matrix (Fin m) (Fin m) ℝ}
    (hloc : ∀ t ∈ Ico 0 T, ∃ ρ : Matrix (Fin m) (Fin m) ℝ,
      (∀ i j, HasDerivAt (fun s => Q s i j) ((C t + (C t)ᵀ) i j) t) ∧
      (∀ i j, HasDerivAt (fun s => C s i j) ((-ρ + C t * (Q t)⁻¹ * (C t)ᵀ) i j) t) ∧
      (Q t).PosDef ∧ (C t)ᵀ = C t ∧ ρᵀ = ρ ∧ 0 ≤ Matrix.trace ((Q t)⁻¹ * ρ))
    (h0 : Matrix.trace ((Q 0)⁻¹ * (C 0)ᵀ) < 0) :
    T ≤ m / |Matrix.trace ((Q 0)⁻¹ * (C 0)ᵀ)| := by
  classical
  choose! ρ hρ using hloc
  exact gram_focusing hm (ρ := ρ) (fun t ht => (hρ t ht).1) (fun t ht => (hρ t ht).2.1)
    (fun t ht => (hρ t ht).2.2.1) (fun t ht => (hρ t ht).2.2.2.1)
    (fun t ht => (hρ t ht).2.2.2.2.1) (fun t ht => (hρ t ht).2.2.2.2.2) h0

/-- A Jacobi field orthogonal to the velocity has covariant derivative orthogonal to it. -/
theorem gpair_vel_cov_zero {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Lightlike.IsCoordMetric g U) {γ w J P : ℝ → Fin n → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hJ : Lightlike.Geodesic.IsJacobiOn g γ w J P I) (hγU : ∀ t ∈ I, γ t ∈ U)
    (hwJ : ∀ s ∈ I, gpairAt g (γ s) (w s) (J s) = 0) :
    ∀ t ∈ I, gpairAt g (γ t) (w t) (P t) = 0 := by
  intro t ht
  have hγ : HasDerivAt γ (w t) t := hJ.geodesic.pos t ht
  have h := hasDerivAt_gpair hg hγ (hγU t ht) (hJ.geodesic.vel t ht) (hJ.deriv_field t ht)
  have hc : HasDerivAt (fun s => gpairAt g (γ s) (w s) (J s)) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hI.mem_nhds ht) hwJ)
  have hu := h.unique hc
  have hcw : (fun a => covDAlong g (γ t) (w t) (w t) (Lightlike.Geodesic.accel g (γ t) (w t)) a) = 0 := by
    funext a
    simp [covDAlong, Lightlike.Geodesic.accel]
  rw [hcw, covDAlong_of_deriv] at hu
  have h0 : gpairAt g (γ t) (0 : Fin n → ℝ) (J t) = 0 := by simp [gpairAt]
  rw [h0, zero_add] at hu
  exact hu

end Lightlike.Penrose
