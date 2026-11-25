import Lightlike.Spacetime.PenroseSingularity.GeneratorFamily
import Lightlike.Spacetime.PenroseSingularity.SurfaceParam

/-!
# The flow family of null normals through a generator (G1-012, step D3b wiring)

For a null geodesic `γ` on `[0, L]` starting on a regular level set `f⁻¹(0)` with initial velocity `μ • k (γ 0)`
for a smooth vector field `k`, the parametrisation of the level set near `γ 0` and the geodesics with initial
phases `(xS σ, μ • k (xS σ))` form a flow family containing `γ`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **The flow family of a smooth field along a level set, through a generator.** -/
theorem exists_normal_family (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (hn : 2 ≤ n) {f : M → Fin 2 → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f)
    {k : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hk : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    {γ : ℝ → M} {L : ℝ} (hL : 0 ≤ L) (hγ : IsNullGeodesicOn g γ (Icc 0 L)) (hx : f (γ 0) = 0)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (γ 0))) {μ : ℝ}
    (hv : (phase (n := n) γ 0).snd = μ • k (γ 0)) :
    ∃ (xS : (Fin (n - 2) → ℝ) → M) (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
      (zS : (Fin (n - 2) → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M)
      (Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (J : Set ℝ) (Sg : Set (Fin (n - 2) → ℝ)),
      FlowFamily g Γ zS Nz J Sg ∧ (0 : Fin (n - 2) → ℝ) ∈ Sg ∧ Icc 0 L ⊆ J ∧
      (∀ t ∈ Icc 0 L, Γ (zS 0) t = γ t) ∧
      (∀ σ ∈ Sg, zS σ = (⟨xS σ, μ • k (xS σ)⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧
      (∀ σ ∈ Sg, f (xS σ) = 0) ∧
      ContMDiffOn 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ xS Sg ∧ xS 0 = γ 0 ∧
      Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0) ∧
      ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ 0),
        mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (γ 0) v = 0 ↔
          ∃ u, mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 u = v := by
  classical
  obtain ⟨xS, Sg₀, hSo, hS0, hsm, hx0, hfx, hinj, hker, -⟩ := exists_surface_param hn hf hx hsurj
  set zS : (Fin (n - 2) → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M :=
    fun σ => ⟨xS σ, μ • k (xS σ)⟩ with hzS
  have hkμ : ∀ q : M, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, μ • k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q := fun q =>
    ContMDiffAt.smul_section contMDiffAt_const (hk.contMDiffAt)
  have hzSm : ContMDiffOn 𝓘(ℝ, Fin (n - 2) → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞ zS Sg₀ := by
    intro σ hσ
    exact ((hkμ (xS σ)).comp σ ((hsm.contMDiffAt (hSo.mem_nhds hσ)))).contMDiffWithinAt
  have hz0 : zS 0 = phase (n := n) γ 0 := by
    have hdep : ∀ y : M, y = γ 0 →
        (⟨y, μ • k y⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) = ⟨γ 0, μ • k (γ 0)⟩ := by
      rintro y rfl; rfl
    have h1 : zS 0 = ⟨γ 0, μ • k (γ 0)⟩ := hdep _ hx0
    rw [h1]
    exact congrArg (Bundle.TotalSpace.mk (γ 0)) hv.symm
  obtain ⟨Γ, Nz, J, Sg, hF, hσ, hJ, hSg, hΓ⟩ := exists_flowFamily_of_generator g hL hγ hSo hzSm hS0 hz0
  exact ⟨xS, Γ, zS, Nz, J, Sg, hF, hσ, hJ, hΓ, fun σ _ => rfl, fun σ hσ => hfx σ (hSg hσ),
    hsm.mono hSg, hx0, hinj, hker⟩

end Lightlike.Penrose
