import Lightlike.Spacetime.PenroseSingularity.FamilyFrame
import Lightlike.Spacetime.PenroseSingularity.TrappedSpacelike
import Lightlike.Spacetime.PenroseSingularity.FamilyInit

/-!
# The initial expansion of a null normal family (G1-012, step D3b wiring)

For a parametrised piece of a trapped spacelike surface, the matrix `Q = g(u_i, u_j)` is positive definite and
`tr (Q⁻¹ Cᵀ)`, with `C = g(∇_{u_i} k, u_j)`, is the expansion of `k` over an orthonormal frame, hence negative.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix MatrixOrder

noncomputable section

namespace Lightlike.Penrose

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- **The expansion of a null normal over a parametrised piece of a trapped spacelike surface is negative**:
for linearly independent tangent vectors `u_i` in `ker df_x`, `Q = g(u_i, u_j)` is positive definite and
`tr (Q⁻¹ Cᵀ) < 0`, with `C_ij = g(∇_{u_i} k, u_j)`. -/
theorem trace_neg_of_trapped (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (f : M → Fin 2 → ℝ)
    (k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (x : M)
    (hspace : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    (hexp : ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
      (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) → frameExpansion g cov k x e < 0)
    (hm : m = n - 2) (u : Fin m → TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (hu : LinearIndependent ℝ u)
    (huK : ∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (u i) = 0) :
    (Matrix.of fun i j => g.g x (u i) (u j)).PosDef ∧
      ∃ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) ∧
        (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) ∧
        Matrix.trace ((Matrix.of fun i j => g.g x (u i) (u j))⁻¹ *
          (Matrix.of fun i j => g.g x (cov k x (u i)) (u j))ᵀ) = frameExpansion g cov k x e := by
  subst hm
  obtain ⟨hQ, e, heK, hortho, hsum⟩ := exists_frame_trace
    (ContinuousLinearMap.toLinearMap₁₂ (g.g x))
    (ContinuousLinearMap.toLinearMap₁₂ ((g.g x).comp (cov k x)))
    (fun v w => g.symm x v w)
    (LinearMap.ker (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x).toLinearMap)
    u hu (fun i => LinearMap.mem_ker.2 (huK i)) (fun v hv hv0 => hspace v (LinearMap.mem_ker.1 hv) hv0)
  refine ⟨hQ, e, fun a => LinearMap.mem_ker.1 (heK a), hortho, ?_⟩
  refine hsum.symm.trans ?_
  simp [frameExpansion]

section Flow

variable [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]
  {gM : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
  {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M}
  {zS : (Fin m → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)}
  {J : Set ℝ} {Sg : Set (Fin m → ℝ)} {σ : Fin m → ℝ}

/-- **The initial expansion of a null normal flow family is negative**: `Q(0)` is positive definite and
`θ(0) = tr (Q⁻¹ Cᵀ)(0) < 0`, for a family starting on a trapped spacelike surface along a null normal. -/
theorem FlowFamily.theta0_neg {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita gM.toNondegMetric) (hF : FlowFamily gM Γ zS Nz J Sg) (hm : 0 < m)
    (hk0 : ∀ σ ∈ Sg, gM.g (zS σ).proj (zS σ).snd (zS σ).snd = 0)
    (hperp : ∀ σ ∈ Sg, ∀ j : Fin m, gM.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0)
    {xS : (Fin m → ℝ) → M} {k : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hz : ∀ σ' ∈ Sg, zS σ' = (⟨xS σ', k (xS σ')⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
    (hσ : σ ∈ Sg)
    (hk : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (xS σ))
    (hxS : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ))
    (f : M → Fin 2 → ℝ) (hfd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ))
    (hfx : ∀ᶠ σ' in nhds σ, f (xS σ') = 0)
    (hspace : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ),
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ) v = 0 → v ≠ 0 → 0 < gM.g (xS σ) v v)
    (hexp : ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ),
      (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ) (e i) = 0) →
      (∀ i j, gM.g (xS σ) (e i) (e j) = if i = j then 1 else 0) → frameExpansion gM cov k (xS σ) e < 0)
    (hmn : m = n - 2) :
    (Qg gM Γ zS σ 0).PosDef ∧ ∃ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ),
      (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ) (e i) = 0) ∧
      (∀ i j, gM.g (xS σ) (e i) (e j) = if i = j then 1 else 0) ∧
      Matrix.trace ((Qg gM Γ zS σ 0)⁻¹ * (Cg gM Γ zS σ 0)ᵀ) = frameExpansion gM cov k (xS σ) e ∧
      frameExpansion gM cov k (xS σ) e < 0 := by
  classical
  set u : Fin m → TangentSpace 𝓘(ℝ, Fin n → ℝ) (xS σ) :=
    fun i => mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ (Pi.single i 1) with hu
  have hQ : Qg gM Γ zS σ 0 = Matrix.of fun i j => gM.g (xS σ) (u i) (u j) := by
    ext i j; exact hF.Qg_zero_eq hz hσ i j
  have hC : Cg gM Γ zS σ 0 = Matrix.of fun i j => gM.g (xS σ) (cov k (xS σ) (u i)) (u j) := by
    ext i j; exact hF.Cg_zero_eq hLC hm hk0 hperp hz hσ hk hxS i j
  have hlin : LinearIndependent ℝ u := by
    have := (Pi.basisFun ℝ (Fin m)).linearIndependent.map'
      (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS σ).toLinearMap
      (LinearMap.ker_eq_bot.2 hinj)
    convert this using 1
    funext i
    have hb : (Pi.basisFun ℝ (Fin m)) i = Pi.single i 1 := by simp
    simp only [Function.comp_apply, hb]
    rfl
  have huK : ∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f (xS σ) (u i) = 0 := by
    intro i
    have hc := fderiv_comp_mfderiv hfd hxS (Pi.single i 1)
    have hev : (fun σ' => f (xS σ')) =ᶠ[nhds σ] fun _ => (0 : Fin 2 → ℝ) := hfx
    rw [hev.fderiv_eq] at hc
    have h0 : fderiv ℝ (fun _ : Fin m → ℝ => (0 : Fin 2 → ℝ)) σ (Pi.single i 1) = 0 := by simp
    exact hc.symm.trans h0
  obtain ⟨hpd, e, heK, hortho, htr⟩ := trace_neg_of_trapped gM cov f k (xS σ) hspace hexp hmn u hlin huK
  rw [hQ, hC]
  exact ⟨hpd, e, heK, hortho, htr, hexp e heK hortho⟩

end Flow

end Lightlike.Penrose
