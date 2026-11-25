import Lightlike.Spacetime.PenroseSingularity.LevelParam
import Lightlike.Spacetime.PenroseSingularity.FamilyInit

/-!
# A local parametrisation of a regular level set of a manifold (G1-012, step D3b wiring)

For a smooth `f : M → ℝ²` with surjective derivative at `x` and `f x = 0`, a chart at `x` and the
parametrisation of `LevelParam` give `xS : ℝ^(n-2) → M` smooth near `0` with `xS 0 = x`, `f ∘ xS = 0` near `0`,
injective derivative and `range (d xS) = ker (d f_x)`.
-/

open Set Filter Topology Manifold Module
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- **A local parametrisation of the zero level set.** -/
theorem exists_surface_param (hn : 2 ≤ n) {f : M → Fin 2 → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) {x : M} (hx : f x = 0)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x)) :
    ∃ (xS : (Fin (n - 2) → ℝ) → M) (Sg₀ : Set (Fin (n - 2) → ℝ)), IsOpen Sg₀ ∧ (0 : Fin (n - 2) → ℝ) ∈ Sg₀ ∧
      ContMDiffOn 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ xS Sg₀ ∧ xS 0 = x ∧ (∀ σ ∈ Sg₀, f (xS σ) = 0) ∧
      Function.Injective (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0) ∧
      ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 ↔
          ∃ u, mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 u = v := by
  classical
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  set F : (Fin n → ℝ) → (Fin 2 → ℝ) := fun y => f (ψ.symm y) with hF
  have hxs : x ∈ ψ.source := mem_extChartAt_source x
  have hψx : ψ x ∈ ψ.target := ψ.map_source hxs
  have hsymx : ψ.symm (ψ x) = x := ψ.left_inv hxs
  have htgt : ψ.target ∈ 𝓝 (ψ x) := extChartAt_target_mem_nhds x
  have hsymm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm (ψ x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt htgt
  have hFc : ContDiffAt ℝ ∞ F (ψ x) := by
    have h2 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f (ψ.symm (ψ x)) := by
      rw [hsymx]; exact hf.contMDiffAt
    exact contMDiffAt_iff_contDiffAt.1 (h2.comp (ψ x) hsymm)
  -- the derivative of the chart
  set D := mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ x with hD
  have hDinv : D.IsInvertible := isInvertible_mfderiv_extChartAt hxs
  have hDinj : Function.Injective D := by
    obtain ⟨e, he⟩ := hDinv
    rw [← he]; exact e.injective
  have hψd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ x :=
    mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hxs)
  have hFd : DifferentiableAt ℝ F (ψ x) := hFc.differentiableAt (by simp)
  have hfF : ∀ v, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = fderiv ℝ F (ψ x) (D v : Fin n → ℝ) := by
    intro v
    have hev : f =ᶠ[𝓝 x] fun y => F (ψ y) := by
      filter_upwards [(extChartAt_source_mem_nhds x : ψ.source ∈ 𝓝 x)] with y hy
      simp only [hF]; rw [ψ.left_inv hy]
    have hFm : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) F (ψ x) := hFd.mdifferentiableAt
    have h1 := hFm.hasMFDerivAt.comp x hψd.hasMFDerivAt
    have h2 := h1.congr_of_eventuallyEq hev
    rw [h2.mfderiv]
    simp only [ContinuousLinearMap.comp_apply]
    rw [mfderiv_eq_fderiv]
    rfl
  have hsurjF : Function.Surjective (fderiv ℝ F (ψ x)) := by
    intro y
    obtain ⟨v, hv⟩ := hsurj y
    exact ⟨D v, by rw [← hfF]; exact hv⟩
  have hdim : finrank ℝ (Fin n → ℝ) = finrank ℝ (Fin 2 → ℝ) + (n - 2) := by
    simp; omega
  have hFU : ContDiffOn ℝ ∞ F ψ.target := by
    have h1 : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ F ψ.target :=
      hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)
    exact contMDiffOn_iff_contDiffOn.1 h1
  have hFd' : Function.Surjective (fderiv ℝ F (ψ x)) := hsurjF
  obtain ⟨p, ⟨V, hVo, hV0, hpV⟩, hpc, hp0, hpF, hpinj, hpker⟩ :=
    exists_level_param hdim (isOpen_extChartAt_target x) hψx hFU hFd'
  obtain ⟨W, hWF, hWo, hW0⟩ := eventually_nhds_iff.1 hpF
  set Sg₀ : Set (Fin (n - 2) → ℝ) := V ∩ p ⁻¹' ψ.target ∩ W with hSg₀
  have hSo : IsOpen Sg₀ := ((hpV.continuousOn.isOpen_inter_preimage hVo (isOpen_extChartAt_target x)).inter hWo)
  have hS0 : (0 : Fin (n - 2) → ℝ) ∈ Sg₀ := ⟨⟨hV0, by rw [mem_preimage, hp0]; exact hψx⟩, hW0⟩
  set xS : (Fin (n - 2) → ℝ) → M := fun σ => ψ.symm (p σ) with hxS
  have hx0 : xS 0 = x := by simp [hxS, hp0, hsymx]
  have hsm : ContMDiffOn 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ xS Sg₀ :=
    (contMDiffOn_extChartAt_symm x).comp (hpV.contMDiffOn.mono fun σ hσ => hσ.1.1)
      (fun σ hσ => hσ.1.2)
  have hxd : MDifferentiableAt 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 :=
    (hsm.contMDiffAt (hSo.mem_nhds hS0)).mdifferentiableAt (by simp)
  have hψ' : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ (xS 0) := by rw [hx0]; exact hψd
  have hev : (fun σ => ψ (xS σ)) =ᶠ[𝓝 0] p := by
    filter_upwards [hSo.mem_nhds hS0] with σ hσ
    exact ψ.right_inv hσ.1.2
  have key : ∀ u, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ (xS 0) (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 u) = fderiv ℝ p 0 u := by
    intro u
    rw [← fderiv_comp_mfderiv hψ' hxd u, hev.fderiv_eq]
  have hDx : ∀ (y : M), y = x → ∀ w : Fin n → ℝ,
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ y w : Fin n → ℝ) = D w := by
    rintro y rfl w; rfl
  refine ⟨xS, Sg₀, hSo, hS0, hsm, hx0, ?_, ?_, ?_⟩
  · intro σ hσ
    show F (p σ) = 0
    rw [hWF σ hσ.2]; simp [hF, hsymx, hx]
  · intro u₁ u₂ h
    apply hpinj
    rw [← key u₁, ← key u₂, h]
  · intro v
    rw [hfF v]
    constructor
    · intro h
      obtain ⟨u, hu⟩ := (hpker (D v)).1 h
      refine ⟨u, hDinj ?_⟩
      exact ((hDx _ hx0 _).symm.trans (key u)).trans hu
    · rintro ⟨u, hu⟩
      refine (hpker (D v)).2 ⟨u, ?_⟩
      exact (key u).symm.trans ((hDx _ hx0 _).trans (congrArg D hu))

end Lightlike.Penrose
