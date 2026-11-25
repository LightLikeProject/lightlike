import Mathlib

/-!
# A smooth local parametrisation of a regular level set (G1-012, step D3b wiring)

For a smooth `f : E → F` between finite-dimensional real spaces with surjective derivative at `x₀`, the
level set `f⁻¹(f x₀)` is locally the image of a smooth map `p` from `ℝ^m` (`m = dim E - dim F`) with
`p 0 = x₀` whose derivative is a linear isomorphism onto `ker f'(x₀)` (the inverse function theorem for
`x ↦ (f x, Π x)`).
-/

open Module
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Penrose

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_level_param {m : ℕ} (hdim : finrank ℝ E = finrank ℝ F + m) {f : E → F} {x₀ : E}
    (hf : ContDiffAt ℝ ∞ f x₀) (hA : Function.Surjective (fderiv ℝ f x₀)) :
    ∃ p : (Fin m → ℝ) → E, ContDiffAt ℝ ∞ p 0 ∧ p 0 = x₀ ∧ (∀ᶠ σ in nhds (0 : Fin m → ℝ), f (p σ) = f x₀) ∧
      Function.Injective (fderiv ℝ p 0) ∧
      (∀ v, fderiv ℝ f x₀ v = 0 ↔ ∃ u, fderiv ℝ p 0 u = v) := by
  classical
  set A : E →L[ℝ] F := fderiv ℝ f x₀ with hAdef
  -- the kernel has dimension `m`
  have hrank : finrank ℝ (LinearMap.ker (A : E →ₗ[ℝ] F)) = m := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (A : E →ₗ[ℝ] F)
    have h2 : LinearMap.range (A : E →ₗ[ℝ] F) = ⊤ := LinearMap.range_eq_top.2 hA
    rw [h2, finrank_top] at h1
    omega
  have hker : finrank ℝ (Fin m → ℝ) = finrank ℝ (LinearMap.ker (A : E →ₗ[ℝ] F)) := by
    rw [hrank]; simp
  let e : (Fin m → ℝ) ≃ₗ[ℝ] LinearMap.ker (A : E →ₗ[ℝ] F) := LinearEquiv.ofFinrankEq _ _ hker
  let ι : (Fin m → ℝ) →ₗ[ℝ] E := (LinearMap.ker (A : E →ₗ[ℝ] F)).subtype ∘ₗ e.toLinearMap
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  obtain ⟨Pr, hPr⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 hι)
  set PrC : E →L[ℝ] (Fin m → ℝ) := LinearMap.toContinuousLinearMap Pr with hPrC
  set Fd : E →L[ℝ] F × (Fin m → ℝ) := A.prod PrC with hFd
  have hinj : Function.Injective Fd := by
    refine (injective_iff_map_eq_zero Fd).2 fun v hv => ?_
    have h1 : A v = 0 := congrArg Prod.fst hv
    have h2 : PrC v = 0 := congrArg Prod.snd hv
    have hvk : v ∈ LinearMap.ker (A : E →ₗ[ℝ] F) := h1
    obtain ⟨u, hu⟩ := e.surjective ⟨v, hvk⟩
    have hvu : v = ι u := by
      have := congrArg Subtype.val hu
      simpa [ι] using this.symm
    have hPv : Pr (ι u) = 0 := by rw [← hvu]; exact h2
    have hu0 : u = 0 := by
      have := LinearMap.congr_fun hPr u
      simpa [hPv] using this.symm
    rw [hvu, hu0]; simp
  have hsurj : Function.Surjective Fd :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (Fd : E →ₗ[ℝ] F × (Fin m → ℝ))) (by rw [hdim]; simp)).1 hinj
  let Feq : E ≃L[ℝ] F × (Fin m → ℝ) :=
    (LinearEquiv.ofBijective (Fd : E →ₗ[ℝ] F × (Fin m → ℝ)) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  set Φ : E → F × (Fin m → ℝ) := fun x => (f x, PrC x) with hΦ
  have hΦd : HasFDerivAt Φ (Feq : E →L[ℝ] F × (Fin m → ℝ)) x₀ := by
    have := hf.differentiableAt (by simp) |>.hasFDerivAt.prodMk PrC.hasFDerivAt
    exact this
  have hΦc : ContDiffAt ℝ ∞ Φ x₀ := hf.prodMk PrC.contDiff.contDiffAt
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict : HasStrictFDerivAt Φ (Feq : E →L[ℝ] F × (Fin m → ℝ)) x₀ := hΦc.hasStrictFDerivAt' hΦd hn0
  set G : F × (Fin m → ℝ) → E := hΦc.localInverse hΦd hn0 with hG
  have hGc : ContDiffAt ℝ ∞ G (Φ x₀) := hΦc.to_localInverse hΦd hn0
  have hGd : HasFDerivAt G (Feq.symm : F × (Fin m → ℝ) →L[ℝ] E) (Φ x₀) := hstrict.to_localInverse.hasFDerivAt
  have hGΦ : G (Φ x₀) = x₀ := hΦc.localInverse_apply_image hΦd hn0
  have hGr : ∀ᶠ y in nhds (Φ x₀), Φ (G y) = y := hstrict.eventually_right_inverse
  -- the parametrisation
  set aff : (Fin m → ℝ) → F × (Fin m → ℝ) := fun σ => (f x₀, PrC x₀ + σ) with haff
  have haffΦ : aff 0 = Φ x₀ := by simp [haff, hΦ]
  have haffc : Continuous aff := by fun_prop
  have haffd : HasFDerivAt aff ((ContinuousLinearMap.inr ℝ F (Fin m → ℝ)) : (Fin m → ℝ) →L[ℝ] F × (Fin m → ℝ)) 0 := by
    have : HasFDerivAt (fun σ : Fin m → ℝ => ((f x₀, PrC x₀) : F × (Fin m → ℝ)) + (0, σ))
        (ContinuousLinearMap.inr ℝ F (Fin m → ℝ)) 0 := by
      exact ((ContinuousLinearMap.inr ℝ F (Fin m → ℝ)).hasFDerivAt).const_add _
    convert this using 1
    funext σ
    simp [haff]
  refine ⟨fun σ => G (aff σ), ?_, ?_, ?_, ?_, ?_⟩
  · have h2 : ContDiffAt ℝ ∞ aff 0 := by fun_prop
    rw [← haffΦ] at hGc
    exact hGc.comp 0 h2
  · simp [haffΦ, hGΦ]
  · have : ∀ᶠ σ in nhds (0 : Fin m → ℝ), Φ (G (aff σ)) = aff σ :=
      (haffc.continuousAt.eventually (by rw [haffΦ]; exact hGr))
    filter_upwards [this] with σ hσ
    have := congrArg Prod.fst hσ
    simpa [hΦ, haff] using this
  · have hd : HasFDerivAt (fun σ => G (aff σ))
        ((Feq.symm : F × (Fin m → ℝ) →L[ℝ] E).comp (ContinuousLinearMap.inr ℝ F (Fin m → ℝ))) 0 := by
      have hGd' : HasFDerivAt G (Feq.symm : F × (Fin m → ℝ) →L[ℝ] E) (aff 0) := by rw [haffΦ]; exact hGd
      exact hGd'.comp 0 haffd
    rw [hd.fderiv]
    intro u v huv
    have := Feq.symm.injective huv
    simpa using this
  · intro v
    have hd : HasFDerivAt (fun σ => G (aff σ))
        ((Feq.symm : F × (Fin m → ℝ) →L[ℝ] E).comp (ContinuousLinearMap.inr ℝ F (Fin m → ℝ))) 0 := by
      have hGd' : HasFDerivAt G (Feq.symm : F × (Fin m → ℝ) →L[ℝ] E) (aff 0) := by rw [haffΦ]; exact hGd
      exact hGd'.comp 0 haffd
    rw [hd.fderiv]
    constructor
    · intro hv
      refine ⟨PrC v, ?_⟩
      have h1 : Feq v = (0, PrC v) := by
        refine Prod.ext ?_ rfl
        simpa [hFd, Feq, hAdef] using hv
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      rw [← h1]; simp
    · rintro ⟨u, rfl⟩
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      have := Feq.apply_symm_apply (0, u)
      exact congrArg Prod.fst this

end Lightlike.Penrose
