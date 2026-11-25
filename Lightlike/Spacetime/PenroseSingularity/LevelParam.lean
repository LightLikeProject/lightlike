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

/-- **The local inverse of a smooth map is smooth on a neighbourhood** (not only at the point). -/
theorem eventually_contDiffAt_localInverse {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [CompleteSpace E] [CompleteSpace E'] {Φ : E → E'} {x₀ : E} {U : Set E} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hΦ : ContDiffOn ℝ ∞ Φ U) {Feq : E ≃L[ℝ] E'} (hd : HasFDerivAt Φ (Feq : E →L[ℝ] E') x₀)
    (hc : ContDiffAt ℝ ∞ Φ x₀) (hn0 : (∞ : WithTop ℕ∞) ≠ 0) :
    ∀ᶠ y in nhds (Φ x₀), ContDiffAt ℝ ∞ (hc.localInverse hd hn0) y := by
  set e := hc.toOpenPartialHomeomorph Φ hd hn0 with he
  have hsymm : hc.localInverse hd hn0 = e.symm := rfl
  rw [hsymm]
  have hxs : x₀ ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd hn0
  have hyt : Φ x₀ ∈ e.target := hc.image_mem_toOpenPartialHomeomorph_target hd hn0
  -- the derivative of `Φ` is invertible near `x₀`
  have hfc : ContinuousAt (fderiv ℝ Φ) x₀ := by
    have : ContDiffAt ℝ 1 Φ x₀ := hc.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact (this.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hopen := (ContinuousLinearEquiv.isOpen (𝕜 := ℝ) (E := E) (F := E'))
  have hder : HasFDerivAt Φ (Feq : E →L[ℝ] E') x₀ := hd
  have hmem : fderiv ℝ Φ x₀ ∈ Set.range ((↑) : (E ≃L[ℝ] E') → E →L[ℝ] E') := ⟨Feq, hder.fderiv.symm⟩
  have hnb : ∀ᶠ a in nhds x₀, fderiv ℝ Φ a ∈ Set.range ((↑) : (E ≃L[ℝ] E') → E →L[ℝ] E') :=
    hfc.eventually (hopen.mem_nhds hmem)
  have hcont : ContinuousAt e.symm (Φ x₀) := e.continuousAt_symm hyt
  have hsx : e.symm (Φ x₀) = x₀ := by
    have := e.left_inv hxs
    simpa [he] using this
  have hev : ∀ᶠ y in nhds (Φ x₀), e.symm y ∈ U ∧ fderiv ℝ Φ (e.symm y) ∈
      Set.range ((↑) : (E ≃L[ℝ] E') → E →L[ℝ] E') := by
    have h1 : ∀ᶠ a in nhds x₀, a ∈ U ∧ fderiv ℝ Φ a ∈ Set.range ((↑) : (E ≃L[ℝ] E') → E →L[ℝ] E') :=
      (Filter.eventually_of_mem (hU.mem_nhds hx₀) fun a ha => ha).and hnb
    exact hcont.eventually (by rw [hsx]; exact h1)
  filter_upwards [hev, e.open_target.mem_nhds hyt] with y ⟨hyU, ⟨f₀', hf₀'⟩⟩ hyt'
  have hΦa : ContDiffAt ℝ ∞ Φ (e.symm y) := hΦ.contDiffAt (hU.mem_nhds hyU)
  have hdiff : HasFDerivAt Φ (f₀' : E →L[ℝ] E') (e.symm y) := by
    rw [hf₀']; exact (hΦa.differentiableAt (by simp)).hasFDerivAt
  exact e.contDiffAt_symm hyt' hdiff hΦa

theorem exists_level_param {m : ℕ} (hdim : finrank ℝ E = finrank ℝ F + m) {f : E → F} {x₀ : E} {U : Set E}
    (hU : IsOpen U) (hx₀ : x₀ ∈ U) (hfU : ContDiffOn ℝ ∞ f U) (hA : Function.Surjective (fderiv ℝ f x₀)) :
    ∃ p : (Fin m → ℝ) → E, (∃ V : Set (Fin m → ℝ), IsOpen V ∧ (0 : Fin m → ℝ) ∈ V ∧ ContDiffOn ℝ ∞ p V) ∧
      ContDiffAt ℝ ∞ p 0 ∧ p 0 = x₀ ∧ (∀ᶠ σ in nhds (0 : Fin m → ℝ), f (p σ) = f x₀) ∧
      Function.Injective (fderiv ℝ p 0) ∧
      (∀ v, fderiv ℝ f x₀ v = 0 ↔ ∃ u, fderiv ℝ p 0 u = v) := by
  classical
  have hf : ContDiffAt ℝ ∞ f x₀ := hfU.contDiffAt (hU.mem_nhds hx₀)
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
  have hΦU : ContDiffOn ℝ ∞ Φ U := hfU.prodMk PrC.contDiff.contDiffOn
  have hGev := eventually_contDiffAt_localInverse hU hx₀ hΦU (Feq := Feq) hΦd hΦc hn0
  obtain ⟨N, hNn, hNo, hN0⟩ := eventually_nhds_iff.1 hGev
  refine ⟨fun σ => G (aff σ), ⟨aff ⁻¹' N, hNo.preimage haffc, by simpa [haffΦ] using hN0, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    exact (hNn _ hσ).comp σ (by fun_prop) |>.contDiffWithinAt
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
