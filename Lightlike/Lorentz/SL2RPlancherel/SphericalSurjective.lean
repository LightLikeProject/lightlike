import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PhiCutoff
import Lightlike.Lorentz.SL2RPlancherel.SphericalL2

/-!
# Surjectivity of the spherical Plancherel isometry for `SL(2,ℝ)`

`sphericalL2 : L²(1, ∞) →ₗᵢ L²(0, ∞)` is surjective (`surjective_sphericalL2`), hence a unitary
equivalence (`sphericalL2Equiv`).  An element `u` orthogonal to the range is orthogonal to every
`phiL2 h` with `h` even Schwartz (`phiL2_mem_range_of_even`); choosing `h` with `ĥ(ρ/2π)` equal to the
even extension of an arbitrary smooth compactly supported test function on `(0, ∞)`, one gets
`∫ φ · (√(ρ tanh πρ)/(2π)) · u = 0`, so `u = 0` almost everywhere.
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- An even smooth compactly supported real function `Ψ` is, rescaled by `2π`, the Fourier transform
of an even Schwartz function. -/
theorem exists_even_schwartz_fourier (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hc : HasCompactSupport Ψ)
    (he : ∀ x, Ψ (-x) = Ψ x) :
    ∃ h : SchwartzMap ℝ ℂ, (∀ t, h (-t) = h t) ∧
      ∀ ξ : ℝ, SchwartzMap.fourierTransformCLM ℂ h ξ = ((Ψ (2 * Real.pi * ξ) : ℝ) : ℂ) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set f : ℝ → ℂ := fun ξ => ((Ψ (2 * Real.pi * ξ) : ℝ) : ℂ) with hf
  have hfs : ContDiff ℝ ∞ f :=
    Complex.ofRealCLM.contDiff.comp (hΨ.comp (contDiff_const.mul contDiff_id))
  have hfc : HasCompactSupport f := by
    have h1 : HasCompactSupport (fun ξ : ℝ => Ψ (2 * Real.pi * ξ)) :=
      hc.comp_homeomorph (Homeomorph.mulLeft₀ (2 * Real.pi) (by positivity))
    exact h1.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  set G : SchwartzMap ℝ ℂ := hfc.toSchwartzMap hfs with hG
  have hGx : ∀ x, G x = f x := fun x => rfl
  have hGe : ∀ x, G (-x) = G x := by
    intro x
    rw [hGx, hGx, hf]
    simp only
    rw [mul_neg, he]
  set h : SchwartzMap ℝ ℂ := 𝓕⁻ G with hh
  have hev : ∀ t, 𝓕 (G : ℝ → ℂ) (-t) = 𝓕 (G : ℝ → ℂ) t := by
    intro t
    have := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) (G : ℝ → ℂ) t
    have e : (G : ℝ → ℂ) ∘ (LinearIsometryEquiv.neg ℝ (E := ℝ)) = G :=
      funext fun x => hGe x
    rw [e] at this
    simpa using this.symm
  have hht : ∀ t, h t = 𝓕 (G : ℝ → ℂ) (-t) := by
    intro t
    rw [hh, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  refine ⟨h, fun t => ?_, fun ξ => ?_⟩
  · rw [hht, hht, neg_neg, hev]
  · have h2 : (SchwartzMap.fourierTransformCLM ℂ h) = G := by
      rw [SchwartzMap.fourierTransformCLM_apply, hh, FourierTransform.fourier_fourierInv_eq]
    rw [h2]
    rfl

theorem phiW_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < phiW ρ := by
  unfold phiW
  have hp := Real.pi_pos
  have ht : 0 < Real.tanh (Real.pi * ρ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 (by positivity)) (Real.cosh_pos _)
  positivity

/-- **S7 core**: an element of `L²(0, ∞)` orthogonal to all `Φ h`, `h` even Schwartz, vanishes. -/
theorem eq_zero_of_forall_inner_phiL2 (u : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))))
    (hu : ∀ h : SchwartzMap ℝ ℂ, (∀ t, h (-t) = h t) → inner ℂ (phiL2 h) u = 0) : u = 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hloc : LocallyIntegrable (fun x => ((phiW x : ℝ) : ℂ) * u x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).continuous_mul
      (Complex.continuous_ofReal.comp continuous_phiW)
  have hzero := (isOpen_Ioi (a := (0 : ℝ))).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => ((phiW x : ℝ) : ℂ) * u x) (μ := volume.restrict (Ioi (0 : ℝ))) (hloc.locallyIntegrableOn _) ?_
  · rw [Lp.eq_zero_iff_ae_eq_zero]
    have hmem : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), x ∈ Ioi (0 : ℝ) :=
      ae_restrict_mem measurableSet_Ioi
    filter_upwards [hzero, hmem] with x hx hx0
    have := hx hx0
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by exact_mod_cast h) (phiW_pos hx0).ne'
    · simpa using h
  · intro g hg hgc hgs
    set Ψ : ℝ → ℝ := fun x => g x + g (-x) with hΨ
    have hΨs : ContDiff ℝ ∞ Ψ := hg.add (hg.comp contDiff_neg)
    have hΨc : HasCompactSupport Ψ :=
      hgc.add (hgc.comp_homeomorph (Homeomorph.neg ℝ))
    have hΨe : ∀ x, Ψ (-x) = Ψ x := fun x => by simp [hΨ, add_comm]
    obtain ⟨h, hhe, hF⟩ := exists_even_schwartz_fourier Ψ hΨs hΨc hΨe
    have h0 := hu h hhe
    rw [MeasureTheory.L2.inner_def] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    have hmem : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), x ∈ Ioi (0 : ℝ) :=
      ae_restrict_mem measurableSet_Ioi
    filter_upwards [(memLp_phi_Ioi h).coeFn_toLp, hmem] with x hx hx0
    have hx' : (phiL2 h : ℝ → ℂ) x = phi h x := hx
    have hgx : g (-x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have := hgs hm
      simp only [mem_Ioi] at this hx0
      linarith
    have hΨx : Ψ x = g x := by simp [hΨ, hgx]
    have hphi : phi h x = ((phiW x : ℝ) : ℂ) * ((g x : ℝ) : ℂ) := by
      unfold phi
      rw [hF, ← hΨx]
      congr 3
      field_simp
    rw [hx', hphi]
    simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.real_smul]
    ring

/-- **Surjectivity of the spherical Plancherel isometry**: every `u ∈ L²(0, ∞)` is
`sphericalL2 f` for some `f ∈ L²(1, ∞)`. -/
theorem surjective_sphericalL2 : Function.Surjective sphericalL2 := by
  set K : Submodule ℂ (Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :=
    LinearMap.range sphericalL2.toLinearMap with hK
  have hKc : IsClosed (K : Set (Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))))) :=
    isClosed_range_sphericalL2
  have hbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    refine eq_zero_of_forall_inner_phiL2 u fun h he => ?_
    have hm : phiL2 h ∈ K := phiL2_mem_range_of_even h he
    exact (Submodule.mem_orthogonal' K u).1 hu _ hm |> fun h0 => by
      rw [← inner_conj_symm, h0, map_zero]
  have htop : K.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.2 hbot
  rw [hKc.submodule_topologicalClosure_eq] at htop
  intro u
  have : u ∈ K := by rw [htop]; trivial
  obtain ⟨f, hf⟩ := this
  exact ⟨f, hf⟩

/-- **Spherical Plancherel theorem for `SL(2,ℝ)`** (K-biinvariant part, `L²(SL₂(ℝ)//K) ≃ L²((0,∞),
ρ tanh(πρ) dρ/(2π)²)` in the square-root normalisation): the spherical transform is a unitary
equivalence `L²(1, ∞) ≃ₗᵢ[ℂ] L²(0, ∞)`. -/
def sphericalL2Equiv : Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ))) ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  LinearIsometryEquiv.ofSurjective sphericalL2 surjective_sphericalL2

theorem sphericalL2Equiv_apply (f : Lp ℂ 2 (volume.restrict (Ioi (1 : ℝ)))) :
    sphericalL2Equiv f = sphericalL2 f := rfl

end Lightlike.Lorentz.SL2RPlancherel
