import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.EHManifold.FRIntegral

/-!
# The first variation of the `f(R)` action, after one integration by parts

`fR_first_variation`: for a smooth nondegenerate symmetric coordinate metric `g`, a smooth symmetric
perturbation `h` supported in a compact set `T`, and `f` with `f`, `f'` of class `C¹`,

`d/dt ∫_T √|g_t| f(R(g_t)) = -∫_T √|g| (f'(R) R^{αβ} - ½ f(R) g^{αβ}) h_{αβ} - ∫_T √|g| W^ρ ∂_ρ (f'(R))`

at `t = 0`, with `W^ρ = g^{σν} δΓ^ρ_{σν} - g^{ρσ} δΓ^κ_{κσ}`. For `f(R) = R` the last term vanishes.

To reach the field equations (6) of Sotiriou–Faraoni, `f'(R) R_{μν} - ½ f(R) g_{μν} - [∇_μ ∇_ν - g_{μν} □] f'(R)`,
a second integration by parts (moving the derivative from `δg` in `W` to `∂ f'(R)`) is still needed; it is
not done here.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, eqs. (5), (6), p. 5.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The partial derivative of a product. -/
lemma pd_mul_of_differentiableAt {u F : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hu : DifferentiableAt ℝ u x) (hF : DifferentiableAt ℝ F x) (ρ : Fin n) :
    pd ρ (fun y => u y * F y) x = pd ρ u x * F x + u x * pd ρ F x := by
  unfold pd
  have h := (hu.hasFDerivAt.mul hF.hasFDerivAt).fderiv
  show (fderiv ℝ (u * F) x) (Pi.single ρ 1) = _
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Integration by parts** against a `C¹` function with compact support: `∫ u ∂_ρ F = -∫ (∂_ρ u) F`. -/
lemma integral_mul_pd_eq_neg (u F : (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 1 u) (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (ρ : Fin n) :
    ∫ y, u y * pd ρ F y = -∫ y, pd ρ u y * F y := by
  have hP : ContDiff ℝ 1 (fun y => u y * F y) := hu.mul hF
  have hPc : HasCompactSupport (fun y => u y * F y) := hc.mul_left
  have h0 := integral_pd_eq_zero (fun y => u y * F y) hP hPc ρ
  have hpd : ∀ y, pd ρ (fun y => u y * F y) y = pd ρ u y * F y + u y * pd ρ F y := fun y =>
    pd_mul_of_differentiableAt ((hu.differentiable (by simp)).differentiableAt)
      ((hF.differentiable (by simp)).differentiableAt) ρ
  have hcu : Continuous (fun y => pd ρ u y) := by
    unfold pd
    exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcF : Continuous (fun y => pd ρ F y) := by
    unfold pd
    exact (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpdFc : HasCompactSupport (fun y => pd ρ F y) := by
    unfold pd
    exact hc.fderiv_apply (𝕜 := ℝ) (Pi.single ρ 1)
  have i1 : Integrable (fun y => pd ρ u y * F y) :=
    (hcu.mul hF.continuous).integrable_of_hasCompactSupport hc.mul_left
  have i2 : Integrable (fun y => u y * pd ρ F y) :=
    (hu.continuous.mul hcF).integrable_of_hasCompactSupport hpdFc.mul_left
  simp only [hpd] at h0
  rw [integral_add i1 i2] at h0
  linarith

variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)
include hg hh hgs hhs hdet

/-- **The first variation of the `f(R)` action, after one integration by parts.** -/
theorem fR_first_variation (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 1 (deriv f))
    {T : Set (Fin n → ℝ)} (hT : IsCompact T) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) :
    HasDerivAt (fun t : ℝ => ∫ x in T, fRDensity g h f t x)
      ((-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β)) -
        ∫ x in T, ∑ ρ, (√|(g x).det| * Wvec g h ρ x) *
          pd ρ (fun y => deriv f (scalarCurvature g y)) x) 0 := by
  have hmain := fR_variation g h hg hh hgs hhs hdet f hf hT
  have hmeasT : MeasurableSet T := hT.isClosed.measurableSet
  have hRc : ContDiff ℝ ∞ (fun y => scalarCurvature g y) := contDiff_scalarCurvature g hg hdet
  obtain ⟨u, hu⟩ : ∃ u : (Fin n → ℝ) → ℝ, u = fun y => deriv f (scalarCurvature g y) := ⟨_, rfl⟩
  have huc : ContDiff ℝ 1 u := by
    rw [hu]
    exact hf'.comp (hRc.of_le (by simp))
  have hFs : ∀ ρ, ContDiff ℝ ∞ (fun y => √|(g y).det| * Wvec g h ρ y) := fun ρ =>
    contDiff_flux g h hg hh hdet ρ
  -- the flux vanishes near every point outside `T`
  have hzero : ∀ x, x ∉ T → ∀ ρ, (fun y => √|(g y).det| * Wvec g h ρ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    intro x hx ρ
    filter_upwards [hT.isClosed.isOpen_compl.mem_nhds hx] with y hy
    have hyz : ∀ a b, (fun z => h z a b) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := fun a b =>
      notMem_tsupport_iff_eventuallyEq.1 (fun hmem => hy (hsupp a b hmem))
    have hW : Wvec g h ρ y = 0 := by
      unfold Wvec
      simp [dChristoffel_eq_zero g h hg hh y hyz]
    show √|(g y).det| * Wvec g h ρ y = 0
    rw [hW, mul_zero]
  have hFc : ∀ ρ, HasCompactSupport (fun y => √|(g y).det| * Wvec g h ρ y) := fun ρ =>
    HasCompactSupport.intro hT fun x hx => (hzero x hx ρ).self_of_nhds
  -- integration by parts for each `ρ`, on `T`
  have hparts : ∀ ρ, ∫ x in T, u x * pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x =
      -∫ x in T, pd ρ u x * (√|(g x).det| * Wvec g h ρ x) := by
    intro ρ
    have h1 := integral_mul_pd_eq_neg u (fun y => √|(g y).det| * Wvec g h ρ y) huc
      ((hFs ρ).of_le (by simp)) (hFc ρ) ρ
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero,
      h1]
    · intro x hx
      have hz0 : √|(g x).det| * Wvec g h ρ x = 0 := (hzero x hx ρ).self_of_nhds
      rw [hz0, mul_zero]
    · intro x hx
      have hpd0 : pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x = 0 := by
        unfold pd
        rw [(hzero x hx ρ).fderiv_eq]
        simp
      rw [hpd0, mul_zero]
  -- continuity and integrability on `T`
  have hGc : Continuous g := continuous_matrix fun i j => (hg i j).continuous
  have hbulk : Continuous (fun x => -√|(g x).det| * ∑ α, ∑ β, h x α β *
      (deriv f (scalarCurvature g x) * ricciUp g x α β -
        (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β)) :=
    ((Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)).neg).mul
      (continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
        (hh α β).continuous.mul
          (((hu ▸ huc.continuous : Continuous fun y => deriv f (scalarCurvature g y)).mul
            (contDiff_ricciUp g hg hdet α β).continuous).sub
          ((continuous_const.mul (hf.continuous.comp hRc.continuous)).mul
            (contDiff_inv_entry g hg hdet α β).continuous)))
  have hpdF : ∀ ρ, Continuous (fun x => pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x) := fun ρ =>
    (contDiff_pd (hFs ρ) ρ).continuous
  have hdivc : Continuous (fun x => deriv f (scalarCurvature g x) * ehFluxDiv g h x) := by
    unfold ehFluxDiv
    exact (hu ▸ huc.continuous : Continuous fun y => deriv f (scalarCurvature g y)).mul
      (continuous_finsetSum _ fun ρ _ => hpdF ρ)
  have e1 := integral_add (hbulk.continuousOn.integrableOn_compact hT : IntegrableOn _ T volume)
    (hdivc.continuousOn.integrableOn_compact hT : IntegrableOn _ T volume)
  have e2 : ∫ x in T, deriv f (scalarCurvature g x) * ehFluxDiv g h x =
      -∫ x in T, ∑ ρ, (√|(g x).det| * Wvec g h ρ x) *
        pd ρ (fun y => deriv f (scalarCurvature g y)) x := by
    have hsum : ∀ x, deriv f (scalarCurvature g x) * ehFluxDiv g h x =
        ∑ ρ, u x * pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x := by
      intro x
      rw [hu]
      unfold ehFluxDiv
      rw [Finset.mul_sum]
    simp only [hsum]
    have iu : ∀ ρ ∈ (Finset.univ : Finset (Fin n)),
        IntegrableOn (fun x => u x * pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x) T volume :=
      fun ρ _ => (huc.continuous.mul (hpdF ρ)).continuousOn.integrableOn_compact hT
    have hpdu : ∀ ρ, Continuous (fun x => pd ρ u x) := fun ρ => by
      unfold pd
      exact (huc.continuous_fderiv (by simp)).clm_apply continuous_const
    have ipd : ∀ ρ ∈ (Finset.univ : Finset (Fin n)),
        IntegrableOn (fun x => pd ρ u x * (√|(g x).det| * Wvec g h ρ x)) T volume :=
      fun ρ _ => ((hpdu ρ).mul (hFs ρ).continuous).continuousOn.integrableOn_compact hT
    rw [integral_finsetSum _ iu]
    simp only [hparts]
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ ipd]
    congr 1
    refine setIntegral_congr_fun hmeasT fun x _ => Finset.sum_congr rfl fun ρ _ => ?_
    rw [hu]
    ring
  have hval : ∫ x in T, (-√|(g x).det| * ∑ α, ∑ β, h x α β *
        (deriv f (scalarCurvature g x) * ricciUp g x α β -
          (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        deriv f (scalarCurvature g x) * ehFluxDiv g h x) =
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β)) -
        ∫ x in T, ∑ ρ, (√|(g x).det| * Wvec g h ρ x) *
          pd ρ (fun y => deriv f (scalarCurvature g y)) x := by
    rw [e1, e2, sub_eq_add_neg]
    congr 1
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show -√|(g x).det| * _ = -(√|(g x).det| * _)
    ring
  rw [hval] at hmain
  exact hmain

end Lightlike
