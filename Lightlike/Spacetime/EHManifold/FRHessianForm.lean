import Lightlike.Spacetime.EHManifold.FRHessian
import Lightlike.Spacetime.EHManifold.FRHessianAlg

/-!
# The Hessian form of the `f(R)` first variation

For a smooth nondegenerate symmetric coordinate metric `g` on `ℝⁿ` and a `C²` function `φ`:

* `covHessUp g φ a b x` is `∇^a ∇^b φ = g^{aα} g^{bβ} (∂_α ∂_β φ - Γ^μ_{αβ} ∂_μ φ)` and `dalembertian g φ x`
  is `□φ = g^{αβ} (∂_α ∂_β φ - Γ^μ_{αβ} ∂_μ φ)`;
* `flux_sub_pd_hessCoeff`: pointwise,
  `√|g| W₀^ρ ∂_ρ φ - ∂_μ (c^{μαβ}) h_{αβ} = -√|g| h_{ab} (∇^a ∇^b φ - g^{ab} □φ)`;
* `integral_flux_mul_pd_hessian`: `∫_T √|g| W^ρ ∂_ρ φ = -∫_T √|g| h_{ab} (∇^a ∇^b φ - g^{ab} □φ)` for `h`
  supported in the compact set `T`;
* `fR_field_equation_variation`: the first variation of `∫ √|g| f(R)` along `g + t h` is
  `-∫_T √|g| h_{ab} (f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R))`.

The tensor in the last line is the left side of the metric `f(R)` field equations, with raised indices.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, Rev. Mod. Phys. 82 (2010) 451,
  arXiv:0805.1726, section II.A, equations (5)–(6), p. 5.
-/

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- Mixed second partial derivatives of a `C²` function commute. -/
lemma pd_pd_comm_of_contDiff_two {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (x : Fin n → ℝ)
    (μ ν : Fin n) : pd μ (fun y => pd ν f y) x = pd ν (fun y => pd μ f y) x := by
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt
  have hsym := hfx.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)).differentiableAt
  have key : ∀ a b : Fin n, pd a (fun y => pd b f y) x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single a 1) (Pi.single b 1) := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ f y (Pi.single b 1)) x (Pi.single a 1) = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  rw [key, key, hsym]

/-- The covariant Hessian of a function with raised indices, in coordinates:
`∇^a ∇^b φ = g^{aα} g^{bβ} (∂_α ∂_β φ - Γ^μ_{αβ} ∂_μ φ)`. -/
def covHessUp (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → ℝ) (a b : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ α, ∑ β, (g x)⁻¹ a α * (g x)⁻¹ b β *
    (pd α (fun y => pd β φ y) x - ∑ μ, christoffel g μ α β x * pd μ φ x)

/-- The d'Alembertian (Laplace–Beltrami operator) of a function, in coordinates:
`□φ = g^{αβ} (∂_α ∂_β φ - Γ^μ_{αβ} ∂_μ φ)`. -/
def dalembertian (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ α, ∑ β, (g x)⁻¹ α β * (pd α (fun y => pd β φ y) x - ∑ μ, christoffel g μ α β x * pd μ φ x)

/-- The four contractions of the algebraic Hessian identity, written with the covariant Hessian and the
d'Alembertian. -/
lemma hess_form (G H q : Fin n → Fin n → ℝ) (C : Fin n → Fin n → Fin n → ℝ) (p : Fin n → ℝ) :
    (∑ a, ∑ b, H a b * ∑ α, ∑ β, G a α * G b β * q α β) -
        (∑ a, ∑ b, ∑ μ, H a b * p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν) -
        (∑ α, ∑ β, G α β * q α β) * (∑ α, ∑ β, G α β * H α β) +
        (∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) * (∑ α, ∑ β, G α β * H α β) =
      ∑ a, ∑ b, H a b * ((∑ α, ∑ β, G a α * G b β * (q α β - ∑ μ, C μ α β * p μ)) -
        G a b * ∑ α, ∑ β, G α β * (q α β - ∑ μ, C μ α β * p μ)) := by
  have e1 : ∀ a b, ∑ α, ∑ β, G a α * G b β * (q α β - ∑ μ, C μ α β * p μ) =
      (∑ α, ∑ β, G a α * G b β * q α β) - ∑ μ, p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν := by
    intro a b
    have r : ∑ μ, ∑ γ, ∑ ν, p μ * (G a γ * G b ν * C μ γ ν) =
        ∑ γ, ∑ ν, ∑ μ, p μ * (G a γ * G b ν * C μ γ ν) :=
      sum3_first_last (fun μ γ ν => p μ * (G a γ * G b ν * C μ γ ν))
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [r]
    congr 1
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun μ _ => by ring
  have e2 : ∑ α, ∑ β, G α β * (q α β - ∑ μ, C μ α β * p μ) =
      (∑ α, ∑ β, G α β * q α β) - (∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) := by
    have r : ∑ ρ, ∑ σ, ∑ ν, p ρ * (G σ ν * C ρ σ ν) = ∑ σ, ∑ ν, ∑ ρ, p ρ * (G σ ν * C ρ σ ν) :=
      sum3_first_last (fun ρ σ ν => p ρ * (G σ ν * C ρ σ ν))
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [r]
    congr 1
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun μ _ => by ring
  have e3 : ∀ a b, H a b * ((∑ α, ∑ β, G a α * G b β * (q α β - ∑ μ, C μ α β * p μ)) -
        G a b * ∑ α, ∑ β, G α β * (q α β - ∑ μ, C μ α β * p μ)) =
      H a b * (∑ α, ∑ β, G a α * G b β * q α β) -
        (∑ μ, H a b * p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν) -
        (∑ α, ∑ β, G α β * q α β) * (G a b * H a b) + (∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) * (G a b * H a b) := by
    intro a b
    have e4 : ∑ μ, H a b * p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν =
        H a b * ∑ μ, p μ * ∑ γ, ∑ ν, G a γ * G b ν * C μ γ ν := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by ring
    rw [e1 a b, e2, e4]
    ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e3 a b]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (∑ α, ∑ β, G α β * q α β) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (∑ ρ, p ρ * ∑ σ, ∑ ν, G σ ν * C ρ σ ν) := ⟨_, rfl⟩
  rw [← ht, ← hu]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)

include hg hgs hhs hdet in
/-- **The Hessian identity, pointwise**:
`√|g| W₀^ρ ∂_ρ φ - ∂_μ (c^{μαβ}) h_{αβ} = -√|g| h_{ab} (∇^a ∇^b φ - g^{ab} □φ)`. -/
theorem flux_sub_pd_hessCoeff (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (x : Fin n → ℝ) :
    (∑ ρ, (√|(g x).det| * Wvec0 g h ρ x) * pd ρ φ x) -
        ∑ μ, ∑ α, ∑ β, pd μ (hessCoeff g φ μ α β) x * h x α β =
      -(√|(g x).det| * ∑ a, ∑ b, h x a b *
        (covHessUp g φ a b x - (g x)⁻¹ a b * dalembertian g φ x)) := by
  have hG : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
      have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
      rw [Matrix.transpose_nonsing_inv, this]
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hT a) b).symm
  have hC : ∀ i j k, christoffel g i j k x = christoffel g i k j x := fun i j k =>
    christoffel_symm g hgs i j k x
  have hq : ∀ a b, pd a (fun y => pd b φ y) x = pd b (fun y => pd a φ y) x := fun a b =>
    pd_pd_comm_of_contDiff_two hφ x a b
  have hgd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    ((hg a b).differentiable (by simp)).differentiableAt
  have hW : ∑ ρ, (√|(g x).det| * Wvec0 g h ρ x) * pd ρ φ x =
      √|(g x).det| * ∑ ρ, ((∑ σ, ∑ ν, (g x)⁻¹ σ ν * (-∑ a, ∑ b, (g x)⁻¹ ρ a * h x a b * christoffel g b σ ν x)) -
        ∑ σ, (g x)⁻¹ ρ σ * ∑ κ, (-∑ a, ∑ b, (g x)⁻¹ κ a * h x a b * christoffel g b κ σ x)) * pd ρ φ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold Wvec0
    simp only [dChristoffel0_eq]
    ring
  have hc : ∀ μ α β, pd μ (hessCoeff g φ μ α β) x =
      √|(g x).det| * (∑ κ, christoffel g κ κ μ x) * (∑ ρ, ((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x) +
        √|(g x).det| * ∑ ρ, (((-∑ γ, (christoffel g ρ μ γ x * (g x)⁻¹ γ α +
              christoffel g α μ γ x * (g x)⁻¹ ρ γ)) * (g x)⁻¹ μ β +
            (g x)⁻¹ ρ α * (-∑ γ, (christoffel g μ μ γ x * (g x)⁻¹ γ β +
              christoffel g β μ γ x * (g x)⁻¹ μ γ)) -
          ((-∑ γ, (christoffel g ρ μ γ x * (g x)⁻¹ γ μ +
              christoffel g μ μ γ x * (g x)⁻¹ ρ γ)) * (g x)⁻¹ α β +
            (g x)⁻¹ ρ μ * (-∑ γ, (christoffel g α μ γ x * (g x)⁻¹ γ β +
              christoffel g β μ γ x * (g x)⁻¹ α γ)))) * pd ρ φ x +
          ((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd μ (fun y => pd ρ φ y) x) := by
    intro μ α β
    rw [pd_hessCoeff g hg hdet φ hφ μ μ α β x, pd_sqrt_abs_det g x hgs hgd (hdet x) μ]
    simp only [pd_inv_eq g x hgs hgd (hdet x)]
  have key := hess_assemble (fun a b => (g x)⁻¹ a b) (fun a b => h x a b)
    (fun μ ρ => pd μ (fun y => pd ρ φ y) x) (fun i j k => christoffel g i j k x)
    (fun ρ => pd ρ φ x) (√|(g x).det|) hG (hhs x) hq hC
  have hform := hess_form (fun a b => (g x)⁻¹ a b) (fun a b => h x a b)
    (fun μ ρ => pd μ (fun y => pd ρ φ y) x) (fun i j k => christoffel g i j k x)
    (fun ρ => pd ρ φ x)
  beta_reduce at key hform
  rw [hW]
  simp only [hc]
  refine key.trans ?_
  rw [hform]
  unfold covHessUp dalembertian
  ring

include hg hh hgs hhs hdet in
/-- **The second integration by parts in Hessian form**: for `h` supported in the compact set `T`,
`∫_T √|g| W^ρ ∂_ρ φ = -∫_T √|g| h_{ab} (∇^a ∇^b φ - g^{ab} □φ)`. -/
theorem integral_flux_mul_pd_hessian (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ)
    {T : Set (Fin n → ℝ)} (hT : IsCompact T) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) :
    ∫ x in T, ∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x =
      -∫ x in T, √|(g x).det| * ∑ a, ∑ b, h x a b *
        (covHessUp g φ a b x - (g x)⁻¹ a b * dalembertian g φ x) := by
  rw [integral_flux_mul_pd g h hg hh hgs hhs hdet φ hφ hT hsupp, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    flux_sub_pd_hessCoeff g h hg hgs hhs hdet φ hφ x)

include hg hh hgs hhs hdet in
/-- **The first variation of the `f(R)` action in field-equation form.** For `f` of class `C¹` with `f'` of
class `C²`, and `h` supported in the compact set `T`,

`d/dt|₀ ∫_T √|g_t| f(R(g_t)) = -∫_T √|g| h_{ab} (f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R))`. -/
theorem fR_field_equation_variation (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f))
    {T : Set (Fin n → ℝ)} (hT : IsCompact T) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) :
    HasDerivAt (fun t : ℝ => ∫ x in T, fRDensity g h f t x)
      ((-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β)) +
        ∫ x in T, √|(g x).det| * ∑ a, ∑ b, h x a b *
          (covHessUp g (fun y => deriv f (scalarCurvature g y)) a b x -
            (g x)⁻¹ a b * dalembertian g (fun y => deriv f (scalarCurvature g y)) x)) 0 := by
  have hmain := fR_first_variation g h hg hh hgs hhs hdet f hf (hf'.of_le (by norm_num)) hT hsupp
  have hRc : ContDiff ℝ ∞ (fun y => scalarCurvature g y) := contDiff_scalarCurvature g hg hdet
  have hφ : ContDiff ℝ 2 (fun y => deriv f (scalarCurvature g y)) :=
    hf'.comp (hRc.of_le (by simp))
  rw [integral_flux_mul_pd_hessian g h hg hh hgs hhs hdet _ hφ hT hsupp, sub_neg_eq_add] at hmain
  exact hmain

end Lightlike
