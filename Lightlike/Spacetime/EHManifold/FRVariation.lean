import Lightlike.Spacetime.PalatiniCoord
import Lightlike.Spacetime.EHManifold.PieceVariation

/-!
# The first variation of the scalar curvature and of the `f(R)` density at a point

For `g_t = g + t h` (coordinate metric `g`, smooth symmetric perturbation `h`):

* `hasDerivAt_scalarCurvature_flux`:
  `d/dt R(g_t) = -R^{αβ} h_{αβ} + (1/√|g|) ∂_ρ (√|g| W^ρ)` at `t = 0`;
* `hasDerivAt_fRDensity`: for the density `√|g_t| f(R(g_t))` (`fRDensity`), with `f` differentiable at
  `R(g)`, `d/dt = -√|g| (f'(R) R^{αβ} - ½ f(R) g^{αβ}) h_{αβ} + f'(R) ∂_ρ (√|g| W^ρ)` at `t = 0`.

The first term is the algebraic part of the field equations of metric `f(R)` gravity (Sotiriou–Faraoni
(6)); the second gives, after two integrations by parts, the terms `-[∇_μ ∇_ν - g_{μν} □] f'(R)`. The
integrations by parts are not done here.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, arXiv:0805.1726, section II.A, eqs. (5), (6), p. 5.
-/

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The `f(R)` Lagrangian density `√|g_t| f(R(g_t))` of the perturbed metric `g_t = g + t h`. -/
def fRDensity (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  √|(g x + t • h x).det| * f (scalarCurvature (fun z => g z + t • h z) x)

/-- The trace of `G H` for a symmetric `G`, as a double sum. -/
lemma trace_mul_eq_sum_of_symm (G H : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ a b, G a b = G b a) :
    (G * H).trace = ∑ α, ∑ β, H α β * G α β := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hG β α, mul_comm]

variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
include hg hh hgs hhs

/-- **The first variation of the scalar curvature at a point**:
`d/dt R(g + t h) = -R^{αβ} h_{αβ} + (1/√|g|) ∂_ρ (√|g| W^ρ)` at `t = 0`. -/
theorem hasDerivAt_scalarCurvature_flux (x : Fin n → ℝ) (hx : (g x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => scalarCurvature (fun z => g z + t • h z) x)
      (-(∑ α, ∑ β, h x α β * ricciUp g x α β) + ehFluxDiv g h x / √|(g x).det|) 0 := by
  have e0 : (fun z => g z + (0 : ℝ) • h z) = g := by
    funext z
    rw [zero_smul, add_zero]
  have hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
      have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
      rw [Matrix.transpose_nonsing_inv, this]
    have := congrFun (congrFun hT a) b
    rw [Matrix.transpose_apply] at this
    exact this.symm
  have hsq : √|(g x).det| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 hx)).ne'
  obtain ⟨D, hRD⟩ : ∃ D : ℝ, HasDerivAt (fun t : ℝ => scalarCurvature (fun z => g z + t • h z) x) D 0 :=
    ⟨_, hasDerivAt_scalarCurvature g h hg hh x hx⟩
  have hs := hasDerivAt_sqrt_abs_det_add_smul (g x) (h x) hx
  have hL := hasDerivAt_lagrangian g h hg hh hgs hhs x hx 0
  have hprod := hs.mul (hRD.sub_const (2 * 0))
  have huniq := hL.unique hprod
  simp only [zero_smul, add_zero, mul_zero, sub_zero, e0, zero_mul] at huniq
  rw [trace_mul_eq_sum_of_symm _ _ hinv] at huniq
  have hsplit : ∑ α, ∑ β, h x α β *
        (ricciUp g x α β - 1 / 2 * scalarCurvature g x * (g x)⁻¹ α β) =
      ∑ α, ∑ β, h x α β * ricciUp g x α β -
        1 / 2 * scalarCurvature g x * ∑ α, ∑ β, h x α β * (g x)⁻¹ α β := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  rw [hsplit] at huniq
  have hfd : ∑ ρ, pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x = ehFluxDiv g h x := rfl
  rw [hfd] at huniq
  have hDeq : D = -(∑ α, ∑ β, h x α β * ricciUp g x α β) + ehFluxDiv g h x / √|(g x).det| := by
    field_simp
    linarith
  rw [hDeq] at hRD
  exact hRD

/-- **The first variation of the `f(R)` density at a point.** -/
theorem hasDerivAt_fRDensity (x : Fin n → ℝ) (hx : (g x).det ≠ 0) (f : ℝ → ℝ) (f' : ℝ)
    (hf : HasDerivAt f f' (scalarCurvature g x)) :
    HasDerivAt (fun t : ℝ => fRDensity g h f t x)
      (-√|(g x).det| * ∑ α, ∑ β, h x α β *
          (f' * ricciUp g x α β - (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β) +
        f' * ehFluxDiv g h x) 0 := by
  have e0 : (fun z => g z + (0 : ℝ) • h z) = g := by
    funext z
    rw [zero_smul, add_zero]
  have hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
      have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
      rw [Matrix.transpose_nonsing_inv, this]
    have := congrFun (congrFun hT a) b
    rw [Matrix.transpose_apply] at this
    exact this.symm
  have hsq : √|(g x).det| ≠ 0 := (Real.sqrt_pos.2 (abs_pos.2 hx)).ne'
  have hs := hasDerivAt_sqrt_abs_det_add_smul (g x) (h x) hx
  have hR := hasDerivAt_scalarCurvature_flux g h hg hh hgs hhs x hx
  have hf0 : HasDerivAt f f' ((fun t : ℝ => scalarCurvature (fun z => g z + t • h z) x) 0) := by
    show HasDerivAt f f' (scalarCurvature (fun z => g z + (0 : ℝ) • h z) x)
    rw [e0]
    exact hf
  have hcomp := hf0.comp (0 : ℝ) hR
  have hprod := hs.mul hcomp
  refine hprod.congr_deriv ?_
  show 1 / 2 * √|(g x).det| * ((g x)⁻¹ * h x).trace *
        f (scalarCurvature (fun z => g z + (0 : ℝ) • h z) x) +
      √|(g x + (0 : ℝ) • h x).det| *
        (f' * (-(∑ α, ∑ β, h x α β * ricciUp g x α β) + ehFluxDiv g h x / √|(g x).det|)) = _
  rw [e0, zero_smul, add_zero, trace_mul_eq_sum_of_symm _ _ hinv]
  have hsplit : ∑ α, ∑ β, h x α β *
        (f' * ricciUp g x α β - 1 / 2 * f (scalarCurvature g x) * (g x)⁻¹ α β) =
      f' * ∑ α, ∑ β, h x α β * ricciUp g x α β -
        1 / 2 * f (scalarCurvature g x) * ∑ α, ∑ β, h x α β * (g x)⁻¹ α β := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_ <;> ring
  rw [hsplit]
  field_simp
  ring

end Lightlike
