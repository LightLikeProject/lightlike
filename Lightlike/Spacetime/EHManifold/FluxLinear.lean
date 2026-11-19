import Lightlike.Spacetime.EHManifold.PieceVariation

/-!
# The flux divergence of the Palatini identity is additive in the perturbation

`ehFluxDiv_add`: `ehFluxDiv g (h₁ + h₂) = ehFluxDiv g h₁ + ehFluxDiv g h₂` for smooth perturbations of a
smooth nondegenerate coordinate metric, and `ehFluxDiv_zero`. They come from the additivity of the first
variation of the Christoffel symbols (`dChristoffel_add`) and of the vector `W` (`Wvec_add`).

Supporting lemmas for perturbations that are not supported in one chart; no catalogue entry.
-/

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The partial derivative of a sum of two differentiable functions. -/
lemma pd_add_of_differentiableAt {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h₁ : DifferentiableAt ℝ f₁ x) (h₂ : DifferentiableAt ℝ f₂ x) (k : Fin n) :
    pd k (fun y => f₁ y + f₂ y) x = pd k f₁ x + pd k f₂ x := by
  unfold pd
  rw [(h₁.hasFDerivAt.add h₂.hasFDerivAt).fderiv]
  rfl

variable (g h₁ h₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
  (hh₁ : ∀ a b, ContDiff ℝ ∞ (fun y => h₁ y a b)) (hh₂ : ∀ a b, ContDiff ℝ ∞ (fun y => h₂ y a b))

include hh₁ hh₂ in
/-- The first variation of the Christoffel symbols is additive in the perturbation. -/
theorem dChristoffel_add (i j k : Fin n) (y : Fin n → ℝ) :
    dChristoffel g (fun z => h₁ z + h₂ z) i j k y =
      dChristoffel g h₁ i j k y + dChristoffel g h₂ i j k y := by
  have hp : ∀ a b c, pd a (fun z => (h₁ z + h₂ z) b c) y =
      pd a (fun z => h₁ z b c) y + pd a (fun z => h₂ z b c) y := fun a b c =>
    pd_add_of_differentiableAt ((hh₁ b c).differentiable (by simp)).differentiableAt
      ((hh₂ b c).differentiable (by simp)).differentiableAt a
  unfold dChristoffel
  simp only [hp, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

include hh₁ hh₂ in
/-- The vector `W` of the Palatini identity is additive in the perturbation. -/
theorem Wvec_add (ρ : Fin n) (y : Fin n → ℝ) :
    Wvec g (fun z => h₁ z + h₂ z) ρ y = Wvec g h₁ ρ y + Wvec g h₂ ρ y := by
  unfold Wvec
  simp only [dChristoffel_add g h₁ h₂ hh₁ hh₂, mul_add, Finset.sum_add_distrib]
  ring

variable (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hdet : ∀ x, (g x).det ≠ 0)

include hh₁ hh₂ hg hdet in
/-- **The flux divergence is additive in the perturbation.** -/
theorem ehFluxDiv_add (x : Fin n → ℝ) :
    ehFluxDiv g (fun z => h₁ z + h₂ z) x = ehFluxDiv g h₁ x + ehFluxDiv g h₂ x := by
  unfold ehFluxDiv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hfun : (fun y => √|(g y).det| * Wvec g (fun z => h₁ z + h₂ z) ρ y) =
      fun y => √|(g y).det| * Wvec g h₁ ρ y + √|(g y).det| * Wvec g h₂ ρ y := by
    funext y
    rw [Wvec_add g h₁ h₂ hh₁ hh₂, mul_add]
  rw [hfun]
  exact pd_add_of_differentiableAt
    ((contDiff_flux g h₁ hg hh₁ hdet ρ).differentiable (by simp)).differentiableAt
    ((contDiff_flux g h₂ hg hh₂ hdet ρ).differentiable (by simp)).differentiableAt ρ

include hg in
/-- The flux divergence of the zero perturbation vanishes. -/
theorem ehFluxDiv_zero (x : Fin n → ℝ) :
    ehFluxDiv g (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) x = 0 := by
  have hW : ∀ ρ y, Wvec g (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) ρ y = 0 := by
    intro ρ y
    unfold Wvec
    simp [dChristoffel_eq_zero g (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) hg
      (fun _ _ => contDiff_const) y (fun _ _ => Filter.EventuallyEq.rfl)]
  unfold ehFluxDiv
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hfun : (fun y => √|(g y).det| * Wvec g (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) ρ y) =
      fun _ => (0 : ℝ) := by
    funext y
    rw [hW ρ y, mul_zero]
  rw [hfun]
  unfold pd
  simp

omit hh₁ hh₂ in
include hg hdet in
/-- **The flux divergence of a finite sum of perturbations** is the sum of the flux divergences. -/
theorem ehFluxDiv_sum {ι : Type*} (s : Finset ι) (hs : ι → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hsm : ∀ i a b, ContDiff ℝ ∞ (fun y => hs i y a b)) (x : Fin n → ℝ) :
    ehFluxDiv g (fun z => ∑ i ∈ s, hs i z) x = ∑ i ∈ s, ehFluxDiv g (hs i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ehFluxDiv_zero g hg x
  | insert a s ha ih =>
    have hfun : (fun z => ∑ i ∈ insert a s, hs i z) = fun z => hs a z + ∑ i ∈ s, hs i z := by
      funext z
      rw [Finset.sum_insert ha]
    have hsum : ∀ c d, ContDiff ℝ ∞ (fun y => (∑ i ∈ s, hs i y) c d) := by
      intro c d
      have : (fun y => (∑ i ∈ s, hs i y) c d) = fun y => ∑ i ∈ s, hs i y c d := by
        funext y
        rw [Matrix.sum_apply]
      rw [this]
      exact ContDiff.sum fun i _ => hsm i c d
    rw [hfun, ehFluxDiv_add g (hs a) (fun z => ∑ i ∈ s, hs i z) (hsm a) hsum hg hdet x, ih,
      Finset.sum_insert ha]

end Lightlike
