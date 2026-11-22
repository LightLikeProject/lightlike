import Lightlike.Spacetime.Raychaudhuri.Examples
import Lightlike.Spacetime.EnergyConditionsField

/-!
# The coordinate perfect fluid of FLRW is the covariant perfect-fluid field (GE3, non-vacuity)

`flrwManifold_einstein_iff_friedmann` states Einstein's equations with the coordinate tensor `perfectFluid ρ p g`
(components `(ρ + p) g_{μ0} g_{ν0} + p g_{μν}`). `raychaudhuri_focusing_strongEC` states the strong energy condition for a
tensor field `T`. This file shows that the two are the same object, so the dust solution of Friedmann's equations
(`p = 0`, `ρ ≥ 0`) satisfies the strong energy condition (`fluidField_dust`).

* `matForm_perfectFluid`: for a symmetric `G`, the bilinear form of `perfectFluid ρ p G` is `fluidT (matForm G) ∂_t ρ p`.
* `strongECField_flrw_dust`: on the FLRW manifold, dust with `ρ ≥ 0` satisfies the strong energy condition.

**Limits.** The fluid velocity is the coordinate field `∂_t`; the FLRW metric is the diagonal one of `flrwMetric`.
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

/-- Contraction with `∂_t` for a symmetric coordinate matrix. -/
theorem matForm_e0 (G : Matrix (Fin 4) (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    matForm G (Pi.single 0 1) v = ∑ j, G 0 j * v j := by
  rw [matForm_apply]
  simp [Pi.single_apply]

/-- **The coordinate perfect fluid is the covariant one**: for a symmetric `G`, the form of the matrix
`(ρ + p) G_{μ0} G_{ν0} + p G_{μν}` is `(ρ + p) G(∂_t, ·) G(∂_t, ·) + p G`. -/
theorem matForm_perfectFluid (ρ p : ℝ) (G : Matrix (Fin 4) (Fin 4) ℝ) (hG : ∀ i j, G i j = G j i)
    (v w : Fin 4 → ℝ) :
    matForm (Matrix.of fun μ ν => (ρ + p) * G μ 0 * G ν 0 + p * G μ ν) v w =
      (ρ + p) * (matForm G (Pi.single 0 1) v * matForm G (Pi.single 0 1) w) + p * matForm G v w := by
  have h0 : ∀ x : Fin 4 → ℝ, matForm G (Pi.single 0 1) x = ∑ j, G j 0 * x j := fun x => by
    rw [matForm_e0]; exact Finset.sum_congr rfl fun j _ => by rw [hG 0 j]
  rw [h0, h0, matForm_apply, matForm_apply, Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

variable {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ)

/-- The comoving field `∂_t` has unit length for `flrwManifoldMetric`. -/
theorem flrwManifold_comoving_unit (x : Cosmology.flrwOpen hI k) :
    (Cosmology.flrwManifoldMetric hI ha hpos k).g x (Pi.single 0 1 : Fin 4 → ℝ) (Pi.single 0 1 : Fin 4 → ℝ) = -1 := by
  show matForm (Cosmology.flrwMetric a k x.1) _ _ = -1
  rw [matForm_single]
  simp [Cosmology.flrwMetric]

/-- **The covariant perfect fluid with velocity `∂_t` is the coordinate one** of `flrwManifold_einstein_iff_friedmann`. -/
theorem flrwManifold_fluidField_eq (ρ p : ℝ → ℝ) (x : Cosmology.flrwOpen hI k)
    (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x) :
    (Cosmology.flrwManifoldMetric hI ha hpos k).fluidField (fun _ => (Pi.single 0 1 : Fin 4 → ℝ))
        (fun y => ρ (y.1 0)) (fun y => p (y.1 0)) x v w =
      matForm (Matrix.of fun μ ν => Cosmology.perfectFluid ρ p (Cosmology.flrwMetric a k) μ ν x.1) v w := by
  have hsym : ∀ i j, Cosmology.flrwMetric a k x.1 i j = Cosmology.flrwMetric a k x.1 j i := fun i j => by
    unfold Cosmology.flrwMetric
    rcases eq_or_ne i j with rfl | h
    · rfl
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h.symm]
  unfold Cosmology.perfectFluid
  have h := matForm_perfectFluid (ρ (x.1 0)) (p (x.1 0)) _ hsym v w
  exact (fluidT_apply _ _ _ _ _ _).trans h.symm

/-- **Dust on the FLRW manifold satisfies the strong energy condition** (`p = 0`, `ρ ≥ 0` on `I`). -/
theorem flrwManifold_dust_strongEC (ρ : ℝ → ℝ) (hρ : ∀ t ∈ I, 0 ≤ ρ t) :
    (Cosmology.flrwManifoldMetric hI ha hpos k).StrongECField
      (fun x => matForm (Matrix.of fun μ ν =>
        Cosmology.perfectFluid ρ (fun _ => 0) (Cosmology.flrwMetric a k) μ ν x.1)) := by
  have h := (LorentzianMetric.fluidField_dust (g := Cosmology.flrwManifoldMetric hI ha hpos k)
    (u := fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) (ρ := fun y => ρ (y.1 0))
    (flrwManifold_comoving_unit hI ha hpos k) (fun x => hρ _ x.2.1)).2.2.1
  have hT : (fun x : Cosmology.flrwOpen hI k => matForm (Matrix.of fun μ ν =>
        Cosmology.perfectFluid ρ (fun _ => 0) (Cosmology.flrwMetric a k) μ ν x.1)) =
      (Cosmology.flrwManifoldMetric hI ha hpos k).fluidField (fun _ => (Pi.single 0 1 : Fin 4 → ℝ))
        (fun y => ρ (y.1 0)) (fun _ => 0) := by
    funext x
    ext v w
    exact (flrwManifold_fluidField_eq hI ha hpos k ρ (fun _ => 0) x v w).symm
  rw [hT]
  exact h

end Lightlike
