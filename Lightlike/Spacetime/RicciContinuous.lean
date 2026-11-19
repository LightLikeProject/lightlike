import Lightlike.Spacetime.Curvature

/-!
# Continuity of the curvature of a smooth coordinate metric

For a coordinate metric `g` on an open set `U` (`IsCoordMetric g U`: smooth, symmetric, invertible)
the Christoffel symbols are smooth on `U` (the inverse metric is smooth: determinant and adjugate
are polynomials in the entries, and the determinant does not vanish), so the Riemann and Ricci
tensors are continuous on `U` (`continuousOn_ricci`). Used to pass a vanishing curvature from a dense
open subset to its closure inside `U` (the horizon of Schwarzschild in Eddington–Finkelstein
coordinates).

Supporting lemma; no catalogue entry.
-/

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The determinant of a smooth matrix-valued function is smooth. -/
lemma contDiffOn_det {A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun y => A y i j) U) : ContDiffOn ℝ ∞ (fun y => (A y).det) U := by
  simp only [Matrix.det_apply']
  refine ContDiffOn.sum fun σ _ => ?_
  exact contDiffOn_const.mul (contDiffOn_prod fun i _ => hA _ _)

/-- The inverse of a smooth, invertible matrix-valued function is smooth. -/
lemma contDiffOn_inv_entry {A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun y => A y i j) U) (hdet : ∀ y ∈ U, (A y).det ≠ 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun y => (A y)⁻¹ i j) U := by
  have hd := contDiffOn_det hA
  have hadj : ContDiffOn ℝ ∞ (fun y => (A y).adjugate i j) U := by
    simp only [Matrix.adjugate_apply]
    refine contDiffOn_det fun a b => ?_
    by_cases h : a = j
    · subst h; simp [Matrix.updateRow_self, Pi.single_apply]; exact contDiffOn_const
    · simp [Matrix.updateRow_ne h]; exact hA a b
  have : ∀ y ∈ U, (A y)⁻¹ i j = ((A y).det)⁻¹ * (A y).adjugate i j := fun y hy => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  refine (ContDiffOn.mul (hd.inv hdet) hadj).congr fun y hy => this y hy

/-- Coordinate derivatives of a smooth function are smooth. -/
lemma contDiffOn_pd {f : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (k : Fin n) : ContDiffOn ℝ ∞ (pd k f) U := by
  have h := hf.fderiv_of_isOpen hU (m := ∞) le_rfl
  exact h.clm_apply contDiffOn_const

/-- The Christoffel symbols of a coordinate metric are smooth on its domain. -/
theorem contDiffOn_christoffel {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) (i j k : Fin n) : ContDiffOn ℝ ∞ (christoffel g i j k) U := by
  have hdet : ∀ y ∈ U, (g y).det ≠ 0 := fun y hy => (hg.isUnit_det y hy).ne_zero
  unfold christoffel
  refine contDiffOn_const.mul (ContDiffOn.sum fun l _ => ?_)
  refine (contDiffOn_inv_entry hg.smooth hdet i l).mul ?_
  exact (((contDiffOn_pd (hg.smooth l k) hg.isOpen j).add (contDiffOn_pd (hg.smooth l j) hg.isOpen k)).sub
    (contDiffOn_pd (hg.smooth j k) hg.isOpen l))

/-- **The Riemann tensor of a coordinate metric is continuous on its domain.** -/
theorem continuousOn_riemann {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) (ρ σ μ ν : Fin n) : ContinuousOn (riemann g ρ σ μ ν) U := by
  unfold riemann
  have hΓ := fun a b c => contDiffOn_christoffel hg a b c
  refine ((contDiffOn_pd (hΓ ρ ν σ) hg.isOpen μ).continuousOn.sub
    (contDiffOn_pd (hΓ ρ μ σ) hg.isOpen ν).continuousOn).add ?_
  refine continuousOn_finset_sum _ fun l _ => ?_
  exact ((hΓ ρ μ l).continuousOn.mul (hΓ l ν σ).continuousOn).sub
    ((hΓ ρ ν l).continuousOn.mul (hΓ l μ σ).continuousOn)

/-- **The Ricci tensor of a coordinate metric is continuous on its domain.** -/
theorem continuousOn_ricci {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) (σ ν : Fin n) : ContinuousOn (ricci g σ ν) U := by
  unfold ricci
  exact continuousOn_finset_sum _ fun ρ _ => continuousOn_riemann hg ρ σ ρ ν

end Lightlike
