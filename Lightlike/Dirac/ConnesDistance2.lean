import Mathlib
import Lightlike.Dirac.ConnesDistance

/-!
# Connes' distance formula on flat `ℝⁿ`

Milestone NC2 (needs GE5).  With the flat Dirac operator `D = ∑ γᵢ ∂ᵢ` the commutator `[D, f]` is
Clifford multiplication by `∇f` (`dirac_smul`), whose operator norm is `‖∇f‖` (`opNorm_cliff`).
Hence the unit ball of the commutator norm is the set `Lip1 ρ` of `C¹` functions with
`‖cliff(∇f)‖ ≤ 1`, and Connes' distance
`d(p, q) = sup { |f p - f q| : ‖[D, f]‖ ≤ 1 }` is the Euclidean distance (`connesDist_eq_norm`).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), source key
  `bgv-1992`, for the Dirac operator; the distance formula itself is Connes' (definition only, no
  equation number claimed).
-/

open CliffordAlgebra InnerProductSpace

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Scalar functions with `‖[D, f]‖ ≤ 1`: `C¹` and `‖cliff(∇f x)‖ ≤ 1` everywhere. -/
def Lip1 (ρ : CliffordRep n V) (f : E n → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ ∀ x, ‖cliff ρ (gradient f x)‖ ≤ 1

/-- Connes' distance on `ℝⁿ` attached to the Dirac operator of the module `ρ`. -/
noncomputable def connesDist (ρ : CliffordRep n V) (p q : E n) : ℝ :=
  sSup {r | ∃ f, Lip1 ρ f ∧ r = |f p - f q|}

lemma norm_fderiv_eq_gradient (f : E n → ℝ) (x : E n) : ‖fderiv ℝ f x‖ = ‖gradient f x‖ := by
  simp [gradient]

lemma Lip1.norm_gradient_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {f : E n → ℝ}
    (hf : Lip1 ρ f) (x : E n) : ‖gradient f x‖ ≤ 1 := by
  rw [← opNorm_cliff hρ]; exact hf.2 x

/-- Mean value inequality: functions in `Lip1` are `1`-Lipschitz. -/
lemma Lip1.abs_sub_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {f : E n → ℝ}
    (hf : Lip1 ρ f) (p q : E n) : |f p - f q| ≤ ‖p - q‖ := by
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := f) (C := 1)
    (fun x _ => (hf.1.differentiable one_ne_zero).differentiableAt)
    (fun x _ => by rw [norm_fderiv_eq_gradient]; exact hf.norm_gradient_le hρ x)
    (Set.mem_univ q) (Set.mem_univ p)
  simpa [Real.norm_eq_abs] using h

lemma lip1_zero (ρ : CliffordRep n V) : Lip1 ρ (fun _ => 0) := by
  refine ⟨contDiff_const, fun x => ?_⟩
  simp [cliff_zero]

/-- The linear function `x ↦ ⟪u, x⟫` with `‖u‖ ≤ 1` lies in `Lip1`. -/
lemma lip1_inner {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (u : E n) (hu : ‖u‖ ≤ 1) :
    Lip1 ρ (fun x => inner ℝ u x) := by
  have hgrad : ∀ x, gradient (fun x : E n => inner ℝ u x) x = u := by
    intro x
    have h : HasGradientAt (fun x : E n => inner ℝ u x) u x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      exact (innerSL ℝ u).hasFDerivAt (x := x)
    exact h.gradient
  refine ⟨(innerSL ℝ u).contDiff, fun x => ?_⟩
  rw [hgrad, opNorm_cliff hρ]
  exact hu

/-- The set defining the Connes distance is bounded by the Euclidean distance. -/
lemma connesDist_bdd {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (p q : E n) :
    BddAbove {r | ∃ f, Lip1 ρ f ∧ r = |f p - f q|} :=
  ⟨‖p - q‖, by rintro r ⟨f, hf, rfl⟩; exact hf.abs_sub_le hρ p q⟩

/-- `d(p, q) ≤ ‖p - q‖`. -/
lemma connesDist_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (p q : E n) :
    connesDist ρ p q ≤ ‖p - q‖ :=
  csSup_le ⟨_, 0, lip1_zero ρ, rfl⟩ (by rintro r ⟨f, hf, rfl⟩; exact hf.abs_sub_le hρ p q)

/-- `‖p - q‖ ≤ d(p, q)`: test with the linear function in the direction `p - q`. -/
lemma le_connesDist {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (p q : E n) :
    ‖p - q‖ ≤ connesDist ρ p q := by
  by_cases hpq : p = q
  · subst hpq
    simp only [sub_self, norm_zero]
    exact le_csSup (connesDist_bdd hρ p p) ⟨_, lip1_zero ρ, by simp⟩
  · have hn : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
    set u : E n := ‖p - q‖⁻¹ • (p - q) with hu
    have hu1 : ‖u‖ ≤ 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hval : |inner ℝ u p - inner ℝ u q| = ‖p - q‖ := by
      rw [← inner_sub_right, hu, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [conj_trivial, abs_mul, abs_inv, abs_norm]
      rw [abs_of_nonneg (by positivity)]
      field_simp
    exact hval.symm.le.trans (le_csSup (connesDist_bdd hρ p q) ⟨_, lip1_inner hρ u hu1, rfl⟩)

/-- **Connes' distance formula on `ℝⁿ`**: the spectral distance of the flat Dirac operator is the
Euclidean distance. -/
theorem connesDist_eq_norm {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (p q : E n) :
    connesDist ρ p q = ‖p - q‖ :=
  le_antisymm (connesDist_le hρ p q) (le_connesDist hρ p q)

end Lightlike.Dirac
