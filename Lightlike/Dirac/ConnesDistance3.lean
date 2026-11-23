import Mathlib
import Lightlike.Dirac.ConnesDistance2

/-!
# Scaling of Connes' distance on flat `ℝⁿ`

For the rescaled Dirac operator `c • D` the commutator is `[c D, f] = c • cliff(∇f)`, so the unit
ball of the commutator norm is `{f | |c| ‖∇f‖ ≤ 1}` and the spectral distance is
`‖p - q‖ / |c|` (`connesDistC_eq`): scaling `D` by `2` halves all distances.

## References

Connes' distance formula (definition only); Dirac operator: `bgv-1992`.
-/

open CliffordAlgebra InnerProductSpace

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Functions with `‖[c D, f]‖ ≤ 1`, where `[c D, f] = c • cliff (∇ f)`. -/
def LipC (ρ : CliffordRep n V) (c : ℝ) (f : E n → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ ∀ x, ‖c • cliff ρ (gradient f x)‖ ≤ 1

/-- Connes' distance for the rescaled Dirac operator `c • D`. -/
noncomputable def connesDistC (ρ : CliffordRep n V) (c : ℝ) (p q : E n) : ℝ :=
  sSup {r | ∃ f, LipC ρ c f ∧ r = |f p - f q|}

lemma LipC.norm_gradient_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {c : ℝ}
    (hc : c ≠ 0) {f : E n → ℝ} (hf : LipC ρ c f) (x : E n) : ‖gradient f x‖ ≤ |c|⁻¹ := by
  have h := hf.2 x
  rw [norm_smul, opNorm_cliff hρ, Real.norm_eq_abs] at h
  have hc' : 0 < |c| := abs_pos.mpr hc
  calc ‖gradient f x‖ = |c|⁻¹ * (|c| * ‖gradient f x‖) := by field_simp
    _ ≤ |c|⁻¹ * 1 := by gcongr
    _ = |c|⁻¹ := mul_one _

/-- Functions in `LipC` are `|c|⁻¹`-Lipschitz. -/
lemma LipC.abs_sub_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {c : ℝ} (hc : c ≠ 0)
    {f : E n → ℝ} (hf : LipC ρ c f) (p q : E n) : |f p - f q| ≤ |c|⁻¹ * ‖p - q‖ := by
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := f) (C := |c|⁻¹)
    (fun x _ => (hf.1.differentiable one_ne_zero).differentiableAt)
    (fun x _ => by rw [norm_fderiv_eq_gradient]; exact hf.norm_gradient_le hρ hc x)
    (Set.mem_univ q) (Set.mem_univ p)
  simpa [Real.norm_eq_abs] using h

lemma lipC_zero (ρ : CliffordRep n V) (c : ℝ) : LipC ρ c (fun _ => 0) := by
  refine ⟨contDiff_const, fun x => ?_⟩
  simp [cliff_zero]

lemma gradient_inner_const (u : E n) (x : E n) :
    gradient (fun x : E n => inner ℝ u x) x = u := by
  have h : HasGradientAt (fun x : E n => inner ℝ u x) u x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (innerSL ℝ u).hasFDerivAt (x := x)
  exact h.gradient

/-- The linear function `⟪u, ·⟫` with `|c| ‖u‖ ≤ 1` lies in `LipC`. -/
lemma lipC_inner {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (c : ℝ) (u : E n)
    (hu : |c| * ‖u‖ ≤ 1) : LipC ρ c (fun x => inner ℝ u x) := by
  refine ⟨(innerSL ℝ u).contDiff, fun x => ?_⟩
  rw [gradient_inner_const, norm_smul, opNorm_cliff hρ, Real.norm_eq_abs]
  exact hu

lemma connesDistC_bdd {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {c : ℝ} (hc : c ≠ 0)
    (p q : E n) : BddAbove {r | ∃ f, LipC ρ c f ∧ r = |f p - f q|} :=
  ⟨|c|⁻¹ * ‖p - q‖, by rintro r ⟨f, hf, rfl⟩; exact hf.abs_sub_le hρ hc p q⟩

lemma connesDistC_le {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {c : ℝ} (hc : c ≠ 0)
    (p q : E n) : connesDistC ρ c p q ≤ |c|⁻¹ * ‖p - q‖ :=
  csSup_le ⟨_, 0, lipC_zero ρ c, rfl⟩
    (by rintro r ⟨f, hf, rfl⟩; exact hf.abs_sub_le hρ hc p q)

lemma le_connesDistC {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {c : ℝ} (hc : c ≠ 0)
    (p q : E n) : |c|⁻¹ * ‖p - q‖ ≤ connesDistC ρ c p q := by
  have hc' : 0 < |c| := abs_pos.mpr hc
  by_cases hpq : p = q
  · subst hpq
    simp only [sub_self, norm_zero, mul_zero]
    exact le_csSup (connesDistC_bdd hρ hc p p) ⟨_, lipC_zero ρ c, by simp⟩
  · have hn : 0 < ‖p - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hpq)
    set u : E n := (|c|⁻¹ * ‖p - q‖⁻¹) • (p - q) with hu
    have hu1 : |c| * ‖u‖ ≤ 1 := by
      rw [hu, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_inv, abs_abs, abs_norm]
      apply le_of_eq
      field_simp
    have hval : |inner ℝ u p - inner ℝ u q| = |c|⁻¹ * ‖p - q‖ := by
      rw [← inner_sub_right, hu, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [conj_trivial]
      rw [abs_of_nonneg (by positivity : 0 ≤ (|c|⁻¹ * ‖p - q‖⁻¹) * ‖p - q‖ ^ 2)]
      field_simp
    exact hval.symm.le.trans
      (le_csSup (connesDistC_bdd hρ hc p q) ⟨_, lipC_inner hρ c u hu1, rfl⟩)

/-- **Scaling of Connes' distance**: for `c ≠ 0`, the spectral distance of `c • D` on `ℝⁿ` is
`‖p - q‖ / |c|`; in particular scaling `D` by `2` halves all distances. -/
theorem connesDistC_eq {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] {c : ℝ} (hc : c ≠ 0)
    (p q : E n) : connesDistC ρ c p q = ‖p - q‖ / |c| := by
  rw [div_eq_inv_mul]
  exact le_antisymm (connesDistC_le hρ hc p q) (le_connesDistC hρ hc p q)

/-- Trust check: doubling the Dirac operator halves every distance. -/
theorem connesDistC_two {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (p q : E n) :
    connesDistC ρ 2 p q = connesDist ρ p q / 2 := by
  rw [connesDistC_eq hρ two_ne_zero, connesDist_eq_norm hρ]
  simp

end Lightlike.Dirac
