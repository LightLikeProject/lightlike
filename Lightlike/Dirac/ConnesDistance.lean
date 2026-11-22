import Mathlib
import Lightlike.Dirac.SelfAdjoint

/-!
# Clifford multiplication by a vector and the commutator `[D, f]` on `ℝⁿ`

First layer of the *Connes distance formula* for the flat Dirac operator (milestone NC2, which needs
GE5).  For a vector `v ∈ ℝⁿ` the Clifford multiplication `cliff ρ v = ρ(ι v)` squares to `-‖v‖²`
(`cliff_sq`) and, in a skew Clifford module, multiplies norms by `‖v‖` (`norm_cliff`).  The commutator
of the Dirac operator with a scalar function `f` is the Clifford multiplication by its gradient,
`D(fψ) = f Dψ + cliff(∇f) ψ` (`dirac_smul`), so that `‖[D, f]‖ = sup ‖∇f‖`
(`opNorm_cliff` for the pointwise part).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); definitions only, no equation
  number is claimed.
-/

open CliffordAlgebra InnerProductSpace

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Clifford multiplication by a vector `v ∈ ℝⁿ`: `ρ(ι v)`. -/
noncomputable def cliff (ρ : CliffordRep n V) (v : E n) : V →L[ℝ] V :=
  ρ (ι (Qneg n) v)

/-- `cliff ρ v = ∑ᵢ vᵢ γᵢ`. -/
lemma cliff_eq_sum (ρ : CliffordRep n V) (v : E n) : cliff ρ v = ∑ i, v i • gam ρ i := by
  have hv : v = ∑ i, v i • e i := by
    ext j
    simp [e, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [cliff, gam, map_sum, map_smul]

/-- `cliff ρ v` is linear in `v`. -/
lemma cliff_add (ρ : CliffordRep n V) (v w : E n) : cliff ρ (v + w) = cliff ρ v + cliff ρ w := by
  simp [cliff]

lemma cliff_smul (ρ : CliffordRep n V) (c : ℝ) (v : E n) : cliff ρ (c • v) = c • cliff ρ v := by
  simp [cliff]

lemma cliff_zero (ρ : CliffordRep n V) : cliff ρ 0 = 0 := by
  simp [cliff]

/-- `cliff(v)² = -‖v‖²`. -/
lemma cliff_sq (ρ : CliffordRep n V) (v : E n) (w : V) :
    cliff ρ v (cliff ρ v w) = -(‖v‖ ^ 2) • w := by
  have h := congrArg ρ (ι_sq_scalar (Qneg n) v)
  have h2 : cliff ρ v * cliff ρ v = algebraMap ℝ (V →L[ℝ] V) (-(‖v‖ ^ 2)) := by
    simp [cliff, Qneg_apply]
  have := congrArg (fun L => L w) h2
  simpa [Algebra.algebraMap_eq_smul_one] using this

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Clifford multiplication by a vector is skew-adjoint in a skew Clifford module. -/
lemma inner_cliff {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (v : E n) (a b : V) :
    inner ℝ (cliff ρ v a) b = -inner ℝ a (cliff ρ v b) := by
  rw [cliff_eq_sum]
  simp only [sum_apply, smul_apply, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right, hρ _ _ _, Finset.sum_neg_distrib,
    mul_neg, RCLike.conj_to_real]

/-- Clifford multiplication by `v` multiplies norms by `‖v‖`. -/
lemma norm_cliff {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (v : E n) (w : V) :
    ‖cliff ρ v w‖ = ‖v‖ * ‖w‖ := by
  have h : ‖cliff ρ v w‖ ^ 2 = (‖v‖ * ‖w‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_cliff hρ, cliff_sq,
      inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h

/-- The operator norm of Clifford multiplication by `v` is `‖v‖` on a nonzero module. -/
lemma opNorm_cliff {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) [Nontrivial V] (v : E n) :
    ‖cliff ρ v‖ = ‖v‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_) ?_
  · exact (norm_cliff hρ v w).le
  · obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have := (cliff ρ v).le_opNorm w
    rw [norm_cliff hρ] at this
    exact le_of_mul_le_mul_right this hw'

end Inner

end Lightlike.Dirac
