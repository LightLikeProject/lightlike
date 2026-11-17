import Mathlib
import Lightlike.Canonical.ADM
import Lightlike.Canonical.LieDeriv

/-!
# The bracket of two smeared momentum constraints

`{D[ξ], D[η]} = D[[ξ, η]]` for smooth, compactly supported shifts `ξ, η` and smooth data, computed with the
bracket of `Lightlike/Canonical/ADM.lean` on test fields (Gateaux derivatives along compactly supported
variations), the `π`-gradient of `D[ξ]` being `ℒ_ξ h` (`isPiGradient_momentumConstraint`).
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma hcs_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin d → ℝ) → ℝ) (h : ∀ k ∈ s, HasCompactSupport (f k)) :
    HasCompactSupport (fun x => ∑ k ∈ s, f k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- A Lie derivative along a compactly supported field has compact support. -/
lemma hcs_lieDeriv {ξ : VectorField d} (hξ : ∀ k, HasCompactSupport (fun y => ξ y k)) (h : TensorField d)
    (i j : Fin d) : HasCompactSupport (fun y => lieDeriv ξ h i j y) := by
  unfold lieDeriv
  refine ((hcs_sum _ _ fun k _ => ?_).add (hcs_sum _ _ fun k _ => ?_)).add (hcs_sum _ _ fun k _ => ?_)
  · exact (hξ k).mul_right (f' := fun y => Lightlike.pd k (fun y => h y i j) y)
  · exact (hξ k).fderiv_apply (𝕜 := ℝ) (Pi.single i 1) |>.mul_left (f := fun y => h y k j)
  · exact (hξ k).fderiv_apply (𝕜 := ℝ) (Pi.single j 1) |>.mul_left (f := fun y => h y i k)

lemma continuous_lieDeriv {ξ : VectorField d} {h : TensorField d} (hh : SmoothTensor h) (hξ : SmoothVec ξ)
    (i j : Fin d) : Continuous (fun y => lieDeriv ξ h i j y) :=
  (smoothTensor_lieDeriv hh hξ i j).continuous

/-- The momentum-constraint integrand is integrable for compactly supported shifts. -/
lemma integrable_momentumDensity {ξ : VectorField d} {h π : TensorField d} (hh : SmoothTensor h)
    (hξ : SmoothVec ξ) (hξc : ∀ k, HasCompactSupport (fun y => ξ y k))
    (hπ : ∀ i j, Continuous (fun x => π x i j)) : Integrable (momentumDensity ξ h π) := by
  have hc : Continuous (momentumDensity ξ h π) := by
    unfold momentumDensity
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (hπ i j).mul (continuous_lieDeriv hh hξ i j)
  refine hc.integrable_of_hasCompactSupport ?_
  unfold momentumDensity
  exact hcs_sum _ _ fun i _ => hcs_sum _ _ fun j _ =>
    (hcs_lieDeriv hξc h i j).mul_left (f := fun x => π x i j)

lemma smoothTensor_lieTensor {ξ : VectorField d} {h : TensorField d} (hh : SmoothTensor h) (hξ : SmoothVec ξ) :
    SmoothTensor (lieTensor ξ h) := smoothTensor_lieDeriv hh hξ

/-- The Lie derivative is linear in the tensor. -/
lemma lieDeriv_add_smul {ξ : VectorField d} {h k : TensorField d} (hh : SmoothTensor h) (hk : SmoothTensor k)
    (t : ℝ) (i j : Fin d) (x : Fin d → ℝ) :
    lieDeriv ξ (fun y => h y + t • k y) i j x = lieDeriv ξ h i j x + t * lieDeriv ξ k i j x := by
  have e : ∀ (m a b : Fin d), Lightlike.pd m (fun y => h y a b + t * k y a b) x =
      Lightlike.pd m (fun y => h y a b) x + t * Lightlike.pd m (fun y => k y a b) x := by
    intro m a b
    rw [Lightlike.pd_add (diff_of_smooth (hh a b) x) ((diff_of_smooth (hk a b) x).const_mul t),
      Lightlike.pd_const_mul t (diff_of_smooth (hk a b) x)]
  have h1 : ∀ f g : Fin d → ℝ, ∑ k, f k * (t * g k) = t * ∑ k, f k * g k := fun f g => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∀ f g : Fin d → ℝ, ∑ k, (t * f k) * g k = t * ∑ k, f k * g k := fun f g => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  unfold lieDeriv
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, e, mul_add, add_mul, Finset.sum_add_distrib,
    h1, h2]
  ring

lemma momentumDensity_add_smul {ξ : VectorField d} {h k : TensorField d} (hh : SmoothTensor h)
    (hk : SmoothTensor k) (π : TensorField d) (t : ℝ) (x : Fin d → ℝ) :
    momentumDensity ξ (fun y => h y + t • k y) π x =
      momentumDensity ξ h π x + t * momentumDensity ξ k π x := by
  unfold momentumDensity
  simp only [lieDeriv_add_smul hh hk, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `D[ξ]` is linear in `h`: its derivative at `(h, π)` along `(k, 0)` is `D[ξ](k, π)`. -/
lemma dirDeriv_momentum_h {ξ : VectorField d} (hξ : SmoothVec ξ) (hξc : ∀ k, HasCompactSupport (fun y => ξ y k))
    {h k π : TensorField d} (hh : SmoothTensor h) (hk : SmoothTensor k)
    (hπ : ∀ i j, Continuous (fun x => π x i j)) :
    dirDeriv (momentumConstraint ξ) h π k 0 = momentumConstraint ξ k π := by
  unfold dirDeriv
  have hfun : (fun t : ℝ => momentumConstraint ξ (fun x => h x + t • k x) (fun x => π x + t • (0 : TensorField d) x)) =
      fun t => momentumConstraint ξ h π + t * momentumConstraint ξ k π := by
    funext t
    simp only [Pi.zero_apply, smul_zero, add_zero]
    unfold momentumConstraint
    simp only [momentumDensity_add_smul hh hk]
    rw [integral_add (integrable_momentumDensity hh hξ hξc hπ)
      ((integrable_momentumDensity hk hξ hξc hπ).const_mul t), integral_const_mul]
  rw [hfun]
  simp

/-- **The `π`-gradient of the smeared momentum constraint is `ℒ_ξ h`**: `δD[ξ]/δπ^{ij} = (ℒ_ξ h)_ij`. -/
theorem isPiGradient_momentumConstraint {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hξc : ∀ k, HasCompactSupport (fun y => ξ y k)) :
    IsPiGradient (momentumConstraint ξ) (fun h _ => lieTensor ξ h) := by
  intro h π p ⟨hh, _, hπ⟩ hpc hps
  unfold dirDeriv
  have hint : Integrable (fun x => ∑ i, ∑ j, lieDeriv ξ h i j x * p x i j) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (continuous_lieDeriv hh hξ i j).mul (hps i j).continuous
    · exact hcs_sum _ _ fun i _ => hcs_sum _ _ fun j _ =>
        (hpc i j).mul_left (f := fun x => lieDeriv ξ h i j x)
  have hfun : (fun t : ℝ => momentumConstraint ξ (fun x => h x + t • (0 : TensorField d) x)
        (fun x => π x + t • p x)) =
      fun t => momentumConstraint ξ h π + t * ∫ x, ∑ i, ∑ j, lieDeriv ξ h i j x * p x i j := by
    funext t
    simp only [Pi.zero_apply, smul_zero, add_zero]
    unfold momentumConstraint
    have hpt : ∀ x, momentumDensity ξ h (fun x => π x + t • p x) x =
        momentumDensity ξ h π x + t * ∑ i, ∑ j, lieDeriv ξ h i j x * p x i j := by
      intro x
      unfold momentumDensity
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [hpt]
    rw [integral_add (integrable_momentumDensity hh hξ hξc hπ) (hint.const_mul t), integral_const_mul]
  rw [hfun]
  simp [lieTensor]

/-- **The bracket of two smeared momentum constraints**: `{D[ξ], D[η]} = D[[ξ, η]]` for smooth,
compactly supported shifts, smooth `h` and continuous `π`, with `[ξ,η]^k = ξ^j ∂_j η^k − η^j ∂_j ξ^k`.

Differences, approved by the owner (17 November 2026): (a) same setting as the source, (b) partial, (c) convention, (d) and (e) representation (compared with Thiemann, arXiv:gr-qc/0110034, §I.1.1, eqs. (I.1.1.27), (I.1.1.28), (I.1.1.36), (I.1.1.37) (the lecture-note version of the cited book); Hojman-Kuchar-Teitelboim 1976 has not been read): (a) `C^∞` data and compactly supported test fields, `π`
continuous; (b) one global chart `ℝᵈ`, no manifold and no foliation; (c) units `16πG = 1`; (d) the momentum
constraint in the Lie-derivative form; (e) the bracket through `π`-gradients and Gateaux derivatives, and
the sign conventions of `admBracket` and `lieBracket`. -/
theorem bracket_momentum_momentum {ξ η : VectorField d} (hξ : SmoothVec ξ) (hη : SmoothVec η)
    (hξc : ∀ k, HasCompactSupport (fun y => ξ y k)) (hηc : ∀ k, HasCompactSupport (fun y => η y k))
    {h π : TensorField d} (hh : SmoothTensor h) (hπ : ∀ i j, Continuous (fun x => π x i j)) :
    admBracket (momentumConstraint ξ) (momentumConstraint η) (fun h _ => lieTensor ξ h)
        (fun h _ => lieTensor η h) h π =
      momentumConstraint (fun y k => lieBracket ξ η y k) h π := by
  unfold admBracket
  rw [dirDeriv_momentum_h hξ hξc hh (smoothTensor_lieTensor hh hη) hπ,
    dirDeriv_momentum_h hη hηc hh (smoothTensor_lieTensor hh hξ) hπ]
  unfold momentumConstraint
  rw [← integral_sub (integrable_momentumDensity (smoothTensor_lieTensor hh hη) hξ hξc hπ)
    (integrable_momentumDensity (smoothTensor_lieTensor hh hξ) hη hηc hπ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [momentumDensity, ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun r => π x i j * r) (lieDeriv_comm hh hξ hη i j x)

end Lightlike.Canonical

end
