import Mathlib
import Lightlike.Dirac.SpinConnection

/-!
# Derivative of the spinorial connection term, and its bracket

Two facts needed for the Ricci identity of the spin connection:

* the product rule `∂ᵥ (spinForm (M y) (g y)) = spinForm (∂ᵥ M) (g x) + spinForm (M x) (∂ᵥ g)`
  (`fderiv_spinForm_apply`);
* the bracket `[spinForm A, spinForm B] = spinForm (B A - A B)` for skew `A` (`spinForm_bracket`),
  so that `spinForm` is an anti-homomorphism for the convention `[spinForm A, γₖ] = ∑ⱼ Aₖⱼ γⱼ`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma spinForm_apply (ρ : CliffordRep n V) (M : Matrix (Fin n) (Fin n) ℝ) (w : V) :
    spinForm ρ M w = (1 / 4 : ℝ) • ∑ k, ∑ l, M k l • (gam ρ k (gam ρ l w)) := by
  simp [spinForm]

lemma spinForm_add (ρ : CliffordRep n V) (A B : Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ (A + B) = spinForm ρ A + spinForm ρ B := by
  ext w
  simp only [spinForm_apply, add_apply, Matrix.add_apply, add_smul,
    Finset.sum_add_distrib, smul_add]

lemma spinForm_sub (ρ : CliffordRep n V) (A B : Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ (A - B) = spinForm ρ A - spinForm ρ B := by
  ext w
  simp only [spinForm_apply, sub_apply, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib, smul_sub]

lemma spinForm_smul (ρ : CliffordRep n V) (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ (c • A) = c • spinForm ρ A := by
  ext w
  simp only [spinForm_apply, smul_apply, Matrix.smul_apply, smul_eq_mul,
    mul_smul, ← Finset.smul_sum, smul_comm c (1 / 4 : ℝ)]

lemma spinForm_sum (ρ : CliffordRep n V) {ι : Type*} (s : Finset ι)
    (A : ι → Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ (∑ i ∈ s, A i) = ∑ i ∈ s, spinForm ρ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext w
    simp [spinForm_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, spinForm_add, ih]

/-- Product rule for `y ↦ spinForm (M y) (g y)`. -/
theorem hasFDerivAt_spinForm (ρ : CliffordRep n V) {M : E n → Matrix (Fin n) (Fin n) ℝ}
    {g : E n → V} {x : E n} (hM : ∀ k l, DifferentiableAt ℝ (fun y => M y k l) x)
    (hg : DifferentiableAt ℝ g x) :
    HasFDerivAt (fun y => spinForm ρ (M y) (g y))
      ((1 / 4 : ℝ) • ∑ k, ∑ l, ((M x k l) • ((gam ρ k * gam ρ l).comp (fderiv ℝ g x)) +
        (fderiv ℝ (fun y => M y k l) x).smulRight ((gam ρ k * gam ρ l) (g x)))) x := by
  have key : (fun y => spinForm ρ (M y) (g y)) =
      fun y => (1 / 4 : ℝ) • ∑ k, ∑ l, (M y k l) • ((gam ρ k * gam ρ l) (g y)) := by
    funext y
    rw [spinForm_apply]
    simp only [mul_apply_eq_comp]
  rw [key]
  refine HasFDerivAt.const_smul (HasFDerivAt.fun_sum fun k _ => HasFDerivAt.fun_sum fun l _ => ?_) _
  exact (hM k l).hasFDerivAt.smul (((gam ρ k * gam ρ l).hasFDerivAt).comp x hg.hasFDerivAt)

/-- The derivative of `y ↦ spinForm (M y) (g y)` in the direction `v`. -/
theorem fderiv_spinForm_apply (ρ : CliffordRep n V) {M : E n → Matrix (Fin n) (Fin n) ℝ}
    {g : E n → V} {x : E n} (hM : ∀ k l, DifferentiableAt ℝ (fun y => M y k l) x)
    (hg : DifferentiableAt ℝ g x) (v : E n) :
    fderiv ℝ (fun y => spinForm ρ (M y) (g y)) x v =
      spinForm ρ (fun k l => fderiv ℝ (fun y => M y k l) x v) (g x) +
        spinForm ρ (M x) (fderiv ℝ g x v) := by
  rw [(hasFDerivAt_spinForm ρ hM hg).fderiv]
  simp only [smul_apply, sum_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, spinForm_apply, mul_apply_eq_comp]
  simp only [Finset.sum_add_distrib, smul_add]
  rw [spinForm_apply ρ (fun k l => fderiv ℝ (fun y => M y k l) x v) (g x), add_comm]

lemma sum3_perm {M : Type*} [AddCommMonoid M] (f : Fin n → Fin n → Fin n → M) :
    ∑ k, ∑ l, ∑ j, f k l j = ∑ j, ∑ l, ∑ k, f k l j := by
  calc ∑ k, ∑ l, ∑ j, f k l j = ∑ k, ∑ j, ∑ l, f k l j :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, f k l j := Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, f k l j := Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- For skew `A`, `[spinForm A, spinForm B] = spinForm (B A - A B)`. -/
theorem spinForm_bracket (ρ : CliffordRep n V) {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, A i j = - A j i) :
    spinForm ρ A * spinForm ρ B - spinForm ρ B * spinForm ρ A = spinForm ρ (B * A - A * B) := by
  have hc : ∀ k, spinForm ρ A * gam ρ k - gam ρ k * spinForm ρ A = ∑ j, A k j • gam ρ j :=
    spinForm_comm ρ hA
  have h1 : ∀ k l, spinForm ρ A * (gam ρ k * gam ρ l) - (gam ρ k * gam ρ l) * spinForm ρ A =
      (∑ j, A k j • gam ρ j) * gam ρ l + gam ρ k * (∑ j, A l j • gam ρ j) := by
    intro k l
    rw [← hc k, ← hc l]
    noncomm_ring
  have h2 : spinForm ρ A * spinForm ρ B - spinForm ρ B * spinForm ρ A =
      (1 / 4 : ℝ) • ∑ k, ∑ l, B k l •
        ((∑ j, A k j • gam ρ j) * gam ρ l + gam ρ k * (∑ j, A l j • gam ρ j)) := by
    rw [show spinForm ρ B = (1 / 4 : ℝ) • ∑ k, ∑ l, B k l • (gam ρ k * gam ρ l) from rfl]
    simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← smul_sub,
      ← Finset.sum_sub_distrib, h1]
  rw [h2]
  show _ = (1 / 4 : ℝ) • ∑ i, ∑ j, (B * A - A * B) i j • (gam ρ i * gam ρ j)
  congr 1
  have p1 : ∑ k, ∑ l, B k l • ((∑ j, A k j • gam ρ j) * gam ρ l) =
      ∑ i, ∑ j, (-(A * B) i j) • (gam ρ i * gam ρ j) := by
    simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul, Matrix.mul_apply,
      neg_smul, Finset.sum_neg_distrib, Finset.sum_smul]
    refine (sum3_perm (M := V →L[ℝ] V) _).trans ?_
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun m _ => ?_
    rw [hA m i]
    rw [mul_neg, neg_smul, mul_comm]
  have p2 : ∑ k, ∑ l, B k l • (gam ρ k * (∑ j, A l j • gam ρ j)) =
      ∑ i, ∑ j, (B * A) i j • (gam ρ i * gam ρ j) := by
    simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul, Matrix.mul_apply,
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have e : ∀ i j, (B * A - A * B) i j • (gam ρ i * gam ρ j) =
      (B * A) i j • (gam ρ i * gam ρ j) + (-(A * B) i j) • (gam ρ i * gam ρ j) := by
    intro i j
    rw [← add_smul, Matrix.sub_apply]
    rw [sub_eq_add_neg]
  simp only [smul_add, Finset.sum_add_distrib, e]
  rw [p1, p2, add_comm]

end Lightlike.Dirac
