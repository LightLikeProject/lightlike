import Mathlib
import Lightlike.Dirac.Flat

/-!
# The algebraic core of the spin connection

For a Clifford module `ρ` over `Cl(ℝⁿ, -‖·‖²)` and a skew matrix `ω` (the connection form of the
Levi-Civita connection in an orthonormal frame), the spin connection is `∇ = d + ¼ ∑ᵢⱼ ωᵢⱼ γᵢγⱼ`.
This file proves the identity that makes Clifford multiplication parallel for it:
`[¼ ∑ᵢⱼ ωᵢⱼ γᵢγⱼ, γₖ] = ∑ⱼ ωₖⱼ γⱼ`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); definitions only, no equation
  number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `γᵢγᵢ = -1` as an identity of operators. -/
lemma gam_mul_self (ρ : CliffordRep n V) (i : Fin n) : gam ρ i * gam ρ i = -1 := by
  ext w
  simpa using gam_sq ρ i w

/-- `γᵢγⱼ = -γⱼγᵢ` for `i ≠ j`, as an identity of operators. -/
lemma gam_mul_swap (ρ : CliffordRep n V) {i j : Fin n} (hij : i ≠ j) :
    gam ρ i * gam ρ j = -(gam ρ j * gam ρ i) := by
  ext w
  have := gam_anticomm ρ hij w
  simp only [mul_apply_eq_comp, neg_apply]
  exact eq_neg_of_add_eq_zero_left this

/-- The commutator of a bivector `γᵢγⱼ` with `γₖ`: `[γᵢγⱼ, γₖ] = 2δᵢₖ γⱼ - 2δⱼₖ γᵢ`. -/
lemma gam_comm_pair (ρ : CliffordRep n V) (i j k : Fin n) :
    gam ρ i * gam ρ j * gam ρ k - gam ρ k * (gam ρ i * gam ρ j) =
      (if i = k then (2 : ℝ) • gam ρ j else 0) - (if j = k then (2 : ℝ) • gam ρ i else 0) := by
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik; subst hjk
    simp [mul_assoc]
  · subst hik
    have h1 := gam_mul_self ρ i
    have hba : gam ρ j * gam ρ i = -(gam ρ i * gam ρ j) := gam_mul_swap ρ hjk
    have key : gam ρ i * gam ρ j * gam ρ i = gam ρ j := by
      rw [mul_assoc, hba, mul_neg, ← mul_assoc, h1]; simp
    have key2 : gam ρ i * (gam ρ i * gam ρ j) = -gam ρ j := by
      rw [← mul_assoc, h1]; simp
    rw [key, key2]
    simp [hjk, two_smul]
  · subst hjk
    have h1 := gam_mul_self ρ j
    have hba : gam ρ j * gam ρ i = -(gam ρ i * gam ρ j) := gam_mul_swap ρ (Ne.symm hik)
    have key : gam ρ i * gam ρ j * gam ρ j = -gam ρ i := by
      rw [mul_assoc, h1]; simp
    have key2 : gam ρ j * (gam ρ i * gam ρ j) = gam ρ i := by
      rw [← mul_assoc, hba, neg_mul, mul_assoc, h1]; simp
    rw [key, key2]
    simp [hik, two_smul]
    abel
  · have hca : gam ρ k * gam ρ i = -(gam ρ i * gam ρ k) := gam_mul_swap ρ (Ne.symm hik)
    have hcb : gam ρ k * gam ρ j = -(gam ρ j * gam ρ k) := gam_mul_swap ρ (Ne.symm hjk)
    have h4 : gam ρ k * (gam ρ i * gam ρ j) = gam ρ i * gam ρ j * gam ρ k := by
      rw [← mul_assoc, hca, neg_mul, mul_assoc, hcb, mul_neg, neg_neg, ← mul_assoc]
    simp [hik, hjk, h4]

/-- The spinorial connection form `¼ ∑ᵢⱼ ωᵢⱼ γᵢγⱼ` of a matrix `ω`. -/
noncomputable def spinForm (ρ : CliffordRep n V) (ω : Matrix (Fin n) (Fin n) ℝ) : V →L[ℝ] V :=
  (1 / 4 : ℝ) • ∑ i, ∑ j, ω i j • (gam ρ i * gam ρ j)

/-- For a skew matrix `ω`, `[¼ ∑ ωᵢⱼ γᵢγⱼ, γₖ] = ∑ⱼ ωₖⱼ γⱼ`: Clifford multiplication is
parallel for the connection `d + spinForm ω` when `ω` is the Levi-Civita connection form in an
orthonormal frame. -/
theorem spinForm_comm (ρ : CliffordRep n V) {ω : Matrix (Fin n) (Fin n) ℝ}
    (hω : ∀ i j, ω i j = -ω j i) (k : Fin n) :
    spinForm ρ ω * gam ρ k - gam ρ k * spinForm ρ ω = ∑ j, ω k j • gam ρ j := by
  have h : spinForm ρ ω * gam ρ k - gam ρ k * spinForm ρ ω =
      (1 / 4 : ℝ) • ∑ i, ∑ j, ω i j • (gam ρ i * gam ρ j * gam ρ k - gam ρ k * (gam ρ i * gam ρ j)) := by
    simp only [spinForm, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, ← smul_sub,
      ← Finset.sum_sub_distrib]
  rw [h]
  simp only [gam_comm_pair, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero,
    smul_smul]
  rw [Finset.sum_comm (f := fun x x_1 => if x_1 = k then (ω x x_1 * 2) • gam ρ x else 0)]
  have e1 : ∀ (g : Fin n → Fin n → V →L[ℝ] V),
      ∑ x, ∑ y, (if x = k then g x y else 0) = ∑ y, g k y := by
    intro g
    simp [Finset.sum_ite_eq']
  have e2 : ∀ j, ω j k = - ω k j := fun j => by rw [hω j k]
  rw [e1 (fun x y => (ω x y * 2) • gam ρ y), e1 (fun x y => (ω y x * 2) • gam ρ y)]
  simp only [e2]
  rw [← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sub_smul, smul_smul]
  congr 1
  ring

end Lightlike.Dirac
