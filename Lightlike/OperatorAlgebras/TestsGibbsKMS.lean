import Lightlike.OperatorAlgebras.GibbsKMS

/-!
# Tests for the Gibbs state in infinite dimension: the harmonic oscillator

`H = diag(0, 1, 2, …)` on `ℓ²(ℕ)` (the number operator, the oscillator Hamiltonian up to the constant `1/2`):

* `summable_exp_neg_mul_nat`: `∑ₙ e^{-βn} < ∞` for `β > 0`, so the Gibbs state exists;
* `oscillator_isKMS`: its Gibbs state satisfies the KMS condition `F_{A,B}(t + iβ) = ω(τᵗ(B) A)`;
* `not_summable_exp_zero`: at `β = 0` the partition sum diverges (`e^{-0·H} = 1` is not trace class), the wrong input.
-/

namespace Lightlike.OperatorAlgebras.GibbsKMS

/-- The standard Hilbert basis of `ℓ²(ℕ)`. -/
noncomputable def stdBasisN : HilbertBasis ℕ ℂ (lp (fun _ : ℕ => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- **`∑ₙ e^{-βn} < ∞` for `β > 0`**, a geometric series. -/
lemma summable_exp_neg_mul_nat {β : ℝ} (hβ : 0 < β) : Summable fun n : ℕ => Real.exp (-(β * (n : ℝ))) := by
  have h : (fun n : ℕ => Real.exp (-(β * (n : ℝ)))) = fun n => Real.exp (-β) ^ n := by
    funext n
    rw [show -(β * (n : ℝ)) = n * (-β) by ring, Real.exp_nat_mul]
  rw [h]
  exact summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβ))

/-- **The Gibbs state of the oscillator satisfies the KMS condition** at every `β > 0`. -/
theorem oscillator_isKMS {β : ℝ} (hβ : 0 < β) (A B : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) (t : ℝ) :
    kmsFun stdBasisN (fun n => (n : ℝ)) β A B (t + Complex.I * β) =
      gibbs stdBasisN (fun n => (n : ℝ)) β (dyn stdBasisN (fun n => (n : ℝ)) t B * A) :=
  kmsFun_add_I_mul stdBasisN _ hβ (summable_exp_neg_mul_nat hβ) A B t

/-- **At `β = 0` the partition sum diverges** (a wrong input: `e^{-0·H} = 1` is not trace class on `ℓ²(ℕ)`). -/
theorem not_summable_exp_zero : ¬ Summable fun n : ℕ => Real.exp (-(0 * (n : ℝ))) := by
  have h : (fun n : ℕ => Real.exp (-(0 * (n : ℝ)))) = fun _ => (1 : ℝ) := by
    funext n; simp
  rw [h, summable_const_iff]
  exact one_ne_zero

end Lightlike.OperatorAlgebras.GibbsKMS
