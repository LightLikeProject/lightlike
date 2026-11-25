import QuantumInfo.Entropy.VonNeumann
import QuantumInfo.States.Entanglement

/-!
# Page's value of the average entanglement entropy: the closed form and its trust checks

Milestone SC8 (the Page curve of random pure states, Page 1993, eq. (11); Sen 1996): the average entanglement entropy of
a Haar-random pure state on `ℂ^m ⊗ ℂ^n` with `m ≤ n` is
`Σ_{k=n+1}^{mn} 1/k − (m − 1)/(2n)`.

This module defines the closed form `pageValue m n` and proves the two trust checks of the milestone that do not need the
random-state ensemble:

* `pageValue_two_two`: `m = n = 2` gives `1/3`;
* `pageValue_one_left`: `m = 1` gives `0` (a factor of dimension one carries no entanglement);
* `sVN_traceRight_prod_pure`: a product pure state has reduced von Neumann entropy `0`
  (Physlib's `Sᵥₙ`), the physical counterpart of the previous line;
* `pageValue_wrong_two_two`: dropping the correction `(m − 1)/(2n)` gives `7/12 ≠ 1/3`.
-/

namespace Lightlike.QM.PageEntropy

open Finset

/-- **Page's closed form** `Σ_{k=n+1}^{mn} 1/k − (m − 1)/(2n)` for the average entanglement entropy of a random pure state
of `ℂ^m ⊗ ℂ^n` (meaningful for `m ≤ n`). -/
noncomputable def pageValue (m n : ℕ) : ℝ :=
  (∑ k ∈ Ioc n (m * n), (1 : ℝ) / k) - ((m : ℝ) - 1) / (2 * n)

/-- `m = n = 2` gives `1/3`. -/
theorem pageValue_two_two : pageValue 2 2 = 1 / 3 := by
  unfold pageValue
  have : Ioc (2 : ℕ) (2 * 2) = {3, 4} := by decide
  rw [this]
  norm_num [sum_pair]

/-- A factor of dimension one has no entanglement: `m = 1` gives `0`. -/
theorem pageValue_one_left (n : ℕ) : pageValue 1 n = 0 := by
  simp [pageValue]

/-- Trust check (wrong model): without the correction term `(m − 1)/(2n)` the `m = n = 2` value would be `7/12`. -/
theorem pageValue_wrong_two_two :
    (∑ k ∈ Ioc (2 : ℕ) (2 * 2), (1 : ℝ) / k) = 7 / 12 ∧ (7 / 12 : ℝ) ≠ pageValue 2 2 := by
  have : Ioc (2 : ℕ) (2 * 2) = {3, 4} := by decide
  rw [this, pageValue_two_two]
  norm_num [sum_pair]

/-- **Product pure states have zero entropy**: the reduced state of `ψ₁ ⊗ ψ₂` has von Neumann entropy `0`. -/
theorem sVN_traceRight_prod_pure {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : Sᵥₙ (MState.pure (ψ₁ ⊗ᵠ ψ₂)).traceRight = 0 := by
  rw [MState.pure_prod_pure, MState.traceRight_prod_eq]
  exact Sᵥₙ_of_pure_zero ψ₁

end Lightlike.QM.PageEntropy

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_069.pageValue := _root_.Lightlike.QM.PageEntropy.pageValue
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_069.pageValue_one_left := _root_.Lightlike.QM.PageEntropy.pageValue_one_left
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_069.pageValue_two_two := _root_.Lightlike.QM.PageEntropy.pageValue_two_two
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_069.pageValue_wrong_two_two := _root_.Lightlike.QM.PageEntropy.pageValue_wrong_two_two
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_069.sVN_traceRight_prod_pure := _root_.Lightlike.QM.PageEntropy.sVN_traceRight_prod_pure
