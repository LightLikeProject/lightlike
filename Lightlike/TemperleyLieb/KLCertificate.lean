import Mathlib
import Lightlike.TemperleyLieb.QNumbers

/-!
# The q-number identities behind the third-block recursion of the Kauffman–Lins coefficient

The recursion of `klCoef` in the third block is a contiguous relation between tetrahedral sums. Divided by one of its
summands it becomes an identity between products of q-numbers of linear forms in the summation index `z`, the face sums
`F₁ … F₄` and the opposite-edge sums `B₁, B₂, B₃` of a tetrahedron (balanced: `F₁ + F₂ + F₃ + F₄ = B₁ + B₂ + B₃`).
This file proves those identities for the integer q-number `qz q n = (qⁿ - q⁻ⁿ)/(q - q⁻¹)`:

* `kl_cert_lower`: the identity for a fourth block meeting the total channel (`g₀ = 1`);
* `kl_cert_upper`: the identity for a fourth block not meeting it (`g₀ = 0`).

Numerical evidence (not proof): both identities, and the coefficient ratios they are used with, were checked in exact
rational arithmetic at `q = 3/2` (identities at 2000 random integer tuples; ratios on all instances with
`a, b, c ≤ 4`).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- The q-number of an integer: `qz q n = (qⁿ - q⁻ⁿ) / (q - q⁻¹)`. -/
noncomputable def qz (q : kˣ) (n : ℤ) : k := ((q : k) ^ n - (q : k) ^ (-n)) / ((q : k) - (q : k)⁻¹)

/-- On natural numbers `qz` is the q-number `qb`. -/
lemma qb_eq_qz (q : kˣ) (n : ℕ) : qb q n = qz q n := by
  unfold qb qz
  simp [zpow_natCast, zpow_neg, inv_pow]

/-- **The identity for `g₀ = 1`** (data of the tetrahedron with the raised second channel). -/
theorem kl_cert_lower (q : kˣ) (_hq : (q : k) - (q : k)⁻¹ ≠ 0) (z F₁ F₂ F₃ F₄ B₁ B₂ : ℤ) :
    let B₃ := F₁ + F₂ + F₃ + F₄ - B₁ - B₂
    qz q (B₂ - F₄ + 1) * qz q (F₃ + F₄ - B₃) * qz q (B₁ - z) * qz q (z + 1 - F₃) -
        qz q (F₃ + 1) * qz q (B₃ - F₃ + 1) * qz q (B₁ - z) * qz q (B₂ - z) -
        qz q (B₁ - F₁) * qz q (B₁ - F₂) * qz q (z + 1 - F₃) * qz q (z + 1 - F₄) =
      -(qz q (z + 2) * qz q (B₁ - z) * qz q (B₂ - z) * qz q (B₃ - z)) -
        qz q (z - F₁) * qz q (z - F₂) * qz q (z + 1 - F₃) * qz q (z + 1 - F₄) := by
  intro B₃
  have ht : (q : k) ≠ 0 := q.ne_zero
  simp only [qz, B₃]
  simp only [zpow_add₀ ht, zpow_sub₀ ht, zpow_neg, zpow_ofNat]
  field_simp
  ring


/-- **The identity for `g₀ = 0`** (data of the tetrahedron with the third block raised; `j₁ = F₃ + F₄ - B₃`). -/
theorem kl_cert_upper (q : kˣ) (_hq : (q : k) - (q : k)⁻¹ ≠ 0) (z F₁ F₂ F₃ F₄ B₁ B₂ : ℤ) :
    let B₃ := F₁ + F₂ + F₃ + F₄ - B₁ - B₂
    qz q (B₃ - F₁) * qz q (F₃ + F₄ - B₃ + 1) * (qz q (z + 1 - F₂) * qz q (z + 1 - F₃) * qz q (z + 1 - F₄)) +
        qz q (F₃ + 1) * qz q (F₄ + 1) * (qz q (B₁ - z) * qz q (B₂ - z) * qz q (B₃ - z)) -
        qz q (B₁ - F₂ + 1) * qz q (B₂ - F₂ + 1) * qz q (B₃ - z) * qz q (z + 1 - F₃) * qz q (z + 1 - F₄) =
      qz q (F₃ + F₄ - z) * qz q (z + 2) * (qz q (B₁ - z) * qz q (B₂ - z) * qz q (B₃ - z)) +
        qz q (z - F₁) * qz q (F₃ + F₄ + 1 - z) * (qz q (z + 1 - F₂) * qz q (z + 1 - F₃) * qz q (z + 1 - F₄)) := by
  intro B₃
  have ht : (q : k) ≠ 0 := q.ne_zero
  simp only [qz, B₃]
  simp only [zpow_add₀ ht, zpow_sub₀ ht, zpow_neg, zpow_ofNat]
  field_simp
  ring

end Lightlike.TemperleyLieb
