import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing

/-!
# `dΓ` for finitely many modes: the commutators of second quantization

J. Dereziński, *Introduction to representations of the canonical commutation and anticommutation relations*,
arXiv:math-ph/0511030, Theorem 13 (1), p. 19 (`[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])`) and Theorem 18 (2), (4), p. 22
(`[dΓ(h), a(w)] = -a(h* w)`, `[dΓ(h), a*(w)] = a*(hw)`), for `Z = ℂⁿ` with the creation and annihilation operators
`aᵢ* = a*(eᵢ)`, `aᵢ = a(eᵢ)` of a basis and `dΓ(h) = ∑ᵢⱼ hᵢⱼ aᵢ* aⱼ`. The statements hold in any algebra over `ℂ` whose
elements satisfy the CAR (`ε = -1`) or the CCR (`ε = 1`):

* `IsModeAlgebra ε a ad`: `ε² = 1`, `aⱼ aₖ* = δⱼₖ + ε aₖ* aⱼ`, `aₖ* aᵢ* = ε aᵢ* aₖ*` and `aₗ aⱼ = ε aⱼ aₗ`;
* `isModeAlgebra_car`, `isModeAlgebra_ccr`: the CAR and the CCR are such;
* `commutator_number`: `[aᵢ* aⱼ, aₖ* aₗ] = δⱼₖ aᵢ* aₗ - δᵢₗ aₖ* aⱼ`;
* `dGamma_commutator`: `[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])`;
* `dGamma_commutator_creation`, `dGamma_commutator_annihilation`: `[dΓ(h), aₖ*] = ∑ᵢ hᵢₖ aᵢ*`,
  `[dΓ(h), aₖ] = -∑ⱼ hₖⱼ aⱼ`.
-/

open scoped BigOperators

namespace Lightlike.OperatorAlgebras.SecondQuantFinite

variable {R : Type*} [Ring R] [Algebra ℂ R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A mode algebra** with sign `ε` (`-1` for fermions, `1` for bosons): `aⱼ aₖ* = δⱼₖ + ε aₖ* aⱼ`, and the
creators and the annihilators (anti)commute among themselves, `aₖ* aᵢ* = ε aᵢ* aₖ*`, `aₗ aⱼ = ε aⱼ aₗ`. -/
structure IsModeAlgebra (ε : ℂ) (a ad : ι → R) : Prop where
  /-- `ε² = 1`. -/
  eps_sq : ε * ε = 1
  /-- `aⱼ aₖ* = δⱼₖ + ε aₖ* aⱼ`. -/
  ann_cre : ∀ j k, a j * ad k = (if j = k then 1 else 0) + ε • (ad k * a j)
  /-- `aₖ* aᵢ* = ε aᵢ* aₖ*`. -/
  cre_cre : ∀ i k, ad k * ad i = ε • (ad i * ad k)
  /-- `aₗ aⱼ = ε aⱼ aₗ`. -/
  ann_ann : ∀ j l, a l * a j = ε • (a j * a l)

/-- **The CAR give a mode algebra with `ε = -1`.** -/
theorem isModeAlgebra_car {a ad : ι → R}
    (h1 : ∀ j k, a j * ad k + ad k * a j = if j = k then 1 else 0)
    (h2 : ∀ j k, a j * a k + a k * a j = 0) (h3 : ∀ j k, ad j * ad k + ad k * ad j = 0) :
    IsModeAlgebra (-1) a ad where
  eps_sq := by norm_num
  ann_cre j k := by
    rw [← h1 j k]; simp
  cre_cre i k := by
    rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_left (h3 k i)
  ann_ann j l := by
    rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_left (h2 l j)

/-- **The CCR give a mode algebra with `ε = 1`.** -/
theorem isModeAlgebra_ccr {a ad : ι → R}
    (h1 : ∀ j k, a j * ad k - ad k * a j = if j = k then 1 else 0)
    (h2 : ∀ j k, a j * a k = a k * a j) (h3 : ∀ j k, ad j * ad k = ad k * ad j) :
    IsModeAlgebra 1 a ad where
  eps_sq := by norm_num
  ann_cre j k := by
    rw [← h1 j k]; simp
  cre_cre i k := by
    rw [one_smul]; exact h3 k i
  ann_ann j l := by
    rw [one_smul]; exact h2 l j

variable {ε : ℂ} {a ad : ι → R}

/-- `aₖ* aᵢ* aₗ aⱼ = aᵢ* aₖ* aⱼ aₗ`: the two signs cancel. -/
lemma IsModeAlgebra.four (hm : IsModeAlgebra ε a ad) (i j k l : ι) :
    ad k * ad i * (a l * a j) = ad i * ad k * (a j * a l) := by
  rw [hm.cre_cre i k, hm.ann_ann j l, smul_mul_smul_comm, hm.eps_sq, one_smul]

/-- **`[aᵢ* aⱼ, aₖ* aₗ] = δⱼₖ aᵢ* aₗ - δᵢₗ aₖ* aⱼ`**, for the CAR and the CCR alike. -/
theorem commutator_number (hm : IsModeAlgebra ε a ad) (i j k l : ι) :
    ad i * a j * (ad k * a l) - ad k * a l * (ad i * a j) =
      (if j = k then ad i * a l else 0) - (if i = l then ad k * a j else 0) := by
  have h1 : ad i * a j * (ad k * a l) = (if j = k then ad i * a l else 0) + ε • (ad i * ad k * (a j * a l)) := by
    rw [show ad i * a j * (ad k * a l) = ad i * (a j * ad k) * a l by noncomm_ring, hm.ann_cre j k]
    split_ifs <;> simp [mul_add, add_mul, mul_assoc]
  have h2 : ad k * a l * (ad i * a j) = (if i = l then ad k * a j else 0) + ε • (ad k * ad i * (a l * a j)) := by
    rw [show ad k * a l * (ad i * a j) = ad k * (a l * ad i) * a j by noncomm_ring, hm.ann_cre l i]
    by_cases hil : i = l
    · subst hil; simp [mul_add, add_mul, mul_assoc]
    · have : ¬ l = i := fun h => hil h.symm
      simp [this, hil, mul_add, add_mul, mul_assoc]
  rw [h1, h2, hm.four i j k l]
  abel

/-- **`dΓ(h) = ∑ᵢⱼ hᵢⱼ aᵢ* aⱼ`**, the second quantization of the one-particle operator `h` (a matrix). -/
noncomputable def dGamma (a ad : ι → R) (h : Matrix ι ι ℂ) : R := ∑ i, ∑ j, h i j • (ad i * a j)

/-- `dΓ(A - B) = dΓ(A) - dΓ(B)`. -/
lemma dGamma_sub (A B : Matrix ι ι ℂ) : dGamma a ad (A - B) = dGamma a ad A - dGamma a ad B := by
  simp only [dGamma, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- `dΓ(A B) = ∑ᵢₗ ∑ₖ Aᵢₖ Bₖₗ aᵢ* aₗ`. -/
lemma dGamma_mul (A B : Matrix ι ι ℂ) :
    dGamma a ad (A * B) = ∑ i, ∑ l, ∑ k, (A i k * B k l) • (ad i * a l) := by
  simp only [dGamma, Matrix.mul_apply, Finset.sum_smul]

/-- `[D, dΓ(h)] = ∑ₖₗ hₖₗ [D, aₖ* aₗ]`. -/
lemma commutator_dGamma (D : R) (h : Matrix ι ι ℂ) :
    D * dGamma a ad h - dGamma a ad h * D = ∑ k, ∑ l, h k l • (D * (ad k * a l) - ad k * a l * D) := by
  simp only [dGamma, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, smul_sub, Finset.sum_sub_distrib]

/-- **Dereziński, Theorem 18 (4)**: `[dΓ(h), aₖ*] = ∑ᵢ hᵢₖ aᵢ* = a*(h eₖ)`. -/
theorem dGamma_commutator_creation (hm : IsModeAlgebra ε a ad) (h : Matrix ι ι ℂ) (k : ι) :
    dGamma a ad h * ad k - ad k * dGamma a ad h = ∑ i, h i k • ad i := by
  have hmono : ∀ i j, ad i * a j * ad k - ad k * (ad i * a j) = if j = k then ad i else 0 := by
    intro i j
    rw [mul_assoc, hm.ann_cre j k, ← mul_assoc (ad k), hm.cre_cre i k]
    split_ifs <;> simp [mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  calc dGamma a ad h * ad k - ad k * dGamma a ad h
      = ∑ i, ∑ j, h i j • (ad i * a j * ad k - ad k * (ad i * a j)) := by
        simp only [dGamma, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
          Finset.sum_sub_distrib]
    _ = ∑ i, h i k • ad i := by
        simp only [hmono, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Dereziński, Theorem 18 (2)**: `[dΓ(h), aₖ] = -∑ⱼ hₖⱼ aⱼ = -a(h* eₖ)`. -/
theorem dGamma_commutator_annihilation (hm : IsModeAlgebra ε a ad) (h : Matrix ι ι ℂ) (k : ι) :
    dGamma a ad h * a k - a k * dGamma a ad h = -∑ j, h k j • a j := by
  have hmono : ∀ i j, ad i * a j * a k - a k * (ad i * a j) = -(if k = i then a j else 0) := by
    intro i j
    rw [mul_assoc (ad i), ← mul_assoc (a k), hm.ann_cre k i, add_mul, smul_mul_assoc, mul_assoc (ad i) (a k),
      hm.ann_ann j k, mul_smul_comm, smul_smul, hm.eps_sq, one_smul]
    split_ifs <;> simp only [one_mul, zero_mul, zero_add, neg_zero] <;> abel
  calc dGamma a ad h * a k - a k * dGamma a ad h
      = ∑ i, ∑ j, h i j • (ad i * a j * a k - a k * (ad i * a j)) := by
        simp only [dGamma, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
          Finset.sum_sub_distrib]
    _ = ∑ i, (if k = i then -∑ j, h i j • a j else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hmono]
        split_ifs <;> simp [Finset.sum_neg_distrib]
    _ = -∑ j, h k j • a j := by
        rw [Finset.sum_ite_eq]; simp

/-- **Dereziński, Theorem 13 (1)**: `[dΓ(h₁), dΓ(h₂)] = dΓ([h₁, h₂])`, from Theorem 18 (2), (4) and the Leibniz rule
`[D, aₖ* aₗ] = [D, aₖ*] aₗ + aₖ* [D, aₗ]`. -/
theorem dGamma_commutator (hm : IsModeAlgebra ε a ad) (h₁ h₂ : Matrix ι ι ℂ) :
    dGamma a ad h₁ * dGamma a ad h₂ - dGamma a ad h₂ * dGamma a ad h₁ = dGamma a ad (h₁ * h₂ - h₂ * h₁) := by
  have hc : ∀ k l, dGamma a ad h₁ * (ad k * a l) - ad k * a l * dGamma a ad h₁ =
      ∑ i, h₁ i k • (ad i * a l) - ∑ j, h₁ l j • (ad k * a j) := by
    intro k l
    rw [show dGamma a ad h₁ * (ad k * a l) - ad k * a l * dGamma a ad h₁ =
        (dGamma a ad h₁ * ad k - ad k * dGamma a ad h₁) * a l +
          ad k * (dGamma a ad h₁ * a l - a l * dGamma a ad h₁) by noncomm_ring,
      dGamma_commutator_creation hm, dGamma_commutator_annihilation hm, Finset.sum_mul, mul_neg, Finset.mul_sum,
      ← sub_eq_add_neg]
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [commutator_dGamma, dGamma_sub, dGamma_mul, dGamma_mul]
  simp only [hc, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul]
  congr 1
  · calc ∑ k, ∑ l, ∑ i, (h₂ k l * h₁ i k) • (ad i * a l)
        = ∑ k, ∑ i, ∑ l, (h₂ k l * h₁ i k) • (ad i * a l) := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, (h₂ k l * h₁ i k) • (ad i * a l) := Finset.sum_comm
      _ = ∑ i, ∑ l, ∑ k, (h₁ i k * h₂ k l) • (ad i * a l) := Finset.sum_congr rfl fun i _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

end Lightlike.OperatorAlgebras.SecondQuantFinite
