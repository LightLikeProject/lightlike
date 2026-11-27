import Mathlib
import Lightlike.TemperleyLieb.Vertex
import Lightlike.TemperleyLieb.QNumbers

/-!
# Kauffman-bracket crossings in the Temperley–Lieb algebra

For a Temperley–Lieb family `e` with loop value `δ = -(a² + a⁻²)` the Kauffman-bracket crossing is
`σᵢ = a + a⁻¹ eᵢ` (`cross`), with inverse `σᵢ⁻¹ = a⁻¹ + a eᵢ` (`crossInv`). The crossings satisfy the braid relations
(`cross_braid`, `cross_comm`) and act as the scalar `a` next to an element that the generator kills
(`cross_mul_of_kill`, `mul_cross_of_kill`), e.g. a Jones–Wenzl projector. The model generators at `q = a²` are such a
family (`isTL_model_cross`). These are the first layer of the braiding of the Crane–Yetter vertex.

## References

* L. H. Kauffman and S. Lins, *Temperley–Lieb recoupling theory and invariants of 3-manifolds*, Annals of Mathematics
  Studies 134, Princeton (1994), Chap. 2 (the bracket) and Chap. 3 (the projectors).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

/-- **The Kauffman-bracket crossing** `σᵢ = a + a⁻¹ eᵢ` of a Temperley–Lieb family `e`. -/
def cross (a : k) (e : ℕ → A) (i : ℕ) : A := a • (1 : A) + a⁻¹ • e i

/-- The inverse crossing `σᵢ⁻¹ = a⁻¹ + a eᵢ`. -/
def crossInv (a : k) (e : ℕ → A) (i : ℕ) : A := a⁻¹ • (1 : A) + a • e i

variable {e : ℕ → A} {a : k}

lemma sq_eq_smul_of_isTL (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (i : ℕ) : e i * e i = (-(a ^ 2 + a⁻¹ ^ 2)) • e i := by
  rw [h.sq i, Algebra.smul_def]

/-- `σᵢ σᵢ⁻¹ = 1`. -/
theorem cross_mul_crossInv (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (i : ℕ) :
    cross a e i * crossInv a e i = 1 := by
  unfold cross crossInv
  simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, sq_eq_smul_of_isTL h]
  match_scalars <;> field_simp <;> ring

/-- `σᵢ⁻¹ σᵢ = 1`. -/
theorem crossInv_mul_cross (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (i : ℕ) :
    crossInv a e i * cross a e i = 1 := by
  unfold cross crossInv
  simp only [add_mul, mul_add, smul_mul_smul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, sq_eq_smul_of_isTL h]
  match_scalars <;> field_simp <;> ring

/-- **The braid relation** `σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁`. -/
theorem cross_braid (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (i : ℕ) :
    cross a e i * cross a e (i + 1) * cross a e i = cross a e (i + 1) * cross a e i * cross a e (i + 1) := by
  have hbl : e i * (e (i + 1) * e i) = e i := by rw [← mul_assoc, h.braid_l i]
  have hbr : e (i + 1) * (e i * e (i + 1)) = e (i + 1) := by rw [← mul_assoc, h.braid_r i]
  have hs0 := sq_eq_smul_of_isTL h i
  have hs1 := sq_eq_smul_of_isTL h (i + 1)
  have hs0' : ∀ x : A, e i * (e i * x) = (-(a ^ 2 + a⁻¹ ^ 2)) • (e i * x) := fun x => by
    rw [← mul_assoc, hs0, smul_mul_assoc]
  have hs1' : ∀ x : A, e (i + 1) * (e (i + 1) * x) = (-(a ^ 2 + a⁻¹ ^ 2)) • (e (i + 1) * x) := fun x => by
    rw [← mul_assoc, hs1, smul_mul_assoc]
  unfold cross
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, hbl, hbr, hs0, hs1,
    hs0', hs1', smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

/-- Distant crossings commute. -/
theorem cross_comm (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) {i j : ℕ} (hij : i + 2 ≤ j) :
    cross a e i * cross a e j = cross a e j * cross a e i := by
  unfold cross
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h.comm i j hij]
  match_scalars <;> ring

/-- A crossing next to an element killed by its generator (on the left) is the factor `a`. -/
theorem cross_mul_of_kill {p : A} {i : ℕ} (hp : e i * p = 0) : cross a e i * p = a • p := by
  unfold cross
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, hp, one_mul, smul_zero, add_zero]

/-- The same on the right. -/
theorem mul_cross_of_kill {p : A} {i : ℕ} (hp : p * e i = 0) : p * cross a e i = a • p := by
  unfold cross
  rw [mul_add, mul_smul_comm, mul_smul_comm, hp, mul_one, smul_zero, add_zero]

/-- **The model generators at `q = a²` are a Temperley–Lieb family with the Kauffman-bracket loop value**
`δ = -(a² + a⁻²)`, on the strands from `s` on. -/
theorem isTL_model_cross (a : kˣ) (s : ℕ) :
    IsTL (-((a : k) ^ 2 + (a : k)⁻¹ ^ 2))
      (fun j => (modelE (a ^ 2) (j + s) : Module.End k (ModelSpace k))) := by
  have h := isTL_shift (k := k) (a ^ 2) s
  rwa [loopVal_eq, Units.val_pow_eq_pow_val, ← inv_pow] at h

end Lightlike.TemperleyLieb
