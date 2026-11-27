import Mathlib
import Lightlike.TemperleyLieb.Vertex
import Lightlike.TemperleyLieb.QNumbers
import Lightlike.TemperleyLieb.JwNatural

/-!
# Kauffman-bracket crossings in the Temperley–Lieb algebra

For a Temperley–Lieb family `e` with loop value `δ = -(a² + a⁻²)` the Kauffman-bracket crossing is
`σᵢ = a + a⁻¹ eᵢ` (`cross`), with inverse `σᵢ⁻¹ = a⁻¹ + a eᵢ` (`crossInv`). The crossings satisfy the braid relations
(`cross_braid`, `cross_comm`) and act as the scalar `a` next to an element that the generator kills
(`cross_mul_of_kill`, `mul_cross_of_kill`), e.g. a Jones–Wenzl projector. The model generators at `q = a²` are such a
family (`isTL_model_cross`).

A generator slides across two crossings (`cross_cross_e`, `cross_cross_e'`). The strand crossing `T(s, n)`
(`strandT`) and the bundle crossing `X(s; m, n)` of an `n`-block over an `m`-block (`bundleX`) shift the generators of
the blocks they cross (`strandT_e`, `bundleX_e_left`, `bundleX_e_right`, with `strandT_two_e`: two adjacent strands
crossing a block carry their cup), so the Jones–Wenzl projectors of both blocks pass through a bundle crossing
(`bundleX_jw_left`, `bundleX_jw_right`). These are the first layers of the braiding of the Crane–Yetter vertex.

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


/-- A crossing commutes with a distant generator. -/
theorem cross_e_far (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) {i j : ℕ} (hij : i + 2 ≤ j ∨ j + 2 ≤ i) :
    cross a e i * e j = e j * cross a e i := by
  unfold cross
  rcases hij with hij | hij
  · rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, one_mul, mul_one, h.comm i j hij]
  · rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, one_mul, mul_one,
      h.comm j i hij]

/-- **The generator slides across two crossings**: `σᵢ σᵢ₊₁ eᵢ = eᵢ₊₁ σᵢ σᵢ₊₁`. -/
theorem cross_cross_e (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (i : ℕ) :
    cross a e i * cross a e (i + 1) * e i = e (i + 1) * (cross a e i * cross a e (i + 1)) := by
  have hbl : e i * (e (i + 1) * e i) = e i := by rw [← mul_assoc, h.braid_l i]
  have hbr : e (i + 1) * (e i * e (i + 1)) = e (i + 1) := by rw [← mul_assoc, h.braid_r i]
  unfold cross
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, hbl, hbr,
    sq_eq_smul_of_isTL h, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

/-- The mirror slide `σᵢ₊₁ σᵢ eᵢ₊₁ = eᵢ σᵢ₊₁ σᵢ`. -/
theorem cross_cross_e' (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (i : ℕ) :
    cross a e (i + 1) * cross a e i * e (i + 1) = e i * (cross a e (i + 1) * cross a e i) := by
  have hbl : e i * (e (i + 1) * e i) = e i := by rw [← mul_assoc, h.braid_l i]
  have hbr : e (i + 1) * (e i * e (i + 1)) = e (i + 1) := by rw [← mul_assoc, h.braid_r i]
  unfold cross
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, hbl, hbr,
    sq_eq_smul_of_isTL h, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

/-- **A strand crossing a block**: `T(s, n) = σ_s σ_{s+1} ⋯ σ_{s+n-1}` (the strand at `s + n` moves to `s`). -/
def strandT (a : k) (e : ℕ → A) (s : ℕ) : ℕ → A
  | 0 => 1
  | n + 1 => strandT a e s n * cross a e (s + n)

/-- `T(s, n)` commutes with a generator beyond its strands. -/
theorem strandT_e_far (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (s : ℕ) {j : ℕ} :
    ∀ n, s + n + 1 ≤ j → strandT a e s n * e j = e j * strandT a e s n
  | 0, _ => by simp [strandT]
  | n + 1, hj => by
    simp only [strandT]
    rw [mul_assoc, cross_e_far h (Or.inl (by omega)), ← mul_assoc, strandT_e_far h s n (by omega), mul_assoc]

/-- **`T(s, n)` shifts the generators of the block it crosses**: `T(s, n) eⱼ = eⱼ₊₁ T(s, n)` for
`s ≤ j ≤ s + n - 2`. -/
theorem strandT_e (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (s : ℕ) :
    ∀ n j, s ≤ j → j + 2 ≤ s + n → strandT a e s n * e j = e (j + 1) * strandT a e s n
  | 0, j, _, hj => by omega
  | 1, j, _, hj => by omega
  | n + 2, j, hs, hj => by
    by_cases hjn : j + 2 ≤ s + (n + 1)
    · have ih := strandT_e ha h s (n + 1) j hs hjn
      simp only [strandT] at ih ⊢
      rw [mul_assoc, cross_e_far h (Or.inr (by omega)), ← mul_assoc, ih, mul_assoc]
    · obtain rfl : j = s + n := by omega
      simp only [strandT, show s + (n + 1) = s + n + 1 by omega]
      rw [mul_assoc, mul_assoc, ← mul_assoc (cross a e (s + n)), cross_cross_e ha h (s + n), ← mul_assoc,
        strandT_e_far h s n (by omega)]
      simp only [mul_assoc]

/-- `T(s, n)` commutes with a generator before its strands. -/
theorem strandT_e_far_left (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (s : ℕ) {j : ℕ} (hj : j + 2 ≤ s) :
    ∀ n, strandT a e s n * e j = e j * strandT a e s n
  | 0 => by simp [strandT]
  | n + 1 => by
    simp only [strandT]
    rw [mul_assoc, cross_e_far h (Or.inr (by omega)), ← mul_assoc, strandT_e_far_left h s hj n, mul_assoc]

/-- `T(s, n)` commutes with a crossing beyond its strands. -/
theorem strandT_cross_far (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (s : ℕ) {j : ℕ} :
    ∀ n, s + n + 1 ≤ j → strandT a e s n * cross a e j = cross a e j * strandT a e s n
  | 0, _ => by simp [strandT]
  | n + 1, hj => by
    simp only [strandT]
    rw [mul_assoc, cross_comm h (show s + n + 2 ≤ j by omega), ← mul_assoc, strandT_cross_far h s n (by omega),
      mul_assoc]

/-- **Two adjacent strands crossing a block carry their cup**: `T(t+1, m) T(t, m) e_{t+m} = e_t T(t+1, m) T(t, m)`. -/
theorem strandT_two_e (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (t : ℕ) :
    ∀ m, strandT a e (t + 1) m * strandT a e t m * e (t + m) = e t * (strandT a e (t + 1) m * strandT a e t m)
  | 0 => by simp [strandT]
  | m + 1 => by
    have ih := strandT_two_e ha h t m
    simp only [strandT]
    have hc : strandT a e t m * cross a e (t + 1 + m) = cross a e (t + 1 + m) * strandT a e t m :=
      strandT_cross_far h t m (by omega)
    have hcc := cross_cross_e' ha h (t + m)
    rw [show t + 1 + m = t + m + 1 by omega] at hc ⊢
    rw [show t + (m + 1) = t + m + 1 by omega]
    calc strandT a e (t + 1) m * cross a e (t + m + 1) * (strandT a e t m * cross a e (t + m)) * e (t + m + 1)
        = strandT a e (t + 1) m * strandT a e t m * (cross a e (t + m + 1) * cross a e (t + m) * e (t + m + 1)) := by
          rw [mul_assoc (strandT a e (t + 1) m), ← mul_assoc (cross a e (t + m + 1)), ← hc]; simp only [mul_assoc]
      _ = strandT a e (t + 1) m * strandT a e t m * e (t + m) * (cross a e (t + m + 1) * cross a e (t + m)) := by
          rw [hcc]; simp only [mul_assoc]
      _ = e t * (strandT a e (t + 1) m * strandT a e t m) * (cross a e (t + m + 1) * cross a e (t + m)) := by rw [ih]
      _ = e t * (strandT a e (t + 1) m * cross a e (t + m + 1) * (strandT a e t m * cross a e (t + m))) := by
          rw [mul_assoc (strandT a e (t + 1) m) (cross a e (t + m + 1)), ← mul_assoc (cross a e (t + m + 1)), ← hc]
          simp only [mul_assoc]

/-- **The bundle crossing** `X(s; m, n)`: the block of `n` strands at `s + m` crosses the block of `m` strands at `s`
(afterwards the `n` strands are at `s` and the `m` strands at `s + n`). -/
def bundleX (a : k) (e : ℕ → A) (s m : ℕ) : ℕ → A
  | 0 => 1
  | n + 1 => strandT a e (s + n) m * bundleX a e s m n

/-- The generators of the `m`-block move right by `n`. -/
theorem bundleX_e_left (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (s m : ℕ) {j : ℕ} (hs : s ≤ j)
    (hj : j + 2 ≤ s + m) : ∀ n, bundleX a e s m n * e j = e (j + n) * bundleX a e s m n
  | 0 => by simp [bundleX]
  | n + 1 => by
    simp only [bundleX]
    rw [mul_assoc, bundleX_e_left ha h s m hs hj n, ← mul_assoc, strandT_e ha h (s + n) m (j + n) (by omega) (by omega),
      mul_assoc, show j + n + 1 = j + (n + 1) by omega]

/-- `X(s; m, n)` commutes with a generator beyond both blocks. -/
theorem bundleX_e_far (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (s m : ℕ) {j : ℕ} :
    ∀ n, s + m + n ≤ j → bundleX a e s m n * e j = e j * bundleX a e s m n
  | 0, _ => by simp [bundleX]
  | n + 1, hj => by
    simp only [bundleX]
    rw [mul_assoc, bundleX_e_far h s m n (by omega), ← mul_assoc, strandT_e_far h (s + n) m (by omega), mul_assoc]

/-- The generators of the `n`-block move left by `m`. -/
theorem bundleX_e_right (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (s m : ℕ) :
    ∀ n j, j + 2 ≤ n → bundleX a e s m n * e (s + m + j) = e (s + j) * bundleX a e s m n
  | 0, j, hj => by omega
  | 1, j, hj => by omega
  | n + 2, j, hj => by
    by_cases hjn : j + 2 ≤ n + 1
    · have ih := bundleX_e_right ha h s m (n + 1) j hjn
      simp only [bundleX] at ih ⊢
      rw [mul_assoc, ih, ← mul_assoc, strandT_e_far_left h (s + (n + 1)) (by omega) m, mul_assoc]
    · rw [show j = n by omega]
      simp only [bundleX]
      have hf := bundleX_e_far h s m n (j := s + m + n) le_rfl
      have h2 := strandT_two_e ha h (s + n) m
      rw [show s + n + 1 = s + (n + 1) by omega, show s + n + m = s + m + n by omega] at h2
      rw [mul_assoc, mul_assoc, hf, ← mul_assoc (strandT a e (s + n) m), ← mul_assoc, ← mul_assoc, h2]
      simp only [mul_assoc]

/-- **The projector of the `m`-block passes through the bundle crossing**, to the strands `s + n, …`. -/
theorem bundleX_jw_left (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (δ : k) (s m n : ℕ) :
    bundleX a e s m n * jw δ (fun j => e (j + s)) m = jw δ (fun j => e (j + (s + n))) m * bundleX a e s m n :=
  jw_intertwine δ _ _ _ m fun j hj => by
    rw [bundleX_e_left ha h s m (j := j + s) (by omega) (by omega) n, show j + s + n = j + (s + n) by omega]

/-- **The projector of the `n`-block passes through the bundle crossing**, to the strands `s, …`. -/
theorem bundleX_jw_right (ha : a ≠ 0) (h : IsTL (-(a ^ 2 + a⁻¹ ^ 2)) e) (δ : k) (s m n : ℕ) :
    bundleX a e s m n * jw δ (fun j => e (j + (s + m))) n = jw δ (fun j => e (j + s)) n * bundleX a e s m n :=
  jw_intertwine δ _ _ _ n fun j hj => by
    rw [show j + (s + m) = s + m + j by omega, bundleX_e_right ha h s m n j (by omega), show s + j = j + s by omega]

end Lightlike.TemperleyLieb
