import Mathlib
import Lightlike.TemperleyLieb.Basic

/-!
# Jones–Wenzl projectors

In any algebra `A` with a family `e` satisfying the Temperley–Lieb relations (`IsTL δ e`), the Jones–Wenzl
projectors are `jw 0 = jw 1 = 1`, `jw (n+2) = jw (n+1) − (d_n / d_{n+1}) jw (n+1) e_n jw (n+1)` with
`d = chebD δ`.  If `d_i ≠ 0` for `i < N`, then for `n ≤ N`: `jw n` is idempotent, it is annihilated by
`e_i` (left and right) for `i + 1 < n`, it commutes with `e_i` for `n ≤ i`, and it absorbs the lower
projectors (`jw m * jw n = jw n = jw n * jw m` for `m ≤ n`).  Moreover
`e_n jw (n+1) e_n = (d_{n+1}/d_n) jw n e_n` (the partial trace identity, `jw_partial_trace`).

## References

* L. H. Kauffman, S. L. Lins, *Temperley–Lieb recoupling theory and invariants of 3-manifolds*,
  Annals of Mathematics Studies 134 (1994), Chapter 3.
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]

/-- The Jones–Wenzl projector on `n` strands. -/
noncomputable def jw (δ : k) (e : ℕ → A) : ℕ → A
  | 0 => 1
  | 1 => 1
  | n + 2 => jw δ e (n + 1) -
      (chebD δ n / chebD δ (n + 1)) • (jw δ e (n + 1) * e n * jw δ e (n + 1))

variable {δ : k} {e : ℕ → A}

/-- The recursion of `jw`. -/
theorem jw_succ_succ (n : ℕ) : jw δ e (n + 2) = jw δ e (n + 1) -
    (chebD δ n / chebD δ (n + 1)) • (jw δ e (n + 1) * e n * jw δ e (n + 1)) := rfl

/-- `eᵢ² = δ eᵢ` with scalar multiplication. -/
theorem IsTL.sq' (he : IsTL δ e) (i : ℕ) : e i * e i = δ • e i := by
  rw [he.sq, Algebra.smul_def]

/-- The properties of `jw n`. -/
structure JwProps (δ : k) (e : ℕ → A) (n : ℕ) : Prop where
  /-- Idempotent. -/
  idem : jw δ e n * jw δ e n = jw δ e n
  /-- Killed on the left by `eᵢ`, `i + 1 < n`. -/
  killL : ∀ i, i + 1 < n → e i * jw δ e n = 0
  /-- Killed on the right by `eᵢ`, `i + 1 < n`. -/
  killR : ∀ i, i + 1 < n → jw δ e n * e i = 0
  /-- Commutes with `eᵢ`, `n ≤ i`. -/
  comm : ∀ i, n ≤ i → e i * jw δ e n = jw δ e n * e i
  /-- Absorbs the lower projectors on the left. -/
  absL : ∀ m, m ≤ n → jw δ e m * jw δ e n = jw δ e n
  /-- Absorbs the lower projectors on the right. -/
  absR : ∀ m, m ≤ n → jw δ e n * jw δ e m = jw δ e n

/-- `jw 0 = 1`. -/
theorem jw_zero : jw δ e 0 = 1 := by simp [jw]

/-- `jw 1 = 1`. -/
theorem jw_one : jw δ e 1 = 1 := by simp [jw]

/-- `jw m = 1` for `m ≤ 1`. -/
theorem jw_of_le_one {m : ℕ} (h : m ≤ 1) : jw δ e m = 1 := by
  rcases m with _ | _ | m
  · exact jw_zero
  · exact jw_one
  · omega

/-- `jw 0` has the properties. -/
theorem jwProps_zero : JwProps δ e 0 where
  idem := by simp [jw_zero]
  killL := by intro i h; omega
  killR := by intro i h; omega
  comm := by intro i _; simp [jw_zero]
  absL := by intro m hm; simp [jw_of_le_one (by omega : m ≤ 1), jw_zero]
  absR := by intro m hm; simp [jw_of_le_one (by omega : m ≤ 1), jw_zero]

/-- `jw 1` has the properties. -/
theorem jwProps_one : JwProps δ e 1 where
  idem := by simp [jw_one]
  killL := by intro i h; omega
  killR := by intro i h; omega
  comm := by intro i _; simp [jw_one]
  absL := by intro m hm; simp [jw_of_le_one hm, jw_one]
  absR := by intro m hm; simp [jw_of_le_one hm, jw_one]

/-- Partial trace identity (the index shifted by one). -/
theorem pt_succ (he : IsTL δ e) {m : ℕ} (hp : JwProps δ e (m + 1)) (hd1 : chebD δ (m + 1) ≠ 0) :
    e (m + 1) * jw δ e (m + 2) * e (m + 1) =
      (chebD δ (m + 2) / chebD δ (m + 1)) • (jw δ e (m + 1) * e (m + 1)) := by
  set J := jw δ e (m + 1) with hJ
  have hc : e (m + 1) * J = J * e (m + 1) := hp.comm (m + 1) le_rfl
  have h1 : e (m + 1) * J * e (m + 1) = δ • (J * e (m + 1)) := by
    rw [hc, mul_assoc, he.sq', mul_smul_comm]
  have h2 : e (m + 1) * (J * e m * J) * e (m + 1) = J * e (m + 1) := by
    calc e (m + 1) * (J * e m * J) * e (m + 1) = (e (m + 1) * J) * e m * (J * e (m + 1)) := by
          simp only [mul_assoc]
      _ = (J * e (m + 1)) * e m * (J * e (m + 1)) := by rw [hc]
      _ = J * (e (m + 1) * e m * (J * e (m + 1))) := by simp only [mul_assoc]
      _ = J * (e (m + 1) * e m * (e (m + 1) * J)) := by rw [← hc]
      _ = J * (e (m + 1) * e m * e (m + 1)) * J := by simp only [mul_assoc]
      _ = J * e (m + 1) * J := by rw [he.braid_r]
      _ = J * (J * e (m + 1)) := by rw [mul_assoc, hc]
      _ = J * e (m + 1) := by rw [← mul_assoc, hp.idem]
  have hrec : jw δ e (m + 2) = J - (chebD δ m / chebD δ (m + 1)) • (J * e m * J) := jw_succ_succ m
  rw [hrec, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, h1, h2, ← sub_smul]
  congr 1
  rw [chebD_succ_succ]
  field_simp

/-- **Partial trace identity**: `e_n jw(n+1) e_n = (d_{n+1}/d_n) jw n e_n`. -/
theorem jw_partial_trace (he : IsTL δ e) {n : ℕ} (hp : JwProps δ e n) (hdn : chebD δ n ≠ 0) :
    e n * jw δ e (n + 1) * e n = (chebD δ (n + 1) / chebD δ n) • (jw δ e n * e n) := by
  rcases n with _ | m
  · simp [jw_one, jw_zero, he.sq', chebD]
  · exact pt_succ he hp hdn

/-- **The step of the Jones–Wenzl induction.** -/
theorem jwProps_succ_succ (he : IsTL δ e) {n : ℕ} (hp0 : JwProps δ e n) (hp1 : JwProps δ e (n + 1))
    (hd0 : chebD δ n ≠ 0) (hd1 : chebD δ (n + 1) ≠ 0) : JwProps δ e (n + 2) := by
  set J := jw δ e (n + 1) with hJ
  set P := jw δ e n with hP
  set c : k := chebD δ n / chebD δ (n + 1) with hc
  set c' : k := chebD δ (n + 1) / chebD δ n with hc'
  have hcc : c * c' = 1 := by rw [hc, hc']; field_simp
  have hrec : jw δ e (n + 2) = J - c • (J * e n * J) := jw_succ_succ n
  have hpt : e n * J * e n = c' • (P * e n) := jw_partial_trace he hp0 hd0
  have hPe : e n * P = P * e n := hp0.comm n le_rfl
  have hJe : e (n + 1) * J = J * e (n + 1) := hp1.comm (n + 1) le_rfl
  have hidem : J * J = J := hp1.idem
  have hPJ : P * J = J := hp1.absL n (by omega)
  have hJP : J * P = J := hp1.absR n (by omega)
  have hXX : (J * e n * J) * (J * e n * J) = c' • (J * e n * J) := by
    calc (J * e n * J) * (J * e n * J) = J * e n * (J * J) * e n * J := by noncomm_ring
      _ = J * (e n * J * e n) * J := by rw [hidem]; simp only [mul_assoc]
      _ = J * (c' • (P * e n)) * J := by rw [hpt]
      _ = c' • (J * P * e n * J) := by simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
      _ = c' • (J * e n * J) := by rw [hJP]
  have hkL : ∀ i, i < n → e i * (J - c • (J * e n * J)) = 0 := by
    intro i hi
    have h0 : e i * J = 0 := hp1.killL i (by omega)
    simp only [mul_sub, mul_smul_comm, ← mul_assoc, h0, zero_mul, smul_zero, sub_zero]
  have hkR : ∀ i, i < n → (J - c • (J * e n * J)) * e i = 0 := by
    intro i hi
    have h0 : J * e i = 0 := hp1.killR i (by omega)
    simp only [sub_mul, smul_mul_assoc, mul_assoc, h0, mul_zero, smul_zero, sub_zero]
  have hidem2 : jw δ e (n + 2) * jw δ e (n + 2) = jw δ e (n + 2) := by
    rw [hrec]
    have hJX : J * (J * e n * J) = J * e n * J := by simp only [← mul_assoc, hidem]
    have hXJ : (J * e n * J) * J = J * e n * J := by simp only [mul_assoc, hidem]
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, hidem, hJX, hXJ, hXX, smul_smul, hcc,
      one_smul]
    module
  refine ⟨hidem2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrec]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : i < n + 1) with h | h
    · exact hkL i h
    · subst h
      have : e i * (J * e i * J) = c' • (P * e i * J) := by
        calc e i * (J * e i * J) = (e i * J * e i) * J := by simp only [mul_assoc]
          _ = c' • (P * e i * J) := by rw [hpt, smul_mul_assoc]
      have h3 : P * e i * J = e i * J := by
        rw [← hPe, mul_assoc, hPJ]
      rw [mul_sub, mul_smul_comm, this, h3, smul_smul, hcc, one_smul, sub_self]
  · intro i hi
    rw [hrec]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : i < n + 1) with h | h
    · exact hkR i h
    · subst h
      have : (J * e i * J) * e i = c' • (J * P * e i) := by
        calc (J * e i * J) * e i = J * (e i * J * e i) := by simp only [mul_assoc]
          _ = c' • (J * P * e i) := by rw [hpt, mul_smul_comm, ← mul_assoc]
      rw [sub_mul, smul_mul_assoc, this, smul_smul, hJP]
      have : c * c' = 1 := hcc
      rw [this, one_smul, sub_self]
  · intro i hi
    rw [hrec]
    have hi1 : e i * J = J * e i := hp1.comm i (by omega)
    have hin : e i * e n = e n * e i := (he.comm n i (by omega)).symm
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    congr 2
    calc e i * (J * e n * J) = (e i * J) * e n * J := by simp only [mul_assoc]
      _ = J * (e i * e n) * J := by rw [hi1]; simp only [mul_assoc]
      _ = J * (e n * e i) * J := by rw [hin]
      _ = J * e n * (e i * J) := by simp only [mul_assoc]
      _ = J * e n * (J * e i) := by rw [hi1]
      _ = (J * e n * J) * e i := by simp only [mul_assoc]
  · intro m hm
    rcases Nat.lt_or_eq_of_le hm with h | h
    · rw [hrec]
      have hmJ : jw δ e m * J = J := hp1.absL m (by omega)
      simp only [mul_sub, mul_smul_comm, ← mul_assoc, hmJ]
    · subst h
      exact hidem2
  · intro m hm
    rcases Nat.lt_or_eq_of_le hm with h | h
    · rw [hrec]
      have hmJ' : J * jw δ e m = J := hp1.absR m (by omega)
      rw [sub_mul, smul_mul_assoc, mul_assoc (J * e n) J (jw δ e m), hmJ']
    · subst h
      exact hidem2

/-- **Jones–Wenzl projectors exist and have the standard properties up to `N`**: if `d_i ≠ 0` for `i < N`,
then `JwProps δ e n` holds for every `n ≤ N`. -/
theorem jwProps_of_le (he : IsTL δ e) (N : ℕ) (hd : ∀ i, i < N → chebD δ i ≠ 0) :
    ∀ n, n ≤ N → JwProps δ e n := by
  have key : ∀ n, n + 1 ≤ N → JwProps δ e n ∧ JwProps δ e (n + 1) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨jwProps_zero, jwProps_one⟩
    | succ n ih =>
      intro hn
      obtain ⟨h0, h1⟩ := ih (by omega)
      exact ⟨h1, jwProps_succ_succ he h0 h1 (hd n (by omega)) (hd (n + 1) (by omega))⟩
  intro n hn
  rcases n with _ | n
  · exact jwProps_zero
  · exact (key n (by omega)).2

end Lightlike.TemperleyLieb
