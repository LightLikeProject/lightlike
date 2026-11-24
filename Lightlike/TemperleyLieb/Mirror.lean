import Mathlib
import Lightlike.TemperleyLieb.Model
import Lightlike.TemperleyLieb.Unique
import Lightlike.TemperleyLieb.Vertex

/-!
# Mirror symmetry of the model

`reflect N` reverses the first `N` bits and flips each of them.  On local operators it fixes the matrices of the
generators: `reflectOp N ∘ e_j = e_{N-2-j} ∘ reflectOp N` for `j + 2 ≤ N` (`reflectOp_modelE`), and it commutes with
`e_j` for `j ≥ N`.  Together with `jw_unique` this gives the Jones–Wenzl projector as the mirror image of itself.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- Reverse the bits at the positions `< N` and flip them; the later bits are unchanged. -/
def reflect (N : ℕ) (σ : ℕ → Bool) : ℕ → Bool := fun j => if j < N then !σ (N - 1 - j) else σ j

/-- `reflect N` is an involution. -/
lemma reflect_reflect (N : ℕ) (σ : ℕ → Bool) : reflect N (reflect N σ) = σ := by
  funext j
  simp only [reflect]
  split_ifs with h1 h2 <;> first | (exfalso; omega) | (simp only [Bool.not_not]; congr 1; omega) | simp

/-- The linear map induced by `reflect N`. -/
noncomputable def reflectOp (k : Type*) [Field k] (N : ℕ) : Module.End k (ModelSpace k) :=
  Finsupp.lmapDomain k k (reflect N)

/-- `reflectOp` on a basis vector. -/
@[simp] lemma reflectOp_single (N : ℕ) (σ : ℕ → Bool) (c : k) :
    reflectOp k N (single σ c) = single (reflect N σ) c := by
  simp [reflectOp]

/-- `reflectOp N` is an involution. -/
lemma reflectOp_mul_self (N : ℕ) : reflectOp k N * reflectOp k N = 1 := by
  refine model_ext fun σ => ?_
  simp [reflect_reflect]

/-- Bit `j'` of the reflected sequence (`N = j + j' + 2`). -/
lemma reflect_apply_lo (σ : ℕ → Bool) (j j' : ℕ) : reflect (j + j' + 2) σ j' = !σ (j + 1) := by
  simp only [reflect]; split_ifs <;> first | (exfalso; omega) | (congr 2; omega)

/-- Bit `j' + 1` of the reflected sequence. -/
lemma reflect_apply_hi (σ : ℕ → Bool) (j j' : ℕ) : reflect (j + j' + 2) σ (j' + 1) = !σ j := by
  simp only [reflect]; split_ifs <;> first | (exfalso; omega) | (congr 2; omega)

/-- Reflection turns `set2` at `j` into `set2` at the mirror position with swapped, flipped bits. -/
lemma reflect_set2 (σ : ℕ → Bool) (j j' : ℕ) (x y : Bool) :
    reflect (j + j' + 2) (set2 σ j x y) = set2 (reflect (j + j' + 2) σ) j' (!y) (!x) := by
  funext n
  simp only [reflect, set2, Function.update_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | (simp_all <;> omega) | (simp_all; congr 1; omega)

/-- **Mirror symmetry of the generators**: `e_{j'} ∘ reflect = reflect ∘ e_j` for `N = j + j' + 2`. -/
theorem modelE_reflect (q : kˣ) (j j' : ℕ) :
    modelE q j' * reflectOp k (j + j' + 2) = reflectOp k (j + j' + 2) * modelE q j := by
  refine model_ext fun σ => ?_
  have b0 := reflect_apply_lo σ j j'
  have b1 := reflect_apply_hi σ j j'
  rcases h0 : σ j with _ | _ <;> rcases h1 : σ (j + 1) with _ | _
  all_goals
    simp only [Module.End.mul_apply, reflectOp_single, modelE_single, one_smul, eBasis, h0, h1, b0, b1,
      h0, h1, Bool.not_false, Bool.not_true, map_sub, map_smul, reflect_set2, map_zero]
    try (simp only [reflectOp_single, reflect_set2, h0, h1, Finsupp.smul_single, smul_eq_mul, mul_one])
    try simp only [map_zero]

/-- Conjugation by an involution commutes with the construction of the projector. -/
lemma conj_jw {A : Type*} [Ring A] [Algebra k A] (δ : k) (ρ : A) (hρ : ρ * ρ = 1) (e : ℕ → A) (m : ℕ) :
    ρ * jw δ e m * ρ = jw δ (fun j => ρ * e j * ρ) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [jw_zero, hρ]
    · simp [jw_one, hρ]
    · have h1 := ih (m + 1) (by omega)
      rw [jw_succ_succ, jw_succ_succ, ← h1, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
      congr 2
      calc ρ * (jw δ e (m + 1) * e m * jw δ e (m + 1)) * ρ
          = (ρ * jw δ e (m + 1) * ρ) * (ρ * e m * ρ) * (ρ * jw δ e (m + 1) * ρ) := by
            simp only [mul_assoc, ← mul_assoc (ρ) ρ, hρ, one_mul]
        _ = _ := by rw [h1]

/-- `reflectOp` conjugates the generators `e_j` to the mirror generators. -/
lemma reflect_conj_e (q : kˣ) (j j' : ℕ) :
    reflectOp k (j + j' + 2) * modelE q j * reflectOp k (j + j' + 2) = modelE q j' := by
  have h := modelE_reflect (k := k) q j j'
  rw [← h, mul_assoc, reflectOp_mul_self, mul_one]

/-- **Mirror symmetry of the Jones–Wenzl projector**: the reflection of the projector on the strands
`s, …, s + m - 1` is the projector on the mirror strands `s', …, s' + m - 1`, `N = s + s' + m`. -/
theorem jwAt_mirror (q : kˣ) (s s' m : ℕ) (hd : ∀ j, j < m → chebD (loopVal q) j ≠ 0) :
    jwAt q s' m = reflectOp k (s + s' + m) * jwAt q s m * reflectOp k (s + s' + m) := by
  set N := s + s' + m with hN
  have hρ := reflectOp_mul_self (k := k) N
  have hY : reflectOp k N * jwAt q s m * reflectOp k N =
      jw (loopVal q) (fun j => reflectOp k N * modelE q (j + s) * reflectOp k N) m := by
    unfold jwAt; exact conj_jw _ _ hρ _ m
  have hP := jwProps_of_le (isTL_shift q s) m hd m le_rfl
  have hP' := jwProps_of_le (isTL_shift q s') m hd m le_rfl
  have hf : ∀ t, t + 1 < m → reflectOp k N * modelE q (t + s) * reflectOp k N = modelE q (s' + (m - 2 - t)) := by
    intro t ht
    have := reflect_conj_e (k := k) q (t + s) (s' + (m - 2 - t))
    rwa [show t + s + (s' + (m - 2 - t)) + 2 = N by omega] at this
  have hg : ∀ t, t + 1 < m → reflectOp k N * modelE q (s + (m - 2 - t)) * reflectOp k N = modelE q (t + s') := by
    intro t ht
    have := reflect_conj_e (k := k) q (s + (m - 2 - t)) (t + s')
    rwa [show s + (m - 2 - t) + (t + s') + 2 = N by omega] at this
  rw [hY]
  unfold jwAt
  apply jw_unique
  · intro j hj
    have := hP'.killR (m - 2 - j) (by omega)
    rw [hf j hj]
    convert this using 3
    omega
  · intro j hj
    rw [← hY]
    have h1 : modelE q (m - 2 - j + s) * jwAt q s m = 0 := hP.killL (m - 2 - j) (by omega)
    have key : modelE q (j + s') * reflectOp k N = reflectOp k N * modelE q (m - 2 - j + s) := by
      have := modelE_reflect (k := k) q (m - 2 - j + s) (j + s')
      rwa [show m - 2 - j + s + (j + s') + 2 = N by omega] at this
    show modelE q (j + s') * (reflectOp k N * jwAt q s m * reflectOp k N) = 0
    rw [← mul_assoc, ← mul_assoc, key, mul_assoc (reflectOp k N), h1]
    simp

/-- Conjugation by an involution transports `U - c U E U`. -/
lemma conj_sub_smul_mul {A : Type*} [Ring A] [Algebra k A] (c : k) (ρ U E : A) (hρ : ρ * ρ = 1) :
    ρ * (U - c • (U * E * U)) * ρ =
      ρ * U * ρ - c • ((ρ * U * ρ) * (ρ * E * ρ) * (ρ * U * ρ)) := by
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
  congr 2
  simp only [mul_assoc, ← mul_assoc ρ ρ, hρ, one_mul]

/-- **The recursion from the left end**: `jw (n+2)` on the strands `s, …, s + n + 1` is
`U - (d_n/d_{n+1}) U e_s U` with `U` the projector on the strands `s + 1, …, s + n + 1`. -/
theorem jwAt_succ_succ_left (q : kˣ) (s n : ℕ) (hd : ∀ j, j < n + 2 → chebD (loopVal q) j ≠ 0) :
    jwAt q s (n + 2) = jwAt q (s + 1) (n + 1) -
      (chebD (loopVal q) n / chebD (loopVal q) (n + 1)) •
        (jwAt q (s + 1) (n + 1) * modelE q s * jwAt q (s + 1) (n + 1)) := by
  set N := s + n + 2 with hN
  have hρ := reflectOp_mul_self (k := k) N
  have m1 : jwAt q s (n + 2) = reflectOp k N * jwAt q 0 (n + 2) * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 s (n + 2) hd
    rwa [show 0 + s + (n + 2) = N by omega] at this
  have m2 : jwAt q (s + 1) (n + 1) = reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 (s + 1) (n + 1) (fun j hj => hd j (by omega))
    rwa [show 0 + (s + 1) + (n + 1) = N by omega] at this
  have m3 : reflectOp k N * modelE q n * reflectOp k N = modelE q s := by
    have := reflect_conj_e (k := k) q n s
    rwa [show n + s + 2 = N by omega] at this
  have h0 : jwAt q 0 (n + 2) = jwAt q 0 (n + 1) -
      (chebD (loopVal q) n / chebD (loopVal q) (n + 1)) •
        (jwAt q 0 (n + 1) * modelE q n * jwAt q 0 (n + 1)) := jw_succ_succ n
  rw [m1, h0]
  have h := conj_sub_smul_mul (A := Module.End k (ModelSpace k))
    (chebD (loopVal q) n / chebD (loopVal q) (n + 1)) (reflectOp k N) (jwAt q 0 (n + 1)) (modelE q n) hρ
  refine h.trans ?_
  rw [← m2, m3]

end Lightlike.TemperleyLieb
