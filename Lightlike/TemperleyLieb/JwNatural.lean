import Mathlib
import Lightlike.TemperleyLieb.Mirror
import Lightlike.TemperleyLieb.Natural

/-!
# Naturality of the Jones–Wenzl projectors against cups and caps

`jw_intertwine`: if `X * f j = g j * X` for `j + 1 < n`... for the generators used by `jw n`, then
`X * jw δ f n = jw δ g n * X`.  Applied to the cap or cup with the naturality relations of `Natural.lean` this
gives: a projector entirely to the left of a cap (cup) commutes with it, and a projector to the right of it is
transported with a shift by two strands.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- An element that intertwines the generators intertwines the projectors. -/
theorem jw_intertwine {A : Type*} [Ring A] [Algebra k A] (δ : k) (X : A) (f g : ℕ → A) (n : ℕ)
    (h : ∀ j, j + 1 < n → X * f j = g j * X) : X * jw δ f n = jw δ g n * X := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [jw_zero]
    · simp [jw_one]
    · have h1 := ih (n + 1) (by omega) (fun j hj => h j (by omega))
      have h2 := h n (by omega)
      have h3 : X * (jw δ f (n + 1) * f n * jw δ f (n + 1)) =
          jw δ g (n + 1) * g n * jw δ g (n + 1) * X := by
        calc X * (jw δ f (n + 1) * f n * jw δ f (n + 1))
            = (X * jw δ f (n + 1)) * f n * jw δ f (n + 1) := by simp only [mul_assoc]
          _ = jw δ g (n + 1) * (X * f n) * jw δ f (n + 1) := by rw [h1]; simp only [mul_assoc]
          _ = jw δ g (n + 1) * g n * (X * jw δ f (n + 1)) := by rw [h2]; simp only [mul_assoc]
          _ = jw δ g (n + 1) * g n * jw δ g (n + 1) * X := by rw [h1]; simp only [mul_assoc]
      rw [jw_succ_succ, jw_succ_succ, mul_sub, mul_smul_comm, h1, h3, sub_mul, smul_mul_assoc]

/-- A projector to the right of a cap is transported down by two strands. -/
theorem cap_mul_jwAt_far (q : kˣ) {m s : ℕ} (hm : m ≤ s) (n : ℕ) :
    capOp q m * jwAt q (s + 2) n = jwAt q s n * capOp q m :=
  jw_intertwine (loopVal q) (capOp q m) _ _ n (fun j _ => show capOp q m * modelE q (j + (s + 2)) = modelE q (j + s) * capOp q m from
    cap_mul_e_far q (m := m) (j := j + s) (by omega))

/-- A projector to the left of a cap commutes with it. -/
theorem cap_mul_jwAt_near (q : kˣ) {m s n : ℕ} (h : s + n ≤ m) :
    capOp q m * jwAt q s n = jwAt q s n * capOp q m :=
  jw_intertwine (loopVal q) (capOp q m) _ _ n (fun j hj => show capOp q m * modelE q (j + s) = modelE q (j + s) * capOp q m from
    cap_mul_e_near q (m := m) (j := j + s) (by omega))

/-- A projector is transported up by two strands through a cup to its left. -/
theorem cup_mul_jwAt_far (q : kˣ) {m s : ℕ} (hm : m ≤ s) (n : ℕ) :
    cupOp q m * jwAt q s n = jwAt q (s + 2) n * cupOp q m :=
  jw_intertwine (loopVal q) (cupOp q m) _ _ n (fun j _ => show cupOp q m * modelE q (j + s) = modelE q (j + (s + 2)) * cupOp q m from
    (e_mul_cup_far q (m := m) (j := j + s) (by omega)).symm)

/-- A projector to the left of a cup commutes with it. -/
theorem cup_mul_jwAt_near (q : kˣ) {m s n : ℕ} (h : s + n ≤ m) :
    cupOp q m * jwAt q s n = jwAt q s n * cupOp q m :=
  jw_intertwine (loopVal q) (cupOp q m) _ _ n (fun j hj => show cupOp q m * modelE q (j + s) = modelE q (j + s) * cupOp q m from
    (e_mul_cup_near q (m := m) (j := j + s) (by omega)).symm)

end Lightlike.TemperleyLieb
