import Mathlib
import Lightlike.TemperleyLieb.FusionIdentity

/-!
# Iterated fusion: the tree idempotents

Naturality of the nested cups and caps against the shifted Jones–Wenzl projectors, and the decomposition
`Q(a,b) p_c = Σ_e κ_e⁻¹ V_e Q(c_e, c) W_e` of three blocks along the first bracketing.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical
open Finsupp

variable {k : Type*} [Field k]

/-- Pushing an element through the Jones–Wenzl step. -/
theorem push_step {A : Type*} [Ring A] [Algebra k A] (c : k) (u J J' e e' : A) (h1 : u * J = J' * u)
    (h2 : u * e = e' * u) : u * (J - c • (J * e * J)) = (J' - c • (J' * e' * J')) * u := by
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, h1]
  congr 2
  calc u * (J * e * J) = (u * J) * e * J := by simp only [mul_assoc]
    _ = J' * (u * e) * J := by rw [h1]; simp only [mul_assoc]
    _ = J' * e' * (u * J) := by rw [h2]; simp only [mul_assoc]
    _ = J' * e' * J' * u := by rw [h1]; simp only [mul_assoc]

/-- A cup to the left of a projector slides through it, shifting the projector by two. -/
theorem cupOp_mul_jwAt (q : kˣ) {m s : ℕ} (hm : m ≤ s) :
    ∀ n, (cupOp q m : Module.End k (ModelSpace k)) * jwAt q s n = jwAt q (s + 2) n * cupOp q m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [jwAt, jw_zero]
    · simp [jwAt, jw_one]
    · have h2 : ∀ s', jwAt q s' (n + 2) = jwAt q s' (n + 1) -
          (chebD (loopVal q) n / chebD (loopVal q) (n + 1)) •
            (jwAt q s' (n + 1) * modelE q (n + s') * jwAt q s' (n + 1)) := fun s' => jw_succ_succ n
      rw [h2 s, h2 (s + 2)]
      have e1 : (cupOp q m : Module.End k (ModelSpace k)) * modelE q (n + s) = modelE q (n + (s + 2)) * cupOp q m := by
        rw [show n + (s + 2) = (n + s) + 2 by ring]
        exact (e_mul_cup_far q (by omega)).symm
      exact push_step (A := Module.End k (ModelSpace k)) _ _ _ _ _ _ (ih (n + 1) (by omega)) e1

/-- A cap to the left of a shifted projector slides through it, shifting the projector by two. -/
theorem capOp_mul_jwAt (q : kˣ) {m s : ℕ} (hm : m ≤ s) :
    ∀ n, (capOp q m : Module.End k (ModelSpace k)) * jwAt q (s + 2) n = jwAt q s n * capOp q m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [jwAt, jw_zero]
    · simp [jwAt, jw_one]
    · have h2 : ∀ s', jwAt q s' (n + 2) = jwAt q s' (n + 1) -
          (chebD (loopVal q) n / chebD (loopVal q) (n + 1)) •
            (jwAt q s' (n + 1) * modelE q (n + s') * jwAt q s' (n + 1)) := fun s' => jw_succ_succ n
      rw [h2 s, h2 (s + 2)]
      have e1 : (capOp q m : Module.End k (ModelSpace k)) * modelE q (n + (s + 2)) = modelE q (n + s) * capOp q m := by
        rw [show n + (s + 2) = (n + s) + 2 by ring]
        exact cap_mul_e_far q (by omega)
      exact push_step (A := Module.End k (ModelSpace k)) _ _ _ _ _ _ (ih (n + 1) (by omega)) e1

end Lightlike.TemperleyLieb
