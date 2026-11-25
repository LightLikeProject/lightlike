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

/-- The nested cups slide through a projector to their right. -/
theorem nestCup_mul_jwAt (q : kˣ) {l s : ℕ} (hl : l ≤ s) (n : ℕ) :
    ∀ i, (nestCup q l i : Module.End k (ModelSpace k)) * jwAt q s n = jwAt q (s + 2 * i) n * nestCup q l i := by
  intro i
  induction i with
  | zero => simp [nestCup]
  | succ i ih =>
    have h := cupOp_mul_jwAt q (m := l + i) (s := s + 2 * i) (by omega) n
    calc (nestCup q l (i + 1) : Module.End k (ModelSpace k)) * jwAt q s n
        = cupOp q (l + i) * (nestCup q l i * jwAt q s n) := by simp only [nestCup, mul_assoc]
      _ = cupOp q (l + i) * (jwAt q (s + 2 * i) n * nestCup q l i) := by rw [ih]
      _ = (cupOp q (l + i) * jwAt q (s + 2 * i) n) * nestCup q l i := by rw [mul_assoc]
      _ = jwAt q (s + 2 * i + 2) n * cupOp q (l + i) * nestCup q l i := by rw [h]
      _ = jwAt q (s + 2 * (i + 1)) n * nestCup q l (i + 1) := by
          rw [show s + 2 * (i + 1) = s + 2 * i + 2 by ring]; simp only [nestCup, mul_assoc]

/-- The nested caps slide through a shifted projector to their right. -/
theorem nestCap_mul_jwAt (q : kˣ) {l s : ℕ} (hl : l ≤ s) (n : ℕ) :
    ∀ i, (nestCap q l i : Module.End k (ModelSpace k)) * jwAt q (s + 2 * i) n = jwAt q s n * nestCap q l i := by
  intro i
  induction i with
  | zero => simp [nestCap]
  | succ i ih =>
    have h := capOp_mul_jwAt q (m := l + i) (s := s + 2 * i) (by omega) n
    calc (nestCap q l (i + 1) : Module.End k (ModelSpace k)) * jwAt q (s + 2 * (i + 1)) n
        = nestCap q l i * (capOp q (l + i) * jwAt q (s + 2 * i + 2) n) := by
          rw [show s + 2 * (i + 1) = s + 2 * i + 2 by ring]; simp only [nestCap, mul_assoc]
      _ = nestCap q l i * (jwAt q (s + 2 * i) n * capOp q (l + i)) := by rw [h]
      _ = (nestCap q l i * jwAt q (s + 2 * i) n) * capOp q (l + i) := by rw [mul_assoc]
      _ = jwAt q s n * nestCap q l i * capOp q (l + i) := by rw [ih]
      _ = jwAt q s n * nestCap q l (i + 1) := by simp only [nestCap, mul_assoc]

/-- An element of `C m` commutes with a projector on strands starting beyond `m`. -/
theorem CSub_mul_jwAt (q : kˣ) {m s : ℕ} (hm : m + 1 ≤ s) {x : Module.End k (ModelSpace k)} (hx : x ∈ CSub q m) :
    ∀ n, x * jwAt q s n = jwAt q s n * x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [jwAt, jw_zero]
    · simp [jwAt, jw_one]
    · have h2 : jwAt q s (n + 2) = jwAt q s (n + 1) -
          (chebD (loopVal q) n / chebD (loopVal q) (n + 1)) •
            (jwAt q s (n + 1) * modelE q (n + s) * jwAt q s (n + 1)) := jw_succ_succ n
      rw [h2]
      have e1 : x * modelE q (n + s) = modelE q (n + s) * x :=
        (comm_tlSub (modelE_isTL q) (m := m) (n := n + s) (by omega) hx).symm
      exact push_step (A := Module.End k (ModelSpace k)) _ _ _ _ _ _ (ih (n + 1) (by omega)) e1

/-- `Q(a,b) ∈ C (a + b - 1)`. -/
theorem Qab_mem (q : kˣ) (a b : ℕ) : (Qab q a b : Module.End k (ModelSpace k)) ∈ CSub q (a + b - 1) := by
  have h1 : jwAt q 0 a ∈ CSub q (a + b - 1) :=
    tlSub_mono (m := 0 + a - 1) (n := a + b - 1) (by omega) (jwAt_mem q 0 a)
  exact Subalgebra.mul_mem _ h1 (jwAt_mem q a b)

/-- **Iterated fusion, first bracketing**: `Q(a,b) p_c = Σ_e κ_e⁻¹ Q(a,b) · nestCup · Q(c_e, c) · nestCap · Q(a,b)`
with `c_e = a + b - 2 e`. -/
theorem Qab_mul_jwAt_decomp [CharZero k] (q : kˣ) (a b c : ℕ) (hab : 1 ≤ a + b)
    (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Qab q a b * jwAt q (a + b) c = ∑ e : Fin (min a b + 1), (kapRec q a b e)⁻¹ •
      (Qab q a b * nestCup q (a - e) e * Qab q (a + b - 2 * e) c * nestCap q (a - e) e * Qab q a b) := by
  have hfi := fusion_identity (k := k) q a b hd hq2
  have hc : (Qab q a b : Module.End k (ModelSpace k)) * jwAt q (a + b) c =
      (∑ e : Fin (min a b + 1), Eop q a b e) * jwAt q (a + b) c := by rw [← hfi]
  rw [hc, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hea : (e : ℕ) ≤ a := (Nat.lt_succ_iff.mp e.2).trans (min_le_left _ _)
  have heb : (e : ℕ) ≤ b := (Nat.lt_succ_iff.mp e.2).trans (min_le_right _ _)
  have hQJ := CSub_mul_jwAt q (m := a + b - 1) (s := a + b) (by omega) (Qab_mem q a b) c
  have hnc := nestCap_mul_jwAt q (l := a - e) (s := a + b - 2 * e) (by omega) c e
  rw [show a + b - 2 * (e : ℕ) + 2 * e = a + b by omega] at hnc
  have hp := jwAt_idem (k := k) q (c := a + b - 2 * e) (N := a + b + 1) (by omega) (fun j hj => hd j (by omega))
  unfold Eop
  rw [smul_mul_assoc]
  congr 1
  unfold Vop Wop Qab
  calc jwAt q 0 a * jwAt q a b * nestCup q (a - e) e * jwAt q 0 (a + b - 2 * e) *
        (jwAt q 0 (a + b - 2 * e) * nestCap q (a - e) e * (jwAt q 0 a * jwAt q a b)) * jwAt q (a + b) c
      = jwAt q 0 a * jwAt q a b * nestCup q (a - e) e * (jwAt q 0 (a + b - 2 * e) * jwAt q 0 (a + b - 2 * e)) *
        nestCap q (a - e) e * ((jwAt q 0 a * jwAt q a b) * jwAt q (a + b) c) := by simp only [mul_assoc]
    _ = jwAt q 0 a * jwAt q a b * nestCup q (a - e) e * jwAt q 0 (a + b - 2 * e) *
        nestCap q (a - e) e * (jwAt q (a + b) c * (jwAt q 0 a * jwAt q a b)) := by
          rw [hp]
          unfold Qab at hQJ
          rw [hQJ]
    _ = jwAt q 0 a * jwAt q a b * nestCup q (a - e) e * jwAt q 0 (a + b - 2 * e) *
        (nestCap q (a - e) e * jwAt q (a + b) c) * (jwAt q 0 a * jwAt q a b) := by simp only [mul_assoc]
    _ = _ := by rw [hnc]; simp only [mul_assoc]

end Lightlike.TemperleyLieb
