import Mathlib
import Lightlike.TemperleyLieb.Natural
import Lightlike.TemperleyLieb.Reduction
import Lightlike.TemperleyLieb.Mirror
import Lightlike.TemperleyLieb.JwNatural

/-!
# Sliding through nested cups

A generator acting just to the right of a nest of `i` cups at the junction `l + i` equals its mirror image
on the left (`e_mul_nestCup_slide`): the cups join the strand `l + i + t` to `l + i - 1 - t`. The basic
moves are the far commutation of two cups (`cup_mul_cup_far`) and the pulling of a strand through a cup
(`e_mul_cup_succ`, `e_mul_cup_pred`). Two commuting families of generators that agree after multiplication by
`N` have Jones–Wenzl projectors that agree after it (`jw_mul_eq_of_slide`), so a projector on `m ≤ i` strands right
of the junction slides to the mirror strands (`jwAt_mul_nestCup_slide`).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

lemma insertTwo_insertTwo_far (σ : ℕ → Bool) {m j : ℕ} (h : m ≤ j) (x y x' y' : Bool) :
    insertTwo (insertTwo σ j x' y') m x y = insertTwo (insertTwo σ m x y) (j + 2) x' y' := by
  funext n
  simp only [insertTwo]
  split_ifs <;> first | rfl | omega | (congr 1; omega) | simp_all <;> omega

/-- Two cups far apart commute (the right one shifting by two). -/
theorem cup_mul_cup_far (q : kˣ) {m j : ℕ} (h : m ≤ j) :
    cupOp q (j + 2) * cupOp q m = cupOp q m * cupOp q j := by
  refine model_ext fun σ => ?_
  have r : ∀ x y x' y', insertTwo (insertTwo σ j x' y') m x y = insertTwo (insertTwo σ m x y) (j + 2) x' y' :=
    fun x y x' y' => insertTwo_insertTwo_far σ h x y x' y'
  simp only [Module.End.mul_apply, cupOp_single, cupBasis, one_smul, map_sub, map_smul, r, smul_sub, smul_smul]
  abel

/-- **A generator slides through a nest of cups** to its mirror position. -/
theorem e_mul_nestCup_slide (q : kˣ) (l : ℕ) : ∀ i t, t + 2 ≤ i →
    modelE q (l + i + t) * nestCup q l i = (modelE q (l + i - 2 - t) : Module.End k (ModelSpace k)) * nestCup q l i
  | 0, t, h => by omega
  | i + 1, t, h => by
    simp only [nestCup]
    rcases t with _ | t
    · -- the innermost strand: pull it through the outer cup on both sides
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have h1 := e_mul_cup_succ (k := k) q (l + (i + 1))
      have h2 := e_mul_cup_pred (k := k) q (l + i)
      rw [show l + (i + 1 + 1) + 0 = l + (i + 1) + 1 by omega, ← mul_assoc, h1,
        show l + (i + 1 + 1) - 2 - 0 = l + i by omega, ← mul_assoc, show l + (i + 1) = l + i + 1 by omega, h2]
      simp only [nestCup]
      rw [← mul_assoc, ← mul_assoc, show l + i + 1 + 1 = l + i + 2 by omega,
        cup_mul_cup_far (k := k) q (m := l + i) (j := l + i) le_rfl]
    · have h1 := e_mul_cup_far (k := k) q (m := l + i) (j := l + i + t) (by omega)
      have h2 := e_mul_cup_near (k := k) q (m := l + i) (j := l + (i + 1) - 2 - (t + 1)) (by omega)
      rw [show l + (i + 1) + (t + 1) = l + i + t + 2 by omega, ← mul_assoc, h1, mul_assoc,
        e_mul_nestCup_slide q l i t (by omega), ← mul_assoc, ← mul_assoc, h2,
        show l + i - 2 - t = l + (i + 1) - 2 - (t + 1) by omega]

/-- `jw` only sees the generators `e j`, `j + 1 < n`. -/
lemma jw_congr {A : Type*} [Ring A] [Algebra k A] (δ : k) {e f : ℕ → A} :
    ∀ n, (∀ j, j + 1 < n → e j = f j) → jw δ e n = jw δ f n
  | 0, _ => by simp [jw]
  | 1, _ => by simp [jw]
  | n + 2, h => by
    rw [jw_succ_succ, jw_succ_succ, jw_congr δ (n + 1) fun j hj => h j (by omega), h n (by omega)]

/-- **Sliding a projector**: if two commuting families of generators agree after multiplication by `N`,
so do their Jones–Wenzl projectors. -/
theorem jw_mul_eq_of_slide {A : Type*} [Ring A] [Algebra k A] (δ : k) (E F : ℕ → A) (N : A) :
    ∀ n, (∀ j j', j + 1 < n → j' + 1 < n → E j * F j' = F j' * E j) →
      (∀ j, j + 1 < n → E j * N = F j * N) → jw δ E n * N = jw δ F n * N
  | 0, _, _ => by simp [jw]
  | 1, _, _ => by simp [jw]
  | n + 2, hc, hs => by
    have ih := jw_mul_eq_of_slide δ E F N (n + 1) (fun j j' h1 h2 => hc j j' (by omega) (by omega))
      (fun j hj => hs j (by omega))
    set J := jw δ E (n + 1)
    set J' := jw δ F (n + 1)
    have hFJ : ∀ j', j' + 1 < n + 2 → F j' * J = J * F j' := fun j' hj' =>
      jw_intertwine δ (F j') E E (n + 1) fun j hj => (hc j j' (by omega) hj').symm
    have hEJ' : E n * J' = J' * E n :=
      jw_intertwine δ (E n) F F (n + 1) fun j hj => hc n j (by omega) (by omega)
    have hJJ' : J * J' = J' * J :=
      jw_intertwine δ J F F (n + 1) fun j hj => (hFJ j (by omega)).symm
    have key : J * E n * J * N = J' * F n * J' * N := by
      calc J * E n * J * N = J * (E n * J') * N := by simp only [mul_assoc]; rw [ih]
        _ = J * J' * (E n * N) := by rw [hEJ']; simp only [mul_assoc]
        _ = J' * (J * F n) * N := by rw [hs n (by omega), hJJ']; simp only [mul_assoc]
        _ = J' * F n * J' * N := by rw [← hFJ n (by omega)]; simp only [mul_assoc]; rw [ih]
    rw [jw_succ_succ, jw_succ_succ, sub_mul, sub_mul, smul_mul_assoc, smul_mul_assoc, ih, key]

/-- **A projector slides through a nest of cups** to the mirror strands:
`p_{[l+i, l+i+m)} · nestCup_l^i = p_{[l+i-m, l+i)} · nestCup_l^i` for `m ≤ i`. -/
theorem jwAt_mul_nestCup_slide (q : kˣ) {l i m : ℕ} (hm : m ≤ i)
    (hd : ∀ j, j < m → chebD (loopVal q) j ≠ 0) :
    (jwAt q (l + i) m : Module.End k (ModelSpace k)) * nestCup q l i = jwAt q (l + i - m) m * nestCup q l i := by
  have hTL := isTL_shift (k := k) q 0
  have hF : jw (loopVal q) (fun j => (modelE q (l + i - 2 - j) : Module.End k (ModelSpace k))) m =
      jwAt q (l + i - m) m := by
    have hρ := reflectOp_mul_self (k := k) (0 + (l + i - m) + m)
    rw [jwAt_mirror q 0 (l + i - m) m hd]
    unfold jwAt
    rw [conj_jw _ _ hρ _ m]
    refine jw_congr _ m fun t ht => ?_
    have := reflect_conj_e (k := k) q (t + 0) (l + i - m + (m - 2 - t))
    rw [show t + 0 + (l + i - m + (m - 2 - t)) + 2 = 0 + (l + i - m) + m by omega,
      show l + i - m + (m - 2 - t) = l + i - 2 - t by omega] at this
    exact this.symm
  rw [← hF]
  unfold jwAt
  refine jw_mul_eq_of_slide _ _ _ _ m (fun j j' h1 h2 => ?_) (fun j hj => ?_)
  · have := hTL.comm (l + i - 2 - j') (j + (l + i)) (by omega)
    simpa using this.symm
  · rw [show j + (l + i) = l + i + j by omega]
    exact e_mul_nestCup_slide q l i j (by omega)

end Lightlike.TemperleyLieb
