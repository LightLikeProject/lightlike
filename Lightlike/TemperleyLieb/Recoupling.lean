import Mathlib
import Lightlike.TemperleyLieb.Shift

/-!
# Recoupling: the two decompositions of the projector on three blocks

`P₃ = Q(a,b) p_c` is the sum of the first-bracketing tree idempotents `treeL e d` and also of the second-bracketing
ones `treeR f d'`.  Every `treeL e d` is one-dimensional inside `C (N-1)`, so the scalars `treeL · treeR · treeL`
are well defined: these are the recoupling coefficients, and their row sums are `1`.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- The projector on three blocks. -/
noncomputable def P3 (q : kˣ) (a b c : ℕ) : Module.End k (ModelSpace k) := Qab q a b * jwAt q (a + b) c

/-- `Q(a,b)` commutes with a projector on the strands beyond `a + b`. -/
theorem Qab_comm_jwAt (q : kˣ) (a b c : ℕ) :
    (Qab q a b : Module.End k (ModelSpace k)) * jwAt q (a + b) c = jwAt q (a + b) c * Qab q a b := by
  have h1 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q (a + b) c = jwAt q (a + b) c * jwAt q 0 a :=
    jwAt_comm_jwAt q (by omega) c
  have h2 := congrArg (sh a) (jwAt_comm_jwAt (k := k) q (A := b) (s := b) le_rfl c)
  rw [sh_mul, sh_mul, sh_jwAt, sh_jwAt] at h2
  simp only [zero_add] at h2
  rw [add_comm b a] at h2
  unfold Qab
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

/-- `treeL · P₃ = treeL`. -/
theorem treeL_mul_P3 (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    treeL q a b c e d * P3 q a b c = treeL q a b c e d := by
  have hdAc : ∀ j, j ≤ a + b - 2 * e + c → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hQ := Qab_idem (k := k) q a b (fun j hj => hd j (by omega))
  have hnc := nestCap_mul_jwAt (k := k) q (l := a - e) (s := a + b - 2 * e) (by omega) c e
  rw [show a + b - 2 * e + 2 * e = a + b by omega] at hnc
  have hEJ := Eop_mul_jwAt_shift (k := k) q (a + b - 2 * e) c d hdAc
  unfold treeL P3
  rw [smul_mul_assoc]
  congr 1
  calc Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e * Qab q a b *
        (Qab q a b * jwAt q (a + b) c)
      = Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e *
        ((Qab q a b * Qab q a b) * jwAt q (a + b) c) := by simp only [mul_assoc]
    _ = Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e *
        (jwAt q (a + b) c * Qab q a b) := by rw [hQ, Qab_comm_jwAt]
    _ = Qab q a b * nestCup q (a - e) e * (Eop q (a + b - 2 * e) c d * jwAt q (a + b - 2 * e) c) *
        nestCap q (a - e) e * Qab q a b := by
          simp only [← mul_assoc]; rw [mul_assoc _ (nestCap q (a - e) e), hnc]; simp only [mul_assoc]
    _ = _ := by rw [hEJ]

/-- `p_c ≠ 0`. -/
theorem jwAt_ne_zero (q : kˣ) (c : ℕ) : (jwAt q 0 c : Module.End k (ModelSpace k)) ≠ 0 := by
  intro h
  have := jwAt_dicke (k := k) q c 0
  rw [h] at this
  exact dicke_ne_zero (k := k) q (Nat.zero_le c) this.symm

/-- **The first-bracketing tree idempotents are non-zero.** -/
theorem treeL_ne_zero (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c)
    (hdA : d ≤ a + b - 2 * e)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1) :
    treeL q a b c e d ≠ 0 := by
  set A := a + b - 2 * e with hA
  have hdAc : ∀ j, j ≤ A + c → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hκ1 := kapRec_ne (k := k) q e a b hea heb (fun j h1 h2 => hq2 j h1 (by omega))
  have hκ2 := kapRec_ne (k := k) q d A c hdA hdc (fun j h1 h2 => hq2 j h1 (by omega))
  have hW1 := Wop_mul_Vop q a b e hea heb (fun j hj => hd j (by omega))
  have hW2 := Wop_mul_Vop q A c d hdA hdc hdAc
  have hpA := jwAt_mul_Qab' (k := k) q A c hdAc
  -- `W_d W_e V_e V_d = κ_e κ_d p_D`
  have hmid : Wop q A c d * (Wop q a b e * Vop q a b e) * Vop q A c d =
      (kapRec q a b e * kapRec q A c d) • jwAt q 0 (A + c - 2 * d) := by
    rw [hW1, mul_smul_comm, smul_mul_assoc]
    have : jwAt q 0 A * Vop q A c d = Vop q A c d := by
      unfold Vop; rw [← mul_assoc, ← mul_assoc, hpA]
    rw [mul_assoc, this, hW2, smul_smul]
  intro h0
  have hT : treeL q a b c e d = ((kapRec q a b e)⁻¹ * (kapRec q A c d)⁻¹) •
      (Vop q a b e * Vop q A c d * Wop q A c d * Wop q a b e) := by
    rw [treeL_eq q a b c e d hdAc]
    unfold Eop
    rw [mul_smul_comm, smul_mul_assoc, smul_smul]
    simp only [mul_assoc, hA]
  rw [hT] at h0
  have h1 : Vop q a b e * Vop q A c d * Wop q A c d * Wop q a b e = 0 := by
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd h (mul_ne_zero (inv_ne_zero hκ1) (inv_ne_zero hκ2))
    · exact h
  have hm : (Wop q A c d * Wop q a b e) * (Vop q a b e * Vop q A c d) =
      (kapRec q a b e * kapRec q A c d) • jwAt q 0 (A + c - 2 * d) := by
    rw [← hmid]; simp only [mul_assoc]
  have h1' : (Vop q a b e * Vop q A c d) * (Wop q A c d * Wop q a b e) = 0 := by
    rw [← h1]; simp only [mul_assoc]
  have h2 : ((Wop q A c d * Wop q a b e) * (Vop q a b e * Vop q A c d)) *
      ((Wop q A c d * Wop q a b e) * (Vop q a b e * Vop q A c d)) = 0 := by
    calc _ = (Wop q A c d * Wop q a b e) * ((Vop q a b e * Vop q A c d) * (Wop q A c d * Wop q a b e)) *
          (Vop q a b e * Vop q A c d) := by simp only [mul_assoc]
      _ = 0 := by rw [h1']; simp
  rw [hm, smul_mul_assoc, mul_smul_comm, smul_smul] at h2
  have hpp : jwAt q 0 (A + c - 2 * d) * jwAt q 0 (A + c - 2 * d) = (jwAt q 0 (A + c - 2 * d) : Module.End k (ModelSpace k)) :=
    jwAt_idem (k := k) q (N := A + c + 1) (by omega) (fun j hj => hdAc j (by omega))
  rw [hpp] at h2
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero hκ1 hκ2) (mul_ne_zero hκ1 hκ2))
  · exact jwAt_ne_zero q _ h

/-- The two bracketings give the same projector. -/
theorem jwAt_mul_sh_Qab (q : kˣ) (a b c : ℕ) :
    (jwAt q 0 a : Module.End k (ModelSpace k)) * sh a (Qab q b c) = P3 q a b c := by
  unfold Qab P3
  rw [sh_mul, sh_jwAt, sh_jwAt, zero_add, add_comm b a, Qab, mul_assoc]

/-- The recoupling coefficient: the scalar by which `treeL e d · treeR f d' · treeL e d` multiplies `treeL e d`. -/
noncomputable def recoup (q : kˣ) (a b c e d f d' : ℕ) : k :=
  if h : ∃ μ : k, treeL q a b c e d * treeR q a b c f d' * treeL q a b c e d = μ • treeL q a b c e d
  then h.choose else 0

/-- The scalar is unique when the tree idempotent is non-zero. -/
theorem smul_left_cancel_of_ne_zero {T : Module.End k (ModelSpace k)} (hT : T ≠ 0) {μ ν : k}
    (h : μ • T = ν • T) : μ = ν := by
  by_contra hne
  have : (μ - ν) • T = 0 := by
    refine LinearMap.ext fun v => ?_
    have := congrArg (fun S : Module.End k (ModelSpace k) => S v) h
    simp only [LinearMap.smul_apply] at this ⊢
    rw [sub_smul, this, sub_self]; rfl
  rcases smul_eq_zero.mp this with h1 | h1
  · exact hne (sub_eq_zero.mp h1)
  · exact hT h1

/-- Specification of the recoupling coefficient (first colour `a ≥ 1`, last colour `c ≥ 1`). -/
theorem recoup_spec [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d f d' : ℕ) (ha : 1 ≤ a)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f) :
    treeL q a b c e d * treeR q a b c f d' * treeL q a b c e d = recoup q a b c e d f d' • treeL q a b c e d := by
  have hY := treeR_mem (k := k) q hδ (a := a) (b := b) (c := c) (f := f) (d := d') hd hfb hfc hda hdf (by omega)
  obtain ⟨μ, hμ⟩ := treeL_sandwich q a b c e d (by omega) hd hea heb hdc hdA hY
  have hex : ∃ μ : k, treeL q a b c e d * treeR q a b c f d' * treeL q a b c e d = μ • treeL q a b c e d := ⟨μ, hμ⟩
  unfold recoup
  rw [dif_pos hex]
  exact hex.choose_spec

/-- **Row sums of the recoupling matrix are `1`.** -/
theorem recoup_row_sum [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d : ℕ) (ha : 1 ≤ a)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    (hea : e ≤ a) (heb : e ≤ b) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e) :
    ∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1), recoup q a b c e d f d' = 1 := by
  have hT0 := treeL_ne_zero (k := k) q a b c e d hea heb hdc hdA hd hq2
  have hidem := treeL_mul (k := k) q a b c hd hq2 (e := e) (d := d) (e' := e) (d' := d)
    (le_min hea heb) (le_min hea heb) (le_min hdA hdc |>.trans_eq (by rw [min_comm])) (le_min hdA hdc |>.trans_eq (by rw [min_comm]))
  rw [if_pos ⟨rfl, rfl⟩] at hidem
  have hsum : ∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1), treeR q a b c f d' = P3 q a b c := by
    rw [← jwAt_mul_Qab_trees q a b c hd hq2, jwAt_mul_sh_Qab]
  have hL := treeL_mul_P3 (k := k) q a b c e d hea heb hd
  have key : treeL q a b c e d * P3 q a b c * treeL q a b c e d = treeL q a b c e d := by
    rw [hL, hidem]
  have hexp : treeL q a b c e d * P3 q a b c * treeL q a b c e d =
      (∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1), recoup q a b c e d f d') •
        treeL q a b c e d := by
    rw [← hsum, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun d' _ => ?_
    have hfb : (f : ℕ) ≤ b := (Nat.lt_succ_iff.mp f.2).trans (min_le_left _ _)
    have hfc : (f : ℕ) ≤ c := (Nat.lt_succ_iff.mp f.2).trans (min_le_right _ _)
    exact recoup_spec q hδ a b c e d f d' ha hd hea heb hdc hdA hfb hfc
      ((Nat.lt_succ_iff.mp d'.2).trans (min_le_left _ _)) ((Nat.lt_succ_iff.mp d'.2).trans (min_le_right _ _))
  rw [hexp] at key
  have := smul_left_cancel_of_ne_zero hT0 (μ := ∑ f : Fin (min b c + 1), ∑ d' : Fin (min a (b + c - 2 * f) + 1),
    recoup q a b c e d f d') (ν := 1) (by rw [key, one_smul])
  exact this

end Lightlike.TemperleyLieb
