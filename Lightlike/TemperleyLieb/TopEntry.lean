import Mathlib
import Lightlike.TemperleyLieb.Expansion
import Lightlike.TemperleyLieb.Pentagon
import Lightlike.TemperleyLieb.FusionIdentity

/-!
# The recoupling coefficient with both channels of the third block maximal

When no arc joins the third block `c` to the first channel (`d = 0`) and none joins `b` to `c` (`f = 0`), the
pairing of the two tree vectors is a single vertex norm: `U_L'(e,0) U_R(0,e) = κ(a, b + c, e) p_D`, so
`Fc q a b c e 0 0 e = κ(a, b+c, e) / κ(a, b, e)` (`kapRec`). This is one of the base values of the recursion that
identifies `Fc` with the Kauffman–Lins coefficient (`KLCoef.lean`).

Numerical evidence (not proof): the model of the operators re-implemented on bit strings at a random complex `q`
gives `Fc(a,b,c,e,0,0,e) = κ(a,b+c,e)/κ(a,b,e)` for `a, b ≤ 3`, `c ≤ 3` (error `≤ 4.5e-16`).
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- The translated vertex with no arc is the translated projector: `sh a (V(b,c;0)) = p_{[a, a+b+c)}`. -/
theorem sh_Vop_zero (q : kˣ) (a b c : ℕ) (hd : ∀ j, j < b + c → chebD (loopVal q) j ≠ 0) :
    sh a (Vop q b c 0 : Module.End k (ModelSpace k)) = jwAt q a (b + c) := by
  have h1 : (Vop q b c 0 : Module.End k (ModelSpace k)) = jwAt q 0 (b + c) := by
    unfold Vop
    simp only [nestCup, mul_one, Nat.mul_zero, Nat.sub_zero]
    exact Qab_mul_full_eq q b c hd
  rw [h1, sh_jwAt, zero_add]

/-- `Q(a, b) · p_{[a, a+b+c)} · Q(a, b + c) = Q(a, b + c)`: the projector on the first `a` strands and the one on
the strands `a, …, a+b+c-1` absorb the smaller one on `a, …, a+b-1`. -/
theorem Qab_mul_jwAt_mul_Qab (q : kˣ) (a b c : ℕ) (hd : ∀ j, j < a + b + c → chebD (loopVal q) j ≠ 0) :
    (Qab q a b : Module.End k (ModelSpace k)) * jwAt q a (b + c) * Qab q a (b + c) = Qab q a (b + c) := by
  have hpa := jwProps_of_le (isTL_shift q 0) (a + b + c) hd a (by omega)
  have hpb := jwProps_of_le (isTL_shift q a) (b + c) (fun j hj => hd j (by omega)) (b + c) le_rfl
  have habs : (jwAt q a b : Module.End k (ModelSpace k)) * jwAt q a (b + c) = jwAt q a (b + c) :=
    hpb.absL b (by omega)
  have hidem : (jwAt q a (b + c) : Module.End k (ModelSpace k)) * jwAt q a (b + c) = jwAt q a (b + c) := hpb.idem
  have hidem0 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q 0 a = jwAt q 0 a := hpa.idem
  have hcomm : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q a (b + c) = jwAt q a (b + c) * jwAt q 0 a :=
    jwAt_comm_jwAt q le_rfl (b + c)
  unfold Qab
  calc (jwAt q 0 a * jwAt q a b : Module.End k (ModelSpace k)) * jwAt q a (b + c) * (jwAt q 0 a * jwAt q a (b + c))
      = jwAt q 0 a * (jwAt q a b * jwAt q a (b + c)) * (jwAt q 0 a * jwAt q a (b + c)) := by
        simp only [mul_assoc]
    _ = jwAt q 0 a * jwAt q a (b + c) * (jwAt q 0 a * jwAt q a (b + c)) := by rw [habs]
    _ = jwAt q 0 a * (jwAt q a (b + c) * jwAt q 0 a) * jwAt q a (b + c) := by simp only [mul_assoc]
    _ = jwAt q 0 a * (jwAt q 0 a * jwAt q a (b + c)) * jwAt q a (b + c) := by rw [hcomm]
    _ = (jwAt q 0 a * jwAt q 0 a) * (jwAt q a (b + c) * jwAt q a (b + c)) := by simp only [mul_assoc]
    _ = jwAt q 0 a * jwAt q a (b + c) := by rw [hidem0, hidem]

/-- **The pairing with both channels of the third block maximal** is the vertex norm of `(a, b + c)` with `e` arcs:
`U_L'(a,b,c;e,0) · U_R(a,b,c;0,e) = κ(a, b+c, e) · p_{a+b+c-2e}`. -/
theorem ULd_mul_UR_top (q : kˣ) (a b c e : ℕ) (hea : e ≤ a) (heb : e ≤ b)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    ULd q a b c e 0 * UR q a b c 0 e = kapRec q a (b + c) e • jwAt q 0 (a + b - 2 * e + c - 2 * 0) := by
  set X := a + b - 2 * e with hX
  have hXc : X + c - 2 * 0 = a + (b + c) - 2 * e := by omega
  -- the outer projector absorbs `Q(X, c)` and `p_X`
  have hfull : (jwAt q 0 (X + c) : Module.End k (ModelSpace k)) * Qab q X c = jwAt q 0 (X + c) :=
    full_mul_Qab q X c (fun j hj => hd j (by omega))
  have hpXc := jwProps_of_le (isTL_shift q 0) (X + c + 1) (fun j hj => hd j (by omega)) (X + c) (by omega)
  have habsX : (jwAt q 0 (X + c) : Module.End k (ModelSpace k)) * jwAt q 0 X = jwAt q 0 (X + c) :=
    hpXc.absR X (by omega)
  have hsh := sh_Vop_zero (k := k) q a b c (fun j hj => hd j (by omega))
  have hmid := Qab_mul_jwAt_mul_Qab (k := k) q a b c (fun j hj => hd j (by omega))
  have hvn := vertex_norm_value (k := k) q e a (b + c) hea (by omega) (fun j hj => hd j (by omega))
  rw [show a + (b + c) - 2 * e = X + c - 2 * 0 by omega] at hvn
  unfold ULd UR Wop
  simp only [Nat.mul_zero, Nat.sub_zero]
  rw [hsh]
  unfold Vop
  rw [show a + (b + c) - 2 * e = X + c by omega]
  simp only [nestCap, mul_one, Nat.mul_zero, Nat.sub_zero] at hvn ⊢
  calc (jwAt q 0 (X + c) * Qab q X c * (jwAt q 0 X * nestCap q (a - e) e * Qab q a b) *
        (jwAt q a (b + c) * (Qab q a (b + c) * nestCup q (a - e) e * jwAt q 0 (X + c))) :
        Module.End k (ModelSpace k))
      = (jwAt q 0 (X + c) * Qab q X c) * jwAt q 0 X * nestCap q (a - e) e *
          (Qab q a b * jwAt q a (b + c) * Qab q a (b + c)) * nestCup q (a - e) e * jwAt q 0 (X + c) := by
        simp only [mul_assoc]
    _ = jwAt q 0 (X + c) * (nestCap q (a - e) e * Qab q a (b + c) * nestCup q (a - e) e) *
          jwAt q 0 (X + c) := by
        rw [hfull, habsX, hmid]; simp only [mul_assoc]
    _ = kapRec q a (b + c) e • jwAt q 0 (X + c) := hvn

/-- **The recoupling coefficient with both channels of the third block maximal**:
`Fc q a b c e 0 0 e = κ(a, b+c, e) / κ(a, b, e)`. -/
theorem Fc_top (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e : ℕ) (hea : e ≤ a) (heb : e ≤ b) (hN : 1 ≤ a + b + c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    Fc q a b c e 0 0 e = kapRec q a (b + c) e / kapRec q a b e := by
  have h1 := gram_spec q hδ a b c e 0 0 e hN hd hea heb (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    (Nat.zero_le _) hea (by omega)
  have h2 := ULd_mul_UR_top q a b c e hea heb hd
  have h3 : (gramCoef q a b c e 0 0 e - kapRec q a (b + c) e) •
      (jwAt q 0 (a + b - 2 * e + c - 2 * 0) : Module.End k (ModelSpace k)) = 0 :=
    (sub_smul (gramCoef q a b c e 0 0 e) (kapRec q a (b + c) e)
      (jwAt q 0 (a + b - 2 * e + c - 2 * 0) : Module.End k (ModelSpace k))).trans
      (sub_eq_zero.mpr (h1.symm.trans h2))
  have hg : gramCoef q a b c e 0 0 e = kapRec q a (b + c) e :=
    sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (jwAt_ne_zero q _))
  unfold Fc
  rw [if_pos ⟨le_min hea heb, Nat.zero_le _⟩, hg]
  simp only [kapRec, inv_one, mul_one]
  rw [div_eq_inv_mul]

/-- **The recoupling coefficient with an empty third block** is the identity matrix:
`Fc q a b 0 e 0 0 d' = δ_{e d'}`. -/
theorem Fc_zero_third (q : kˣ) (hδ : loopVal q ≠ 0) (a b e d' : ℕ) (he : e ≤ min a b) (hd' : d' ≤ min a b)
    (hN : 1 ≤ a + b) (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Fc q a b 0 e 0 0 d' = if d' = e then 1 else 0 := by
  have hea : e ≤ a := he.trans (min_le_left _ _)
  have heb : e ≤ b := he.trans (min_le_right _ _)
  by_cases h : d' = e
  · subst h
    rw [if_pos rfl, Fc_top q hδ a b 0 d' hea heb (by omega) (fun j hj => hd j (by omega)), Nat.add_zero]
    exact div_self (kapRec_ne q d' a b hea heb hq2)
  · rw [if_neg h]
    unfold Fc
    rw [if_pos ⟨he, by simp⟩, gramCoef_zero_of_ne q hδ a b 0 e 0 0 d' (by omega) (fun j hj => hd j (by omega))
      hea heb (Nat.zero_le _) le_rfl le_rfl (Nat.zero_le _) (hd'.trans (min_le_left _ _))
      (by have := hd'.trans (min_le_right _ _); omega) (by omega), mul_zero]

end Lightlike.TemperleyLieb
