import Mathlib
import Lightlike.TemperleyLieb.GramVanish

/-!
# The expansion of a second-bracketing tree vector in the first-bracketing basis

`U_R(f,d') = Σ_{e,d} α(e,d) U_L(e,d)` with `α = (κ_e κ_d)⁻¹ g(e,d; f,d')` where `g` is the Gram scalar
(`g = 0` for different total channels).
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- The first-bracketing tree vector `V_e V_d`. -/
noncomputable def UL (q : kˣ) (a b c e d : ℕ) : Module.End k (ModelSpace k) :=
  Vop q a b e * Vop q (a + b - 2 * e) c d

/-- The dual first-bracketing tree vector `W_d W_e`. -/
noncomputable def ULd (q : kˣ) (a b c e d : ℕ) : Module.End k (ModelSpace k) :=
  Wop q (a + b - 2 * e) c d * Wop q a b e

/-- The second-bracketing tree vector `sh V_f · V_{d'}`. -/
noncomputable def UR (q : kˣ) (a b c f d' : ℕ) : Module.End k (ModelSpace k) :=
  sh a (Vop q b c f) * Vop q a (b + c - 2 * f) d'

/-- `treeL = (κ_e κ_d)⁻¹ · U_L U_L'`. -/
theorem treeL_eq_UU (q : kˣ) (a b c e d : ℕ)
    (hd : ∀ j, j ≤ a + b - 2 * e + c → chebD (loopVal q) j ≠ 0) :
    treeL q a b c e d = ((kapRec q a b e)⁻¹ * (kapRec q (a + b - 2 * e) c d)⁻¹) •
      (UL q a b c e d * ULd q a b c e d) := by
  rw [treeL_eq q a b c e d hd]
  unfold Eop UL ULd
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]

/-- The right projector of `U_L` is absorbed. -/
theorem UL_mul_proj (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b) (hdA : d ≤ a + b - 2 * e) (hdc : d ≤ c)
    (hd : ∀ j, j ≤ a + b - 2 * e + c → chebD (loopVal q) j ≠ 0) :
    UL q a b c e d * jwAt q 0 (a + b - 2 * e + c - 2 * d) = UL q a b c e d := by
  unfold UL
  rw [mul_assoc, Vop_mul_jwAt (k := k) q (a + b - 2 * e) c hd hdA hdc]

/-- `P₃ · U_R = U_R`. -/
theorem P3_mul_UR (q : kˣ) (a b c f d' : ℕ) (hfb : f ≤ b) (hfc : f ≤ c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    P3 q a b c * UR q a b c f d' = UR q a b c f d' := by
  have hdc : ∀ j, j ≤ a + (b + c - 2 * f) → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hQs : sh a (Qab q b c : Module.End k (ModelSpace k)) = jwAt q a b * jwAt q (b + a) c := by
    unfold Qab; rw [sh_mul, sh_jwAt, sh_jwAt]; simp
  have hsh := congrArg (sh a) (Qab_idem (k := k) q b c (fun j hj => hd j (by omega)))
  rw [sh_mul, hQs] at hsh
  have hp : (jwAt q 0 a : Module.End k (ModelSpace k)) * (jwAt q a b * jwAt q (b + a) c) =
      (jwAt q a b * jwAt q (b + a) c) * jwAt q 0 a := by
    rw [← mul_assoc, jwAt_comm_jwAt q le_rfl b, mul_assoc, jwAt_comm_jwAt q (by omega) c, mul_assoc]
  have hP3 : P3 q a b c = jwAt q 0 a * (jwAt q a b * jwAt q (b + a) c) := by
    rw [← jwAt_mul_sh_Qab, hQs]
  have hQ := jwAt_mul_Qab' (k := k) q a (b + c - 2 * f) hdc
  have hpJ := jwAt_comm_jwAt (k := k) q (A := a) (s := a) le_rfl (b + c - 2 * f)
  have hpn := jwAt_mul_nestCup (k := k) q (a := a) (l := b - f + a) (by omega) f
  unfold UR
  rw [sh_Vop, hP3]
  set Qs : Module.End k (ModelSpace k) := jwAt q a b * jwAt q (b + a) c with hQsdef
  calc jwAt q 0 a * Qs * (Qs * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d')
      = jwAt q 0 a * (Qs * Qs) * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        simp only [mul_assoc]
    _ = (jwAt q 0 a * Qs) * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        rw [hsh]
    _ = Qs * jwAt q 0 a * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        rw [hp]
    _ = Qs * (nestCup q (b - f + a) f * jwAt q 0 a) * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        rw [← hpn]; simp only [mul_assoc]
    _ = Qs * nestCup q (b - f + a) f * (jwAt q 0 a * jwAt q a (b + c - 2 * f)) * Vop q a (b + c - 2 * f) d' := by
        simp only [mul_assoc]
    _ = Qs * nestCup q (b - f + a) f * (jwAt q a (b + c - 2 * f) * jwAt q 0 a) * Vop q a (b + c - 2 * f) d' := by
        rw [hpJ]
    _ = Qs * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * (jwAt q 0 a * Vop q a (b + c - 2 * f) d') := by
        simp only [mul_assoc]
    _ = _ := by
        have : jwAt q 0 a * Vop q a (b + c - 2 * f) d' = Vop q a (b + c - 2 * f) d' := by
          unfold Vop; rw [← mul_assoc, ← mul_assoc, hQ]
        rw [this]

/-- The Gram coefficient `U_L' U_R = g · p_D` (zero when the total channels differ). -/
noncomputable def gramCoef (q : kˣ) (a b c e d f d' : ℕ) : k :=
  if h : ∃ g : k, ULd q a b c e d * UR q a b c f d' = g • jwAt q 0 (a + b - 2 * e + c - 2 * d) then h.choose else 0

/-- **The Gram coefficient as a scalar, in every case.** -/
theorem gram_spec (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d f d' : ℕ) (hN : 1 ≤ a + b + c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hea : e ≤ a) (heb : e ≤ b) (hfb : f ≤ b) (hfc : f ≤ c) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f) :
    ULd q a b c e d * UR q a b c f d' = gramCoef q a b c e d f d' • jwAt q 0 (a + b - 2 * e + c - 2 * d) := by
  have hex : ∃ g : k, ULd q a b c e d * UR q a b c f d' = g • jwAt q 0 (a + b - 2 * e + c - 2 * d) := by
    by_cases hD : a + b - 2 * e + c - 2 * d = a + (b + c - 2 * f) - 2 * d'
    · exact gram_scalar q a b c e d f d' hN hd hea heb hfb hfc hdc hdA hda hdf hD
    · exact ⟨0, by rw [zero_smul]; exact gram_vanish q hδ a b c e d f d' hN hd hea heb hfb hfc hdc hdA hda hdf hD⟩
  unfold gramCoef
  rw [dif_pos hex]
  exact hex.choose_spec

/-- **Expansion of the second-bracketing tree vector in the first-bracketing basis.** -/
theorem expansion [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c f d' : ℕ) (hab : 1 ≤ a + b)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f) :
    UR q a b c f d' = ∑ e : Fin (min a b + 1), ∑ d : Fin (min (a + b - 2 * e) c + 1),
      ((kapRec q a b e)⁻¹ * (kapRec q (a + b - 2 * e) c d)⁻¹ * gramCoef q a b c e d f d') • UL q a b c e d := by
  have hN : 1 ≤ a + b + c := by omega
  conv_lhs => rw [← P3_mul_UR q a b c f d' hfb hfc hd]
  have hP : P3 q a b c = ∑ e : Fin (min a b + 1), ∑ d : Fin (min (a + b - 2 * e) c + 1), treeL q a b c e d :=
    Qab_mul_jwAt_trees q a b c hab hd hq2
  rw [hP, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hea : (e : ℕ) ≤ a := (Nat.lt_succ_iff.mp e.2).trans (min_le_left _ _)
  have heb : (e : ℕ) ≤ b := (Nat.lt_succ_iff.mp e.2).trans (min_le_right _ _)
  have hdd := Nat.lt_succ_iff.mp d.2
  have hdc : (d : ℕ) ≤ c := hdd.trans (min_le_right _ _)
  have hdA : (d : ℕ) ≤ a + b - 2 * e := hdd.trans (min_le_left _ _)
  rw [treeL_eq_UU q a b c e d (fun j hj => hd j (by omega)), smul_mul_assoc, mul_assoc,
    gram_spec q hδ a b c e d f d' hN hd hea heb hfb hfc hdc hdA hda hdf, mul_smul_comm,
    UL_mul_proj q a b c e d hea heb hdA hdc (fun j hj => hd j (by omega)), smul_smul]

/-- **Orthogonality of the first-bracketing tree vectors**: `U_L'(e,d) U_L(e',d') = δ κ_e κ_d p_D`. -/
theorem ULd_mul_UL [CharZero k] (q : kˣ) (a b c : ℕ)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    {e d e' d' : ℕ} (hea : e ≤ a) (heb : e ≤ b) (hea' : e' ≤ a) (heb' : e' ≤ b)
    (hdA : d ≤ a + b - 2 * e) (hdc : d ≤ c) (hdA' : d' ≤ a + b - 2 * e') (hdc' : d' ≤ c) :
    ULd q a b c e d * UL q a b c e' d' =
      if e = e' ∧ d = d' then (kapRec q a b e * kapRec q (a + b - 2 * e) c d) • jwAt q 0 (a + b - 2 * e + c - 2 * d)
      else 0 := by
  unfold ULd UL
  by_cases hee : e = e'
  · subst hee
    have hWV := Wop_mul_Vop q a b e hea heb (fun j hj => hd j (by omega))
    have hpV : jwAt q 0 (a + b - 2 * e) * Vop q (a + b - 2 * e) c d' = Vop q (a + b - 2 * e) c d' := by
      unfold Vop; rw [← mul_assoc, ← mul_assoc, jwAt_mul_Qab' (k := k) q (a + b - 2 * e) c
        (fun j hj => hd j (by omega))]
    have key : Wop q (a + b - 2 * e) c d * Wop q a b e * (Vop q a b e * Vop q (a + b - 2 * e) c d') =
        kapRec q a b e • (Wop q (a + b - 2 * e) c d * Vop q (a + b - 2 * e) c d') := by
      calc _ = Wop q (a + b - 2 * e) c d * (Wop q a b e * Vop q a b e) * Vop q (a + b - 2 * e) c d' := by
            simp only [mul_assoc]
        _ = _ := by rw [hWV, mul_smul_comm, smul_mul_assoc, mul_assoc, hpV]
    rw [key]
    by_cases hdd : d = d'
    · subst hdd
      rw [if_pos ⟨rfl, rfl⟩, Wop_mul_Vop q (a + b - 2 * e) c d hdA hdc (fun j hj => hd j (by omega)), smul_smul]
    · rw [if_neg (fun h => hdd h.2)]
      have hm : 1 ≤ min (a + b - 2 * e) c := by omega
      have h0 := channel_orth q (a + b - 2 * e) c d d' (by omega) (by omega) hdA hdc hdA' hdc'
        (fun j hj => hd j (by omega))
        (lamRec_ne q (a + b - 2 * e) c d d' hdA hdc hdA' hdc' hdd (fun j h1 h2 => hq2 j h1 (by omega)))
      rw [h0, smul_zero]
  · rw [if_neg (fun h => hee h.1)]
    have hm : 1 ≤ min a b := by omega
    have h0 := channel_orth q a b e e' (by omega) (by omega) hea heb hea' heb' (fun j hj => hd j (by omega))
      (lamRec_ne q a b e e' hea heb hea' heb' hee (fun j h1 h2 => hq2 j h1 (by omega)))
    calc Wop q (a + b - 2 * e) c d * Wop q a b e * (Vop q a b e' * Vop q (a + b - 2 * e') c d') =
        Wop q (a + b - 2 * e) c d * (Wop q a b e * Vop q a b e') * Vop q (a + b - 2 * e') c d' := by
          simp only [mul_assoc]
      _ = 0 := by rw [h0]; simp

end Lightlike.TemperleyLieb
