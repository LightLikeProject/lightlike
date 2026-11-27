import Mathlib
import Lightlike.TemperleyLieb.KLCoef
import Lightlike.TemperleyLieb.TopEntry
import Lightlike.TemperleyLieb.VertexNorm
import Lightlike.TemperleyLieb.Slide
import Lightlike.TemperleyLieb.Adjoint

/-!
# Base values of the Kauffman–Lins coefficient

With an empty third block the tetrahedral net is a theta net, `tetKL q a b 0 i i b = θ(a, b, i)`
(`tetKL_zero_third`: its sum has the single term `z = (a+b+i)/2`), and `θ(i, 0, i) = Δ_i`
(`thetaKL_zero_mid`), so the Kauffman–Lins coefficient is the identity matrix (`klCoef_zero_third`), as `Fc` is
(`Fc_zero_third`). This is the base `c = 0` of the identification `Fc = klCoef`.

The blocks with a third block of one strand (`c = 1`) are computed in closed form (`Fc_one_block`,
`Fc_top_one_qb`): `F00 = [a+b-E+2][b-E+1]/([b+1][a+b-2E+2])`, `F01 = -[a-E+1]/[a+b-2E+2]`, `F10 = [E]/[b+1]`,
`F11 = 1`. The proof is an induction on `b`: the recursion of the pentagon with blocks `(a, b, 1, 1)`
(`Fc_b_rec_two`) gives `F11` and `F01` from the levels below (`Fc_one_11_step`, `Fc_one_01_step`), the orthogonality
of the columns (`Fc_one_orth`, from the mirror inverse and the vertical flip) gives `F10` (`Fc_one_10_of_orth`), and
the base values are the cup column (`Fc_cup_low`, `Fc_cup_high`) and the edge entry (`Fc_edge`).
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- `θ(i, 0, i) = Δ_i`. -/
lemma thetaKL_zero_mid (q : kˣ) (i : ℕ) (hi : qfac q i ≠ 0) : thetaKL q i 0 i = deltaKL q i := by
  unfold thetaKL deltaKL
  rw [show (i + 0 + i) / 2 = i by omega, Nat.sub_self, Nat.sub_zero, show qfac q (i + 1) = qfac q i * qb q (i + 1) from rfl]
  simp only [qfac]
  field_simp

/-- With an empty third block the tetrahedral net is the theta net: `tetKL q a b 0 i i b = θ(a, b, i)`. -/
lemma tetKL_zero_third (q : kˣ) {a b e i : ℕ} (hea : e ≤ a) (heb : e ≤ b) (hi : i = a + b - 2 * e)
    (hnz : ∀ n, n ≤ a + b → qfac q n ≠ 0) : tetKL q a b 0 i i b = thetaKL q a b i := by
  have hs : (a + b + i) / 2 = a + b - e := by omega
  have h2 : (i + 0 + i) / 2 = i := by omega
  have h3 : (b + 0 + b) / 2 = b := by omega
  have h5 : (b + i + i + b) / 2 = b + i := by omega
  have h6 : (a + 0 + i + b) / 2 = a + b - e := by omega
  have h7 : (a + b + 0 + i) / 2 = a + b - e := by omega
  have hmax : max (max (a + b - e) i) (max b (a + b - e)) = a + b - e := by omega
  have hmin : min (b + i) (min (a + b - e) (a + b - e)) = a + b - e := by omega
  unfold tetKL tetPre tetTerm thetaKL
  simp only [hs, h2, h3, h5, h6, h7, hmax, hmin, Icc_self, sum_singleton, Nat.sub_self]
  rw [show a + b - e - i = e by omega, show a + b - e - b = a - e by omega, show b + i - (a + b - e) = b - e by omega,
    show b + i - i = b by omega, show b + i - b = i by omega, show a + b - e - a = b - e by omega]
  have := hnz a (by omega); have := hnz b (by omega); have := hnz i (by omega); have := hnz e (by omega)
  have := hnz (a - e) (by omega); have := hnz (b - e) (by omega)
  simp only [qfac]
  field_simp

/-- **The Kauffman–Lins coefficient with an empty third block** is the identity matrix. -/
theorem klCoef_zero_third (q : kˣ) {a b e d' : ℕ} (he : e ≤ min a b) (hnz : ∀ n, n ≤ a + b + 1 → qfac q n ≠ 0)
    (hθ : thetaKL q a b (a + b - 2 * e) ≠ 0) :
    klCoef q a b 0 e 0 0 d' = if d' = e then 1 else 0 := by
  have hea : e ≤ a := he.trans (min_le_left _ _)
  have heb : e ≤ b := he.trans (min_le_right _ _)
  unfold klCoef
  by_cases h : d' = e
  · subst h
    have hadm : KLAdm a b 0 d' 0 0 d' := ⟨he, by simp, by simp, le_min hea (by omega), by omega⟩
    rw [if_pos hadm, if_pos rfl]
    simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero]
    rw [tetKL_zero_third q hea heb rfl (fun n hn => hnz n (by omega)),
      thetaKL_zero_mid q _ (hnz _ (by omega))]
    have hΔ : deltaKL q (a + b - 2 * d') ≠ 0 := by
      unfold deltaKL
      have h1 := hnz (a + b - 2 * d' + 1) (by omega)
      have h0 := hnz (a + b - 2 * d') (by omega)
      refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
      intro hq; apply h1; simp only [qfac, hq, mul_zero]
    field_simp
  · rw [if_neg h, ite_eq_right_iff]
    rintro ⟨-, -, -, hd4, ht⟩
    exact absurd (by simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero] at hd4 ht; omega) h

/-- The quantum factorials up to `N` do not vanish when `q^{2j} ≠ 1` for `1 ≤ j ≤ N`. -/
lemma qfac_ne_of_pow (q : kˣ) {N : ℕ} (hN : 1 ≤ N) (hq2 : ∀ j, 1 ≤ j → j ≤ N → (q : k) ^ (2 * j) ≠ 1) :
    ∀ n, n ≤ N → qfac q n ≠ 0 := by
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl hN
    intro h; apply this
    have hq : (q : k) ≠ 0 := q.ne_zero
    field_simp at h
    linear_combination h
  exact qfac_ne q N fun j h1 h2 => qb_ne q hD j (hq2 j h1 h2)

lemma thetaKL_ne (q : kˣ) {a b c N : ℕ} (hs : (a + b + c) / 2 + 1 ≤ N) (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N)
    (hnz : ∀ n, n ≤ N → qfac q n ≠ 0) :
    thetaKL q a b c ≠ 0 := by
  unfold thetaKL
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (hnz _ (by omega))) (hnz _ (by omega))) (hnz _ (by omega))) (hnz _ (by omega)))
    (mul_ne_zero (mul_ne_zero (hnz _ (by omega)) (hnz _ (by omega))) (hnz _ (by omega)))

/-- **`Fc = klCoef` with an empty third block** (the base `c = 0` of the identification). -/
theorem Fc_eq_klCoef_zero_third (q : kˣ) (hδ : loopVal q ≠ 0) {a b e d' : ℕ} (he : e ≤ min a b)
    (hd' : d' ≤ min a b) (hN : 1 ≤ a + b) (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Fc q a b 0 e 0 0 d' = klCoef q a b 0 e 0 0 d' := by
  have hnz := qfac_ne_of_pow q (N := a + b + 1) (by omega) hq2
  rw [Fc_zero_third q hδ a b e d' he hd' hN hd (fun j h1 h2 => hq2 j h1 (by omega)),
    klCoef_zero_third q he (fun n hn => hnz n (by omega))
      (thetaKL_ne q (N := a + b + 1) (by omega) (by omega) (by omega) (by omega) hnz)]

/-- The Gram product of the lower cup entry: `U_L'(n+1,1,1;1,0) U_R(n+1,1,1;1,0) = p_{n+1}`. -/
theorem ULd_mul_UR_cup_low (q : kˣ) (n : ℕ) (hd : ∀ j, j ≤ n + 2 → chebD (loopVal q) j ≠ 0) :
    ULd q (n + 1) 1 1 1 0 * UR q (n + 1) 1 1 1 0 = (1 : k) • jwAt q 0 (n + 1 + 1 - 2 * 1 + 1 - 2 * 0) := by
  have j0 : ∀ s, (jwAt q s 0 : Module.End k (ModelSpace k)) = 1 := fun s => rfl
  have j1 : ∀ s, (jwAt q s 1 : Module.End k (ModelSpace k)) = 1 := fun s => rfl
  unfold ULd UR Wop Vop Qab
  simp only [show n + 1 + 1 - 2 * 1 = n by omega, show n + 1 - 1 = n by omega, Nat.mul_zero, Nat.sub_zero,
    Nat.add_zero, show 1 + 1 - 2 * 1 = 0 by omega, Nat.sub_self, nestCap, nestCup, j0, j1, mul_one, one_mul,
    sh_mul, sh_jwAt, sh_cupOp, sh_one, zero_add, one_smul, show n + 1 - 0 = n + 1 from rfl]
  have hp := jwProps_of_le (isTL_shift q 0) (n + 2) (fun j hj => hd j (by omega)) (n + 1) (by omega)
  have hn := jwProps_of_le (isTL_shift q 0) (n + 2) (fun j hj => hd j (by omega)) n (by omega)
  have a1 : (jwAt q 0 (n + 1) : Module.End k (ModelSpace k)) * jwAt q 0 n = jwAt q 0 (n + 1) := hp.absR n (by omega)
  have a2 : (jwAt q 0 (n + 1) : Module.End k (ModelSpace k)) * jwAt q 0 (n + 1) = jwAt q 0 (n + 1) :=
    hp.absR (n + 1) le_rfl
  have a3 : (jwAt q 0 n : Module.End k (ModelSpace k)) * jwAt q 0 n = jwAt q 0 n := hn.absR n le_rfl
  have hc := jwAt_comm_cup (k := k) q (n + 1)
  have hcc := cap_cup_succ (k := k) q n
  calc _ = jwAt q 0 (n + 1) * (jwAt q 0 n * jwAt q 0 n) * capOp q n * (jwAt q 0 (n + 1) * cupOp q (n + 1)) *
        (jwAt q 0 (n + 1) * jwAt q 0 (n + 1)) := by simp only [mul_assoc]
    _ = (jwAt q 0 (n + 1) * jwAt q 0 n) * (capOp q n * cupOp q (n + 1)) *
        (jwAt q 0 (n + 1) * (jwAt q 0 (n + 1) * jwAt q 0 (n + 1))) := by rw [a3, hc]; simp only [mul_assoc]
    _ = jwAt q 0 (n + 1) := by rw [a1, hcc, mul_one, a2, a2, a2]

/-- `κ(n+1, 1, 1) = d_{n+1} / d_n`. -/
lemma kapRec_succ_one_one (q : kˣ) (n : ℕ) (hd : chebD (loopVal q) n ≠ 0) :
    kapRec q (n + 1) 1 1 = chebD (loopVal q) (n + 1) / chebD (loopVal q) n := by
  simp only [kapRec, lamRec, sCoef, show ¬ (2 ≤ 1) by omega, if_false, mul_zero, sub_zero, add_zero, mul_one]
  rcases n with _ | m
  · simp [chebD]
  · rw [if_pos (by omega), show m + 1 + 1 - 2 = m by omega, show m + 1 + 1 - 1 = m + 1 by omega,
      chebD_succ_succ]
    field_simp

/-- **The lower entry of the cup column**: `Fc(n+1, 1, 1; 1, 0; 1, 0) = d_n / d_{n+1}`. -/
theorem Fc_cup_low (q : kˣ) (hδ : loopVal q ≠ 0) (n : ℕ) (hd : ∀ j, j ≤ n + 3 → chebD (loopVal q) j ≠ 0) :
    Fc q (n + 1) 1 1 1 0 1 0 = chebD (loopVal q) n / chebD (loopVal q) (n + 1) := by
  have h1 := gram_spec q hδ (n + 1) 1 1 1 0 1 0 (by omega) (fun j hj => hd j (by omega)) (by omega) le_rfl le_rfl
    le_rfl (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have h2 := ULd_mul_UR_cup_low q n (fun j hj => hd j (by omega))
  have h3 : (gramCoef q (n + 1) 1 1 1 0 1 0 - 1) •
      (jwAt q 0 (n + 1 + 1 - 2 * 1 + 1 - 2 * 0) : Module.End k (ModelSpace k)) = 0 :=
    (sub_smul (gramCoef q (n + 1) 1 1 1 0 1 0) (1 : k)
      (jwAt q 0 (n + 1 + 1 - 2 * 1 + 1 - 2 * 0) : Module.End k (ModelSpace k))).trans
      (sub_eq_zero.mpr (h1.symm.trans h2))
  have hg : gramCoef q (n + 1) 1 1 1 0 1 0 = 1 :=
    sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (jwAt_ne_zero q _))
  unfold Fc
  rw [if_pos ⟨by omega, Nat.zero_le _⟩, hg, kapRec_succ_one_one q n (hd n (by omega))]
  simp only [kapRec, inv_one, mul_one, inv_div]

/-- The Gram product of the upper cup entry: `U_L'(n,1,1;0,1) U_R(n,1,1;1,0) = (d_{n+1}/d_n) p_n`. -/
theorem ULd_mul_UR_cup_high (q : kˣ) (n : ℕ) (hd : ∀ j, j ≤ n + 2 → chebD (loopVal q) j ≠ 0) :
    ULd q n 1 1 0 1 * UR q n 1 1 1 0 =
      (chebD (loopVal q) (n + 1) / chebD (loopVal q) n) • jwAt q 0 (n + 1 - 2 * 0 + 1 - 2 * 1) := by
  have j0 : ∀ s, (jwAt q s 0 : Module.End k (ModelSpace k)) = 1 := fun s => rfl
  have j1 : ∀ s, (jwAt q s 1 : Module.End k (ModelSpace k)) = 1 := fun s => rfl
  unfold ULd UR Wop Vop Qab
  simp only [show n + 1 - 2 * 0 + 1 - 2 * 1 = n by omega, show n + 1 - 2 * 0 = n + 1 by omega,
    show n + 1 + 1 - 2 * 1 = n by omega, show n + 1 - 1 = n by omega, Nat.mul_zero, Nat.sub_zero,
    show 1 + 1 - 2 * 1 = 0 by omega, nestCap, nestCup, j0, j1, mul_one, one_mul,
    sh_mul, sh_jwAt, sh_cupOp, sh_one, zero_add, Nat.add_zero]
  have hp := jwProps_of_le (isTL_shift q 0) (n + 2) (fun j hj => hd j (by omega)) (n + 1) (by omega)
  have hn := jwProps_of_le (isTL_shift q 0) (n + 2) (fun j hj => hd j (by omega)) n (by omega)
  have a1 : (jwAt q 0 (n + 1) : Module.End k (ModelSpace k)) * jwAt q 0 n = jwAt q 0 (n + 1) := hp.absR n (by omega)
  have a2 : (jwAt q 0 (n + 1) : Module.End k (ModelSpace k)) * jwAt q 0 (n + 1) = jwAt q 0 (n + 1) :=
    hp.absR (n + 1) le_rfl
  have a3 : (jwAt q 0 n : Module.End k (ModelSpace k)) * jwAt q 0 n = jwAt q 0 n := hn.absR n le_rfl
  have hc := jwAt_comm_cup (k := k) q n
  have ht := cap_jwAt_cup (k := k) q hn (hd n (by omega))
  calc _ = jwAt q 0 n * (capOp q n * (jwAt q 0 (n + 1) * jwAt q 0 (n + 1)) * (jwAt q 0 n * cupOp q n)) *
        (jwAt q 0 n * jwAt q 0 n) := by rw [← a1]; simp only [mul_assoc]
    _ = jwAt q 0 n * (capOp q n * jwAt q 0 (n + 1) * cupOp q n) * (jwAt q 0 n * (jwAt q 0 n * jwAt q 0 n)) := by
        rw [a2, hc]; simp only [mul_assoc]
    _ = _ := by rw [ht, a3, a3, mul_smul_comm, smul_mul_assoc, a3, a3]

/-- **The upper entry of the cup column**: `Fc(n, 1, 1; 0, 1; 1, 0) = 1`. -/
theorem Fc_cup_high (q : kˣ) (hδ : loopVal q ≠ 0) (n : ℕ) (hd : ∀ j, j ≤ n + 2 → chebD (loopVal q) j ≠ 0) :
    Fc q n 1 1 0 1 1 0 = 1 := by
  have h1 := gram_spec q hδ n 1 1 0 1 1 0 (by omega) (fun j hj => hd j (by omega)) (Nat.zero_le _) (Nat.zero_le _)
    le_rfl le_rfl le_rfl (by omega) (Nat.zero_le _) (Nat.zero_le _)
  have h2 := ULd_mul_UR_cup_high q n hd
  have h3 : (gramCoef q n 1 1 0 1 1 0 - chebD (loopVal q) (n + 1) / chebD (loopVal q) n) •
      (jwAt q 0 (n + 1 - 2 * 0 + 1 - 2 * 1) : Module.End k (ModelSpace k)) = 0 :=
    (sub_smul (gramCoef q n 1 1 0 1 1 0) (chebD (loopVal q) (n + 1) / chebD (loopVal q) n)
      (jwAt q 0 (n + 1 - 2 * 0 + 1 - 2 * 1) : Module.End k (ModelSpace k))).trans
      (sub_eq_zero.mpr (h1.symm.trans h2))
  have hg := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (jwAt_ne_zero q _))
  unfold Fc
  rw [if_pos ⟨Nat.zero_le _, by omega⟩, hg]
  simp only [Nat.mul_zero, Nat.sub_zero]
  rw [kapRec_succ_one_one q n (hd n (by omega))]
  have h0 := hd n (by omega)
  have h1' := hd (n + 1) (by omega)
  simp only [kapRec, inv_one, one_mul]
  field_simp

/-- **The recursion of the one-strand block in the second block** (the pentagon with blocks `(a, b, 1, 1)`,
`j = 1`, `m = 0`, `i = e₀`; its right side has the empty block `(a, b, 0)`). -/
theorem Fc_b_rec [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b e₀ d₀ g₀ : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : ∀ x, x ≤ a + b + 1 + 1 → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + 3 → (q : k) ^ (2 * x) ≠ 1)
    (heb : e₀ ≤ b) (h₀ : ValidA a b 1 1 e₀ d₀ g₀) :
    ∑ f ∈ range (b + 1), ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
        Fc q b 1 1 f h 1 0 * (Fc q a (b + 1 - 2 * f) 1 d' g₀ h e₀ * Fc q a b 1 e₀ d₀ f d') =
      Fc q (a + b - 2 * e₀) 1 1 d₀ g₀ 1 0 := by
  have hP := pentagon q hδ a b 1 1 e₀ d₀ g₀ 1 0 e₀ ha hb le_rfl hd (fun x h1 h2 => hq2 x h1 (by omega)) le_rfl le_rfl
    (Nat.zero_le _) (Nat.zero_le _) (h₀.1.trans (min_le_left _ _)) (by have := h₀.1; omega) h₀
  rw [hP]
  simp only [show 1 + 1 - 2 * 1 = 0 by omega, Nat.zero_add, range_one, sum_singleton]
  rw [Fc_zero_third q hδ a b e₀ e₀ h₀.1 h₀.1 (by omega) (fun j hj => hd j (by omega))
    (fun j h1 h2 => hq2 j h1 (by omega)), if_pos rfl, one_mul]

/-- **The edge of the one-strand block**: with every strand of the second and third blocks cupped into the first,
the two tree vectors coincide, `U_R(a,b,1;0,b+1) = U_L(a,b,1;b,1)`. -/
theorem UR_edge_eq_UL (q : kˣ) (a b : ℕ) (hab : b + 1 ≤ a) (hd : ∀ j, j ≤ a + b + 1 → chebD (loopVal q) j ≠ 0) :
    UR q a b 1 0 (b + 1) = UL q a b 1 b 1 := by
  have j1 : ∀ s, (jwAt q s 1 : Module.End k (ModelSpace k)) = 1 := fun s => rfl
  unfold UR UL
  rw [sh_Vop_zero q a b 1 (fun j hj => hd j (by omega))]
  unfold Vop Qab
  simp only [Nat.mul_zero, Nat.sub_zero, j1, mul_one, show a + b - 2 * b = a - b by omega,
    show a + (b + 1) - 2 * (b + 1) = a - b - 1 by omega, show a - b + 1 - 2 * 1 = a - b - 1 by omega,
    show a - b - 1 = a - b - 1 from rfl, show a - (b + 1) = a - b - 1 by omega]
  set N := nestCup q (a - b - 1) (b + 1) with hNdef
  have hd' : ∀ j, j < a + b + 1 → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have slide1 : (jwAt q a (b + 1) : Module.End k (ModelSpace k)) * N = jwAt q (a - b - 1) (b + 1) * N := by
    have := jwAt_mul_nestCup_slide (k := k) q (l := a - b - 1) (i := b + 1) (m := b + 1) le_rfl
      (fun j hj => hd j (by omega))
    rwa [show a - b - 1 + (b + 1) = a by omega, show a - (b + 1) = a - b - 1 by omega] at this
  have slide2 : (jwAt q a b : Module.End k (ModelSpace k)) * N = jwAt q (a - b) b * N := by
    have := jwAt_mul_nestCup_slide (k := k) q (l := a - b - 1) (i := b + 1) (m := b) (by omega)
      (fun j hj => hd j (by omega))
    rwa [show a - b - 1 + (b + 1) = a by omega] at this
  have abs1 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q (a - b - 1) (b + 1) = jwAt q 0 a := by
    have := jwAt_absorb_suffix_all_right (k := k) q 0 (a - b - 1) (b + 1) (fun j hj => hd j (by omega))
    rwa [show b + 1 + (a - b - 1) = a by omega, Nat.zero_add] at this
  have abs2 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q (a - b) b = jwAt q 0 a := by
    have := jwAt_absorb_suffix_all_right (k := k) q 0 (a - b) b (fun j hj => hd j (by omega))
    rwa [show b + (a - b) = a by omega, Nat.zero_add] at this
  have hP := jwProps_of_le (isTL_shift (k := k) q 0) (a + b + 1) hd' a (by omega)
  have absP : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q 0 (a - b) = jwAt q 0 a := hP.absR (a - b) (by omega)
  have hX := jwProps_of_le (isTL_shift (k := k) q 0) (a + b + 1) hd' (a - b) (by omega)
  have idX : (jwAt q 0 (a - b) : Module.End k (ModelSpace k)) * jwAt q 0 (a - b) = jwAt q 0 (a - b) :=
    hX.absR (a - b) le_rfl
  have hW := jwProps_of_le (isTL_shift (k := k) q a) (a + b + 1) (fun j hj => hd j (by omega)) (b + 1) (by omega)
  have idW : (jwAt q a (b + 1) : Module.End k (ModelSpace k)) * jwAt q a (b + 1) = jwAt q a (b + 1) :=
    hW.absR (b + 1) le_rfl
  have cWP : (jwAt q a (b + 1) : Module.End k (ModelSpace k)) * jwAt q 0 a = jwAt q 0 a * jwAt q a (b + 1) :=
    (jwAt_comm_far q (by omega)).symm
  have cVX : (jwAt q a b : Module.End k (ModelSpace k)) * jwAt q 0 (a - b) = jwAt q 0 (a - b) * jwAt q a b :=
    (jwAt_comm_far q (by omega)).symm
  have hcomm := jwAt_mul_nestCup (k := k) q (a := a - b) (l := a - b) le_rfl b
  have hN : N = nestCup q (a - b) b * cupOp q (a - b - 1) := by
    rw [hNdef, nestCup_succ_left, show a - b - 1 + 1 = a - b by omega]
  have hL : jwAt q a (b + 1) * (jwAt q 0 a * jwAt q a (b + 1) * N * jwAt q 0 (a - b - 1)) =
      (jwAt q 0 a * N * jwAt q 0 (a - b - 1) : Module.End k (ModelSpace k)) := by
    calc _ = jwAt q a (b + 1) * jwAt q 0 a * jwAt q a (b + 1) * N * jwAt q 0 (a - b - 1) := by simp only [mul_assoc]
      _ = jwAt q 0 a * (jwAt q a (b + 1) * jwAt q a (b + 1)) * N * jwAt q 0 (a - b - 1) := by
          rw [cWP]; simp only [mul_assoc]
      _ = _ := by rw [idW, mul_assoc (jwAt q 0 a), slide1, ← mul_assoc, abs1]
  have hR : jwAt q 0 a * jwAt q a b * nestCup q (a - b) b * jwAt q 0 (a - b) *
      (jwAt q 0 (a - b) * nestCup q (a - b - 1) 1 * jwAt q 0 (a - b - 1)) =
      (jwAt q 0 a * N * jwAt q 0 (a - b - 1) : Module.End k (ModelSpace k)) := by
    simp only [nestCup, mul_one, Nat.add_zero]
    calc _ = jwAt q 0 a * jwAt q a b * (nestCup q (a - b) b * (jwAt q 0 (a - b) * jwAt q 0 (a - b))) *
          cupOp q (a - b - 1) * jwAt q 0 (a - b - 1) := by simp only [mul_assoc]
      _ = jwAt q 0 a * (jwAt q a b * jwAt q 0 (a - b)) * nestCup q (a - b) b *
          cupOp q (a - b - 1) * jwAt q 0 (a - b - 1) := by rw [idX, ← hcomm]; simp only [mul_assoc]
      _ = (jwAt q 0 a * jwAt q 0 (a - b)) * jwAt q a b * (nestCup q (a - b) b * cupOp q (a - b - 1)) *
          jwAt q 0 (a - b - 1) := by rw [cVX]; simp only [mul_assoc]
      _ = _ := by rw [absP, ← hN, mul_assoc (jwAt q 0 a), slide2, ← mul_assoc, abs2]
  rw [hL, hR]

/-- **The edge entry of the one-strand block** is `1`: `Fc(a, b, 1; b, 1; 0, b+1) = 1` for `b + 1 ≤ a`. -/
theorem Fc_edge [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b : ℕ) (hab : b + 1 ≤ a)
    (hd : ∀ j, j ≤ a + b + 1 → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 + 1 → (q : k) ^ (2 * j) ≠ 1) :
    Fc q a b 1 b 1 0 (b + 1) = 1 := by
  have h1 := gram_spec q hδ a b 1 b 1 0 (b + 1) (by omega) hd (by omega) le_rfl (Nat.zero_le _) (Nat.zero_le _)
    le_rfl (by omega) hab (by omega)
  have h2 := ULd_mul_UL q a b 1 hd (fun j h1 h2 => hq2 j h1 (by omega)) (e := b) (d := 1) (e' := b) (d' := 1)
    (by omega) le_rfl (by omega) le_rfl (by omega) le_rfl (by omega) le_rfl
  rw [if_pos ⟨rfl, rfl⟩] at h2
  rw [UR_edge_eq_UL q a b hab hd, h2] at h1
  set K := kapRec q a b b * kapRec q (a + b - 2 * b) 1 1
  have h3 : (gramCoef q a b 1 b 1 0 (b + 1) - K) •
      (jwAt q 0 (a + b - 2 * b + 1 - 2 * 1) : Module.End k (ModelSpace k)) = 0 :=
    (sub_smul (gramCoef q a b 1 b 1 0 (b + 1)) K
      (jwAt q 0 (a + b - 2 * b + 1 - 2 * 1) : Module.End k (ModelSpace k))).trans (sub_eq_zero.mpr h1.symm)
  have hg := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (jwAt_ne_zero q _))
  have k1 := kapRec_ne (k := k) q b a b (by omega) le_rfl (fun x h1 h2 => hq2 x h1 (by omega))
  have k2 := kapRec_ne (k := k) q 1 (a + b - 2 * b) 1 (by omega) le_rfl (fun x h1 h2 => hq2 x h1 (by omega))
  unfold Fc
  rw [if_pos ⟨by omega, by omega⟩, hg]
  simp only [K]
  field_simp

/-- The two columns of the one-strand block are orthogonal for the vertex-norm weights. -/
theorem Fc_one_orth [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) {a b E : ℕ} (hE : 1 ≤ E) (hEa : E ≤ a)
    (hEb : E ≤ b) (hd : ∀ j, j ≤ a + b + 2 → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 2 → (q : k) ^ (2 * j) ≠ 1) :
    kapRec q a b E * kapRec q (a + b - 2 * E) 1 0 * Fc q a b 1 E 0 0 E * Fc q a b 1 E 0 1 (E - 1) +
      kapRec q a b (E - 1) * kapRec q (a + b - 2 * (E - 1)) 1 1 *
        Fc q a b 1 (E - 1) 1 0 E * Fc q a b 1 (E - 1) 1 1 (E - 1) = 0 := by
  have hinv := Fc_mirror_inv (k := k) q hδ (a := a) (b := b) (c := 1) (f := 0) (d' := E) (g := 1) (h := E - 1)
    (by omega) (by omega) (fun j hj => hd j (by omega)) (fun j h1 h2 => hq2 j h1 (by omega))
    (Nat.zero_le _) (Nat.zero_le _) hEa (by omega) le_rfl (by omega) (by omega) (by omega)
  rw [if_neg (by omega)] at hinv
  have kr1 := kapRec_ne (k := k) q 1 1 b le_rfl (by omega) (fun x h1 h2 => hq2 x h1 (by omega))
  have kr2 := kapRec_ne (k := k) q (E - 1) (1 + b - 2 * 1) a (by omega) (by omega) (fun x h1 h2 => hq2 x h1 (by omega))
  set KR := kapRec q 1 b 1 * kapRec q (1 + b - 2 * 1) a (E - 1)
  have hKR : KR ≠ 0 := mul_ne_zero kr1 kr2
  -- each term, through the flip
  have hterm : ∀ e ∈ range (a + 1), ∀ d ∈ range (1 + 1),
      Fc q 1 b a 1 (E - 1) e d * Fc q a b 1 e d 0 E =
        KR⁻¹ * (kapRec q a b e * kapRec q (a + b - 2 * e) 1 d * Fc q a b 1 e d 1 (E - 1) * Fc q a b 1 e d 0 E) := by
    intro e _ d _
    by_cases h0 : Fc q a b 1 e d 0 E = 0
    · simp [h0]
    · obtain ⟨he, hdd⟩ := Fc_guard h0
      have hf := Fc_flip (k := k) q hδ (a := a) (b := b) (c := 1) (e := e) (d := d) (f := 1) (d' := E - 1)
        (by omega) (fun j hj => hd j (by omega)) (fun j h1 h2 => hq2 j h1 (by omega))
        (he.trans (min_le_left _ _)) (he.trans (min_le_right _ _)) (hdd.trans (min_le_right _ _))
        (hdd.trans (min_le_left _ _)) (by omega) le_rfl (by omega) (by omega)
      rw [hf]; simp only [KR]; field_simp
  rw [sum_congr rfl fun e he => sum_congr rfl fun d hdm => hterm e he d hdm] at hinv
  simp only [← mul_sum] at hinv
  have hsum := (mul_eq_zero.mp hinv).resolve_left (inv_ne_zero hKR)
  -- only (E, 0) and (E-1, 1) contribute
  have hin : ∀ g : ℕ → k, ∑ d ∈ range (1 + 1), g d = g 0 + g 1 := fun g => by simp [sum_range_succ]
  rw [sum_congr rfl fun e _ => hin _, sum_add_distrib] at hsum
  have z0 : ∀ e ∈ range (a + 1), e ≠ E →
      kapRec q a b e * kapRec q (a + b - 2 * e) 1 0 * Fc q a b 1 e 0 1 (E - 1) * Fc q a b 1 e 0 0 E = 0 := by
    intro e _ he
    by_cases h0 : Fc q a b 1 e 0 0 E = 0
    · simp [h0]
    · have := Fc_total q hδ a b 1 e 0 0 E (by omega) (fun j hj => hd j (by omega)) (Nat.zero_le _)
        (Nat.zero_le _) hEa (by omega) h0
      obtain ⟨he', -⟩ := Fc_guard h0
      exact absurd this (by have := he'.trans (min_le_left _ _); have := he'.trans (min_le_right _ _); omega)
  have z1 : ∀ e ∈ range (a + 1), e ≠ E - 1 →
      kapRec q a b e * kapRec q (a + b - 2 * e) 1 1 * Fc q a b 1 e 1 1 (E - 1) * Fc q a b 1 e 1 0 E = 0 := by
    intro e _ he
    by_cases h0 : Fc q a b 1 e 1 0 E = 0
    · simp [h0]
    · have := Fc_total q hδ a b 1 e 1 0 E (by omega) (fun j hj => hd j (by omega)) (Nat.zero_le _)
        (Nat.zero_le _) hEa (by omega) h0
      obtain ⟨he', hdd⟩ := Fc_guard h0
      exact absurd this (by have := hdd.trans (min_le_left _ _); have := he'.trans (min_le_left _ _); omega)
  rw [sum_eq_single E z0 (fun h => absurd (mem_range.mpr (by omega)) h),
    sum_eq_single (E - 1) z1 (fun h => absurd (mem_range.mpr (by omega)) h)] at hsum
  linear_combination hsum
/-- **The recursion in `b`, two terms**: the triple sum of `Fc_b_rec` has the two terms `f = 0, h = 1` and
`f = 1, h = 0`. -/
theorem Fc_b_rec_two [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b e₀ d₀ g₀ : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : ∀ x, x ≤ a + b + 1 + 1 → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + 3 → (q : k) ^ (2 * x) ≠ 1)
    (heb : e₀ ≤ b) (h₀ : ValidA a b 1 1 e₀ d₀ g₀) :
    Fc q b 1 1 0 1 1 0 * Fc q a (b + 1) 1 (e₀ + d₀) g₀ 1 e₀ * Fc q a b 1 e₀ d₀ 0 (e₀ + d₀) +
      Fc q b 1 1 1 0 1 0 * Fc q a (b - 1) 1 (e₀ + d₀ - 1) g₀ 0 e₀ * Fc q a b 1 e₀ d₀ 1 (e₀ + d₀ - 1) =
      Fc q (a + b - 2 * e₀) 1 1 d₀ g₀ 1 0 := by
  rw [← Fc_b_rec q hδ a b e₀ d₀ g₀ ha hb hd hq2 heb h₀]
  obtain ⟨he, hd₀, hg₀, hg1⟩ := h₀
  have hd1 : ∀ x, x ≤ a + b + 1 → chebD (loopVal q) x ≠ 0 := fun x hx => hd x (by omega)
  -- the inner sum over d': only d' = e₀ + d₀ - f survives
  have inner : ∀ f h, f ≤ 1 → (∀ d' ∈ range (a + 1), d' ≠ e₀ + d₀ - f →
      Fc q a (b + 1 - 2 * f) 1 d' g₀ h e₀ * Fc q a b 1 e₀ d₀ f d' = 0) := by
    intro f h hf d' _ hne
    by_cases h2 : Fc q a (b + 1 - 2 * f) 1 d' g₀ h e₀ = 0
    · simp [h2]
    · obtain ⟨hd'1, -⟩ := Fc_guard h2
      by_cases h3 : Fc q a b 1 e₀ d₀ f d' = 0
      · simp [h3]
      · have := Fc_total q hδ a b 1 e₀ d₀ f d' (by omega) hd1 (by omega) hf (hd'1.trans (min_le_left _ _))
          (by have := hd'1.trans (min_le_right _ _); omega) h3
        exact absurd this (by have := hd₀.trans (min_le_left _ _); have := he.trans (min_le_left _ _); omega)
  have hF1 : ∀ f h, ¬ (f + h = 1) → Fc q b 1 1 f h 1 0 = 0 := by
    intro f h hfh
    by_contra h1
    obtain ⟨hf, hh⟩ := Fc_guard h1
    have := Fc_total q hδ b 1 1 f h 1 0 (by omega) (fun x hx => hd x (by omega)) le_rfl le_rfl (Nat.zero_le _)
      (Nat.zero_le _) h1
    exact hfh (by have := hf.trans (min_le_right _ _); have := hh.trans (min_le_left _ _); omega)
  have row : ∀ f, f ≤ 1 → ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
      Fc q b 1 1 f h 1 0 * (Fc q a (b + 1 - 2 * f) 1 d' g₀ h e₀ * Fc q a b 1 e₀ d₀ f d') =
      Fc q b 1 1 f (1 - f) 1 0 * (Fc q a (b + 1 - 2 * f) 1 (e₀ + d₀ - f) g₀ (1 - f) e₀ *
        Fc q a b 1 e₀ d₀ f (e₀ + d₀ - f)) := by
    intro f hf
    rw [sum_eq_single (1 - f) (fun h _ hne => by simp [hF1 f h (by omega)])
      (fun hm => absurd (mem_range.mpr (by omega)) hm)]
    rw [← mul_sum, sum_eq_single (e₀ + d₀ - f) (inner f (1 - f) hf)
      (fun hm => by
        have hgt : a + f < e₀ + d₀ := by simpa using hm
        rw [show Fc q a (b + 1 - 2 * f) 1 (e₀ + d₀ - f) g₀ (1 - f) e₀ = 0 by
          unfold Fc; rw [if_neg fun h => by have := h.1.trans (min_le_left _ _); omega]]
        ring)]
  rw [sum_eq_add 0 1 (by omega) (fun f _ hf => by
      rw [sum_eq_zero fun h _ => sum_eq_zero fun d' _ => by rw [hF1 f h (by omega), zero_mul]])
    (fun hm => absurd (mem_range.mpr (by omega)) hm) (fun hm => absurd (mem_range.mpr (by omega)) hm),
    row 0 (by omega), row 1 le_rfl]
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.mul_one, show 1 - 0 = 1 from rfl, show 1 - 1 = 0 from rfl,
    show b + 1 - 2 = b - 1 by omega, Nat.sub_zero]
  ring
lemma qfac_succ' (q : kˣ) (n : ℕ) : qfac q (n + 1) = qfac q n * qb q (n + 1) := rfl

/-- The lower cup entry in quantum integers: `Fc(n+1,1,1;1,0;1,0) = -[n+1]/[n+2]`. -/
theorem Fc_cup_low_qb (q : kˣ) (hδ : loopVal q ≠ 0) (hD : (q : k) - (q : k)⁻¹ ≠ 0) (n : ℕ)
    (hd : ∀ j, j ≤ n + 3 → chebD (loopVal q) j ≠ 0) :
    Fc q (n + 1) 1 1 1 0 1 0 = -(qb q (n + 1) / qb q (n + 2)) := by
  rw [Fc_cup_low q hδ n hd, chebD_eq_qb q hD, chebD_eq_qb q hD]
  have h1 := hd (n + 1) (by omega)
  rw [chebD_eq_qb q hD] at h1
  have h2 : qb q (n + 1 + 1) ≠ 0 := fun h => h1 (by rw [h, mul_zero])
  rw [pow_succ]
  field_simp

/-- **The top entry of the one-strand block** in quantum integers. -/
theorem Fc_top_one_qb (q : kˣ) (hδ : loopVal q ≠ 0) {a b E : ℕ} (hEa : E ≤ a) (hEb : E ≤ b) (hN : 1 ≤ a + b)
    (hd : ∀ j, j ≤ a + b + 1 → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 2 → (q : k) ^ (2 * j) ≠ 1) :
    Fc q a b 1 E 0 0 E = qb q (a + b - E + 2) * qb q (b - E + 1) / (qb q (b + 1) * qb q (a + b - 2 * E + 2)) := by
  rw [Fc_top q hδ a b 1 E hEa hEb (by omega) hd, kapRec_eq q E a (b + 1) hEa (by omega)
    (fun j h1 h2 => hq2 j h1 (by omega)), kapRec_eq q E a b hEa hEb (fun j h1 h2 => hq2 j h1 (by omega))]
  have hnz := qfac_ne_of_pow q (N := a + b + 2) (by omega) hq2
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl (by omega)
    intro h; apply this
    have hq : (q : k) ≠ 0 := q.ne_zero
    field_simp at h
    linear_combination h
  obtain ⟨α, rfl⟩ : ∃ α, a = E + α := ⟨a - E, by omega⟩
  obtain ⟨β, rfl⟩ : ∃ β, b = E + β := ⟨b - E, by omega⟩
  have e1 : E + α + (E + β + 1) - E + 1 = E + α + β + 1 + 1 := by omega
  have e2 : E + α + (E + β) - E + 1 = E + α + β + 1 := by omega
  have e3 : E + β + 1 - E = β + 1 := by omega
  have e4 : E + β - E = β := by omega
  have e5 : E + α - E = α := by omega
  have e6 : E + α + (E + β + 1) - 2 * E + 1 = α + β + 1 + 1 := by omega
  have e7 : E + α + (E + β) - 2 * E + 1 = α + β + 1 := by omega
  have e8 : E + α + (E + β) - E + 2 = E + α + β + 1 + 1 := by omega
  have e9 : E + β - E + 1 = β + 1 := by omega
  have e10 : E + α + (E + β) - 2 * E + 2 = α + β + 1 + 1 := by omega
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  rw [qfac_succ' q (E + α + β + 1), qfac_succ' q β,
    qfac_succ' q (α + β + 1), qfac_succ' q (E + β)]
  have := hnz (E + α + β + 1) (by omega); have := hnz β (by omega); have := hnz (α + β + 1) (by omega)
  have := hnz (E + β) (by omega); have := hnz E (by omega); have := hnz α (by omega); have := hnz (E + α) (by omega)
  have hb1 : qb q (E + β + 1) ≠ 0 := qb_ne q hD _ (hq2 _ (by omega) (by omega))
  have hb2 : qb q (α + β + 1 + 1) ≠ 0 := qb_ne q hD _ (hq2 _ (by omega) (by omega))
  field_simp
/-- The lower-left entry of the one-strand block from the orthogonality of its columns. -/
theorem Fc_one_10_of_orth [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) {a b E : ℕ} (hE : 1 ≤ E) (hEa : E ≤ a)
    (hEb : E ≤ b) (hd : ∀ j, j ≤ a + b + 2 → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 2 → (q : k) ^ (2 * j) ≠ 1)
    (h11 : Fc q a b 1 (E - 1) 1 1 (E - 1) = 1)
    (h01 : Fc q a b 1 E 0 1 (E - 1) = -(qb q (a - E + 1) / qb q (a + b - 2 * E + 2))) :
    Fc q a b 1 (E - 1) 1 0 E = qb q E / qb q (b + 1) := by
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl (by omega)
    intro h; apply this
    have hq : (q : k) ≠ 0 := q.ne_zero
    field_simp at h
    linear_combination h
  have hO := Fc_one_orth q hδ hE hEa hEb hd hq2
  rw [h11, h01, Fc_top_one_qb q hδ hEa hEb (by omega) (fun j hj => hd j (by omega))
    (fun j h1 h2 => hq2 j h1 (by omega))] at hO
  have hk2 : kapRec q (a + b - 2 * (E - 1)) 1 1 = chebD (loopVal q) (a + b - 2 * E + 2) /
      chebD (loopVal q) (a + b - 2 * E + 1) := by
    rw [show a + b - 2 * (E - 1) = a + b - 2 * E + 1 + 1 by omega, kapRec_succ_one_one q _ (hd _ (by omega))]
  rw [hk2, kapRec_eq q E a b hEa hEb (fun j h1 h2 => hq2 j h1 (by omega)),
    kapRec_eq q (E - 1) a b (by omega) (by omega) (fun j h1 h2 => hq2 j h1 (by omega)),
    chebD_eq_qb q hD, chebD_eq_qb q hD] at hO
  simp only [kapRec, mul_one] at hO
  have hnz := qfac_ne_of_pow q (N := a + b + 2) (by omega) hq2
  set x := Fc q a b 1 (E - 1) 1 0 E
  obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
  obtain ⟨α, rfl⟩ : ∃ α, a = e + 1 + α := ⟨a - (e + 1), by omega⟩
  obtain ⟨β, rfl⟩ : ∃ β, b = e + 1 + β := ⟨b - (e + 1), by omega⟩
  have i1 : e + 1 - 1 = e := by omega
  have i2 : e + 1 + α + (e + 1 + β) - (e + 1) + 1 = e + α + β + 1 + 1 := by omega
  have i3 : e + 1 + α - (e + 1) = α := by omega
  have i4 : e + 1 + β - (e + 1) = β := by omega
  have i5 : e + 1 + α + (e + 1 + β) - 2 * (e + 1) + 1 = α + β + 1 := by omega
  have i6 : e + 1 + α + (e + 1 + β) - e + 1 = e + α + β + 1 + 1 + 1 := by omega
  have i7 : e + 1 + α - e = α + 1 := by omega
  have i8 : e + 1 + β - e = β + 1 := by omega
  have i9 : e + 1 + α + (e + 1 + β) - 2 * e + 1 = α + β + 1 + 1 + 1 := by omega
  have i10 : e + 1 + α + (e + 1 + β) - 2 * (e + 1) + 2 = α + β + 1 + 1 := by omega
  have i11 : e + 1 + α + (e + 1 + β) - 2 * (e + 1) + 1 + 1 = α + β + 1 + 1 := by omega
  have i12 : e + 1 + α + (e + 1 + β) - (e + 1) + 2 = e + α + β + 1 + 1 + 1 := by omega
  have i13 : e + 1 + β - (e + 1) + 1 = β + 1 := by omega
  have i14 : e + 1 + α - (e + 1) + 1 = α + 1 := by omega
  simp only [i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14] at hO ⊢
  rw [qfac_succ' q (e + α + β + 1 + 1), qfac_succ' q (e + α + β + 1), qfac_succ' q α, qfac_succ' q β,
    qfac_succ' q (α + β + 1 + 1), qfac_succ' q (α + β + 1), qfac_succ' q e] at hO
  have := hnz (e + α + β + 1) (by omega); have := hnz α (by omega); have := hnz β (by omega)
  have := hnz (α + β + 1) (by omega); have := hnz e (by omega); have := hnz (e + 1 + α) (by omega)
  have := hnz (e + 1 + β) (by omega)
  have q1 : ∀ n, 1 ≤ n → n ≤ e + 1 + α + (e + 1 + β) + 2 → qb q n ≠ 0 := fun n h1 h2 => qb_ne q hD n (hq2 n h1 h2)
  have := q1 (e + α + β + 1 + 1) (by omega) (by omega); have := q1 (e + α + β + 1 + 1 + 1) (by omega) (by omega)
  have := q1 (α + 1) (by omega) (by omega); have := q1 (β + 1) (by omega) (by omega)
  have := q1 (α + β + 1 + 1) (by omega) (by omega); have := q1 (α + β + 1 + 1 + 1) (by omega) (by omega)
  have := q1 (e + 1) (by omega) (by omega); have := q1 (e + 1 + β + 1) (by omega) (by omega)
  field_simp at hO
  rw [mul_zero] at hO
  have hb := (mul_eq_zero.mp hO).resolve_left (by simp [*])
  set sg : k := (-1 : k) ^ e * (-1) ^ (α + β + 1 + 1)
  have hs : sg * sg = 1 := by
    simp only [sg]; rw [mul_mul_mul_comm, ← pow_add, ← pow_add, ← two_mul, ← two_mul, pow_mul, pow_mul]; norm_num
  have hB := q1 (e + 1 + β + 1) (by omega) (by omega)
  rw [eq_div_iff hB]
  linear_combination sg * hb - (x * qb q (e + 1 + β + 1) - qb q (e + 1)) * hs
/-- `[α+β+E+2][β+1] + [E][α+1] = [E+β+1][α+β+2]`. -/
theorem qb_id_A (q : kˣ) (hD : (q : k) - (q : k)⁻¹ ≠ 0) (α β E : ℕ) :
    qb q (α + β + E + 2) * qb q (β + 1) + qb q E * qb q (α + 1) = qb q (E + β + 1) * qb q (α + β + 2) := by
  have hq : (q : k) ≠ 0 := q.ne_zero
  simp only [qb, pow_add, inv_pow]
  field_simp
  ring

/-- `q - q⁻¹ ≠ 0` from `q² ≠ 1`. -/
lemma hD_of_pow (q : kˣ) {N : ℕ} (hN : 1 ≤ N) (hq2 : ∀ j, 1 ≤ j → j ≤ N → (q : k) ^ (2 * j) ≠ 1) :
    (q : k) - (q : k)⁻¹ ≠ 0 := by
  have := hq2 1 le_rfl hN
  intro h; apply this
  have hq : (q : k) ≠ 0 := q.ne_zero
  field_simp at h
  linear_combination h

/-- Solving `x T + C = 1` against `T + C = 1`. -/
lemma solve_one {x T C : k} (hT : T ≠ 0) (h : 1 * x * T + C = 1) (hk : T + C = 1) : x = 1 := by
  have : (x - 1) * T = 0 := by linear_combination h - hk
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hT)

/-- The step for `F11` (the upper-right entry of the one-strand block is `1`), from the recursion in `b`. -/
theorem Fc_one_11_step [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) {a L E : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L)
    (hE : 1 ≤ E) (hEa : E ≤ a + 1) (hEb : E ≤ L + 1)
    (hd : ∀ j, j ≤ a + L + 3 → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + L + 4 → (q : k) ^ (2 * j) ≠ 1)
    (h10 : 2 ≤ E → Fc q a (L - 1) 1 (E - 1 - 1) 1 0 (E - 1) = qb q (E - 1) / qb q (L - 1 + 1))
    (h01 : 2 ≤ E → Fc q a L 1 (E - 1) 0 1 (E - 1 - 1) = -(qb q (a - (E - 1) + 1) / qb q (a + L - 2 * (E - 1) + 2))) :
    Fc q a (L + 1) 1 (E - 1) 1 1 (E - 1) = 1 := by
  have hD := hD_of_pow q (N := a + L + 4) (by omega) hq2
  have hrec := Fc_b_rec_two q hδ a L (E - 1) 0 1 ha hL (fun x hx => hd x (by omega))
    (fun x h1 h2 => hq2 x h1 (by omega)) (by omega) ⟨by omega, by simp, by omega, le_rfl⟩
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Fc_cup_high q hδ (L + 1) (fun j hj => hd j (by omega)), Fc_cup_low_qb q hδ hD L (fun j hj => hd j (by omega)),
    Fc_cup_high q hδ _ (fun j hj => hd j (by omega))] at hrec
  simp only [Nat.add_zero] at hrec
  rw [Fc_top_one_qb q hδ (by omega) (by omega) (by omega) (fun j hj => hd j (by omega))
      (fun j h1 h2 => hq2 j h1 (by omega))] at hrec
  show Fc q a (L + 2) 1 (E - 1) 1 1 (E - 1) = 1
  set x := Fc q a (L + 2) 1 (E - 1) 1 1 (E - 1)
  have hq1 : ∀ n, 1 ≤ n → n ≤ a + (L + 1) + 4 → qb q n ≠ 0 := fun n h1 h2 => qb_ne q hD n (hq2 n h1 h2)
  rcases Nat.lt_or_ge E 2 with hE2 | hE2
  · -- E = 1: the second term vanishes
    obtain rfl : E = 1 := by omega
    have hz : Fc q a (L + 1) 1 0 0 1 0 = 0 := by
      by_contra h0
      have := Fc_total q hδ a (L + 1) 1 0 0 1 0 (by omega) (fun j hj => hd j (by omega)) (by omega) le_rfl
        (Nat.zero_le _) (Nat.zero_le _) h0
      omega
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_add, hz, mul_zero, add_zero, one_mul] at hrec
    simp only [Nat.sub_zero] at hrec
    rw [mul_comm (qb q (L + 1 + 1)), div_self (mul_ne_zero (hq1 _ (by omega) (by omega)) (hq1 _ (by omega) (by omega))),
      mul_one] at hrec
    exact hrec
  · rw [h10 hE2, h01 hE2] at hrec
    refine solve_one ?_ hrec ?_
    · exact div_ne_zero (mul_ne_zero (hq1 _ (by omega) (by omega)) (hq1 _ (by omega) (by omega)))
        (mul_ne_zero (hq1 _ (by omega) (by omega)) (hq1 _ (by omega) (by omega)))
    · obtain ⟨e, rfl⟩ : ∃ e, E = e + 2 := ⟨E - 2, by omega⟩
      obtain ⟨α, rfl⟩ : ∃ α, a = e + 1 + α := ⟨a - (e + 1), by omega⟩
      obtain ⟨β, rfl⟩ : ∃ β, L = e + β := ⟨L - e, by omega⟩
      have hA := qb_id_A q hD α β (e + 1)
      have h1 := hq1 (e + β + 1) (by omega) (by omega)
      have h2 := hq1 (e + β + 1 + 1) (by omega) (by omega)
      have h3 := hq1 (α + β + 2) (by omega) (by omega)
      simp only [show e + 2 - 1 = e + 1 by omega, show e + 1 + α + (e + β + 1) - (e + 1) + 2 = α + β + (e + 1) + 2 by omega,
        show e + β + 1 - (e + 1) + 1 = β + 1 by omega, show e + β + 2 = e + β + 1 + 1 by omega,
        show e + 1 + α + (e + β + 1) - 2 * (e + 1) + 2 = α + β + 2 by omega,
        show e + 1 + α - (e + 1) + 1 = α + 1 by omega, show e + β + 1 - 1 + 1 = e + β + 1 by omega]
      rw [show α + β + (e + 1) + 2 = α + β + e + 1 + 2 by ring, show e + 1 + β + 1 = e + β + 1 + 1 by ring] at hA
      field_simp
      linear_combination hA
/-- Solving `x T + C = R` against a known solution. -/
lemma solve_eq {x y T C R : k} (hT : T ≠ 0) (h : 1 * x * T + C = R) (hk : y * T + C = R) : x = y := by
  have : (x - y) * T = 0 := by linear_combination h - hk
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hT)

/-- The step for the upper-right entry `F01` of the one-strand block, from the recursion in `b`. -/
theorem Fc_one_01_step [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) {a L E : ℕ} (ha : 1 ≤ a) (hL : 1 ≤ L)
    (hE : 1 ≤ E) (hEa : E ≤ a) (hEb : E ≤ L + 1)
    (hd : ∀ j, j ≤ a + L + 3 → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + L + 4 → (q : k) ^ (2 * j) ≠ 1)
    (h10 : Fc q a L 1 (E - 1) 1 0 E = qb q E / qb q (L + 1))
    (h11 : E ≤ L → Fc q a L 1 (E - 1) 1 1 (E - 1) = 1) :
    Fc q a (L + 1) 1 E 0 1 (E - 1) = -(qb q (a - E + 1) / qb q (a + (L + 1) - 2 * E + 2)) := by
  have hD := hD_of_pow q (N := a + L + 4) (by omega) hq2
  have hq1 : ∀ n, 1 ≤ n → n ≤ a + L + 4 → qb q n ≠ 0 := fun n h1 h2 => qb_ne q hD n (hq2 n h1 h2)
  have hrec := Fc_b_rec_two q hδ a L (E - 1) 1 0 ha hL (fun x hx => hd x (by omega))
    (fun x h1 h2 => hq2 x h1 (by omega)) (by omega) ⟨by omega, by omega, Nat.zero_le _, Nat.zero_le _⟩
  simp only [show E - 1 + 1 = E by omega] at hrec
  rw [h10] at hrec
  obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hX : a + (L + 1) - 2 * (E - 1) = a + L + 2 - 2 * E + 1 := by omega
  rw [hX, Fc_cup_high q hδ (L + 1) (fun j hj => hd j (by omega)), Fc_cup_low_qb q hδ hD L (fun j hj => hd j (by omega)),
    Fc_cup_low_qb q hδ hD _ (fun j hj => hd j (by omega))] at hrec
  refine solve_eq (div_ne_zero (hq1 _ (by omega) (by omega)) (hq1 _ (by omega) (by omega))) hrec ?_
  rcases Nat.lt_or_ge E (L + 2) with hEL | hEL
  · -- E ≤ L + 1 = the old L: the second term is the top entry of the level below
    rw [show L + 1 - 1 = L from rfl, Fc_top_one_qb q hδ (by omega) (by omega) (by omega) (fun j hj => hd j (by omega))
      (fun j h1 h2 => hq2 j h1 (by omega)), h11 (by omega)]
    obtain ⟨e, rfl⟩ : ∃ e, E = e + 1 := ⟨E - 1, by omega⟩
    obtain ⟨α, rfl⟩ : ∃ α, a = e + 1 + α := ⟨a - (e + 1), by omega⟩
    obtain ⟨β, rfl⟩ : ∃ β, L = e + β := ⟨L - e, by omega⟩
    have hA := qb_id_A q hD α β (e + 1)
    rw [show α + β + (e + 1) + 2 = e + α + β + 3 by ring, show e + 1 + β + 1 = e + β + 2 by ring] at hA
    simp only [show e + 1 + α - (e + 1) + 1 = α + 1 by omega,
      show e + 1 + α + (e + β + 1 + 1) - 2 * (e + 1) + 2 = α + β + 3 by omega,
      show e + 1 + α + (e + β) + 2 - 2 * (e + 1) + 1 = α + β + 2 by omega,
      show e + 1 + α + (e + β) + 2 - 2 * (e + 1) + 2 = α + β + 3 by omega,
      show e + β + 1 + 1 = e + β + 2 by omega, show e + 1 - 1 = e by omega,
      show e + 1 + α + (e + β) - e + 2 = e + α + β + 3 by omega, show e + β - e + 1 = β + 1 by omega,
      show e + 1 + α + (e + β) - 2 * e + 2 = α + β + 3 by omega, show e + β + 1 + 2 = e + β + 3 by omega]
    have := hq1 (e + β + 1) (by omega) (by omega); have := hq1 (e + β + 2) (by omega) (by omega)
    have := hq1 (α + β + 3) (by omega) (by omega)
    field_simp
    linear_combination (-1 : k) * hA
  · -- E = L + 2 = the old L + 1: the second term vanishes
    obtain rfl : E = L + 2 := by omega
    have hz : Fc q a (L + 1 - 1) 1 (L + 2 - 1) 0 0 (L + 2 - 1) = 0 := by
      unfold Fc; rw [if_neg fun h => by have := h.1.trans (min_le_right _ _); omega]
    rw [hz]
    obtain ⟨α, rfl⟩ : ∃ α, a = L + 2 + α := ⟨a - (L + 2), by omega⟩
    simp only [show L + 2 + α - (L + 2) + 1 = α + 1 by omega,
      show L + 2 + α + (L + 1 + 1) - 2 * (L + 2) + 2 = α + 2 by omega,
      show L + 2 + α + L + 2 - 2 * (L + 2) + 1 = α + 1 by omega,
      show L + 2 + α + L + 2 - 2 * (L + 2) + 2 = α + 2 by omega]
    have := hq1 (L + 2) (by omega) (by omega); have := hq1 (α + 2) (by omega) (by omega)
    field_simp
    ring
/-- **The one-strand block of `Fc` in closed form**: for the blocks `(a, b, 1)` and every total channel, the entries
are `F01 = -[a-E+1]/[a+b-2E+2]`, `F11 = 1`, `F10 = [E]/[b+1]` (and `F00` is `Fc_top_one_qb`). -/
theorem Fc_one_block [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) : ∀ b a, 1 ≤ a →
    (∀ j, j ≤ a + b + 3 → chebD (loopVal q) j ≠ 0) →
    (∀ j, 1 ≤ j → j ≤ a + b + 4 → (q : k) ^ (2 * j) ≠ 1) →
    (∀ E, 1 ≤ E → E ≤ a → E ≤ b → Fc q a b 1 E 0 1 (E - 1) = -(qb q (a - E + 1) / qb q (a + b - 2 * E + 2))) ∧
    (∀ E, 1 ≤ E → E ≤ a + 1 → E ≤ b → Fc q a b 1 (E - 1) 1 1 (E - 1) = 1) ∧
    (∀ E, 1 ≤ E → E ≤ a → E ≤ b + 1 → Fc q a b 1 (E - 1) 1 0 E = qb q E / qb q (b + 1)) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a ha hd hq2
  have hD := hD_of_pow q (N := a + b + 4) (by omega) hq2
  have hq1 : ∀ n, 1 ≤ n → n ≤ a + b + 4 → qb q n ≠ 0 := fun n h1 h2 => qb_ne q hD n (hq2 n h1 h2)
  match b, ih, hd, hq2, hD, hq1 with
  | 0, _, hd, hq2, hD, hq1 =>
    refine ⟨fun E h1 _ h3 => absurd h3 (by omega), fun E h1 _ h3 => absurd h3 (by omega), fun E h1 h2 h3 => ?_⟩
    obtain rfl : E = 1 := by omega
    rw [show 1 - 1 = 0 from rfl, Fc_edge q hδ a 0 (by omega) (fun j hj => hd j (by omega))
      (fun j h1 h2 => hq2 j h1 (by omega)), div_self (hq1 1 le_rfl (by omega))]
  | 1, _, hd, hq2, hD, hq1 =>
    have h01 : ∀ E, 1 ≤ E → E ≤ a → E ≤ 1 →
        Fc q a 1 1 E 0 1 (E - 1) = -(qb q (a - E + 1) / qb q (a + 1 - 2 * E + 2)) := by
      intro E h1 h2 h3
      obtain rfl : E = 1 := by omega
      obtain ⟨n, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by omega⟩
      rw [show 1 - 1 = 0 from rfl, Fc_cup_low_qb q hδ hD n (fun j hj => hd j (by omega)),
        show n + 1 - 1 + 1 = n + 1 by omega, show n + 1 + 1 - 2 * 1 + 2 = n + 2 by omega]
    have h11 : ∀ E, 1 ≤ E → E ≤ a + 1 → E ≤ 1 → Fc q a 1 1 (E - 1) 1 1 (E - 1) = 1 := by
      intro E h1 h2 h3
      obtain rfl : E = 1 := by omega
      exact Fc_cup_high q hδ a (fun j hj => hd j (by omega))
    refine ⟨h01, h11, fun E h1 h2 h3 => ?_⟩
    rcases Nat.lt_or_ge E 2 with hE | hE
    · obtain rfl : E = 1 := by omega
      exact Fc_one_10_of_orth q hδ le_rfl h2 le_rfl (fun j hj => hd j (by omega)) (fun j h1 h2 => hq2 j h1 (by omega))
        (h11 1 le_rfl (by omega) le_rfl) (h01 1 le_rfl h2 le_rfl)
    · obtain rfl : E = 2 := by omega
      rw [show 2 - 1 = 1 from rfl, Fc_edge q hδ a 1 (by omega) (fun j hj => hd j (by omega))
        (fun j h1 h2 => hq2 j h1 (by omega)), div_self (hq1 2 (by omega) (by omega))]
  | L + 2, ih, hd, hq2, hD, hq1 =>
    have ihL := ih (L + 1) (by omega) a ha (fun j hj => hd j (by omega)) (fun j h1 h2 => hq2 j h1 (by omega))
    have ihL1 := ih L (by omega) a ha (fun j hj => hd j (by omega)) (fun j h1 h2 => hq2 j h1 (by omega))
    have h11 : ∀ E, 1 ≤ E → E ≤ a + 1 → E ≤ L + 2 → Fc q a (L + 2) 1 (E - 1) 1 1 (E - 1) = 1 := by
      intro E h1 h2 h3
      exact Fc_one_11_step q hδ (L := L + 1) ha (by omega) h1 h2 h3 (fun j hj => hd j (by omega))
        (fun j h1 h2 => hq2 j h1 (by omega))
        (fun h => by rw [show L + 1 - 1 = L from rfl]
                     exact ihL1.2.2 (E - 1) (by omega) (by omega) (by omega))
        (fun h => ihL.1 (E - 1) (by omega) (by omega) (by omega))
    have h01 : ∀ E, 1 ≤ E → E ≤ a → E ≤ L + 2 →
        Fc q a (L + 2) 1 E 0 1 (E - 1) = -(qb q (a - E + 1) / qb q (a + (L + 2) - 2 * E + 2)) := by
      intro E h1 h2 h3
      exact Fc_one_01_step q hδ (L := L + 1) ha (by omega) h1 h2 h3 (fun j hj => hd j (by omega))
        (fun j h1 h2 => hq2 j h1 (by omega)) (ihL.2.2 E h1 h2 (by omega))
        (fun h => ihL.2.1 E h1 (by omega) h)
    refine ⟨h01, h11, fun E h1 h2 h3 => ?_⟩
    rcases Nat.lt_or_ge E (L + 3) with hE | hE
    · exact Fc_one_10_of_orth q hδ h1 h2 (by omega) (fun j hj => hd j (by omega)) (fun j h1 h2 => hq2 j h1 (by omega))
        (h11 E h1 (by omega) (by omega)) (h01 E h1 h2 (by omega))
    · obtain rfl : E = L + 3 := by omega
      rw [show L + 3 - 1 = L + 2 from rfl, Fc_edge q hδ a (L + 2) (by omega) (fun j hj => hd j (by omega))
        (fun j h1 h2 => hq2 j h1 (by omega)), div_self (hq1 (L + 3) (by omega) (by omega))]
end Lightlike.TemperleyLieb
