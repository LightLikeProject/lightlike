import Mathlib
import Lightlike.TemperleyLieb.KLCoef
import Lightlike.TemperleyLieb.TopEntry
import Lightlike.TemperleyLieb.VertexNorm
import Lightlike.TemperleyLieb.Slide

/-!
# Base values of the Kauffman–Lins coefficient

With an empty third block the tetrahedral net is a theta net, `tetKL q a b 0 i i b = θ(a, b, i)`
(`tetKL_zero_third`: its sum has the single term `z = (a+b+i)/2`), and `θ(i, 0, i) = Δ_i`
(`thetaKL_zero_mid`), so the Kauffman–Lins coefficient is the identity matrix (`klCoef_zero_third`), as `Fc` is
(`Fc_zero_third`). This is the base `c = 0` of the identification `Fc = klCoef`.
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

lemma thetaKL_ne (q : kˣ) {a b c : ℕ} (hnz : ∀ n, n ≤ a + b + c + 1 → qfac q n ≠ 0) :
    thetaKL q a b c ≠ 0 := by
  unfold thetaKL
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (hnz _ (by omega))) (hnz _ (by omega))) (hnz _ (by omega))) (hnz _ (by omega)))
    (mul_ne_zero (mul_ne_zero (hnz _ (by omega)) (hnz _ (by omega))) (hnz _ (by omega)))

/-- **`Fc = klCoef` with an empty third block** (the base `c = 0` of the identification). -/
theorem Fc_eq_klCoef_zero_third (q : kˣ) (hδ : loopVal q ≠ 0) {a b e d' : ℕ} (he : e ≤ min a b)
    (hd' : d' ≤ min a b) (hN : 1 ≤ a + b) (hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ 2 * (a + b) + 2 → (q : k) ^ (2 * j) ≠ 1) :
    Fc q a b 0 e 0 0 d' = klCoef q a b 0 e 0 0 d' := by
  have hnz := qfac_ne_of_pow q (N := 2 * (a + b) + 2) (by omega) hq2
  rw [Fc_zero_third q hδ a b e d' he hd' hN hd (fun j h1 h2 => hq2 j h1 (by omega)),
    klCoef_zero_third q he (fun n hn => hnz n (by omega)) (thetaKL_ne q fun n hn => hnz n (by omega))]

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
    (hq2 : ∀ x, 1 ≤ x → x ≤ 2 * (a + b) + 4 → (q : k) ^ (2 * x) ≠ 1)
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

end Lightlike.TemperleyLieb
