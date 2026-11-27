import Mathlib
import Lightlike.TemperleyLieb.KLThirdAssembly
import Lightlike.TemperleyLieb.ThirdBlock
import Lightlike.TemperleyLieb.OneStrand

/-!
# The recoupling coefficient of the Temperley–Lieb model is the Kauffman–Lins coefficient

`Fc_eq_klCoef` proves the statement `FcEqKL k` over every field of characteristic zero: at every `q` with
`q^{2n} ≠ 1` for `1 ≤ n ≤ 2(a+b+c)+6`, the normalised recoupling coefficient `Fc` equals the Kauffman–Lins
coefficient `klCoef` on every admissible index. The proof is an induction on the third block `c`:

* an empty first or second block: the two trees are the same operator (`UR_eq_UL_first_zero`,
  `UR_eq_UL_second_zero`), so `Fc = 1` (`Fc_eq_one_of_UR_eq_UL`), and the Kauffman–Lins coefficient is `1`
  (`klCoef_first_zero`, `klCoef_second_zero`);
* an empty third block: `Fc_eq_klCoef_zero_third`;
* one strand: the closed forms of `Fc_one_block` and `Fc_top_one_qb` against those of `klCoef`
  (`Fc_eq_klCoef_one_pos`);
* the step `c → c + 1`: the recursion `Fc_third_rec` of `Fc` and `klCoef_third_rec` of `klCoef` agree term by
  term (`third_rec_term`, off the admissible range both sides vanish, `Fc_eq_klCoef_of_adm`), and the pivot
  `klCoef(a+b-2e, c, 1; d₀, g₀; 0, d₀+g₀)` does not vanish (`Fc_eq_klCoef_step`).
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- A vertex with an empty channel index is the projector: `V(a, b; 0) = p_{a+b}`. -/
lemma Vop_zero_eq (q : kˣ) (a b : ℕ) (hd : ∀ j, j < a + b → chebD (loopVal q) j ≠ 0) :
    (Vop q a b 0 : Module.End k (ModelSpace k)) = jwAt q 0 (a + b) := by
  unfold Vop
  simp only [nestCup, mul_one, Nat.mul_zero, Nat.sub_zero]
  exact Qab_mul_full_eq q a b hd

/-- The projector on the first `a` strands is idempotent (from `a ≤ N`). -/
lemma jwAt_zero_idem (q : kˣ) {a : ℕ} (hd : ∀ j, j < a → chebD (loopVal q) j ≠ 0) :
    (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q 0 a = jwAt q 0 a :=
  (jwProps_of_le (isTL_shift (k := k) q 0) a hd a le_rfl).absR a le_rfl

/-- With an empty second block the two trees agree: `U_R(a, 0, c; 0, d) = U_L(a, 0, c; 0, d)`. -/
theorem UR_eq_UL_second_zero (q : kˣ) (a c d : ℕ) (hd : ∀ j, j ≤ a + c → chebD (loopVal q) j ≠ 0) :
    UR q a 0 c 0 d = UL q a 0 c 0 d := by
  unfold UR UL
  rw [sh_Vop_zero q a 0 c (fun j hj => hd j (by omega)), Vop_zero_eq q a 0 (fun j hj => hd j (by omega))]
  simp only [zero_add, add_zero, Nat.mul_zero, Nat.sub_zero]
  unfold Vop Qab
  have i0 := jwAt_zero_idem (k := k) q (a := a) (fun j hj => hd j (by omega))
  have ia : (jwAt q a c : Module.End k (ModelSpace k)) * jwAt q a c = jwAt q a c :=
    (jwProps_of_le (isTL_shift (k := k) q a) c (fun j hj => hd j (by omega)) c le_rfl).absR c le_rfl
  have cm : (jwAt q a c : Module.End k (ModelSpace k)) * jwAt q 0 a = jwAt q 0 a * jwAt q a c :=
    (jwAt_comm_far q (by omega)).symm
  calc _ = (jwAt q a c * jwAt q 0 a) * jwAt q a c * nestCup q (a - d) d * jwAt q 0 (a + c - 2 * d) := by
        simp only [mul_assoc]
    _ = jwAt q 0 a * (jwAt q a c * jwAt q a c) * nestCup q (a - d) d * jwAt q 0 (a + c - 2 * d) := by
        rw [cm]; simp only [mul_assoc]
    _ = (jwAt q 0 a * jwAt q 0 a) * jwAt q a c * nestCup q (a - d) d * jwAt q 0 (a + c - 2 * d) := by
        rw [ia, i0]
    _ = _ := by simp only [mul_assoc]

/-- With an empty first block the two trees agree: `U_R(0, b, c; f, 0) = U_L(0, b, c; 0, f)`. -/
theorem UR_eq_UL_first_zero (q : kˣ) (b c f : ℕ) (hd : ∀ j, j ≤ b + c → chebD (loopVal q) j ≠ 0) :
    UR q 0 b c f 0 = UL q 0 b c 0 f := by
  unfold UR UL
  rw [sh_Vop q 0 b c f, Vop_zero_eq q 0 (b + c - 2 * f) (fun j hj => hd j (by omega)),
    Vop_zero_eq q 0 b (fun j hj => hd j (by omega))]
  simp only [zero_add, add_zero, Nat.mul_zero, Nat.sub_zero]
  unfold Vop Qab
  have i0 := jwAt_zero_idem (k := k) q (a := b) (fun j hj => hd j (by omega))
  have iD := jwAt_zero_idem (k := k) q (a := b + c - 2 * f) (fun j hj => hd j (by omega))
  calc _ = jwAt q 0 b * jwAt q b c * nestCup q (b - f) f * (jwAt q 0 (b + c - 2 * f) * jwAt q 0 (b + c - 2 * f)) := by
        simp only [mul_assoc]
    _ = (jwAt q 0 b * jwAt q 0 b) * jwAt q b c * nestCup q (b - f) f * jwAt q 0 (b + c - 2 * f) := by
        rw [iD, i0]
    _ = _ := by simp only [mul_assoc]

/-- **`Fc = 1` when the right tree is the left tree.** -/
theorem Fc_eq_one_of_UR_eq_UL [CharZero k] (q : kˣ) {a b c e d f d' : ℕ}
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    (hea : e ≤ a) (heb : e ≤ b) (hdA : d ≤ a + b - 2 * e) (hdc : d ≤ c)
    (h : UR q a b c f d' = UL q a b c e d) : Fc q a b c e d f d' = 1 := by
  have h2 := ULd_mul_UL q a b c hd hq2 hea heb hea heb hdA hdc hdA hdc
  rw [if_pos ⟨rfl, rfl⟩] at h2
  set K := kapRec q a b e * kapRec q (a + b - 2 * e) c d
  have hex : ∃ g : k, ULd q a b c e d * UR q a b c f d' = g • jwAt q 0 (a + b - 2 * e + c - 2 * d) :=
    ⟨K, by rw [h]; exact h2⟩
  have hg : gramCoef q a b c e d f d' = K := by
    unfold gramCoef
    rw [dif_pos hex]
    have hs : K • (jwAt q 0 (a + b - 2 * e + c - 2 * d) : Module.End k (ModelSpace k)) =
        hex.choose • jwAt q 0 (a + b - 2 * e + c - 2 * d) := by
      rw [← h2, ← h]; exact hex.choose_spec
    have h3 : (hex.choose - K) • (jwAt q 0 (a + b - 2 * e + c - 2 * d) : Module.End k (ModelSpace k)) = 0 := by
      exact (sub_smul hex.choose K (jwAt q 0 (a + b - 2 * e + c - 2 * d) : Module.End k (ModelSpace k))).trans
        (sub_eq_zero.mpr hs.symm)
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (jwAt_ne_zero q _))
  have k1 := kapRec_ne (k := k) q e a b hea heb (fun x h1 h2 => hq2 x h1 (by omega))
  have k2 := kapRec_ne (k := k) q d (a + b - 2 * e) c hdA hdc (fun x h1 h2 => hq2 x h1 (by omega))
  unfold Fc
  rw [if_pos ⟨le_min hea heb, le_min hdA hdc⟩, hg]
  simp only [K]
  field_simp

/-- **The Kauffman–Lins coefficient with an empty second block** is `1`. -/
theorem klCoef_second_zero (q : kˣ) {a c d : ℕ} (hda : d ≤ a) (hdc : d ≤ c)
    (hnz : ∀ n, n ≤ a + c + 1 → qfac q n ≠ 0) : klCoef q a 0 c 0 d 0 d = 1 := by
  have hadm : KLAdm a 0 c 0 d 0 d := by simp only [KLAdm, le_min_iff]; omega
  unfold klCoef
  rw [if_pos hadm]
  simp only [Nat.mul_zero, Nat.sub_zero, Nat.add_zero, zero_add]
  rw [show thetaKL q a 0 a = deltaKL q a from thetaKL_zero_mid q a (hnz a (by omega))]
  have ht : tetKL q a 0 c (a + c - 2 * d) a c = thetaKL q a c (a + c - 2 * d) := by
    unfold tetKL tetPre tetTerm thetaKL
    simp only [show (a + 0 + a) / 2 = a by omega, show (a + c + (a + c - 2 * d)) / 2 = a + c - d by omega,
      show (0 + c + c) / 2 = c by omega, show (0 + (a + c - 2 * d) + a + c) / 2 = a + c - d by omega,
      show (a + c + a + c) / 2 = a + c by omega, show (a + 0 + c + (a + c - 2 * d)) / 2 = a + c - d by omega,
      show max (max a (a + c - d)) (max c (a + c - d)) = a + c - d by omega,
      show min (a + c - d) (min (a + c) (a + c - d)) = a + c - d by omega, Icc_self, sum_singleton, Nat.sub_self]
    rw [show a + c - d - a = c - d by omega, show a + c - d - c = a - d by omega,
      show a + c - a = c by omega, show a + c - (a + c - d) = d by omega, show a + c - c = a by omega,
      show a + c - d - (a + c - 2 * d) = d by omega]
    have := hnz a (by omega); have := hnz c (by omega); have := hnz d (by omega)
    have := hnz (a - d) (by omega); have := hnz (c - d) (by omega); have := hnz (a + c - 2 * d) (by omega)
    simp only [qfac]
    field_simp
  rw [ht]
  have hθ := thetaKL_ne q (a := a) (b := c) (c := a + c - 2 * d) (N := a + c + 1) (by omega) (by omega) (by omega)
    (by omega) hnz
  have hΔ : deltaKL q a ≠ 0 := by
    unfold deltaKL
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    intro hq; apply hnz (a + 1) (by omega); simp only [qfac, hq, mul_zero]
  field_simp

/-- **The Kauffman–Lins coefficient with an empty first block** is `1`. -/
theorem klCoef_first_zero (q : kˣ) {b c f : ℕ} (hfb : f ≤ b) (hfc : f ≤ c)
    (hnz : ∀ n, n ≤ b + c + 1 → qfac q n ≠ 0) : klCoef q 0 b c 0 f f 0 = 1 := by
  have hadm : KLAdm 0 b c 0 f f 0 := by simp only [KLAdm, le_min_iff]; omega
  unfold klCoef
  rw [if_pos hadm]
  simp only [Nat.mul_zero, Nat.sub_zero, zero_add]
  rw [show thetaKL q 0 b b = deltaKL q b by
    rw [← thetaKL_zero_mid q b (hnz b (by omega))]; unfold thetaKL
    rw [show (0 + b + b) / 2 = (b + 0 + b) / 2 by omega]
    ring]
  have ht : tetKL q 0 b c (b + c - 2 * f) b (b + c - 2 * f) = thetaKL q b c (b + c - 2 * f) := by
    unfold tetKL tetPre tetTerm thetaKL
    simp only [show (0 + b + b) / 2 = b by omega, show (b + c + (b + c - 2 * f)) / 2 = b + c - f by omega,
      show (0 + (b + c - 2 * f) + (b + c - 2 * f)) / 2 = b + c - 2 * f by omega,
      show (b + (b + c - 2 * f) + b + (b + c - 2 * f)) / 2 = b + (b + c - 2 * f) by omega,
      show (0 + c + b + (b + c - 2 * f)) / 2 = b + c - f by omega,
      show (0 + b + c + (b + c - 2 * f)) / 2 = b + c - f by omega,
      show max (max b (b + c - f)) (max (b + c - f) (b + c - 2 * f)) = b + c - f by omega,
      show min (b + (b + c - 2 * f)) (min (b + c - f) (b + c - f)) = b + c - f by omega, Icc_self, sum_singleton,
      Nat.sub_self]
    rw [show b + (b + c - 2 * f) - b = b + c - 2 * f by omega, show b + (b + c - 2 * f) - (b + c - f) = b - f by omega,
      show b + (b + c - 2 * f) - (b + c - 2 * f) = b by omega, show b + c - f - b = c - f by omega,
      show b + c - f - (b + c - 2 * f) = f by omega, show b + c - f - c = b - f by omega]
    have := hnz b (by omega); have := hnz c (by omega); have := hnz f (by omega)
    have := hnz (b - f) (by omega); have := hnz (c - f) (by omega); have := hnz (b + c - 2 * f) (by omega)
    simp only [qfac]
    field_simp
  rw [ht]
  have hθ := thetaKL_ne q (a := b) (b := c) (c := b + c - 2 * f) (N := b + c + 1) (by omega) (by omega) (by omega)
    (by omega) hnz
  have hΔ : deltaKL q b ≠ 0 := by
    unfold deltaKL
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    intro hq; apply hnz (b + 1) (by omega); simp only [qfac, hq, mul_zero]
  field_simp

/-- The loop values `d_j = (-1)^j [j+1]` do not vanish for `j + 1 ≤ M` when `q^{2n} ≠ 1` for `1 ≤ n ≤ M`. -/
lemma chebD_ne_of_pow (q : kˣ) {M : ℕ} (hq : ∀ n, 1 ≤ n → n ≤ M → (q : k) ^ (2 * n) ≠ 1) :
    ∀ j, j + 1 ≤ M → chebD (loopVal q) j ≠ 0 := by
  intro j hj
  have hD := hD_of_pow q (N := M) (by omega) hq
  rw [chebD_eq_qb q hD]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (qb_ne q hD _ (hq _ (by omega) hj))

/-- The loop value `δ = -[2]` does not vanish when `q^{2n} ≠ 1` for `1 ≤ n ≤ M`, `2 ≤ M`. -/
lemma loopVal_ne_of_pow (q : kˣ) {M : ℕ} (hM : 2 ≤ M) (hq : ∀ n, 1 ≤ n → n ≤ M → (q : k) ^ (2 * n) ≠ 1) :
    loopVal q ≠ 0 := by
  have := chebD_ne_of_pow q hq 1 (by omega)
  simpa only [chebD] using this

/-- **`Fc = klCoef` on every index with the right-tree indices in range**, given it on the admissible ones: off the
admissible totals both sides vanish. -/
lemma Fc_eq_klCoef_of_adm (q : kˣ) (hδ : loopVal q ≠ 0) {a b c e d f d' : ℕ} (hN : 1 ≤ a + b + c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f)
    (hP : KLAdm a b c e d f d' → Fc q a b c e d f d' = klCoef q a b c e d f d') :
    Fc q a b c e d f d' = klCoef q a b c e d f d' := by
  by_cases hA : KLAdm a b c e d f d'
  · exact hP hA
  · rw [klCoef_eq_zero_of_not hA]
    by_contra hne
    obtain ⟨he, hdd⟩ := Fc_guard hne
    have ht := Fc_total q hδ a b c e d f d' hN hd hfb hfc hda hdf hne
    exact hA ⟨he, hdd, le_min hfb hfc, le_min hda hdf, ht⟩

/-- **`Fc = klCoef` with an empty first block.** -/
theorem Fc_eq_klCoef_first_zero [CharZero k] (q : kˣ) {b c e d f d' : ℕ} (hA : KLAdm 0 b c e d f d')
    (hq : ∀ n, 1 ≤ n → n ≤ b + c + 2 → (q : k) ^ (2 * n) ≠ 1) :
    Fc q 0 b c e d f d' = klCoef q 0 b c e d f d' := by
  have hA' := hA
  simp only [KLAdm, le_min_iff] at hA'
  obtain ⟨⟨he, -⟩, ⟨-, hdc⟩, ⟨hfb, hfc⟩, ⟨hd0, -⟩, ht⟩ := hA'
  obtain rfl : e = 0 := by omega
  obtain rfl : d' = 0 := by omega
  obtain rfl : d = f := by omega
  have hd := chebD_ne_of_pow q hq
  rw [klCoef_first_zero q hfb hfc (qfac_ne_of_pow q (by omega) fun n h1 h2 => hq n h1 (by omega))]
  exact Fc_eq_one_of_UR_eq_UL q (fun j hj => hd j (by omega)) (fun j h1 h2 => hq j h1 (by omega)) le_rfl
    (Nat.zero_le _) (by omega) hdc (UR_eq_UL_first_zero q b c d (fun j hj => hd j (by omega)))

/-- **`Fc = klCoef` with an empty second block.** -/
theorem Fc_eq_klCoef_second_zero [CharZero k] (q : kˣ) {a c e d f d' : ℕ} (hA : KLAdm a 0 c e d f d')
    (hq : ∀ n, 1 ≤ n → n ≤ a + c + 2 → (q : k) ^ (2 * n) ≠ 1) :
    Fc q a 0 c e d f d' = klCoef q a 0 c e d f d' := by
  have hA' := hA
  simp only [KLAdm, le_min_iff] at hA'
  obtain ⟨⟨-, he⟩, ⟨hda, hdc⟩, ⟨hf, -⟩, ⟨hd'a, hd'c⟩, ht⟩ := hA'
  obtain rfl : e = 0 := by omega
  obtain rfl : f = 0 := by omega
  obtain rfl : d' = d := by omega
  have hd := chebD_ne_of_pow q hq
  rw [klCoef_second_zero q (by omega) hdc (qfac_ne_of_pow q (by omega) fun n h1 h2 => hq n h1 (by omega))]
  exact Fc_eq_one_of_UR_eq_UL q (fun j hj => hd j (by omega)) (fun j h1 h2 => hq j h1 (by omega)) (Nat.zero_le _)
    le_rfl (by omega) hdc (UR_eq_UL_second_zero q a c d' (fun j hj => hd j (by omega)))

/-- **`Fc = klCoef` on the one-strand third block**, for nonempty first and second blocks. -/
theorem Fc_eq_klCoef_one_pos [CharZero k] (q : kˣ) {a b e d f d' : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : KLAdm a b 1 e d f d') (hq : ∀ n, 1 ≤ n → n ≤ a + b + 4 → (q : k) ^ (2 * n) ≠ 1) :
    Fc q a b 1 e d f d' = klCoef q a b 1 e d f d' := by
  have hδ := loopVal_ne_of_pow q (by omega) hq
  have hd := chebD_ne_of_pow q hq
  have hnz := qfac_ne_of_pow q (N := a + b + 4) (by omega) hq
  have hB := Fc_one_block (k := k) q hδ b a ha (fun j hj => hd j (by omega)) hq
  have hA' := hA
  simp only [KLAdm, le_min_iff] at hA'
  obtain ⟨⟨hea, heb⟩, ⟨hdA, hd1⟩, ⟨hfb, hf1⟩, ⟨hda, hdf⟩, ht⟩ := hA'
  rcases Nat.eq_zero_or_pos d with rfl | hdp <;> rcases Nat.eq_zero_or_pos f with rfl | hfp
  · obtain rfl : d' = e := by omega
    rw [Fc_top_one_qb q hδ hea heb (by omega) (fun j hj => hd j (by omega)) (fun j h1 h2 => hq j h1 (by omega)),
      klCoef_one_00' q hA (fun n hn => hnz n (by omega))]
  · obtain rfl : f = 1 := by omega
    obtain rfl : e = d' + 1 := by omega
    have hB1 := hB.1 (d' + 1) (by omega) hea heb
    rw [show d' + 1 - 1 = d' by omega] at hB1
    rw [hB1, klCoef_one_01' q hA (fun n hn => hnz n (by omega)), show a - (d' + 1) + 1 = a - d' by omega,
      show a + b - 2 * (d' + 1) + 2 = a + b - 2 * d' by omega]
  · obtain rfl : d = 1 := by omega
    obtain rfl : d' = e + 1 := by omega
    have hB3 := hB.2.2 (e + 1) (by omega) hda (by omega)
    rw [show e + 1 - 1 = e by omega] at hB3
    rw [hB3, klCoef_one_10' q hA (fun n hn => hnz n (by omega))]
  · obtain rfl : d = 1 := by omega
    obtain rfl : f = 1 := by omega
    obtain rfl : d' = e := by omega
    have hB2 := hB.2.1 (d' + 1) (by omega) (by omega) (by omega)
    rw [show d' + 1 - 1 = d' by omega] at hB2
    rw [hB2, klCoef_one_11' q hA (fun n hn => hnz n (by omega))]

/-- The statement `Fc = klCoef` for a third block of `c` strands, at a fixed `q`. -/
def FcEqKLAt (q : kˣ) (c : ℕ) : Prop :=
  ∀ a b e d f d', (∀ n, 1 ≤ n → n ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * n) ≠ 1) →
    KLAdm a b c e d f d' → Fc q a b c e d f d' = klCoef q a b c e d f d'

/-- **One term of the third-block recursion**: `Fc` and `klCoef` give the same product. -/
lemma third_rec_term [CharZero k] (q : kˣ) {a b c e₀ d₀ g₀ m i f h d' : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c)
    (h1 : FcEqKLAt q 1) (hcI : FcEqKLAt q c)
    (hq : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + (c + 1)) + 6 → (q : k) ^ (2 * n) ≠ 1)
    (hmb : m ≤ b) (hmz : m ≤ c + 1) (hia : i ≤ a) (hiz : i ≤ b + (c + 1) - 2 * m) :
    Fc q b c 1 f h 0 m * (Fc q a (b + c - 2 * f) 1 d' g₀ h i * Fc q a b c e₀ d₀ f d') =
      klCoef q b c 1 f h 0 m * (klCoef q a (b + c - 2 * f) 1 d' g₀ h i * klCoef q a b c e₀ d₀ f d') := by
  have hδ := loopVal_ne_of_pow q (by omega) hq
  have hd := chebD_ne_of_pow q hq
  have eA : Fc q b c 1 f h 0 m = klCoef q b c 1 f h 0 m :=
    Fc_eq_klCoef_of_adm q hδ (by omega) (fun j hj => hd j (by omega)) (Nat.zero_le _) (Nat.zero_le _) hmb
      (by omega) (h1 b c f h 0 m (fun n h1 h2 => hq n h1 (by omega)))
  rw [← eA]
  by_cases hA0 : Fc q b c 1 f h 0 m = 0
  · rw [hA0, zero_mul, zero_mul]
  obtain ⟨hf, hh⟩ := Fc_guard hA0
  have htA := Fc_total q hδ b c 1 f h 0 m (by omega) (fun j hj => hd j (by omega)) (Nat.zero_le _) (Nat.zero_le _)
    hmb (by omega) hA0
  simp only [le_min_iff] at hf hh
  have eB : Fc q a (b + c - 2 * f) 1 d' g₀ h i = klCoef q a (b + c - 2 * f) 1 d' g₀ h i :=
    Fc_eq_klCoef_of_adm q hδ (by omega) (fun j hj => hd j (by omega)) hh.1 hh.2 hia (by omega)
      (h1 a (b + c - 2 * f) d' g₀ h i (fun n h1 h2 => hq n h1 (by omega)))
  rw [← eB]
  by_cases hB0 : Fc q a (b + c - 2 * f) 1 d' g₀ h i = 0
  · rw [hB0, zero_mul, zero_mul, mul_zero]
  obtain ⟨hd', -⟩ := Fc_guard hB0
  simp only [le_min_iff] at hd'
  rw [Fc_eq_klCoef_of_adm q hδ (by omega) (fun j hj => hd j (by omega)) hf.1 hf.2 hd'.1 hd'.2
    (hcI a b e₀ d₀ f d' (fun n h1 h2 => hq n h1 (by omega)))]

/-- **The step of the induction**: from the third blocks `1` and `c` to `c + 1`, for nonempty first and second
blocks, by the recursion `Fc_third_rec` / `klCoef_third_rec` and a nonzero pivot. -/
theorem Fc_eq_klCoef_step [CharZero k] (q : kˣ) {c : ℕ} (hc : 1 ≤ c) (h1 : FcEqKLAt q 1) (hcI : FcEqKLAt q c)
    {a b e d m i : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hq : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + (c + 1)) + 6 → (q : k) ^ (2 * n) ≠ 1)
    (hA : KLAdm a b (c + 1) e d m i) : Fc q a b (c + 1) e d m i = klCoef q a b (c + 1) e d m i := by
  have hδ := loopVal_ne_of_pow q (by omega) hq
  have hd := chebD_ne_of_pow q hq
  have hD := hD_of_pow q (N := 2 * (a + b + (c + 1)) + 6) (by omega) hq
  have hnz := qfac_ne_of_pow q (N := 2 * (a + b + (c + 1)) + 6) (by omega) hq
  have hqb : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + (c + 1)) + 6 → qb q n ≠ 0 := fun n h1 h2 => qb_ne q hD n (hq n h1 h2)
  have hA' := hA
  simp only [KLAdm, le_min_iff] at hA'
  obtain ⟨⟨hea, heb⟩, ⟨hdA, hdc⟩, ⟨hmb, hmz⟩, ⟨hia, hiz⟩, ht⟩ := hA'
  -- the pivot: `g₀ = 0` when `d ≤ c`, else `g₀ = 1`, `d₀ = c`
  obtain ⟨d₀, g₀, hdd, hv, hpiv⟩ : ∃ d₀ g₀, d₀ + g₀ = d ∧ ValidA a b c 1 e d₀ g₀ ∧
      klCoef q (a + b - 2 * e) c 1 d₀ g₀ 0 (d₀ + g₀) ≠ 0 := by
    rcases Nat.lt_or_ge c d with hcd | hcd
    · refine ⟨c, 1, by omega, ⟨le_min hea heb, le_min (by omega) le_rfl, by omega, le_rfl⟩, ?_⟩
      have hK : KLAdm (a + b - 2 * e) c 1 c 1 0 (c + 1) := by simp only [KLAdm, le_min_iff]; omega
      rw [klCoef_one_10' q hK (fun n hn => hnz n (by omega))]
      exact div_ne_zero (hqb _ (by omega) (by omega)) (hqb _ (by omega) (by omega))
    · refine ⟨d, 0, by omega, ⟨le_min hea heb, le_min hdA hcd, by omega, by omega⟩, ?_⟩
      have hK : KLAdm (a + b - 2 * e) c 1 d 0 0 (d + 0) := by simp only [KLAdm, le_min_iff]; omega
      rw [Nat.add_zero] at hK ⊢
      rw [klCoef_one_00' q hK (fun n hn => hnz n (by omega))]
      exact div_ne_zero (mul_ne_zero (hqb _ (by omega) (by omega)) (hqb _ (by omega) (by omega)))
        (mul_ne_zero (hqb _ (by omega) (by omega)) (hqb _ (by omega) (by omega)))
  subst hdd
  have hF := Fc_third_rec q hδ a b c e d₀ g₀ m i ha hb hc (fun x hx => hd x (by omega))
    (fun x h1 h2 => hq x h1 (by omega)) hmb hmz hia (by omega) hv
  have hK := klCoef_third_rec q a b c e d₀ g₀ m i (fun x h1 h2 => hq x h1 (by omega)) hmb hmz hia (by omega) hv
  have hL : ∑ f ∈ range (b + 1), ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
        Fc q b c 1 f h 0 m * (Fc q a (b + c - 2 * f) 1 d' g₀ h i * Fc q a b c e d₀ f d') =
      ∑ f ∈ range (b + 1), ∑ h ∈ range (1 + 1), ∑ d' ∈ range (a + 1),
        klCoef q b c 1 f h 0 m * (klCoef q a (b + c - 2 * f) 1 d' g₀ h i * klCoef q a b c e d₀ f d') :=
    sum_congr rfl fun f _ => sum_congr rfl fun h _ => sum_congr rfl fun d' _ =>
      third_rec_term q ha hc h1 hcI hq hmb hmz hia (by omega)
  have hP : Fc q (a + b - 2 * e) c 1 d₀ g₀ 0 (d₀ + g₀) = klCoef q (a + b - 2 * e) c 1 d₀ g₀ 0 (d₀ + g₀) := by
    obtain ⟨-, hd₀, hg, hg1⟩ := hv
    simp only [le_min_iff] at hd₀
    exact h1 _ _ _ _ _ _ (fun n h1 h2 => hq n h1 (by omega))
      (by simp only [KLAdm, le_min_iff]; omega)
  rw [hL, hK, hP] at hF
  exact (mul_right_cancel₀ hpiv hF).symm

/-- **`Fc = klCoef`**: the normalised recoupling coefficient of the Temperley–Lieb model is the Kauffman–Lins
coefficient on every admissible index, at every `q` with `q^{2n} ≠ 1` for `1 ≤ n ≤ 2(a+b+c)+6`. By induction on
the third block: empty first or second block (both trees agree, `UR_eq_UL_first_zero`, `UR_eq_UL_second_zero`),
empty third block (`Fc_eq_klCoef_zero_third`), one strand (`Fc_one_block` against the closed forms of
`klCoef`), and the step `c → c + 1` (`Fc_third_rec` against `klCoef_third_rec`, with a nonzero pivot). -/
theorem Fc_eq_klCoef [CharZero k] : FcEqKL k := by
  intro q
  suffices H : ∀ c, FcEqKLAt q c from fun a b c e d f d' hq hA => H c a b e d f d' hq hA
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro a b e d f d' hq hA
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Fc_eq_klCoef_first_zero q hA fun n h1 h2 => hq n h1 (by omega)
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact Fc_eq_klCoef_second_zero q hA fun n h1 h2 => hq n h1 (by omega)
  rcases Nat.lt_or_ge c 2 with hc | hc
  · interval_cases c
    · have hA' := hA
      simp only [KLAdm, le_min_iff] at hA'
      obtain ⟨he, ⟨-, hd0⟩, ⟨-, hf0⟩, ⟨hda, hdf⟩, -⟩ := hA'
      obtain rfl : d = 0 := by omega
      obtain rfl : f = 0 := by omega
      exact Fc_eq_klCoef_zero_third q (loopVal_ne_of_pow q (by omega) hq) (le_min he.1 he.2) (le_min hda (by omega))
        (by omega) (fun j hj => chebD_ne_of_pow q hq j (by omega)) (fun j h1 h2 => hq j h1 (by omega))
    · exact Fc_eq_klCoef_one_pos q ha hb hA fun n h1 h2 => hq n h1 (by omega)
  · obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    exact Fc_eq_klCoef_step q (by omega) (ih 1 (by omega)) (ih c (by omega)) ha hb hq hA
end Lightlike.TemperleyLieb
