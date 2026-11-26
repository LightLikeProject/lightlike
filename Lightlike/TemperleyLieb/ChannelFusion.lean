import Mathlib
import Lightlike.TemperleyLieb.QNumbers

/-!
# The left eigen-equation of the vertex and orthogonality of the channels

`Wop a b i = p_c · nestCap · Q(a,b)` is the dual vertex.  Mirroring `vertex_eigen`, it satisfies
`Wop · (Q e_{a-1} Q) = lamRec a b i · Wop`; since `Vop` has the same eigenvalue on the right, `Wop_i Vop_j`
vanishes unless the eigenvalues `lamRec` of the two channels agree.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- The dual vertex with `i` arcs: `W(a,b;i) = p_{a+b-2i} · nestCap (a-i) i · Q(a,b)`. -/
noncomputable def Wop (q : kˣ) (a b i : ℕ) : Module.End k (ModelSpace k) :=
  jwAt q 0 (a + b - 2 * i) * nestCap q (a - i) i * Qab q a b

/-- The projector on `n + r` strands absorbs the projector on its last `n` strands, on the right. -/
theorem jwAt_absorb_suffix_all_right (q : kˣ) (s : ℕ) : ∀ (r n : ℕ),
    (∀ j, j < n + r → chebD (loopVal q) j ≠ 0) →
    jwAt q s (n + r) * jwAt q (s + r) n = jwAt q s (n + r) := by
  intro r
  induction r with
  | zero =>
    intro n hd
    have hp := jwProps_of_le (isTL_shift q s) n (fun j hj => hd j (by omega)) n le_rfl
    exact hp.idem
  | succ r ih =>
    intro n hd
    have h1 := ih (n + 1) (fun j hj => hd j (by omega))
    have h2 := jwAt_absorb_suffix_right q (s + r) n (fun j hj => hd j (by omega))
    have e1 : n + 1 + r = n + (r + 1) := by omega
    rw [e1] at h1
    calc jwAt q s (n + (r + 1)) * jwAt q (s + (r + 1)) n
        = jwAt q s (n + (r + 1)) * jwAt q (s + r + 1) n := rfl
      _ = (jwAt q s (n + (r + 1)) * jwAt q (s + r) (n + 1)) * jwAt q (s + r + 1) n := by rw [h1]
      _ = jwAt q s (n + (r + 1)) * (jwAt q (s + r) (n + 1) * jwAt q (s + r + 1) n) := by rw [mul_assoc]
      _ = _ := by rw [h2, h1]

/-- **The cap absorbs into the product** (mirror of `Qab_cup`): `cap_α Q(α+1,β+1) = Q(α,β) cap_α Q(α+1,β+1)`. -/
theorem cap_Qab (q : kˣ) (α β : ℕ) (hd : ∀ j, j ≤ α + β + 1 → chebD (loopVal q) j ≠ 0) :
    capOp q α * Qab q (α + 1) (β + 1) = Qab q α β * (capOp q α * Qab q (α + 1) (β + 1)) := by
  have p1 := jwProps_of_le (isTL_shift q 0) (α + 1) (fun j hj => hd j (by omega)) (α + 1) le_rfl
  have h1 : jwAt q 0 α * jwAt q 0 (α + 1) = jwAt q 0 (α + 1) := p1.absL α (by omega)
  have h2 : jwAt q (α + 2) β * jwAt q (α + 1) (β + 1) = jwAt q (α + 1) (β + 1) :=
    jwAt_absorb_suffix_left q (α + 1) β (fun j hj => hd j (by omega))
  have h3 : jwAt q (α + 2) β * jwAt q 0 (α + 1) = jwAt q 0 (α + 1) * jwAt q (α + 2) β :=
    (jwAt_comm_far q (by omega)).symm
  have h4 : jwAt q 0 (α + 1) * jwAt q (α + 2) β = jwAt q (α + 2) β * jwAt q 0 (α + 1) :=
    jwAt_comm_far q (by omega)
  have hQ : Qab q (α + 1) (β + 1) = (jwAt q 0 α * jwAt q (α + 2) β) * Qab q (α + 1) (β + 1) := by
    unfold Qab
    calc jwAt q 0 (α + 1) * jwAt q (α + 1) (β + 1)
        = (jwAt q 0 α * jwAt q 0 (α + 1)) * (jwAt q (α + 2) β * jwAt q (α + 1) (β + 1)) := by rw [h1, h2]
      _ = jwAt q 0 α * ((jwAt q 0 (α + 1) * jwAt q (α + 2) β) * jwAt q (α + 1) (β + 1)) := by
          simp only [mul_assoc]
      _ = jwAt q 0 α * ((jwAt q (α + 2) β * jwAt q 0 (α + 1)) * jwAt q (α + 1) (β + 1)) := by rw [h4]
      _ = _ := by simp only [mul_assoc]
  have hc1 : capOp q α * jwAt q 0 α = jwAt q 0 α * capOp q α :=
    cap_mul_jwAt_near q (m := α) (s := 0) (n := α) (by omega)
  have hc2 : capOp q α * jwAt q (α + 2) β = jwAt q α β * capOp q α :=
    cap_mul_jwAt_far q (m := α) (s := α) (le_refl _) β
  calc capOp q α * Qab q (α + 1) (β + 1)
      = capOp q α * ((jwAt q 0 α * jwAt q (α + 2) β) * Qab q (α + 1) (β + 1)) := by
        conv_lhs => rw [hQ]
    _ = (capOp q α * jwAt q 0 α) * jwAt q (α + 2) β * Qab q (α + 1) (β + 1) := by simp only [mul_assoc]
    _ = jwAt q 0 α * (capOp q α * jwAt q (α + 2) β) * Qab q (α + 1) (β + 1) := by rw [hc1]; simp only [mul_assoc]
    _ = jwAt q 0 α * (jwAt q α β * capOp q α) * Qab q (α + 1) (β + 1) := by rw [hc2]
    _ = _ := by unfold Qab; simp only [mul_assoc]

/-- The full projector absorbs `Q(a,b)` on the right: `p_{a+b} Q(a,b) = p_{a+b}`. -/
theorem full_mul_Qab (q : kˣ) (a b : ℕ) (hd : ∀ j, j < a + b → chebD (loopVal q) j ≠ 0) :
    jwAt q 0 (a + b) * Qab q a b = jwAt q 0 (a + b) := by
  have h1 := jwAt_absorb_suffix_all_right q 0 a b (fun j hj => hd j (by omega))
  have hp := jwProps_of_le (isTL_shift q 0) (a + b) hd (a + b) le_rfl
  have h2 : jwAt q 0 (a + b) * jwAt q 0 a = jwAt q 0 (a + b) := hp.absR a (by omega)
  have h3 : jwAt q 0 (b + a) * jwAt q (0 + a) b = jwAt q 0 (b + a) := by
    have := jwAt_absorb_suffix_all_right q 0 a b (fun j hj => hd j (by omega))
    simpa using this
  rw [show b + a = a + b by omega] at h3
  unfold Qab
  rw [← mul_assoc, h2]
  simpa using h3

/-- **The left eigen-equation**: `W(a,b;i) · (Q e_{a-1} Q) = lamRec a b i · W(a,b;i)`. -/
theorem wertex_eigen (q : kˣ) : ∀ (i a b : ℕ), 1 ≤ a → 1 ≤ b → i ≤ a → i ≤ b →
    (∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0) →
    Wop q a b i * (Qab q a b * modelE q (a - 1) * Qab q a b) = lamRec q a b i • Wop q a b i := by
  intro i
  induction i with
  | zero =>
    intro a b ha hb _ _ hd
    have hp := jwProps_of_le (isTL_shift q 0) (a + b) (fun j hj => hd j (by omega)) (a + b) le_rfl
    have hjw : jwAt q 0 (a + b) = jw (loopVal q) (modelE q) (a + b) := rfl
    have hk : jwAt q 0 (a + b) * modelE q (a - 1) = 0 := by
      rw [hjw]; exact hp.killR (a - 1) (by omega)
    have hPQ := full_mul_Qab q a b (fun j hj => hd j (by omega))
    simp only [Wop, nestCap, mul_one, one_mul, Nat.sub_zero, mul_zero, Nat.add_zero, lamRec, zero_smul]
    calc jwAt q 0 (a + b) * Qab q a b * (Qab q a b * modelE q (a - 1) * Qab q a b)
        = (jwAt q 0 (a + b) * Qab q a b) * Qab q a b * modelE q (a - 1) * Qab q a b := by
          simp only [mul_assoc]
      _ = 0 := by
          rw [hPQ, hPQ, hk, zero_mul]
  | succ i' ih =>
    intro a b ha hb hia hib hd
    obtain ⟨α, rfl⟩ : ∃ α, a = α + 1 := ⟨a - 1, by omega⟩
    obtain ⟨β, rfl⟩ : ∃ β, b = β + 1 := ⟨b - 1, by omega⟩
    have hd' : ∀ j, j ≤ α + β + 1 → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
    have hQ := Qab_idem q (α + 1) (β + 1) (fun j hj => hd j (by omega))
    have hQ2 := Qab_idem q α β (fun j hj => hd j (by omega))
    have hl2 : α - i' + i' = α := by omega
    have hW : Wop q (α + 1) (β + 1) (i' + 1) = Wop q α β i' * capOp q α * Qab q (α + 1) (β + 1) := by
      have hl : α + 1 - (i' + 1) = α - i' := by omega
      have hc : α + 1 + (β + 1) - 2 * (i' + 1) = α + β - 2 * i' := by omega
      unfold Wop
      rw [hl, hc]
      have hcap : nestCap q (α - i') (i' + 1) = nestCap q (α - i') i' * capOp q α := by
        simp only [nestCap, hl2]
      rw [hcap]
      calc jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' * capOp q α) * Qab q (α + 1) (β + 1)
          = jwAt q 0 (α + β - 2 * i') * nestCap q (α - i') i' * (capOp q α * Qab q (α + 1) (β + 1)) := by
            simp only [mul_assoc]
        _ = jwAt q 0 (α + β - 2 * i') * nestCap q (α - i') i' *
              (Qab q α β * (capOp q α * Qab q (α + 1) (β + 1))) := by rw [← cap_Qab q α β hd']
        _ = _ := by simp only [mul_assoc]
    have hWQ : Wop q α β i' * Qab q α β = Wop q α β i' := by
      unfold Wop
      rw [mul_assoc, hQ2]
    have hX := contraction_all q α β hd'
    have key : Wop q α β i' * (capOp q α * Qab q (α + 1) (β + 1) * cupOp q α) =
        lamRec q (α + 1) (β + 1) (i' + 1) • Wop q α β i' := by
      rw [hX, mul_add, mul_smul_comm, mul_smul_comm, hWQ]
      by_cases hαβ : 1 ≤ α ∧ 1 ≤ β
      · have hih := ih α β hαβ.1 hαβ.2 (by omega) (by omega) (fun j hj => hd j (by omega))
        have h' : Wop q α β i' * (Qab q α β * modelE q (α - 1) * Qab q α β) =
            lamRec q α β i' • Wop q α β i' := hih
        rw [h']
        simp only [lamRec, Nat.add_sub_cancel, smul_smul]
        module
      · have hc2 : sCoef q (α + 1) * sCoef q (β + 1) = 0 := by
          rcases Nat.eq_zero_or_pos α with h0 | h0
          · subst h0; simp [sCoef]
          · have : β = 0 := by omega
            subst this; simp [sCoef]
        rw [hc2]
        simp only [lamRec, Nat.add_sub_cancel, hc2, zero_smul, add_zero, zero_mul]
    rw [hW, Nat.add_sub_cancel]
    calc Wop q α β i' * capOp q α * Qab q (α + 1) (β + 1) *
          (Qab q (α + 1) (β + 1) * modelE q α * Qab q (α + 1) (β + 1))
        = Wop q α β i' * capOp q α * (Qab q (α + 1) (β + 1) * Qab q (α + 1) (β + 1)) *
          modelE q α * Qab q (α + 1) (β + 1) := by simp only [mul_assoc]
      _ = Wop q α β i' * capOp q α * Qab q (α + 1) (β + 1) * (cupOp q α * capOp q α) *
          Qab q (α + 1) (β + 1) := by rw [hQ, cup_cap]
      _ = Wop q α β i' * (capOp q α * Qab q (α + 1) (β + 1) * cupOp q α) * capOp q α *
          Qab q (α + 1) (β + 1) := by simp only [mul_assoc]
      _ = lamRec q (α + 1) (β + 1) (i' + 1) • (Wop q α β i' * capOp q α * Qab q (α + 1) (β + 1)) := by
          rw [key, smul_mul_assoc, smul_mul_assoc]

/-- **Orthogonality of the channels**: `W_i V_j = 0` when the eigenvalues of `Q e_{a-1} Q` differ. -/
theorem channel_orth (q : kˣ) (a b i j : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hia : i ≤ a) (hib : i ≤ b)
    (hja : j ≤ a) (hjb : j ≤ b) (hd : ∀ t, t ≤ a + b → chebD (loopVal q) t ≠ 0)
    (hij : lamRec q a b i ≠ lamRec q a b j) : Wop q a b i * Vop q a b j = 0 := by
  have h1 := wertex_eigen q i a b ha hb hia hib hd
  have h2 := vertex_eigen q j a b ha hb hja hjb hd
  have h3 : lamRec q a b i • (Wop q a b i * Vop q a b j) = lamRec q a b j • (Wop q a b i * Vop q a b j) := by
    calc lamRec q a b i • (Wop q a b i * Vop q a b j)
        = (Wop q a b i * (Qab q a b * modelE q (a - 1) * Qab q a b)) * Vop q a b j := by
          rw [h1, smul_mul_assoc]
      _ = Wop q a b i * ((Qab q a b * modelE q (a - 1) * Qab q a b) * Vop q a b j) := by rw [mul_assoc]
      _ = lamRec q a b j • (Wop q a b i * Vop q a b j) := by rw [h2, mul_smul_comm]
  have h4 : (lamRec q a b i - lamRec q a b j) • (Wop q a b i * Vop q a b j) = 0 :=
    (sub_smul (lamRec q a b i) (lamRec q a b j) (Wop q a b i * Vop q a b j)).trans (sub_eq_zero.mpr h3)
  exact (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hij)

/-- The eigenvalues `lamRec a b i` of distinct channels differ (for `q^{2m} ≠ 1`, `1 ≤ m ≤ a+b+1`). -/
theorem lamRec_ne (q : kˣ) (a b i j : ℕ) (hia : i ≤ a) (hib : i ≤ b) (hja : j ≤ a) (hjb : j ≤ b)
    (hij : i ≠ j) (hq2 : ∀ m, 1 ≤ m → m ≤ a + b + 1 → (q : k) ^ (2 * m) ≠ 1) :
    lamRec q a b i ≠ lamRec q a b j := by
  have hq : (q : k) ≠ 0 := q.ne_zero
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl (by omega)
    intro h; apply this
    field_simp at h
    linear_combination h
  have hnz : ∀ m, 1 ≤ m → m ≤ a + b + 1 → qb q m ≠ 0 := fun m h1 h2 => qb_ne q hD m (hq2 m h1 h2)
  rw [lamRec_eq q i a b hia hib hq2, lamRec_eq q j a b hja hjb hq2]
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0; omega
  rcases Nat.eq_zero_or_pos b with h0' | h0'
  · subst h0'; omega
  have ha := hnz a h0 (by omega)
  have hb := hnz b h0' (by omega)
  intro h
  rw [div_eq_div_iff (mul_ne_zero ha hb) (mul_ne_zero ha hb)] at h
  have h' : qb q (a + b - i + 1) * qb q i = qb q (a + b - j + 1) * qb q j := by
    have h5 : (-(qb q (a + b - i + 1) * qb q i)) * (qb q a * qb q b) =
        (-(qb q (a + b - j + 1) * qb q j)) * (qb q a * qb q b) := by linear_combination h
    have h6 := mul_right_cancel₀ (mul_ne_zero ha hb) h5
    exact neg_inj.mp h6
  -- reduce to the field identity in `u = q^i`, `w = q^j`, `Z = q^(a+b+1)`
  have eN : (q : k) ^ (a + b - i + 1) * (q : k) ^ i = (q : k) ^ (a + b + 1) := by
    rw [← pow_add]; congr 1; omega
  have eM : (q : k) ^ (a + b - j + 1) * (q : k) ^ j = (q : k) ^ (a + b + 1) := by
    rw [← pow_add]; congr 1; omega
  have hu : (q : k) ^ i ≠ 0 := pow_ne_zero _ hq
  have hw : (q : k) ^ j ≠ 0 := pow_ne_zero _ hq
  have hZ : (q : k) ^ (a + b + 1) ≠ 0 := pow_ne_zero _ hq
  have e1 : (q : k) ^ (a + b - i + 1) = (q : k) ^ (a + b + 1) / (q : k) ^ i := by
    field_simp; exact eN
  have e2 : (q : k) ^ (a + b - j + 1) = (q : k) ^ (a + b + 1) / (q : k) ^ j := by
    field_simp; exact eM
  rw [qb_eq, qb_eq, qb_eq, qb_eq, e1, e2] at h'
  have hFa : ((q : k) ^ i) ^ 2 - ((q : k) ^ j) ^ 2 ≠ 0 := by
    intro h0
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hm := hq2 (j - i) (by omega) (by omega)
      apply hm
      have hpow : ((q : k) ^ j) ^ 2 = ((q : k) ^ i) ^ 2 * (q : k) ^ (2 * (j - i)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
      have hui : ((q : k) ^ i) ^ 2 ≠ 0 := pow_ne_zero _ hu
      rw [hpow] at h0
      have : ((q : k) ^ i) ^ 2 * ((q : k) ^ (2 * (j - i)) - 1) = 0 := by linear_combination -h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hui)
    · have hm := hq2 (i - j) (by omega) (by omega)
      apply hm
      have hpow : ((q : k) ^ i) ^ 2 = ((q : k) ^ j) ^ 2 * (q : k) ^ (2 * (i - j)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
      have hwj : ((q : k) ^ j) ^ 2 ≠ 0 := pow_ne_zero _ hw
      rw [hpow] at h0
      have : ((q : k) ^ j) ^ 2 * ((q : k) ^ (2 * (i - j)) - 1) = 0 := by linear_combination h0
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hwj)
  have hFb : ((q : k) ^ (a + b + 1)) ^ 2 - ((q : k) ^ i) ^ 2 * ((q : k) ^ j) ^ 2 ≠ 0 := by
    intro h0
    have hm := hq2 (a + b + 1 - i - j) (by omega) (by omega)
    apply hm
    have hpow : ((q : k) ^ (a + b + 1)) ^ 2 = ((q : k) ^ i) ^ 2 * ((q : k) ^ j) ^ 2 * (q : k) ^ (2 * (a + b + 1 - i - j)) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
    have hpos : ((q : k) ^ i) ^ 2 * ((q : k) ^ j) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hw)
    rw [hpow] at h0
    have : ((q : k) ^ i) ^ 2 * ((q : k) ^ j) ^ 2 * ((q : k) ^ (2 * (a + b + 1 - i - j)) - 1) = 0 := by
      linear_combination h0
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hpos)
  generalize (q : k) ^ (a + b + 1) = Z at *
  generalize (q : k) ^ i = u at *
  generalize (q : k) ^ j = w at *
  have key : (u ^ 2 - w ^ 2) * (Z ^ 2 - u ^ 2 * w ^ 2) = 0 := by
    have hD2 : (q : k) ^ 2 - 1 ≠ 0 := by
      have := hq2 1 le_rfl (by omega)
      simpa [sub_eq_zero] using this
    field_simp at h'
    linear_combination h'
  rcases mul_eq_zero.mp key with h1 | h1
  · exact hFa h1
  · exact hFb h1

end Lightlike.TemperleyLieb
