import Lightlike.TuraevViro.LevelOne

/-!
# The F-matrices of `U_q(sl₂)` at a root of unity and the pentagon equation

The associator of the fusion ring at `q = e^{iπ/r}` is given by the quantum 6j symbols:
`F^{abc}_d[e, f] = (-1)^((a+b+c+d)/2) √([e+1] [f+1]) {a b e; c d f}_q` (`fMat`, doubled spins). Its pentagon equation
`F^{pcd}_e[g, l] F^{abl}_e[p, k] = Σ_h F^{abc}_g[p, h] F^{ahd}_e[g, k] F^{bcd}_k[h, l]` (`fMat_pentagon`) is a
consequence of the q-Biedenharn–Elliott identity `qBiedenharnElliott` (the hypothesis, as in `turaevViro_move23`): the
sum over `h` of the BE identity, with the square roots of the dimensions and the signs moved to the F-matrices.

The pentagon is therefore **conditional** on `qBiedenharnElliott hr`, which is proved at `r = 3` and only checked
numerically for other levels.
-/

namespace Lightlike.TV

open Finset

/-- **The F-matrix entry** `F^{abc}_d[e, f]` of the associator `(a ⊗ b) ⊗ c → a ⊗ (b ⊗ c)` with total charge `d`, from
the quantum 6j symbol (doubled spins). -/
noncomputable def fMat (r a b c d e f : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((a + b + c + d) / 2) * Real.sqrt (qnum r (e + 1) * qnum r (f + 1)) * qSixJ r a b e c d f

/-- A symmetry of the quantum 6j symbol (swap of the columns 2 and 3, then flip of the columns 1 and 2). -/
lemma qSixJ_symm_B (r a h g d e k : ℕ) : qSixJ r a h g d e k = qSixJ r d k h a g e := by
  rw [← qSixJ_swap23 r a h g d e k, ← qSixJ_flip12 r a g h d k e]

/-- A symmetry of the quantum 6j symbol (two flips and two column swaps). -/
lemma qSixJ_symm_A (r a b p c g h : ℕ) : qSixJ r a b p c g h = qSixJ r a g h c b p := by
  rw [← qSixJ_swap23 r a b p c g h, ← qSixJ_flip12 r a p b c h g, ← qSixJ_swap23 r c h b a p g,
    ← qSixJ_flip12 r c b h a g p]

/-- A symmetry of the quantum 6j symbol (reversal of the columns, and a flip). -/
lemma qSixJ_symm_D (r p c g d e l : ℕ) : qSixJ r p c g d e l = qSixJ r l e p g c d := by
  rw [← qSixJ_swap12 r p c g d e l, ← qSixJ_swap23 r c p g e d l, ← qSixJ_swap12 r c g p e l d,
    ← qSixJ_flip12 r g c p l e d]

set_option maxHeartbeats 800000 in
/-- Parity of the sign exponents: the three signs of the pentagon are the signs of the Biedenharn–Elliott identity times
the signs of the outer F-matrices, when the ten triads that occur have even sums. -/
lemma sign_parity_aux (a b c d e p g k l h : ℕ) (e1 : (b + c + h) % 2 = 0) (e2 : (b + k + l) % 2 = 0)
    (e3 : (d + c + l) % 2 = 0) (e4 : (d + k + h) % 2 = 0) (e5 : (d + g + e) % 2 = 0)
    (e6 : (a + k + e) % 2 = 0) (e7 : (a + g + h) % 2 = 0) (e8 : (a + b + p) % 2 = 0)
    (e9 : (c + g + p) % 2 = 0) (e10 : (c + b + h) % 2 = 0) :
    ((a + b + c + g) / 2 + (a + h + d + e) / 2 + (b + c + d + k) / 2) % 2 =
      (((p + c + d + e) / 2 + (a + b + l + e) / 2) + (b + c + d + k + a + g + l + e + p + h) / 2) % 2 := by
  omega

/-- A label of an admissible triad is below `r - 1`. -/
lemma lt_of_tri_aux {r x y z : ℕ} (hr : 2 ≤ r) (h1 : x ≤ y + z) (h2 : y + z + x ≤ 2 * (r - 2)) : x < r - 1 := by
  omega

/-- A colour below `r - 1` has `x + 1 < r`. -/
lemma succ_lt_aux {r x : ℕ} (h : x < r - 1) : x + 1 < r := by omega

variable {r : ℕ}

/-- **The pentagon equation of the F-matrices**, from the q-Biedenharn–Elliott identity: for all colours,
`F^{pcd}_e[g, l] F^{abl}_e[p, k] = Σ_{h < r - 1} F^{abc}_g[p, h] F^{ahd}_e[g, k] F^{bcd}_k[h, l]`.
**Conditional** on `qBiedenharnElliott hr`. -/
theorem fMat_pentagon (hr : 2 ≤ r) (hBE : qBiedenharnElliott hr) (a b c d e p g k l : ℕ) :
    fMat r p c d e g l * fMat r a b l e p k =
      ∑ h ∈ range (r - 1), fMat r a b c g p h * fMat r a h d e g k * fMat r b c d k h l := by
  have hB := hBE b c d k a g l e p
  simp only [tvModel] at hB
  have hE : qSixJ r a b p l e k = qSixJ r l e p a b k := (qSixJ_flip12 r a b p l e k).symm
  have hD := qSixJ_symm_D r p c g d e l
  set Q : ℝ := Real.sqrt (qnum r (g + 1) * qnum r (l + 1)) * Real.sqrt (qnum r (p + 1) * qnum r (k + 1)) with hQ
  set s2 : ℝ := (-1 : ℝ) ^ ((p + c + d + e) / 2) * (-1 : ℝ) ^ ((a + b + l + e) / 2) with hs2
  have hL : fMat r p c d e g l * fMat r a b l e p k =
      s2 * Q * (qSixJ r l e p a b k * qSixJ r l e p g c d) := by
    unfold fMat
    rw [hE, hD, hs2, hQ]; ring
  have key : ∀ h ∈ range (r - 1), fMat r a b c g p h * fMat r a h d e g k * fMat r b c d k h l =
      s2 * Q * ((-1 : ℝ) ^ ((b + c + d + k + a + g + l + e + p + h) / 2) * qnum r (h + 1) *
        (qSixJ r b c h d k l * qSixJ r d k h a g e * qSixJ r a g h c b p)) := by
    intro h hh
    have hhr : h < r - 1 := mem_range.mp hh
    unfold fMat
    rw [qSixJ_symm_A r a b p c g h, qSixJ_symm_B r a h g d e k]
    by_cases hT : qSixJ r b c h d k l * qSixJ r d k h a g e * qSixJ r a g h c b p = 0
    · have h1 : qSixJ r b c h d k l * (qSixJ r d k h a g e * qSixJ r a g h c b p) = 0 := by
        rw [← mul_assoc]; exact hT
      have h2 : qSixJ r a g h c b p * qSixJ r d k h a g e * qSixJ r b c h d k l = 0 := by
        rw [mul_comm (qSixJ r a g h c b p), mul_comm _ (qSixJ r b c h d k l)]
        linarith [mul_assoc (qSixJ r b c h d k l) (qSixJ r d k h a g e) (qSixJ r a g h c b p)]
      have : (-1 : ℝ) ^ ((a + b + c + g) / 2) * Real.sqrt (qnum r (p + 1) * qnum r (h + 1)) *
            qSixJ r a g h c b p * ((-1 : ℝ) ^ ((a + h + d + e) / 2) *
            Real.sqrt (qnum r (g + 1) * qnum r (k + 1)) * qSixJ r d k h a g e) *
          ((-1 : ℝ) ^ ((b + c + d + k) / 2) * Real.sqrt (qnum r (h + 1) * qnum r (l + 1)) *
            qSixJ r b c h d k l) = 0 := by
        calc _ = ((-1 : ℝ) ^ ((a + b + c + g) / 2) * Real.sqrt (qnum r (p + 1) * qnum r (h + 1)) *
              ((-1 : ℝ) ^ ((a + h + d + e) / 2) * Real.sqrt (qnum r (g + 1) * qnum r (k + 1))) *
              ((-1 : ℝ) ^ ((b + c + d + k) / 2) * Real.sqrt (qnum r (h + 1) * qnum r (l + 1)))) *
              (qSixJ r a g h c b p * qSixJ r d k h a g e * qSixJ r b c h d k l) := by ring
          _ = 0 := by rw [h2, mul_zero]
      rw [this, hT]; ring
    · have hnz1 : qSixJ r b c h d k l ≠ 0 := fun h0 => hT (by rw [h0]; ring)
      have hnz2 : qSixJ r d k h a g e ≠ 0 := fun h0 => hT (by rw [h0]; ring)
      have hnz3 : qSixJ r a g h c b p ≠ 0 := fun h0 => hT (by rw [h0]; ring)
      obtain ⟨t1, t2, t3, t4⟩ := qSixJ_ok hnz1
      obtain ⟨u1, u2, u3, u4⟩ := qSixJ_ok hnz2
      obtain ⟨v1, v2, v3, v4⟩ := qSixJ_ok hnz3
      obtain ⟨⟨t1a, t1b, t1c, t1d⟩, t1e⟩ := t1
      obtain ⟨⟨t2a, t2b, t2c, t2d⟩, t2e⟩ := t2
      obtain ⟨⟨t3a, t3b, t3c, t3d⟩, t3e⟩ := t3
      obtain ⟨⟨t4a, t4b, t4c, t4d⟩, t4e⟩ := t4
      obtain ⟨⟨u1a, u1b, u1c, u1d⟩, u1e⟩ := u1
      obtain ⟨⟨u2a, u2b, u2c, u2d⟩, u2e⟩ := u2
      obtain ⟨⟨u3a, u3b, u3c, u3d⟩, u3e⟩ := u3
      obtain ⟨⟨u4a, u4b, u4c, u4d⟩, u4e⟩ := u4
      obtain ⟨⟨v1a, v1b, v1c, v1d⟩, v1e⟩ := v1
      obtain ⟨⟨v2a, v2b, v2c, v2d⟩, v2e⟩ := v2
      obtain ⟨⟨v3a, v3b, v3c, v3d⟩, v3e⟩ := v3
      obtain ⟨⟨v4a, v4b, v4c, v4d⟩, v4e⟩ := v4
      have hp : p < r - 1 := lt_of_tri_aux hr v2b (by linarith)
      have hg : g < r - 1 := lt_of_tri_aux hr u2d (by linarith)
      have hk : k < r - 1 := lt_of_tri_aux hr u3d (by linarith)
      have hl : l < r - 1 := lt_of_tri_aux hr t2b (by linarith)
      have hpar := sign_parity_aux a b c d e p g k l h t1a t2a t3a t4a u2a u3a u4a v2a v3a v4a
      have hsign : (-1 : ℝ) ^ ((a + b + c + g) / 2) * (-1 : ℝ) ^ ((a + h + d + e) / 2) *
          (-1 : ℝ) ^ ((b + c + d + k) / 2) = s2 * (-1 : ℝ) ^ ((b + c + d + k + a + g + l + e + p + h) / 2) := by
        rw [hs2, ← pow_add, ← pow_add, ← pow_add, ← pow_add,
          neg_one_pow_eq_pow_mod_two, hpar, ← neg_one_pow_eq_pow_mod_two]
      have dh : 0 ≤ qnum r (h + 1) := (qnum_pos hr (Nat.succ_pos _) (succ_lt_aux hhr)).le
      have dp : 0 ≤ qnum r (p + 1) := (qnum_pos hr (Nat.succ_pos _) (succ_lt_aux hp)).le
      have dg : 0 ≤ qnum r (g + 1) := (qnum_pos hr (Nat.succ_pos _) (succ_lt_aux hg)).le
      have dk : 0 ≤ qnum r (k + 1) := (qnum_pos hr (Nat.succ_pos _) (succ_lt_aux hk)).le
      have dl : 0 ≤ qnum r (l + 1) := (qnum_pos hr (Nat.succ_pos _) (succ_lt_aux hl)).le
      have hsq : Real.sqrt (qnum r (h + 1)) * Real.sqrt (qnum r (h + 1)) = qnum r (h + 1) :=
        Real.mul_self_sqrt dh
      rw [Real.sqrt_mul dp, Real.sqrt_mul dg, Real.sqrt_mul dh, hQ, Real.sqrt_mul dg, Real.sqrt_mul dp]
      calc _ = ((-1 : ℝ) ^ ((a + b + c + g) / 2) * (-1 : ℝ) ^ ((a + h + d + e) / 2) *
              (-1 : ℝ) ^ ((b + c + d + k) / 2)) *
            (Real.sqrt (qnum r (h + 1)) * Real.sqrt (qnum r (h + 1))) *
            (Real.sqrt (qnum r (g + 1)) * Real.sqrt (qnum r (l + 1)) *
              (Real.sqrt (qnum r (p + 1)) * Real.sqrt (qnum r (k + 1)))) *
            (qSixJ r b c h d k l * qSixJ r d k h a g e * qSixJ r a g h c b p) := by ring
        _ = _ := by rw [hsign, hsq]; ring
  rw [hL, Finset.sum_congr rfl key, ← Finset.mul_sum]
  congr 1
  rw [← hB]

/-- **The pentagon equation of the F-matrices at level `r = 3`, unconditionally**: the q-Biedenharn–Elliott identity
is proved at `r = 3` (`qBiedenharnElliott_three`). -/
theorem fMat_pentagon_three (a b c d e p g k l : ℕ) :
    fMat 3 p c d e g l * fMat 3 a b l e p k =
      ∑ h ∈ range (3 - 1), fMat 3 a b c g p h * fMat 3 a h d e g k * fMat 3 b c d k h l :=
  fMat_pentagon (by norm_num) qBiedenharnElliott_three a b c d e p g k l

end Lightlike.TV
