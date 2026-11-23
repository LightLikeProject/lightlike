module

public import Lightlike.Upstream.SpinReps2.BEPositive2
public import Lightlike.Upstream.SpinReps2.SixJZero
public import Lightlike.Upstream.SpinReps2.SixJOrth

/-!
# The Biedenharn–Elliott identity for all spins

For all spins (doubled units) and `beLHS`, `beRHS` as in `BEDefs`:
`beLHS a b c d e f p q r = beRHS a b c d e f p q r`
(`PhyslibAlpha.Sl2.biedenharnElliott`).

The positive case is `biedenharnElliott_pos` (the recoupling pentagon). The cases with a zero spin
are reduced to the 6j symbol with a zero spin (`sixJSym_zero_left`) and 6j orthogonality
(`sixJSym_orth`), after moving the zero by the symmetries of the identity.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace PhyslibAlpha.Sl2.Pentagon

/-! ## Symmetries of the Biedenharn–Elliott identity -/

lemma sj_swap12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₂ j₁ j₃ j₅ j₄ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![0, 2, 1, 3] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_flip12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₄ j₅ j₃ j₁ j₂ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![3, 2, 1, 0] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_swap23 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₃ j₂ j₄ j₆ j₅ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![0, 1, 3, 2] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_flipswap (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₅ j₄ j₃ j₂ j₁ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![3, 1, 2, 0] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

lemma sj_swap13 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₃ j₂ j₁ j₆ j₅ j₄ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![0, 3, 2, 1] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- One term of `beLHS`. -/
noncomputable def beTerm (a b c d e f p q r x : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) * ((x : ℝ) + 1) *
    (sixJSym a b x c d p * sixJSym c d x e f q * sixJSym e f x b a r)

/-- `beLHS` may be summed over any range containing `[0, a + b]` (larger `x` violate the triangle
rule in `(a b x)`). -/
lemma beLHS_eq_sum (a b c d e f p q r N : ℕ) (hN : a + b ≤ N) :
    beLHS a b c d e f p q r = ∑ x ∈ range (N + 1), beTerm a b c d e f p q r x := by
  unfold beLHS
  apply sum_subset
  · intro x hx; simp only [mem_range] at hx ⊢; omega
  · intro x _ hx
    simp only [mem_range, not_lt] at hx
    rw [sixJSym_eq_zero_of_gt (show a + b < x by omega)]
    ring

/-- Symmetry `D ↔ E` of the 2-3 configuration. -/
theorem be_swapDE (a b c d e f p q r : ℕ) :
    beLHS b a d c f e p q r = beLHS a b c d e f p q r ∧
      beRHS b a d c f e p q r = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_swap12 a b x c d p, sj_swap12 c d x e f q, sj_swap12 e f x b a r,
      show b + a + d + c + f + e + p + q + r + x = a + b + c + d + e + f + p + q + r + x by ring]
  · rw [beRHS, beRHS, mul_comm]

/-- Symmetry `A ↔ B` of the 2-3 configuration. -/
theorem be_swapAB (a b c d e f p q r : ℕ) :
    beLHS d c b a e f p r q = beLHS a b c d e f p q r ∧
      beRHS d c b a e f p r q = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_flipswap a b x c d p, sj_flip12 e f x b a r, sj_flip12 c d x e f q,
      show d + c + b + a + e + f + p + r + q + x = a + b + c + d + e + f + p + q + r + x by ring]
    ring
  · rw [beRHS, beRHS, sj_swap23 p q r e a d, sj_swap23 p q r f b c]

/-- Symmetry `A ↔ C` of the 2-3 configuration. -/
theorem be_swapAC (a b c d e f p q r : ℕ) :
    beLHS e f c d a b q p r = beLHS a b c d e f p q r ∧
      beRHS e f c d a b q p r = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_flip12 c d x e f q, sj_flip12 a b x c d p, sj_flipswap e f x b a r,
      show e + f + c + d + a + b + q + p + r + x = a + b + c + d + e + f + p + q + r + x by ring]
    ring
  · rw [beRHS, beRHS, sj_swap12 p q r e a d, sj_swap12 p q r f b c]

/-- Symmetry `B ↔ C` of the 2-3 configuration. -/
theorem be_swapBC (a b c d e f p q r : ℕ) :
    beLHS a b f e d c r q p = beLHS a b c d e f p q r ∧
      beRHS a b f e d c r q p = beRHS a b c d e f p q r := by
  constructor
  · rw [beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega),
      beLHS_eq_sum _ _ _ _ _ _ _ _ _ (a + b + c + d + e + f) (by omega)]
    refine sum_congr rfl fun x _ => ?_
    rw [beTerm, beTerm, sj_flipswap e f x b a r, sj_flipswap c d x e f q, sj_flipswap a b x c d p,
      show a + b + f + e + d + c + r + q + p + x = a + b + c + d + e + f + p + q + r + x by ring]
    ring
  · rw [beRHS, beRHS, sj_swap13 p q r e a d, sj_swap13 p q r f b c, mul_comm]

/-! ## The case `a = 0` -/

lemma sj_M1 (b c d e f q : ℕ) : sixJSym d q e f b c = sixJSym c d b e f q := by
  have := sixJSym_perm (permOf ![2, 0, 1, 3] (by decide)) c d b e f q
  simpa [permOf, edgeM] using this

/-- **Biedenharn–Elliott with `a = 0`** (all other spins arbitrary): the `x`-sum collapses to
`x = b` and three of the 6j symbols take the zero-spin closed form. -/
theorem be_a_zero (b c d e f p q r : ℕ) : beLHS 0 b c d e f p q r = beRHS 0 b c d e f p q r := by
  unfold beLHS beRHS
  rw [sj_flipswap 0 e r q p d, sum_eq_single b]
  · rw [sj_flipswap 0 b b f e r, sixJSym_zero_left b b c d p, sixJSym_zero_left b b f e r,
      sixJSym_zero_left e r q p d]
    by_cases hpd : p = d
    swap
    · rw [ite_eq_right (show ¬(b = b ∧ p = d ∧ Triad b d c) from fun h => hpd h.2.1),
        ite_eq_right (show ¬(r = e ∧ d = p ∧ Triad e p q) from fun h => hpd h.2.1.symm)]
      ring
    by_cases hre : r = e
    swap
    · rw [ite_eq_right (show ¬(b = b ∧ r = e ∧ Triad b e f) from fun h => hre h.2.1),
        ite_eq_right (show ¬(r = e ∧ d = p ∧ Triad e p q) from fun h => hre h.1)]
      ring
    subst p r
    rw [sj_M1 b c d e f q]
    by_cases hM : sixJSym c d b e f q = 0
    · rw [hM]; ring
    obtain ⟨T1, T2, T3, T4⟩ := triad_of_sixJSym_ne_zero hM
    have h1 : Triad b d c := by unfold Triad at *; omega
    have h2 : Triad b e f := by unfold Triad at *; omega
    rw [ite_eq_left ⟨rfl, rfl, h1⟩, ite_eq_left ⟨rfl, rfl, h2⟩, ite_eq_left ⟨rfl, rfl, T3⟩]
    have hb0 : 0 < Real.sqrt ((b : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hd0 : 0 < Real.sqrt ((d : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have he0 : 0 < Real.sqrt ((e : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsign : (-1 : ℝ) ^ ((0 + b + c + d + e + f + d + q + e + b) / 2) *
        (-1) ^ ((b + d + c) / 2) * (-1) ^ ((b + e + f) / 2) = (-1) ^ ((e + d + q) / 2) := by
      rw [← pow_add, ← pow_add]
      exact neg_one_pow_eq_of_mod (by unfold Triad at *; omega)
    rw [← hsign]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  · intro x _ hx
    rw [sixJSym_zero_left, ite_eq_right (fun h => hx h.1)]
    ring
  · intro h
    simp at h

/-! ## The case `p = 0` -/

/-- One term of the `p = 0` case: a constant times the orthogonality summand. -/
lemma be_p_zero_term {a b e f q r x : ℕ} :
    (-1 : ℝ) ^ ((a + b + b + a + e + f + 0 + q + r + x) / 2) * ((x : ℝ) + 1) *
        ((if a = a ∧ b = b ∧ Triad a b x then
            (-1) ^ ((a + b + x) / 2) / (Real.sqrt ((a : ℝ) + 1) * Real.sqrt ((b : ℝ) + 1)) else 0) *
          sixJSym b a x e f q * sixJSym e f x b a r) =
      (-1) ^ ((a + b + e + f + q + r) / 2) /
          (((q : ℝ) + 1) * (Real.sqrt ((a : ℝ) + 1) * Real.sqrt ((b : ℝ) + 1))) *
        (((x : ℝ) + 1) * ((q : ℝ) + 1) * (sixJSym b a x e f q * sixJSym b a x e f r)) := by
  rw [sj_flip12 b a x e f r]
  by_cases hq : sixJSym b a x e f q = 0
  · rw [hq]; ring
  by_cases hr : sixJSym b a x e f r = 0
  · rw [hr]; ring
  obtain ⟨⟨p1, -, -, -⟩, ⟨p2, -, -, -⟩, -, ⟨p4, -, -, -⟩⟩ := triad_of_sixJSym_ne_zero hq
  obtain ⟨T1, ⟨p5, -, -, -⟩, -, -⟩ := triad_of_sixJSym_ne_zero hr
  have hab : Triad a b x := by unfold Triad at T1 ⊢; omega
  rw [ite_eq_left ⟨rfl, rfl, hab⟩]
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have ha0 : 0 < Real.sqrt ((a : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hb0 : 0 < Real.sqrt ((b : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsign : (-1 : ℝ) ^ ((a + b + b + a + e + f + 0 + q + r + x) / 2) * (-1) ^ ((a + b + x) / 2) =
      (-1) ^ ((a + b + e + f + q + r) / 2) := by
    rw [← pow_add]
    exact neg_one_pow_eq_of_mod (by omega)
  rw [← hsign]
  field_simp

/-- **Biedenharn–Elliott with `p = 0`**, for `b, e > 0` (through 6j orthogonality). -/
theorem be_p_zero {a b c d e f q r : ℕ} (hb : 0 < b) (he : 0 < e) :
    beLHS a b c d e f 0 q r = beRHS a b c d e f 0 q r := by
  unfold beLHS beRHS
  rw [sixJSym_zero_left q r e a d, sixJSym_zero_left q r f b c]
  have hz : ∀ x, sixJSym a b x c d 0 = sixJSym 0 d a x b c := fun x =>
    (sj_swap13 a b x c d 0).symm.trans (sj_flip12 x b a 0 d c).symm
  simp only [hz, sixJSym_zero_left d a _ b c]
  by_cases hda : d = a
  swap
  · rw [ite_eq_right (show ¬(r = q ∧ d = a ∧ Triad q a e) from fun h => hda h.2.1), zero_mul]
    refine sum_eq_zero fun x _ => ?_
    rw [ite_eq_right (show ¬(a = d ∧ c = b ∧ Triad d b x) from fun h => hda h.1.symm)]
    ring
  by_cases hcb : c = b
  swap
  · rw [ite_eq_right (show ¬(r = q ∧ c = b ∧ Triad q b f) from fun h => hcb h.2.1), mul_zero]
    refine sum_eq_zero fun x _ => ?_
    rw [ite_eq_right (show ¬(a = d ∧ c = b ∧ Triad d b x) from fun h => hcb h.2.1)]
    ring
  subst d c
  rw [sum_congr rfl fun x _ => be_p_zero_term, ← mul_sum, add_comm a b, sixJSym_orth hb he]
  by_cases hc : q = r ∧ Triad a e q ∧ Triad b q f
  · obtain ⟨rfl, h1, h2⟩ := hc
    rw [ite_eq_left ⟨rfl, h1, h2⟩,
      ite_eq_left ⟨rfl, rfl, by unfold Triad at h1 ⊢; omega⟩,
      ite_eq_left ⟨rfl, rfl, by unfold Triad at h2 ⊢; omega⟩]
    have hq0 : 0 < Real.sqrt ((q : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have ha0 : 0 < Real.sqrt ((a : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hb0 : 0 < Real.sqrt ((b : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsign : (-1 : ℝ) ^ ((b + a + e + f + q + q) / 2) =
        (-1) ^ ((q + a + e) / 2) * (-1) ^ ((q + b + f) / 2) := by
      rw [← pow_add]
      exact neg_one_pow_eq_of_mod (by unfold Triad at h1 h2; omega)
    rw [hsign]
    field_simp
    rw [Real.sq_sqrt (by positivity)]
  · rw [ite_eq_right hc, mul_zero]
    by_cases hqr : r = q
    · subst hqr
      by_cases h1 : Triad r a e
      · rw [ite_eq_left ⟨rfl, rfl, h1⟩, ite_eq_right (fun h => hc ⟨rfl, by unfold Triad at h1 ⊢; omega,
          by obtain ⟨-, -, h2⟩ := h; unfold Triad at h2 ⊢; omega⟩), mul_zero]
      · rw [ite_eq_right (fun h => h1 h.2.2), zero_mul]
    · rw [ite_eq_right (fun h => hqr h.1), zero_mul]

/-- Transfer an identity along a symmetry of both sides. -/
lemma be_of_symm {L L' R R' : ℝ} (hL : L' = L) (hR : R' = R) (h : L' = R') : L = R := by
  rw [← hL, ← hR, h]

end PhyslibAlpha.Sl2.Pentagon

namespace PhyslibAlpha.Sl2

open Pentagon

/-- **The Biedenharn–Elliott identity**, for all spins (doubled units). Proof:
* a zero among `a, b, c, d, e, f` is moved to `a` by the symmetries of the identity and handled by
  `be_a_zero`;
* with all of these positive, a zero in `p` (or in `r`, after `B ↔ C`) is `be_p_zero`;
* otherwise all of `a, b, c, e, p, r` are positive and `biedenharnElliott_pos` (the recoupling
  pentagon) applies. -/
theorem biedenharnElliott (a b c d e f p q r : ℕ) :
    beLHS a b c d e f p q r = beRHS a b c d e f p q r := by
  by_cases ha : a = 0
  · subst ha; exact be_a_zero b c d e f p q r
  by_cases hb : b = 0
  · subst hb
    obtain ⟨hL, hR⟩ := be_swapDE a 0 c d e f p q r
    exact be_of_symm hL hR (be_a_zero a d c f e p q r)
  by_cases hc : c = 0
  · subst hc
    obtain ⟨h1L, h1R⟩ := be_swapAB a b 0 d e f p q r
    obtain ⟨h2L, h2R⟩ := be_swapDE d 0 b a e f p r q
    exact be_of_symm h1L h1R (be_of_symm h2L h2R (be_a_zero d a b f e p r q))
  by_cases hd : d = 0
  · subst hd
    obtain ⟨hL, hR⟩ := be_swapAB a b c 0 e f p q r
    exact be_of_symm hL hR (be_a_zero c b a e f p r q)
  by_cases he : e = 0
  · subst he
    obtain ⟨hL, hR⟩ := be_swapAC a b c d 0 f p q r
    exact be_of_symm hL hR (be_a_zero f c d a b q p r)
  by_cases hf : f = 0
  · subst hf
    obtain ⟨h1L, h1R⟩ := be_swapAC a b c d e 0 p q r
    obtain ⟨h2L, h2R⟩ := be_swapDE e 0 c d a b q p r
    exact be_of_symm h1L h1R (be_of_symm h2L h2R (be_a_zero e d c b a q p r))
  by_cases hp : p = 0
  · subst hp
    exact be_p_zero (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero he)
  by_cases hr : r = 0
  · subst hr
    obtain ⟨hL, hR⟩ := be_swapBC a b c d e f p q 0
    exact be_of_symm hL hR (be_p_zero (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hd))
  exact biedenharnElliott_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
    (Nat.pos_of_ne_zero hc) (Nat.pos_of_ne_zero he) (Nat.pos_of_ne_zero hp) (Nat.pos_of_ne_zero hr)

end PhyslibAlpha.Sl2
