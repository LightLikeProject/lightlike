import Mathlib
import Lightlike.TemperleyLieb.Mirror
import Lightlike.TemperleyLieb.CupCap
import Lightlike.TemperleyLieb.Reduction
import Lightlike.TemperleyLieb.Expansion
import Lightlike.TemperleyLieb.Pentagon
import Lightlike.TemperleyLieb.FusionIdentity

/-!
# The mirror image of caps and cups

The reflection `reflectOp N` (`Mirror.lean`) reverses and flips the first `N` bits. A cap at the positions
`j, j+1` of a word with `j + j' + 2` letters is turned into the cap at the mirror positions `j', j'+1`
(`reflect_capOp`), and likewise for cups (`reflect_cupOp`): the cap and cup weights only see the pairs `01`
and `10`, which the reflection fixes. With `jwAt_mirror` these are the rules by which the mirror turns the
second-bracketing tree vectors of the blocks `(a, b, c)` into the first-bracketing ones of `(c, b, a)`.
-/

namespace Lightlike.TemperleyLieb

open Finsupp Finset

variable {k : Type*} [Field k]

lemma reflect_removeTwo (σ : ℕ → Bool) (j j' : ℕ) :
    removeTwo (reflect (j + j' + 2) σ) j' = reflect (j + j') (removeTwo σ j) := by
  funext n
  simp only [reflect, removeTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega) | (congr 1; omega)

lemma reflect_insertTwo (σ : ℕ → Bool) (j j' : ℕ) (x y : Bool) :
    reflect (j + j' + 2) (insertTwo σ j x y) = insertTwo (reflect (j + j') σ) j' (!y) (!x) := by
  funext n
  simp only [reflect, insertTwo]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega) | (congr 1; omega)

lemma capWeight_reflect (q : kˣ) (x y : Bool) : capWeight q (!y) (!x) = capWeight q x y := by
  cases x <;> cases y <;> rfl

/-- **The mirror of a cap**: `R_{j+j'} cap_j = cap_{j'} R_{j+j'+2}`. -/
theorem reflect_capOp (q : kˣ) (j j' : ℕ) :
    reflectOp k (j + j') * capOp q j = capOp q j' * reflectOp k (j + j' + 2) := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, reflectOp_single, capOp_single, capBasis, one_smul, reflectOp_single]
  rw [reflect_removeTwo, reflect_apply_lo σ j j', reflect_apply_hi σ j j', capWeight_reflect]

/-- **The mirror of a cup**: `R_{j+j'+2} cup_j = cup_{j'} R_{j+j'}`. -/
theorem reflect_cupOp (q : kˣ) (j j' : ℕ) :
    reflectOp k (j + j' + 2) * cupOp q j = cupOp q j' * reflectOp k (j + j') := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, reflectOp_single, cupOp_single, cupBasis, one_smul, map_sub, map_smul]
  rw [reflect_insertTwo, reflect_insertTwo]
  rfl

/-- The mirror of a projector, as a commutation: `R_{s+s'+m} p_{[s,s+m)} = p_{[s',s'+m)} R_{s+s'+m}`. -/
theorem reflect_jwAt (q : kˣ) (s s' m : ℕ) (hd : ∀ j, j < m → chebD (loopVal q) j ≠ 0) :
    reflectOp k (s + s' + m) * jwAt q s m = jwAt q s' m * reflectOp k (s + s' + m) := by
  rw [jwAt_mirror q s s' m hd, mul_assoc, mul_assoc, reflectOp_mul_self, mul_one]

/-- **The mirror of nested cups**: `R_{n+2i} nestCup_l^i = nestCup_{n-l}^i R_n` for `l ≤ n`. -/
theorem reflect_nestCup (q : kˣ) {l n : ℕ} (hl : l ≤ n) : ∀ i,
    reflectOp k (n + 2 * i) * nestCup q l i = nestCup q (n - l) i * reflectOp k n
  | 0 => by simp [nestCup]
  | i + 1 => by
    have hc := reflect_cupOp (k := k) q (l + i) (n - l + i)
    rw [show l + i + (n - l + i) + 2 = n + 2 * (i + 1) by omega, show l + i + (n - l + i) = n + 2 * i by omega] at hc
    simp only [nestCup]
    rw [← mul_assoc, hc, mul_assoc, reflect_nestCup q hl i, ← mul_assoc]

/-- **The mirror of the second-bracketing tree vector** of the blocks `(a, b, c)` is the first-bracketing one
of `(c, b, a)`: `R_{a+b+c} U_R(a,b,c;f,d') = U_L(c,b,a;f,d') R_D`. -/
theorem reflect_UR (q : kˣ) (a b c f d' : ℕ) (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f)
    (hd : ∀ j, j < a + b + c + 1 → chebD (loopVal q) j ≠ 0) :
    reflectOp k (a + b + c) * UR q a b c f d' = UL q c b a f d' * reflectOp k (a + (b + c - 2 * f) - 2 * d') := by
  unfold UR UL Vop Qab
  simp only [sh_mul, sh_jwAt, sh_nestCup, Nat.zero_add, mul_assoc]
  set Y := b + c - 2 * f with hY
  set D := a + Y - 2 * d' with hD
  rw [show c + b - 2 * f = Y by omega, show Y + a - 2 * d' = D by omega]
  have hd' : ∀ m, m ≤ a + b + c → ∀ j, j < m → chebD (loopVal q) j ≠ 0 := fun m hm j hj => hd j (by omega)
  have push : ∀ {n n' : ℕ} {X X' : Module.End k (ModelSpace k)},
      reflectOp k n * X = X' * reflectOp k n' → ∀ T, reflectOp k n * (X * T) = X' * (reflectOp k n' * T) :=
    fun h T => by rw [← mul_assoc, h, mul_assoc]
  have h1 : reflectOp k (a + b + c) * jwAt q a b = jwAt q c b * reflectOp k (a + b + c) := by
    have := reflect_jwAt (k := k) q a c b (hd' b (by omega)); rwa [show a + c + b = a + b + c by omega] at this
  have h2 : reflectOp k (a + b + c) * jwAt q (b + a) c = jwAt q 0 c * reflectOp k (a + b + c) := by
    have := reflect_jwAt (k := k) q (b + a) 0 c (hd' c (by omega)); rwa [show b + a + 0 + c = a + b + c by omega] at this
  have h3 : reflectOp k (a + b + c) * nestCup q (b - f + a) f = nestCup q (c - f) f * reflectOp k (a + Y) := by
    have := reflect_nestCup (k := k) q (l := b - f + a) (n := a + Y) (by omega) f
    rwa [show a + Y + 2 * f = a + b + c by omega, show a + Y - (b - f + a) = c - f by omega] at this
  have h4 : reflectOp k (a + Y) * jwAt q a Y = jwAt q 0 Y * reflectOp k (a + Y) := by
    have := reflect_jwAt (k := k) q a 0 Y (hd' Y (by omega)); rwa [show a + 0 + Y = a + Y by omega] at this
  have h5 : reflectOp k (a + Y) * jwAt q 0 a = jwAt q Y a * reflectOp k (a + Y) := by
    have := reflect_jwAt (k := k) q 0 Y a (hd' a (by omega)); rwa [show 0 + Y + a = a + Y by omega] at this
  have h6 : reflectOp k (a + Y) * nestCup q (a - d') d' = nestCup q (Y - d') d' * reflectOp k D := by
    have := reflect_nestCup (k := k) q (l := a - d') (n := D) (by omega) d'
    rwa [show D + 2 * d' = a + Y by omega, show D - (a - d') = Y - d' by omega] at this
  have r7 : reflectOp k D * jwAt q 0 D = jwAt q 0 D * reflectOp k D := by
    have := reflect_jwAt (k := k) q 0 0 D (hd' D (by omega)); rwa [show 0 + 0 + D = D by omega] at this
  have r1 := push h1
  have r2 := push h2
  have r3 := push h3
  have r4 := push h4
  have r5 := push h5
  have r6 := push h6
  simp only [r1, r2, r3, r4, r5, r6, r7]
  have c1 : (jwAt q c b : Module.End k (ModelSpace k)) * jwAt q 0 c = jwAt q 0 c * jwAt q c b :=
    (jwAt_comm_far q (by omega)).symm
  have c2 : (jwAt q 0 Y : Module.End k (ModelSpace k)) * jwAt q Y a = jwAt q Y a * jwAt q 0 Y :=
    jwAt_comm_far q (by omega)
  rw [← mul_assoc (jwAt q c b), c1, mul_assoc]
  congr 3
  rw [← mul_assoc (jwAt q Y a), ← c2, mul_assoc]
/-- The mirror of a first-bracketing tree vector: `R_{a+b+c} U_L(a,b,c;e,d) = U_R(c,b,a;e,d) R_{D}`. -/
theorem reflect_UL (q : kˣ) (a b c e d : ℕ) (heb : e ≤ b) (hea : e ≤ a) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hd : ∀ j, j < a + b + c + 1 → chebD (loopVal q) j ≠ 0) :
    reflectOp k (a + b + c) * UL q a b c e d = UR q c b a e d * reflectOp k (a + b - 2 * e + c - 2 * d) := by
  have h := reflect_UR (k := k) q c b a e d heb hea hdc (by omega) (fun j hj => hd j (by omega))
  rw [show c + b + a = a + b + c by omega, show c + (b + a - 2 * e) - 2 * d = a + b - 2 * e + c - 2 * d by omega] at h
  have hρ := reflectOp_mul_self (k := k) (a + b + c)
  have hρ' := reflectOp_mul_self (k := k) (a + b - 2 * e + c - 2 * d)
  calc reflectOp k (a + b + c) * UL q a b c e d
      = reflectOp k (a + b + c) * (UL q a b c e d * reflectOp k (a + b - 2 * e + c - 2 * d)) *
          reflectOp k (a + b - 2 * e + c - 2 * d) := by rw [mul_assoc, mul_assoc, hρ', mul_one]
    _ = UR q c b a e d * reflectOp k (a + b - 2 * e + c - 2 * d) := by
        rw [← h, ← mul_assoc, hρ, one_mul]

/-- `gramCoef = κ κ Fc` on the admissible `(e, d)`. -/
lemma gramCoef_eq_kap_mul_Fc (q : kˣ) {a b c e d f d' : ℕ} (he : e ≤ min a b) (hdd : d ≤ min (a + b - 2 * e) c)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1) :
    gramCoef q a b c e d f d' = kapRec q a b e * kapRec q (a + b - 2 * e) c d * Fc q a b c e d f d' := by
  have k1 := kapRec_ne (k := k) q e a b (he.trans (min_le_left _ _)) (he.trans (min_le_right _ _))
    (fun x h1 h2 => hq2 x h1 (by omega))
  have k2 := kapRec_ne (k := k) q d (a + b - 2 * e) c (hdd.trans (min_le_left _ _)) (hdd.trans (min_le_right _ _))
    (fun x h1 h2 => hq2 x h1 (by omega))
  unfold Fc; rw [if_pos ⟨he, hdd⟩]; field_simp

/-- **The mirror inverse**: the recoupling matrices of `(a, b, c)` and `(c, b, a)` are inverse to each other. -/
theorem Fc_mirror_inv [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) {a b c f d' g h : ℕ}
    (hab : 1 ≤ a + b) (hcb : 1 ≤ c + b)
    (hd : ∀ j, j ≤ a + b + c + 1 → chebD (loopVal q) j ≠ 0)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + c + 1 → (q : k) ^ (2 * j) ≠ 1)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f)
    (hgc : g ≤ c) (hgb : g ≤ b) (hhA : h ≤ c + b - 2 * g) (hha : h ≤ a) :
    ∑ e ∈ range (a + 1), ∑ d ∈ range (c + 1), Fc q c b a g h e d * Fc q a b c e d f d' =
      if g = f ∧ h = d' then 1 else 0 := by
  set D := a + (b + c - 2 * f) - 2 * d' with hD
  have hd1 : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hE := expansion_range q hδ a b c f d' hab hd1 hq2 hfb hfc hda hdf
  have hterm : ∀ e ∈ range (a + 1), ∀ d ∈ range (c + 1),
      reflectOp k (a + b + c) * (Fc q a b c e d f d' • UL q a b c e d) =
        (Fc q a b c e d f d' • UR q c b a e d) * reflectOp k D := by
    intro e _ d _
    by_cases h0 : Fc q a b c e d f d' = 0
    · simp [h0]
    · obtain ⟨he, hdd⟩ := Fc_guard h0
      have ht := Fc_total q hδ a b c e d f d' (by omega) hd1 hfb hfc hda hdf h0
      rw [mul_smul_comm, reflect_UL q a b c e d (he.trans (min_le_right _ _)) (he.trans (min_le_left _ _))
        (hdd.trans (min_le_right _ _)) (hdd.trans (min_le_left _ _)) (fun j hj => hd j (by omega)), ht,
        smul_mul_assoc]
  have hM := reflect_UR (k := k) q a b c f d' hfb hfc hda hdf (fun j hj => hd j (by omega))
  rw [hE] at hM
  simp only [mul_sum] at hM
  rw [sum_congr rfl fun e he => sum_congr rfl fun d hdm => hterm e he d hdm] at hM
  simp only [← sum_mul] at hM
  have hUL : UL q c b a f d' = ∑ e ∈ range (a + 1), ∑ d ∈ range (c + 1), Fc q a b c e d f d' • UR q c b a e d := by
    have := congrArg (· * reflectOp k D) hM
    rw [← hD] at this
    simp only [mul_assoc, reflectOp_mul_self, mul_one] at this
    exact this.symm
  have hq2' : ∀ j, 1 ≤ j → j ≤ c + b + a + 1 → (q : k) ^ (2 * j) ≠ 1 := fun j h1 h2 => hq2 j h1 (by omega)
  have hL := ULd_mul_UL q c b a (fun j hj => hd j (by omega)) hq2' (e := g) (d := h) (e' := f) (d' := d')
    hgc hgb hfc hfb hhA hha (by omega) hda
  set K := kapRec q c b g * kapRec q (c + b - 2 * g) a h with hK
  have hKne : K ≠ 0 := mul_ne_zero (kapRec_ne q g c b hgc hgb (fun x h1 h2 => hq2' x h1 (by omega)))
    (kapRec_ne q h (c + b - 2 * g) a hhA hha (fun x h1 h2 => hq2' x h1 (by omega)))
  have hpair : ∀ e ∈ range (a + 1), ∀ d ∈ range (c + 1),
      ULd q c b a g h * (Fc q a b c e d f d' • UR q c b a e d) =
        (K * (Fc q c b a g h e d * Fc q a b c e d f d')) • jwAt q 0 (c + b - 2 * g + a - 2 * h) := by
    intro e _ d _
    by_cases h0 : Fc q a b c e d f d' = 0
    · simp [h0]
    · obtain ⟨he, hdd⟩ := Fc_guard h0
      rw [mul_smul_comm, gram_spec q hδ c b a g h e d (by omega) (fun j hj => hd j (by omega)) hgc hgb
        (he.trans (min_le_right _ _)) (he.trans (min_le_left _ _)) hha hhA (hdd.trans (min_le_right _ _))
        (by have := hdd.trans (min_le_left _ _); omega), gramCoef_eq_kap_mul_Fc q (le_min hgc hgb) (le_min hhA hha)
        hq2', smul_smul]
      congr 1; ring
  rw [hUL, mul_sum] at hL
  simp only [mul_sum] at hL
  rw [sum_congr rfl fun e he => sum_congr rfl fun d hdm => hpair e he d hdm] at hL
  simp only [← sum_smul, ← mul_sum] at hL
  have hp := jwAt_ne_zero (k := k) q (c + b - 2 * g + a - 2 * h)
  by_cases hgf : g = f ∧ h = d'
  · rw [if_pos hgf] at hL ⊢
    have h3 : (K * ∑ e ∈ range (a + 1), ∑ d ∈ range (c + 1), Fc q c b a g h e d * Fc q a b c e d f d' - K) •
        (jwAt q 0 (c + b - 2 * g + a - 2 * h) : Module.End k (ModelSpace k)) = 0 :=
      (sub_smul _ _ (jwAt q 0 (c + b - 2 * g + a - 2 * h) : Module.End k (ModelSpace k))).trans (sub_eq_zero.mpr hL)
    have := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hp)
    field_simp at this ⊢
    linear_combination this
  · rw [if_neg hgf] at hL ⊢
    have := (smul_eq_zero.mp hL).resolve_right hp
    exact (mul_eq_zero.mp this).resolve_left hKne

end Lightlike.TemperleyLieb
