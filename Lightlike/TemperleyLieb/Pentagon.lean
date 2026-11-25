import Mathlib
import Lightlike.TemperleyLieb.Expansion
import Lightlike.TemperleyLieb.ShiftComm

/-!
# The five bracketings of four blocks and the relations between them

`TA = ((ab)c)d`, `TB = (a(bc))d`, `TC = a((bc)d)`, `TD = a(b(cd))`, `TE = (ab)(cd)`.
Each arrow of the pentagon is one `expansion` (the `F`-move on three blocks), multiplied by a fixed
operator on the left or on the right.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- `(ab)(cd)` with channels `e` (for `a, b`), `j` (for `c, d`), `g` (total). -/
noncomputable def TE (q : kˣ) (a b c d e j g : ℕ) : Module.End k (ModelSpace k) :=
  Vop q a b e * sh (a + b - 2 * e) (Vop q c d j) * Vop q (a + b - 2 * e) (c + d - 2 * j) g

/-- `UL4` as a left factor times a three-block left tree. -/
theorem UL4_eq (q : kˣ) (a b c d e d₁ g : ℕ) :
    UL4 q a b c d e d₁ g = Vop q a b e * UL q (a + b - 2 * e) c d d₁ g := by
  simp only [UL4, UL, mul_assoc]

/-- A left factor times a three-block right tree. -/
theorem TE_eq_mul_UR (q : kˣ) (a b c d e j g : ℕ) :
    TE q a b c d e j g = Vop q a b e * UR q (a + b - 2 * e) c d j g := by
  simp only [TE, UR, mul_assoc]

/-- **`(ab)(cd)` in the basis `((ab)c)d`** (the arrow `E → A` of the pentagon). -/
theorem TE_expand [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c d e j g : ℕ) (hc : 1 ≤ c)
    (hd : ∀ i, i ≤ a + b + c + d → chebD (loopVal q) i ≠ 0)
    (hq2 : ∀ i, 1 ≤ i → i ≤ a + b + c + d + 1 → (q : k) ^ (2 * i) ≠ 1)
    (hea : e ≤ a) (heb : e ≤ b) (hjc : j ≤ c) (hjd : j ≤ d)
    (hga : g ≤ a + b - 2 * e) (hgf : g ≤ c + d - 2 * j) :
    TE q a b c d e j g = ∑ d₁ ∈ Finset.range (a + b - 2 * e + 1), ∑ g' ∈ Finset.range (d + 1),
      Fc q (a + b - 2 * e) c d d₁ g' j g • UL4 q a b c d e d₁ g' := by
  rw [TE_eq_mul_UR, expansion_range q hδ (a + b - 2 * e) c d j g (by omega)
    (fun i hi => hd i (by omega)) (fun i h1 h2 => hq2 i h1 (by omega)) hjc hjd hga hgf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g' _ => ?_
  rw [UL4_eq, mul_smul_comm]

/-- `a(b(cd))` with channels `j` (for `c, d`), `k` (for `b, cd`), `i` (total). -/
noncomputable def TD (q : kˣ) (a b c d j m i : ℕ) : Module.End k (ModelSpace k) :=
  sh a (sh b (Vop q c d j) * Vop q b (c + d - 2 * j) m) * Vop q a (b + (c + d - 2 * j) - 2 * m) i

/-- `a(b(cd))` as a translate of `cd` times a three-block right tree. -/
theorem TD_eq_mul_UR (q : kˣ) (a b c d j m i : ℕ) :
    TD q a b c d j m i = sh (a + b) (Vop q c d j) * UR q a b (c + d - 2 * j) m i := by
  simp only [TD, UR, sh_mul, sh_sh, mul_assoc]

/-- A non-zero `Fc` has admissible indices. -/
theorem Fc_guard {q : kˣ} {a b c e d f d' : ℕ} (h : Fc (k := k) q a b c e d f d' ≠ 0) :
    e ≤ min a b ∧ d ≤ min (a + b - 2 * e) c := by
  by_contra hc
  exact h (by simp only [Fc, if_neg hc])

/-- `(ab)(cd)` as a translate of `cd` times a three-block left tree. -/
theorem TE_eq_mul_UL (q : kˣ) {a b e : ℕ} (c d j g : ℕ) (hea : e ≤ a) (heb : e ≤ b) :
    TE q a b c d e j g = sh (a + b) (Vop q c d j) * UL q a b (c + d - 2 * j) e g := by
  unfold TE UL
  rw [mul_assoc, ← mul_assoc (Vop q a b e), Vop_comm_sh q hea heb]
  simp only [mul_assoc]

/-- **`a(b(cd))` in the basis `(ab)(cd)`** (the arrow `D → E` of the pentagon). -/
theorem TD_expand [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c d j m i : ℕ) (hab : 1 ≤ a + b)
    (hd : ∀ x, x ≤ a + b + c + d → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + c + d + 1 → (q : k) ^ (2 * x) ≠ 1)
    (hjc : j ≤ c) (hjd : j ≤ d) (hkb : m ≤ b) (hkz : m ≤ c + d - 2 * j) (hia : i ≤ a)
    (hiz : i ≤ b + (c + d - 2 * j) - 2 * m) :
    TD q a b c d j m i = ∑ e ∈ Finset.range (a + 1), ∑ g ∈ Finset.range (c + d - 2 * j + 1),
      Fc q a b (c + d - 2 * j) e g m i • TE q a b c d e j g := by
  rw [TD_eq_mul_UR, expansion_range q hδ a b (c + d - 2 * j) m i hab (fun x hx => hd x (by omega))
    (fun x h1 h2 => hq2 x h1 (by omega)) hkb hkz hia hiz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_smul_comm]
  by_cases h0 : Fc (k := k) q a b (c + d - 2 * j) e g m i = 0
  · rw [h0]; simp
  · have hg := Fc_guard h0
    rw [TE_eq_mul_UL q c d j g (hg.1.trans (min_le_left _ _)) (hg.1.trans (min_le_right _ _))]

/-- The Gram coefficient vanishes between different total channels. -/
theorem gramCoef_zero_of_ne (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d f d' : ℕ) (hN : 1 ≤ a + b + c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hea : e ≤ a) (heb : e ≤ b) (hfb : f ≤ b) (hfc : f ≤ c) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f)
    (hne : a + b - 2 * e + c - 2 * d ≠ a + (b + c - 2 * f) - 2 * d') :
    gramCoef (k := k) q a b c e d f d' = 0 := by
  have h1 := gram_spec q hδ a b c e d f d' hN hd hea heb hfb hfc hdc hdA hda hdf
  have h2 : ULd q a b c e d * UR (k := k) q a b c f d' = 0 :=
    gram_vanish q hδ a b c e d f d' hN hd hea heb hfb hfc hdc hdA hda hdf hne
  rw [h2] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_right (jwAt_ne_zero q _)

/-- A non-zero `Fc` forces equal total channels. -/
theorem Fc_total (q : kˣ) (hδ : loopVal q ≠ 0) (a b c e d f d' : ℕ) (hN : 1 ≤ a + b + c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f)
    (h : Fc (k := k) q a b c e d f d' ≠ 0) :
    a + b - 2 * e + c - 2 * d = a + (b + c - 2 * f) - 2 * d' := by
  by_contra hne
  obtain ⟨he, hdd⟩ := Fc_guard h
  apply h
  have hz := gramCoef_zero_of_ne (k := k) q hδ a b c e d f d' hN hd (he.trans (min_le_left _ _))
    (he.trans (min_le_right _ _)) hfb hfc (hdd.trans (min_le_right _ _)) (hdd.trans (min_le_left _ _)) hda hdf hne
  simp only [Fc, hz, mul_zero, ite_self]

/-- `(a(bc))d` with channels `f` (for `b, c`), `d'` (for `a, bc`), `g` (total). -/
noncomputable def TB (q : kˣ) (a b c d f d' g : ℕ) : Module.End k (ModelSpace k) :=
  UR q a b c f d' * Vop q (a + (b + c - 2 * f) - 2 * d') d g

/-- **`(a(bc))d` in the basis `((ab)c)d`** (the arrow `B → A` of the pentagon). -/
theorem TB_expand [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c d f d' g : ℕ) (hab : 1 ≤ a + b)
    (hd : ∀ x, x ≤ a + b + c + d → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + c + d + 1 → (q : k) ^ (2 * x) ≠ 1)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f) :
    TB q a b c d f d' g = ∑ e ∈ Finset.range (a + 1), ∑ d₁ ∈ Finset.range (c + 1),
      Fc q a b c e d₁ f d' • UL4 q a b c d e d₁ g := by
  unfold TB
  rw [expansion_range q hδ a b c f d' hab (fun x hx => hd x (by omega))
    (fun x h1 h2 => hq2 x h1 (by omega)) hfb hfc hda hdf, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun d₁ _ => ?_
  rw [smul_mul_assoc]
  by_cases h0 : Fc (k := k) q a b c e d₁ f d' = 0
  · rw [h0]; simp
  · rw [← Fc_total q hδ a b c e d₁ f d' (by omega) (fun x hx => hd x (by omega)) hfb hfc hda hdf h0]
    simp only [UL4]

end Lightlike.TemperleyLieb
