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

/-- `a((bc)d)` with channels `f` (for `b, c`), `h` (for `bc, d`), `i` (total). -/
noncomputable def TC (q : kˣ) (a b c d f h i : ℕ) : Module.End k (ModelSpace k) :=
  sh a (UL q b c d f h) * Vop q a (b + c - 2 * f + d - 2 * h) i

/-- `a(b(cd))` as a translate of a three-block right tree times the root vertex. -/
theorem TD_eq_sh_UR (q : kˣ) (a b c d j m i : ℕ) :
    TD q a b c d j m i = sh a (UR q b c d j m) * Vop q a (b + (c + d - 2 * j) - 2 * m) i := by
  simp only [TD, UR]

/-- **`a(b(cd))` in the basis `a((bc)d)`** (the arrow `D → C` of the pentagon). -/
theorem TD_expand_C [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c d j m i : ℕ) (hb : 1 ≤ b)
    (hd : ∀ x, x ≤ a + b + c + d → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + c + d + 1 → (q : k) ^ (2 * x) ≠ 1)
    (hjc : j ≤ c) (hjd : j ≤ d) (hmb : m ≤ b) (hmz : m ≤ c + d - 2 * j) :
    TD q a b c d j m i = ∑ f ∈ Finset.range (b + 1), ∑ h ∈ Finset.range (d + 1),
      Fc q b c d f h j m • TC q a b c d f h i := by
  rw [TD_eq_sh_UR, expansion_range q hδ b c d j m (by omega) (fun x hx => hd x (by omega))
    (fun x h1 h2 => hq2 x h1 (by omega)) hjc hjd hmb hmz, sh_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [sh_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [sh_smul, smul_mul_assoc]
  by_cases h0 : Fc (k := k) q b c d f h j m = 0
  · rw [h0]; simp
  · rw [← Fc_total q hδ b c d f h j m (by omega) (fun x hx => hd x (by omega)) hjc hjd hmb hmz h0]
    simp only [TC]

/-- `a((bc)d)` as a left translate factor times a three-block right tree. -/
theorem TC_eq (q : kˣ) (a b c d f h i : ℕ) :
    TC q a b c d f h i = sh a (Vop q b c f) * UR q a (b + c - 2 * f) d h i := by
  simp only [TC, UL, UR, sh_mul, mul_assoc]

/-- `(a(bc))d` as the same left translate factor times a three-block left tree. -/
theorem TB_eq (q : kˣ) (a b c d f d' g : ℕ) :
    TB q a b c d f d' g = sh a (Vop q b c f) * UL q a (b + c - 2 * f) d d' g := by
  simp only [TB, UL, UR, mul_assoc]

/-- **`a((bc)d)` in the basis `(a(bc))d`** (the arrow `C → B` of the pentagon). -/
theorem TC_expand [CharZero k] (q : kˣ) (hδ : loopVal q ≠ 0) (a b c d f h i : ℕ) (ha : 1 ≤ a)
    (hd : ∀ x, x ≤ a + b + c + d → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + c + d + 1 → (q : k) ^ (2 * x) ≠ 1)
    (hfb : f ≤ b) (hfc : f ≤ c) (hhX : h ≤ b + c - 2 * f) (hhd : h ≤ d) (hia : i ≤ a)
    (hiz : i ≤ b + c - 2 * f + d - 2 * h) :
    TC q a b c d f h i = ∑ d' ∈ Finset.range (a + 1), ∑ g ∈ Finset.range (d + 1),
      Fc q a (b + c - 2 * f) d d' g h i • TB q a b c d f d' g := by
  rw [TC_eq, expansion_range q hδ a (b + c - 2 * f) d h i (by omega) (fun x hx => hd x (by omega))
    (fun x h1 h2 => hq2 x h1 (by omega)) hhX hhd hia (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_smul_comm, TB_eq]

/-- **Pairing of `ULd4` with a two-level sum of `UL4`s** at fixed last channel `g`: it extracts the coefficient
of the `(e₀, d₀)` term. -/
theorem pair_UL4 [CharZero k] (q : kˣ) (a b c d e₀ d₀ g₀ g : ℕ) (r₁ : ℕ) (r₂ : ℕ → ℕ) (C : ℕ → ℕ → k)
    (hd : ∀ x, x ≤ a + b + c + d → chebD (loopVal q) x ≠ 0)
    (hq2 : ∀ x, 1 ≤ x → x ≤ a + b + c + d + 1 → (q : k) ^ (2 * x) ≠ 1)
    (hC : ∀ e d₁, C e d₁ ≠ 0 → e ≤ min a b ∧ d₁ ≤ min (a + b - 2 * e) c)
    (he₀ : e₀ ≤ min a b) (hd₀ : d₀ ≤ min (a + b - 2 * e₀) c) (hg₀ : g₀ ≤ a + b - 2 * e₀ + c - 2 * d₀ ∧ g₀ ≤ d)
    (hg : C e₀ d₀ ≠ 0 → g ≤ a + b - 2 * e₀ + c - 2 * d₀ ∧ g ≤ d)
    (h1 : e₀ < r₁) (h2 : d₀ < r₂ e₀) :
    ULd4 q a b c d e₀ d₀ g₀ * ∑ e ∈ Finset.range r₁, ∑ d₁ ∈ Finset.range (r₂ e), C e d₁ • UL4 q a b c d e d₁ g =
      if g₀ = g then (C e₀ d₀ * (kapRec q a b e₀ * kapRec q (a + b - 2 * e₀) c d₀ *
        kapRec q (a + b - 2 * e₀ + c - 2 * d₀) d g₀)) • jwAt q 0 (a + b - 2 * e₀ + c - 2 * d₀ + d - 2 * g₀) else 0 := by
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single e₀]
  · rw [Finset.mul_sum, Finset.sum_eq_single d₀]
    · rw [mul_smul_comm]
      by_cases h0 : C e₀ d₀ = 0
      · simp [h0]
      · obtain ⟨hga, hgd⟩ := hg h0
        rw [ULd4_mul_UL4_diag q a b c d e₀ d₀ g₀ g hd (he₀.trans (min_le_left _ _)) (he₀.trans (min_le_right _ _))
          (hd₀.trans (min_le_left _ _)) (hd₀.trans (min_le_right _ _)) hg₀.1 hg₀.2 hga hgd hq2]
        split_ifs with hgg
        · rw [smul_smul]
        · simp
    · intro d₁ hd₁ hne
      rw [mul_smul_comm]
      by_cases h0 : C e₀ d₁ = 0
      · simp [h0]
      · have hv := hC e₀ d₁ h0
        have hz : ULd4 q a b c d e₀ d₀ g₀ * UL4 q a b c d e₀ d₁ g = 0 := by
          unfold ULd4 UL4
          have h3 := ULd_mul_UL (k := k) q a b c (fun x hx => hd x (by omega)) (fun x h1 h2 => hq2 x h1 (by omega))
            (e := e₀) (d := d₀) (e' := e₀) (d' := d₁) (he₀.trans (min_le_left _ _)) (he₀.trans (min_le_right _ _))
            (he₀.trans (min_le_left _ _)) (he₀.trans (min_le_right _ _)) (hd₀.trans (min_le_left _ _))
            (hd₀.trans (min_le_right _ _)) (hv.2.trans (min_le_left _ _)) (hv.2.trans (min_le_right _ _))
          rw [if_neg (fun h => hne h.2.symm)] at h3
          calc _ = Wop q (a + b - 2 * e₀ + c - 2 * d₀) d g₀ * (ULd q a b c e₀ d₀ * UL q a b c e₀ d₁) *
                Vop q (a + b - 2 * e₀ + c - 2 * d₁) d g := by simp only [mul_assoc]
            _ = 0 := by rw [h3]; simp
        rw [hz, smul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr h2) h
  · intro e he hne
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun d₁ _ => ?_
    rw [mul_smul_comm]
    by_cases h0 : C e d₁ = 0
    · simp [h0]
    · have hv := hC e d₁ h0
      have hz : ULd4 q a b c d e₀ d₀ g₀ * UL4 q a b c d e d₁ g = 0 := by
        unfold ULd4 UL4
        have h3 := ULd_mul_UL (k := k) q a b c (fun x hx => hd x (by omega)) (fun x h1 h2 => hq2 x h1 (by omega))
          (e := e₀) (d := d₀) (e' := e) (d' := d₁) (he₀.trans (min_le_left _ _)) (he₀.trans (min_le_right _ _))
          (hv.1.trans (min_le_left _ _)) (hv.1.trans (min_le_right _ _)) (hd₀.trans (min_le_left _ _))
          (hd₀.trans (min_le_right _ _)) (hv.2.trans (min_le_left _ _)) (hv.2.trans (min_le_right _ _))
        rw [if_neg (fun h => hne h.1.symm)] at h3
        calc _ = Wop q (a + b - 2 * e₀ + c - 2 * d₀) d g₀ * (ULd q a b c e₀ d₀ * UL q a b c e d₁) *
              Vop q (a + b - 2 * e + c - 2 * d₁) d g := by simp only [mul_assoc]
          _ = 0 := by rw [h3]; simp
      rw [hz, smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr h1) h

end Lightlike.TemperleyLieb
