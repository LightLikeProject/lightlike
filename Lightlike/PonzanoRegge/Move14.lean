module

public import Lightlike.PonzanoRegge.Unconditional

/-!
# The 1-4 Pachner move

The 1-4 move replaces a tetrahedron `ABCD` by the four tetrahedra `ABCE, ABDE, ACDE, BCDE` around
a new interior vertex `E`. It adds four edges `AE, BE, CE, DE` and six triangles.

**Main result.** Fix the spin `d` of the new edge `DE`. Summing the Ponzano–Regge weight over the
spins `a, b, c` of the other three new edges gives the old weight times `(2j_DE + 1)² = (d + 1)²`
(doubled units):

  `Σ_{a,b,c} weight(move14 K)(…, a, b, c, d) = (d + 1)² · weight K col`.

Summing `d` too gives the famous divergent vertex factor `Σ_d (d + 1)²`. The sums over `a, b, c`
are finite (triangle inequalities), the sum over `d` is not. **Regularisation:** cut off the spin
of one new edge per new vertex (`DE`, `d ≤ L`). Then the 1-4 move multiplies the amplitude by
the vertex factor `Λ_L = Σ_{d ≤ L} (d + 1)²` exactly (`amplitude_move14`).

**Proof.** Three steps:
1. The three tetrahedra around `AE` are the right-hand side of the 2-3 move for the triangle
   `BCD` (`pachner23_local`, with Biedenharn–Elliott, now proven). Summing `a` turns them into
   `{ABCD} · {BCDE}`.
2. `{BCDE}` now appears squared. All signs cancel, and 6j orthogonality sums `c`
   (`sixJSym_sq_orth`, valid for all spins, including zero).
3. The count `Σ_{b admissible} (b + 1) = (2j_BD + 1)(d + 1)` sums `b` (`sum_tri_succ`).

Independent check: `scripts/pr14_check.py`, exact on 20,480 colourings (old spins `≤ 3/2`,
`d ≤ 2`). The wrong factor `(2d+1)` and a dropped edge sign are both rejected.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.PR

/-! ## Pure 6j lemmas -/

/-- Two initial-segment sums agree when the summand vanishes beyond both. -/
lemma sum_range_eq_of_vanish {f : ℕ → ℝ} {m n : ℕ} (hm : ∀ x, m ≤ x → f x = 0)
    (hn : ∀ x, n ≤ x → f x = 0) : ∑ x ∈ range m, f x = ∑ x ∈ range n, f x := by
  rcases le_total m n with h | h
  · exact sum_subset (range_mono h) fun x _ hx => hm x (by simpa using hx)
  · exact (sum_subset (range_mono h) fun x _ hx => hn x (by simpa using hx)).symm

/-- A sum of squares of a "single-term" closed form. -/
lemma sum_sq_single (N y z q : ℕ) (T : Prop) [Decidable T] (s : ℝ) (hs : s ^ 2 = 1) :
    ∑ x ∈ range N, ((x : ℝ) + 1) *
      (if x = y ∧ q = z ∧ T then s / (Real.sqrt ((y : ℝ) + 1) * Real.sqrt ((z : ℝ) + 1))
        else 0) ^ 2 =
    if y < N ∧ q = z ∧ T then 1 / ((z : ℝ) + 1) else 0 := by
  by_cases hy : y < N
  · rw [sum_eq_single y]
    · by_cases h : q = z ∧ T
      · rw [ite_eq_left ⟨rfl, h⟩, ite_eq_left ⟨hy, h⟩, div_pow, hs, mul_pow,
          Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        field_simp
      · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right (fun h' => h h'.2)]
        ring
    · intro x _ hx
      rw [ite_eq_right (fun h => hx h.1)]
      ring
    · intro h
      exact absurd (mem_range.mpr hy) h
  · rw [ite_eq_right (fun h => hy h.1)]
    refine sum_eq_zero fun x hx => ?_
    have : x ≠ y := fun h => hy (h ▸ mem_range.mp hx)
    rw [ite_eq_right (fun h => this h.1)]
    ring

/-- **Diagonal 6j orthogonality for all spins** (doubled units):
`Σ_x (x + 1) {B A x; E F q}² = [Tri A E q ∧ Tri B q F] / (q + 1)`. Physlib's orthogonality needs
two positive spins (`sixJSym_orth`); a zero spin is handled by the closed form
`sixJSym_zero_left` moved into place by the tetrahedral symmetries. -/
theorem sixJSym_sq_orth (B A E F q : ℕ) :
    ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 =
      if Tri A E q ∧ Tri B q F then 1 / ((q : ℝ) + 1) else 0 := by
  have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
  -- from the version with the extra factor `(q + 1)`
  have of_orth : (∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
      (sixJSym B A x E F q * sixJSym B A x E F q) =
        if Tri A E q ∧ Tri B q F then 1 else 0) →
      ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 =
        if Tri A E q ∧ Tri B q F then 1 / ((q : ℝ) + 1) else 0 := by
    intro h
    have h' : ((q : ℝ) + 1) * ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 =
        if Tri A E q ∧ Tri B q F then 1 else 0 := by
      rw [← h, mul_sum]
      exact sum_congr rfl fun x _ => by ring
    split_ifs at h' ⊢ with hc
    · field_simp; linarith
    · exact (mul_eq_zero.mp h').resolve_left hq1
  by_cases hB : 0 < B
  · by_cases hE : 0 < E
    · apply of_orth
      rw [sixJSym_orth hB hE]
      simp
    · -- `E = 0`: move it to the first slot
      have hE0 : E = 0 := by omega
      subst hE0
      have : ∀ x, sixJSym B A x 0 F q = sixJSym 0 F x B A q := fun x => (sj_flip12 _ _ _ _ _ _).symm
      simp only [this, sixJSym_zero_left]
      rw [sum_sq_single _ F A q _ _ (by rw [← pow_mul, mul_comm, pow_mul]; norm_num)]
      by_cases h : F < B + A + 1 ∧ q = A ∧ Tri F A B
      · obtain ⟨h1, rfl, h3⟩ := h
        rw [ite_eq_left ⟨h1, rfl, h3⟩, ite_eq_left (by unfold Tri at h3 ⊢; omega)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (by unfold Tri at h' ⊢; omega))]
  · have hB0 : B = 0 := by omega
    subst hB0
    simp only [sixJSym_zero_left]
    rw [sum_sq_single _ A F q _ _ (by rw [← pow_mul, mul_comm, pow_mul]; norm_num)]
    by_cases h : A < 0 + A + 1 ∧ q = F ∧ Tri A F E
    · obtain ⟨-, rfl, h3⟩ := h
      rw [ite_eq_left ⟨by omega, rfl, h3⟩, ite_eq_left (by unfold Tri at h3 ⊢; omega)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (by unfold Tri at h' ⊢; omega))]

/-- `Σ_{k ≤ m} (l + 2k + 1) = (m + 1)(l + m + 1)`. -/
lemma sum_odd_shift (l m : ℕ) : ∑ k ∈ range (m + 1), (l + 2 * k + 1) = (m + 1) * (l + m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; ring

lemma sum_tri_succ_of_le {p d N : ℕ} (hpd : p ≤ d) (hN : p + d < N) :
    ∑ b ∈ range N, (if Tri p b d then ((b : ℝ) + 1) else 0) = ((p : ℝ) + 1) * ((d : ℝ) + 1) := by
  rw [← sum_filter]
  have himg : (range N).filter (fun b => Tri p b d) =
      (range (p + 1)).image (fun k => d - p + 2 * k) := by
    ext b
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hb, h1, h2, h3, h4⟩
      exact ⟨(b - (d - p)) / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      unfold Tri
      omega
  rw [himg, sum_image (fun k _ k' _ (h : d - p + 2 * k = d - p + 2 * k') => by omega)]
  have := sum_odd_shift (d - p) p
  have hcast : ∑ k ∈ range (p + 1), (((d - p + 2 * k : ℕ) : ℝ) + 1) =
      ((∑ k ∈ range (p + 1), (d - p + 2 * k + 1) : ℕ) : ℝ) := by push_cast; rfl
  rw [hcast, this]
  push_cast [show d - p + p + 1 = d + 1 by omega]
  ring

/-- **The Clebsch–Gordan dimension count** (doubled units): the admissible `b` for `p ⊗ d`
satisfy `Σ (b + 1) = (p + 1)(d + 1)`. -/
lemma sum_tri_succ {p d N : ℕ} (hN : p + d < N) :
    ∑ b ∈ range N, (if Tri p b d then ((b : ℝ) + 1) else 0) = ((p : ℝ) + 1) * ((d : ℝ) + 1) := by
  rcases le_total p d with h | h
  · exact sum_tri_succ_of_le h hN
  · have hsymm : ∀ b, Tri p b d ↔ Tri d b p := fun b => by unfold Tri; omega
    simp only [hsymm]
    rw [sum_tri_succ_of_le h (by omega), mul_comm]

/-! ## The local 1-4 identity -/

variable {V : Type*} [DecidableEq V]

lemma pair_eq_pair_iff' {a b c d : V} :
    ({a, b} : Finset V) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff]

/-- A 6j symbol with an inadmissible face vanishes. -/
lemma tetAmp_eq_zero_of_not_tri (col : Colouring V) (p : Fin 4 → V)
    (h : ¬ Tri (col {p 2, p 3}) (col {p 1, p 3}) (col {p 1, p 2})) : tetAmp col p = 0 := by
  by_contra h0
  rw [tetAmp_eq] at h0
  exact h (tri_of_sixJSym_ne_zero h0).1

/-- The colouring after the 1-4 move: `BE, CE, AE` get the spins `b, c, a`. -/
def upd14 (col : Colouring V) (A B C E : V) (a b c : ℕ) : Colouring V :=
  Function.update (Function.update (Function.update col {B, E} b) {C, E} c) {A, E} a

/-- **The local weight of the four new tetrahedra** `ABCE, ABDE, ACDE, BCDE`. It is the product of
the four new edges, the six new triangles and the four 6j symbols. The first factor holds what does
not involve `AE`; the second is the right-hand side of the 2-3 move around `AE`. -/
noncomputable def term14 (col : Colouring V) (A B C D E : V) (a b c : ℕ) : ℝ :=
  (edgeW b * edgeW c * edgeW (col {D, E}) *
      (triSign (upd14 col A B C E a b c) B C E * triSign (upd14 col A B C E a b c) B D E *
        triSign (upd14 col A B C E a b c) C D E) *
      tetAmp (upd14 col A B C E a b c) ![B, C, D, E]) *
    (edgeW a * (triSign (upd14 col A B C E a b c) B A E *
        triSign (upd14 col A B C E a b c) C A E * triSign (upd14 col A B C E a b c) D A E) *
      (tetAmp (upd14 col A B C E a b c) ![B, C, A, E] *
        tetAmp (upd14 col A B C E a b c) ![C, D, A, E] *
        tetAmp (upd14 col A B C E a b c) ![D, B, A, E]))

set_option hygiene false in
/-- Evaluate the updated colourings at explicit edges (needs `hAB … hDE` in context) and put
the old edges in the order `AB AC AD BC BD CD DE`. -/
macro "ev14" : tactic => `(tactic| simp only [upd14, Function.update_apply, pair_eq_pair_iff',
  hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm, hAD.symm, hAE.symm,
  hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm, eq_self_iff_true, true_and,
  and_true, false_and, and_false, or_false, false_or, ↓reduceIte, Matrix.cons_val_zero,
  Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
  Matrix.tail_cons, pair_comm B A, pair_comm C A, pair_comm D A, pair_comm C B, pair_comm D B,
  pair_comm D C, pair_comm E D, pair_comm E A, pair_comm E B, pair_comm E C])

set_option hygiene false in
/-- `ev14` at a hypothesis. -/
macro "ev14_at " h:ident : tactic => `(tactic| simp only [upd14, Function.update_apply,
  pair_eq_pair_iff', hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE, hAB.symm, hAC.symm,
  hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm, hDE.symm,
  eq_self_iff_true, true_and, and_true, false_and, and_false, or_false, false_or, ↓reduceIte,
  pair_comm B A, pair_comm C A, pair_comm D A, pair_comm C B, pair_comm D B, pair_comm D C,
  pair_comm E D, pair_comm E A, pair_comm E B, pair_comm E C] at $h:ident)

/-- **The local 1-4 Pachner move.** With the spin `d = col {D, E}` of the new edge `DE` fixed,
the four new tetrahedra summed over the spins `a, b, c` of `AE, BE, CE` give `(d + 1)²` times the
old tetrahedron `ABCD`. -/
theorem pachner14_local (col : Colouring V) {A B C D E : V} (hAB : A ≠ B) (hAC : A ≠ C)
    (hAD : A ≠ D) (hAE : A ≠ E) (hBC : B ≠ C) (hBD : B ≠ D) (hBE : B ≠ E) (hCD : C ≠ D)
    (hCE : C ≠ E) (hDE : D ≠ E) :
    ∑ a ∈ range (col {A, D} + col {D, E} + 1), ∑ b ∈ range (col {B, D} + col {D, E} + 1),
      ∑ c ∈ range (col {C, D} + col {D, E} + 1), term14 col A B C D E a b c =
    ((col {D, E} : ℝ) + 1) ^ 2 * tetAmp col ![A, B, C, D] := by
  -- the 6j symbol of `BCDE`, in orthogonality position
  have hqBCDE : ∀ (κ : Colouring V), tetAmp κ ![B, C, D, E] = tetAmp κ ![D, E, C, B] := fun κ =>
    (tetAmp_reindex κ (injective_vec4 hDE hCD.symm hBD.symm hCE.symm hBE.symm hBC.symm)
      (by intro i; fin_cases i; exacts [⟨2, rfl⟩, ⟨3, rfl⟩, ⟨1, rfl⟩, ⟨0, rfl⟩])).symm
  have hS : ∀ a b c, tetAmp (upd14 col A B C E a b c) ![B, C, D, E] =
      sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) := by
    intro a b c
    rw [hqBCDE, tetAmp_eq]
    ev14
  have hS' : ∀ b c, tetAmp (Function.update (Function.update col {B, E} b) {C, E} c)
      ![B, C, D, E] = sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) := by
    intro b c
    rw [hqBCDE, tetAmp_eq]
    ev14
  have hABCD : ∀ b c, tetAmp (Function.update (Function.update col {B, E} b) {C, E} c)
      ![B, C, D, A] = tetAmp col ![A, B, C, D] := by
    intro b c
    rw [← tetAmp_reindex _ (q := ![A, B, C, D]) (injective_vec4 hAB hAC hAD hBC hBD hCD)
      (by intro i; fin_cases i; exacts [⟨3, rfl⟩, ⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]),
      tetAmp_eq, tetAmp_eq (col := col)]
    ev14
  -- Step 1: for fixed `b, c`, the sum over `a` is the 2-3 move around `AE`, plus sign bookkeeping
  have hstep : ∀ b c, ∑ a ∈ range (col {A, D} + col {D, E} + 1), term14 col A B C D E a b c =
      ((b : ℝ) + 1) * ((c : ℝ) + 1) * ((col {D, E} : ℝ) + 1) * tetAmp col ![A, B, C, D] *
        (sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 := by
    intro b c
    have hG : ∀ a, edgeW b * edgeW c * edgeW (col {D, E}) *
        (triSign (upd14 col A B C E a b c) B C E * triSign (upd14 col A B C E a b c) B D E *
          triSign (upd14 col A B C E a b c) C D E) *
        tetAmp (upd14 col A B C E a b c) ![B, C, D, E] =
        edgeW b * edgeW c * edgeW (col {D, E}) *
          ((-1 : ℝ) ^ ((col {B, C} + c + b) / 2) * (-1) ^ ((col {B, D} + col {D, E} + b) / 2) *
            (-1) ^ ((col {C, D} + col {D, E} + c) / 2)) *
          sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) := by
      intro a
      rw [hS]
      simp only [triSign]
      ev14
    have h23 := pachner23_local (Function.update (Function.update col {B, E} b) {C, E} c)
      (beAt_of_biedenharnElliott biedenharnElliott _ _ _ _ _ _)
      hBC hBD hAB.symm hBE hCD hAC.symm hCE hAD.symm hDE hAE
    have hH : ∑ a ∈ range (col {A, D} + col {D, E} + 1),
        edgeW a * (triSign (upd14 col A B C E a b c) B A E *
          triSign (upd14 col A B C E a b c) C A E * triSign (upd14 col A B C E a b c) D A E) *
        (tetAmp (upd14 col A B C E a b c) ![B, C, A, E] *
          tetAmp (upd14 col A B C E a b c) ![C, D, A, E] *
          tetAmp (upd14 col A B C E a b c) ![D, B, A, E]) =
        (-1 : ℝ) ^ ((col {B, C} + col {C, D} + col {B, D}) / 2) * (tetAmp col ![A, B, C, D] *
          sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) := by
      have hbound : Function.update (Function.update col {B, E} b) {C, E} c {B, A} +
          Function.update (Function.update col {B, E} b) {C, E} c {B, E} = col {A, B} + b := by
        ev14
      rw [sum_range_eq_of_vanish (n := col {A, B} + b + 1) ?_ ?_]
      · rw [← hbound]
        refine h23.symm.trans ?_
        rw [hS', hABCD]
        simp only [triSign]
        ev14
      · intro x hx
        rw [tetAmp_eq_zero_of_not_tri _ ![C, D, A, E] (by ev14; unfold Tri; omega)]
        ring
      · intro x hx
        rw [tetAmp_eq_zero_of_not_tri _ ![D, B, A, E] (by ev14; unfold Tri; omega)]
        ring
    rw [sum_congr rfl fun a _ => by rw [term14, hG a], ← mul_sum, hH]
    -- the signs cancel
    by_cases hS0 : sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D}) = 0
    · rw [hS0]; ring
    obtain ⟨T1, T2, T3, T4⟩ := tri_of_sixJSym_ne_zero hS0
    have hsgn : (-1 : ℝ) ^ b * (-1) ^ c * (-1) ^ col {D, E} *
        ((-1) ^ ((col {B, C} + c + b) / 2) * (-1) ^ ((col {B, D} + col {D, E} + b) / 2) *
          (-1) ^ ((col {C, D} + col {D, E} + c) / 2)) *
        (-1) ^ ((col {B, C} + col {C, D} + col {B, D}) / 2) = 1 := by
      simp only [← pow_add]
      exact Even.neg_one_pow (Nat.even_iff.mpr (by unfold Tri at *; omega))
    unfold edgeW
    linear_combination ((b : ℝ) + 1) * ((c : ℝ) + 1) * ((col {D, E} : ℝ) + 1) *
      tetAmp col ![A, B, C, D] *
      (sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 * hsgn
  -- reorder the sums: `b`, then `c`, then `a`
  rw [sum_comm, sum_congr rfl fun b _ => sum_comm,
    sum_congr rfl fun b _ => sum_congr rfl fun c _ => hstep b c]
  -- Step 2: orthogonality in `c`
  have hc : ∀ b : ℕ, ∑ c ∈ range (col {C, D} + col {D, E} + 1),
      ((c : ℝ) + 1) * (sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 =
      if Tri b (col {D, E}) (col {B, D}) ∧ Tri (col {B, C}) (col {B, D}) (col {C, D}) then
        1 / ((col {B, D} : ℝ) + 1) else 0 := by
    intro b
    rw [← sixJSym_sq_orth]
    refine sum_range_eq_of_vanish (fun x hx => ?_) (fun x hx => ?_)
    · have : sixJSym (col {B, C}) b x (col {D, E}) (col {C, D}) (col {B, D}) = 0 := by
        by_contra h; have := (tri_of_sixJSym_ne_zero h).2.2.2; unfold Tri at this; omega
      rw [this]; ring
    · have : sixJSym (col {B, C}) b x (col {D, E}) (col {C, D}) (col {B, D}) = 0 := by
        by_contra h; have := (tri_of_sixJSym_ne_zero h).1; unfold Tri at this; omega
      rw [this]; ring
  have hrow : ∀ b : ℕ, ∑ c ∈ range (col {C, D} + col {D, E} + 1),
      ((b : ℝ) + 1) * ((c : ℝ) + 1) * ((col {D, E} : ℝ) + 1) * tetAmp col ![A, B, C, D] *
        (sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 =
      ((col {D, E} : ℝ) + 1) * tetAmp col ![A, B, C, D] / ((col {B, D} : ℝ) + 1) *
        (if Tri (col {B, C}) (col {B, D}) (col {C, D}) then
          (if Tri (col {B, D}) b (col {D, E}) then ((b : ℝ) + 1) else 0) else 0) := by
    intro b
    have : ∀ c : ℕ, ((b : ℝ) + 1) * ((c : ℝ) + 1) * ((col {D, E} : ℝ) + 1) *
        tetAmp col ![A, B, C, D] *
        (sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2 =
        ((b : ℝ) + 1) * ((col {D, E} : ℝ) + 1) * tetAmp col ![A, B, C, D] *
        (((c : ℝ) + 1) * (sixJSym (col {B, C}) b c (col {D, E}) (col {C, D}) (col {B, D})) ^ 2) :=
      fun c => by ring
    rw [sum_congr rfl fun c _ => this c, ← mul_sum, hc]
    have hq1 : ((col {B, D} : ℝ) + 1) ≠ 0 := by positivity
    by_cases h1 : Tri (col {B, C}) (col {B, D}) (col {C, D})
    · by_cases h2 : Tri b (col {D, E}) (col {B, D})
      · rw [ite_eq_left ⟨h2, h1⟩, ite_eq_left h1, ite_eq_left (by unfold Tri at h2 ⊢; omega)]
        field_simp
      · rw [ite_eq_right (fun h => h2 h.1), ite_eq_left h1,
          ite_eq_right (fun h => h2 (by unfold Tri at h ⊢; omega))]
        ring
    · rw [ite_eq_right (fun h => h1 h.2), ite_eq_right h1]
      ring
  rw [sum_congr rfl fun b _ => hrow b, ← mul_sum]
  -- Step 3: the dimension count in `b`
  by_cases h1 : Tri (col {B, C}) (col {B, D}) (col {C, D})
  · simp only [ite_eq_left h1]
    rw [sum_tri_succ (by omega)]
    have hq1 : ((col {B, D} : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · have hT0 : tetAmp col ![A, B, C, D] = 0 :=
      tetAmp_eq_zero_of_not_tri _ _ (by ev14; unfold Tri at h1 ⊢; omega)
    rw [hT0]
    ring

/-! ## The 1-4 move on a complex -/

/-- Preconditions of a 1-4 move on `K`: `ABCD` is a tetrahedron of `K` and `E` is a new vertex. -/
structure IsMove14 (K : Complex3 V) (A B C D E : V) : Prop where
  hAB : A ≠ B
  hAC : A ≠ C
  hAD : A ≠ D
  hAE : A ≠ E
  hBC : B ≠ C
  hBD : B ≠ D
  hBE : B ≠ E
  hCD : C ≠ D
  hCE : C ≠ E
  hDE : D ≠ E
  mem : {A, B, C, D} ∈ K.tets
  fresh : ∀ t ∈ K.tets, E ∉ t

/-- **The 1-4 Pachner move**: replace `ABCD` by `ABCE, ABDE, ACDE, BCDE`. -/
def move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) : Complex3 V where
  tets := {{A, B, C, E}, {A, B, D, E}, {A, C, D, E}, {B, C, D, E}} ∪ K.tets.erase {A, B, C, D}
  card_eq t ht := by
    rcases mem_union.mp ht with ht | ht
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact card_four h.hAB h.hAC h.hAE h.hBC h.hBE h.hCE
      · exact card_four h.hAB h.hAD h.hAE h.hBD h.hBE h.hDE
      · exact card_four h.hAC h.hAD h.hAE h.hCD h.hCE h.hDE
      · exact card_four h.hBC h.hBD h.hBE h.hCD h.hCE h.hDE
    · exact K.card_eq t (mem_of_mem_erase ht)

/-- A 2-element subset of `{P, Q, R, E}` through `E` is `PE`, `QE` or `RE`. -/
lemma edge_of_sub {s : Finset V} {P Q R E : V} (hs : #s = 2) (hE : E ∈ s)
    (hsub : s ⊆ {P, Q, R, E}) : s = {P, E} ∨ s = {Q, E} ∨ s = {R, E} := by
  have h1 : #(s.erase E) = 1 := by rw [card_erase_of_mem hE, hs]
  obtain ⟨x, hx⟩ := card_eq_one.mp h1
  have hxs : x ∈ s.erase E := hx ▸ mem_singleton_self x
  have hxE : x ≠ E := (mem_erase.mp hxs).1
  have hxm : x ∈ ({P, Q, R, E} : Finset V) := hsub (mem_of_mem_erase hxs)
  have hseq : s = {x, E} := by rw [← insert_erase hE, hx, pair_comm]
  simp only [mem_insert, mem_singleton] at hxm
  rcases hxm with rfl | rfl | rfl | rfl
  · exact Or.inl hseq
  · exact Or.inr (Or.inl hseq)
  · exact Or.inr (Or.inr hseq)
  · exact absurd rfl hxE

/-- A 3-element subset of `{P, Q, R, E}` through `E` is `PQE`, `PRE` or `QRE`. -/
lemma tri_of_sub {s : Finset V} {P Q R E : V} (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hs : #s = 3) (hE : E ∈ s) (hsub : s ⊆ {P, Q, R, E}) :
    s = {P, Q, E} ∨ s = {P, R, E} ∨ s = {Q, R, E} := by
  have h2 : #(s.erase E) = 2 := by rw [card_erase_of_mem hE, hs]
  have hsub' : s.erase E ⊆ {P, Q, R} := by
    intro y hy
    have hyE := (mem_erase.mp hy).1
    have := hsub (mem_of_mem_erase hy)
    simp only [mem_insert, mem_singleton] at this ⊢
    tauto
  have hne : s.erase E ≠ {P, Q, R} := fun h' => by
    rw [h', card_three hPQ hPR hQR] at h2; omega
  have key : ∀ X Y : V, X ≠ Y → s.erase E ⊆ {X, Y} → s = {X, Y, E} := by
    intro X Y hXY hsub''
    have := eq_of_subset_of_card_le hsub'' (by rw [card_pair hXY, h2])
    rw [← insert_erase hE, this]
    ext z; simp only [mem_insert, mem_singleton]; tauto
  rcases not_mem_of_card_le hPQ hPR hQR (by omega) hne with hP | hQ | hR
  · exact Or.inr (Or.inr (key Q R hQR (subset_of_not_mem hsub' hP (by small_subset))))
  · exact Or.inr (Or.inl (key P R hPR (subset_of_not_mem hsub' hQ (by small_subset))))
  · exact Or.inl (key P Q hPQ (subset_of_not_mem hsub' hR (by small_subset)))

/-- A proper subset of `ABCD` lies in one of the four new tetrahedra. -/
lemma sub_new_of_sub {s : Finset V} {A B C D E : V} (hAB : A ≠ B) (hAC : A ≠ C) (hAD : A ≠ D)
    (hBC : B ≠ C) (hBD : B ≠ D) (hCD : C ≠ D) (hs : #s ≤ 3) (hsub : s ⊆ {A, B, C, D}) :
    s ⊆ {A, B, C, E} ∨ s ⊆ {A, B, D, E} ∨ s ⊆ {A, C, D, E} ∨ s ⊆ {B, C, D, E} := by
  by_cases hD : D ∈ s
  · by_cases hC : C ∈ s
    · by_cases hB : B ∈ s
      · by_cases hA : A ∈ s
        · exfalso
          have := card_le_card (show ({A, B, C, D} : Finset V) ⊆ s by
            intro z hz; simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl | rfl | rfl <;> assumption)
          rw [card_four hAB hAC hAD hBC hBD hCD] at this; omega
        · exact Or.inr (Or.inr (Or.inr (subset_of_not_mem hsub hA (by small_subset))))
      · exact Or.inr (Or.inr (Or.inl (subset_of_not_mem hsub hB (by small_subset))))
    · exact Or.inr (Or.inl (subset_of_not_mem hsub hC (by small_subset)))
  · exact Or.inl (subset_of_not_mem hsub hD (by small_subset))

/-- Edges after the 1-4 move: the old ones plus `AE, BE, CE, DE`. -/
theorem edges_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) :
    (move14 K h).edges = K.edges ∪ {{A, E}, {B, E}, {C, E}, {D, E}} := by
  ext s
  simp only [Complex3.mem_edges, move14, mem_union, mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨t, ht, hst, hs⟩
    rcases ht with (rfl | rfl | rfl | rfl) | ⟨-, ht⟩
    all_goals try exact Or.inl ⟨t, ht, hst, hs⟩
    all_goals by_cases hE : E ∈ s
    all_goals first
      | exact Or.inl ⟨_, h.mem, subset_of_not_mem hst hE (by small_subset), hs⟩
      | (right; rcases edge_of_sub hs hE hst with rfl | rfl | rfl <;> simp)
  · rintro (⟨t, ht, hst, hs⟩ | (rfl | rfl | rfl | rfl))
    · by_cases h1 : t = {A, B, C, D}
      · subst h1
        rcases sub_new_of_sub (E := E) h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD (by omega) hst with
          h' | h' | h' | h'
        · exact ⟨_, Or.inl (Or.inl rfl), h', hs⟩
        · exact ⟨_, Or.inl (Or.inr (Or.inl rfl)), h', hs⟩
        · exact ⟨_, Or.inl (Or.inr (Or.inr (Or.inl rfl))), h', hs⟩
        · exact ⟨_, Or.inl (Or.inr (Or.inr (Or.inr rfl))), h', hs⟩
      · exact ⟨t, Or.inr ⟨h1, ht⟩, hst, hs⟩
    · exact ⟨{A, B, C, E}, by simp, by small_subset, card_pair h.hAE⟩
    · exact ⟨{A, B, C, E}, by simp, by small_subset, card_pair h.hBE⟩
    · exact ⟨{A, B, C, E}, by simp, by small_subset, card_pair h.hCE⟩
    · exact ⟨{A, B, D, E}, by simp, by small_subset, card_pair h.hDE⟩

/-- Triangles after the 1-4 move: the old ones plus the six through `E`. -/
theorem tris_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) :
    (move14 K h).tris =
      K.tris ∪ {{A, B, E}, {A, C, E}, {A, D, E}, {B, C, E}, {B, D, E}, {C, D, E}} := by
  ext s
  simp only [Complex3.mem_tris, move14, mem_union, mem_erase, mem_insert, mem_singleton]
  constructor
  · rintro ⟨t, ht, hst, hs⟩
    rcases ht with (rfl | rfl | rfl | rfl) | ⟨-, ht⟩
    all_goals try exact Or.inl ⟨t, ht, hst, hs⟩
    all_goals by_cases hE : E ∈ s
    all_goals try exact Or.inl ⟨_, h.mem, subset_of_not_mem hst hE (by small_subset), hs⟩
    · right; rcases tri_of_sub h.hAB h.hAC h.hBC hs hE hst with rfl | rfl | rfl <;> simp
    · right; rcases tri_of_sub h.hAB h.hAD h.hBD hs hE hst with rfl | rfl | rfl <;> simp
    · right; rcases tri_of_sub h.hAC h.hAD h.hCD hs hE hst with rfl | rfl | rfl <;> simp
    · right; rcases tri_of_sub h.hBC h.hBD h.hCD hs hE hst with rfl | rfl | rfl <;> simp
  · rintro (⟨t, ht, hst, hs⟩ | (rfl | rfl | rfl | rfl | rfl | rfl))
    · by_cases h1 : t = {A, B, C, D}
      · subst h1
        rcases sub_new_of_sub (E := E) h.hAB h.hAC h.hAD h.hBC h.hBD h.hCD (by omega) hst with
          h' | h' | h' | h'
        · exact ⟨_, Or.inl (Or.inl rfl), h', hs⟩
        · exact ⟨_, Or.inl (Or.inr (Or.inl rfl)), h', hs⟩
        · exact ⟨_, Or.inl (Or.inr (Or.inr (Or.inl rfl))), h', hs⟩
        · exact ⟨_, Or.inl (Or.inr (Or.inr (Or.inr rfl))), h', hs⟩
      · exact ⟨t, Or.inr ⟨h1, ht⟩, hst, hs⟩
    · exact ⟨{A, B, C, E}, by simp, by small_subset, card_three h.hAB h.hAE h.hBE⟩
    · exact ⟨{A, B, C, E}, by simp, by small_subset, card_three h.hAC h.hAE h.hCE⟩
    · exact ⟨{A, B, D, E}, by simp, by small_subset, card_three h.hAD h.hAE h.hDE⟩
    · exact ⟨{A, B, C, E}, by simp, by small_subset, card_three h.hBC h.hBE h.hCE⟩
    · exact ⟨{A, B, D, E}, by simp, by small_subset, card_three h.hBD h.hBE h.hDE⟩
    · exact ⟨{A, C, D, E}, by simp, by small_subset, card_three h.hCD h.hCE h.hDE⟩

/-! ## The weight and the amplitude under the 1-4 move -/

lemma triSign_swap (col : Colouring V) (u v w : V) : triSign col u v w = triSign col v u w := by
  unfold triSign
  rw [pair_comm v u, pair_comm u w, pair_comm w v]
  congr 1
  omega

omit [DecidableEq V] in
lemma ne_of_mem_not_mem {s t : Finset V} {x : V} (hs : x ∈ s) (ht : x ∉ t) : s ≠ t :=
  fun h => ht (h ▸ hs)

set_option hygiene false in
/-- Close `x ∉ {…}` and `x ∈ {…}` goals for the five distinct vertices. -/
macro "distinct14" : tactic => `(tactic| simp [hAB, hAC, hAD, hAE, hBC, hBD, hBE, hCD, hCE, hDE,
  hAB.symm, hAC.symm, hAD.symm, hAE.symm, hBC.symm, hBD.symm, hBE.symm, hCD.symm, hCE.symm,
  hDE.symm])

set_option hygiene false in
/-- Non-membership of a small vertex set in a list of small vertex sets, by a separating vertex. -/
macro "notmem14" : tactic => `(tactic| (simp only [mem_insert, mem_singleton, not_or]; (repeat' apply And.intro); all_goals first | (refine ne_of_mem_not_mem (x := A) ?_ ?_ <;> first | (simp; done) | (distinct14; done)) | (refine ne_of_mem_not_mem (x := B) ?_ ?_ <;> first | (simp; done) | (distinct14; done)) | (refine ne_of_mem_not_mem (x := C) ?_ ?_ <;> first | (simp; done) | (distinct14; done)) | (refine ne_of_mem_not_mem (x := D) ?_ ?_ <;> first | (simp; done) | (distinct14; done))))

/-- **The weight after a 1-4 move factorises**: the part of `K` away from `ABCD`, times the local
weight `term14` of the four new tetrahedra. -/
theorem weight_move14_eq (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    (col : Colouring V) (a b c d : ℕ) :
    weight (move14 K h) (upd14 (Function.update col {D, E} d) A B C E a b c) =
      ((∏ e ∈ K.edges, edgeW (col e)) * (∏ f ∈ K.tris, triW col f) *
        ∏ t ∈ K.tets.erase {A, B, C, D}, tetW col t) *
      term14 (Function.update col {D, E} d) A B C D E a b c := by
  have hAB := h.hAB; have hAC := h.hAC; have hAD := h.hAD; have hAE := h.hAE
  have hBC := h.hBC; have hBD := h.hBD; have hBE := h.hBE; have hCD := h.hCD
  have hCE := h.hCE; have hDE := h.hDE
  -- away from `E` the new colouring is the old one
  have hoff : ∀ e : Finset V, E ∉ e →
      upd14 (Function.update col {D, E} d) A B C E a b c e = col e := by
    intro e he
    have hne : ∀ X : V, e ≠ {X, E} := fun X h' => he (h' ▸ by simp)
    simp only [upd14]
    rw [Function.update_of_ne (hne A), Function.update_of_ne (hne C),
      Function.update_of_ne (hne B), Function.update_of_ne (hne D)]
  have hEt : ∀ t ∈ K.tets, ∀ e ⊆ t, E ∉ e := fun t ht e he hE => h.fresh t ht (he hE)
  have hdE : Disjoint K.edges {{A, E}, {B, E}, {C, E}, {D, E}} := by
    rw [disjoint_left]
    intro e he hnew
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp he
    simp only [mem_insert, mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl | rfl <;> exact hEt t ht _ hst (by simp)
  have hdT : Disjoint K.tris {{A, B, E}, {A, C, E}, {A, D, E}, {B, C, E}, {B, D, E}, {C, D, E}} := by
    rw [disjoint_left]
    intro f hf hnew
    obtain ⟨t, ht, hft, -⟩ := Complex3.mem_tris.mp hf
    simp only [mem_insert, mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hEt t ht _ hft (by simp)
  have hdK : Disjoint ({{A, B, C, E}, {A, B, D, E}, {A, C, D, E}, {B, C, D, E}} : Finset (Finset V))
      (K.tets.erase {A, B, C, D}) := by
    rw [disjoint_left]
    intro t hnew ht
    have := h.fresh t (mem_of_mem_erase ht)
    simp only [mem_insert, mem_singleton] at hnew
    rcases hnew with rfl | rfl | rfl | rfl <;> exact this (by simp)
  rw [weight, edges_move14, tris_move14, prod_union hdE, prod_union hdT,
    show (move14 K h).tets = _ ∪ _ from rfl, prod_union hdK]
  -- the old factors
  have p1 : ∏ e ∈ K.edges, edgeW (upd14 (Function.update col {D, E} d) A B C E a b c e) =
      ∏ e ∈ K.edges, edgeW (col e) := prod_congr rfl fun e he => by
    obtain ⟨t, ht, hst, -⟩ := Complex3.mem_edges.mp he
    rw [hoff e (hEt t ht e hst)]
  have p2 : ∏ f ∈ K.tris, triW (upd14 (Function.update col {D, E} d) A B C E a b c) f =
      ∏ f ∈ K.tris, triW col f := prod_congr rfl fun f hf => by
    obtain ⟨t, ht, hft, -⟩ := Complex3.mem_tris.mp hf
    exact triW_congr fun e he _ => hoff e (hEt t ht e (he.trans hft))
  have p3 : ∏ t ∈ K.tets.erase {A, B, C, D},
      tetW (upd14 (Function.update col {D, E} d) A B C E a b c) t =
      ∏ t ∈ K.tets.erase {A, B, C, D}, tetW col t := prod_congr rfl fun t ht =>
    tetW_congr fun e he _ => hoff e (hEt t (mem_of_mem_erase ht) e he)
  rw [p1, p2, p3]
  -- the new factors
  rw [prod_insert (by notmem14), prod_insert (by notmem14), prod_insert (by notmem14),
    prod_singleton]
  rw [prod_insert (by notmem14), prod_insert (by notmem14), prod_insert (by notmem14),
    prod_insert (by notmem14), prod_insert (by notmem14), prod_singleton]
  rw [prod_insert (by notmem14), prod_insert (by notmem14), prod_insert (by notmem14),
    prod_singleton]
  have vA : upd14 (Function.update col {D, E} d) A B C E a b c {A, E} = a := by ev14
  have vB : upd14 (Function.update col {D, E} d) A B C E a b c {B, E} = b := by ev14
  have vC : upd14 (Function.update col {D, E} d) A B C E a b c {C, E} = c := by ev14
  have vD : upd14 (Function.update col {D, E} d) A B C E a b c {D, E} = d := by ev14
  rw [vA, vB, vC, vD, triW_three _ hAB hAE hBE, triW_three _ hAC hAE hCE, triW_three _ hAD hAE hDE,
    triW_three _ hBC hBE hCE, triW_three _ hBD hBE hDE, triW_three _ hCD hCE hDE,
    tetW_eq_tetAmp _ (card_four hAB hAC hAE hBC hBE hCE) (p := ![B, C, A, E])
      (injective_vec4 hBC hAB.symm hBE hAC.symm hCE hAE) (fun i => by fin_cases i <;> simp),
    tetW_eq_tetAmp _ (card_four hAB hAD hAE hBD hBE hDE) (p := ![D, B, A, E])
      (injective_vec4 hBD.symm hAD.symm hDE hAB.symm hBE hAE) (fun i => by fin_cases i <;> simp),
    tetW_eq_tetAmp _ (card_four hAC hAD hAE hCD hCE hDE) (p := ![C, D, A, E])
      (injective_vec4 hCD hAC.symm hCE hAD.symm hDE hAE) (fun i => by fin_cases i <;> simp),
    tetW_eq_tetAmp _ (card_four hBC hBD hBE hCD hCE hDE) (p := ![B, C, D, E])
      (injective_vec4 hBC hBD hBE hCD hCE hDE) (fun i => by fin_cases i <;> simp)]
  rw [term14, Function.update_self, triSign_swap _ B A E, triSign_swap _ C A E,
    triSign_swap _ D A E]
  ring

/-- **The Ponzano–Regge weight under the 1-4 move.** Give the new edge `DE` the spin `d` and sum
the weight of the moved complex over the spins `a, b, c` of `AE, BE, CE` (all other edges keep
their spins; outside the ranges the triangle inequalities kill every term). The result is the
old weight times `(2j_DE + 1)² = (d + 1)²`. -/
theorem weight_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E)
    (col : Colouring V) (d : ℕ) :
    ∑ a ∈ range (col {A, D} + d + 1), ∑ b ∈ range (col {B, D} + d + 1),
      ∑ c ∈ range (col {C, D} + d + 1),
        weight (move14 K h) (upd14 (Function.update col {D, E} d) A B C E a b c) =
      ((d : ℝ) + 1) ^ 2 * weight K col := by
  have hAB := h.hAB; have hAC := h.hAC; have hAD := h.hAD; have hAE := h.hAE
  have hBC := h.hBC; have hBD := h.hBD; have hBE := h.hBE; have hCD := h.hCD
  have hCE := h.hCE; have hDE := h.hDE
  have hloc := pachner14_local (Function.update col {D, E} d) hAB hAC hAD hAE hBC hBD hBE hCD
    hCE hDE
  have e1 : Function.update col {D, E} d {A, D} = col {A, D} := by ev14
  have e2 : Function.update col {D, E} d {B, D} = col {B, D} := by ev14
  have e3 : Function.update col {D, E} d {C, D} = col {C, D} := by ev14
  have e4 : tetAmp (Function.update col {D, E} d) ![A, B, C, D] = tetAmp col ![A, B, C, D] := by
    rw [tetAmp_eq, tetAmp_eq (col := col)]
    ev14
  rw [e1, e2, e3, Function.update_self, e4] at hloc
  simp only [weight_move14_eq, ← mul_sum]
  rw [hloc, weight, ← mul_prod_erase _ _ h.mem,
    tetW_eq_tetAmp _ (card_four hAB hAC hAD hBC hBD hCD) (p := ![A, B, C, D])
      (injective_vec4 hAB hAC hAD hBC hBD hCD) (fun i => by fin_cases i <;> simp)]
  ring

/-- The colouring of all vertex sets given by spins on the edges of `K` (zero elsewhere). -/
def Complex3.extCol (K : Complex3 V) (σ : ∀ e ∈ K.edges, ℕ) : Colouring V :=
  fun e => if he : e ∈ K.edges then σ e he else 0

lemma amplitude_eq (K : Complex3 V) (L : ℕ) :
    amplitude K L = ∑ σ ∈ K.edges.pi (fun _ => range (L + 1)), weight K (K.extCol σ) := rfl

/-- **The cut-off amplitude under the 1-4 move.** The old edges and the new edge `DE` are cut off
at `L`; the other three new edges `AE, BE, CE` are summed over the ranges `a ≤ j_AD + d`,
`b ≤ j_BD + d`, `c ≤ j_CD + d`, written out by hand (doubled units). The result is the old cut-off
amplitude times the vertex factor `Λ_L = Σ_{d ≤ L} (d + 1)² = Σ_{j ≤ L/2} (2j + 1)²`. The
formula for `Λ_L` is this repository's computation: Barrett–Naish-Guzman §2.2.1 states that the
1-4 move holds with their cutoff but gives no `(2j + 1)²` or `Λ_L` formula, so this is not
"Ponzano–Regge's regularisation". The truncated ranges of `a, b, c` are proven complete (every
term outside them vanishes) only in `GaugeFixed.lean` (`weight_move14_eq_zero`); in this theorem
they are part of the statement. -/
theorem amplitude_move14 (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) (L : ℕ) :
    ∑ σ ∈ K.edges.pi (fun _ => range (L + 1)), ∑ d ∈ range (L + 1),
      ∑ a ∈ range (K.extCol σ {A, D} + d + 1), ∑ b ∈ range (K.extCol σ {B, D} + d + 1),
        ∑ c ∈ range (K.extCol σ {C, D} + d + 1),
          weight (move14 K h) (upd14 (Function.update (K.extCol σ) {D, E} d) A B C E a b c) =
      (∑ d ∈ range (L + 1), ((d : ℝ) + 1) ^ 2) * amplitude K L := by
  rw [amplitude_eq, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [sum_congr rfl fun d _ => weight_move14 K h (K.extCol σ) d, ← sum_mul]

end Lightlike.PR
