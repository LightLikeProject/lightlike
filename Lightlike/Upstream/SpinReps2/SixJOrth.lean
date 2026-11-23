module

public import Lightlike.Upstream.SpinReps2.SixJZero

/-!
# Orthogonality of the 6j symbols for all spins

Physlib's `sum_sixJ_mul_sixJ` proves the orthogonality of the 6j symbols for the parametrisation
of its recoupling coefficients, and needs two positive spins (`0 < a`, `0 < c`). This file states
the orthogonality for `sixJSym`, Physlib's 6j symbol in doubled spins, and for **all** spins,
including zero:

`Σ_x (x + 1)(q + 1) {B A x; E F q} {B A x; E F r} = δ_{qr} [(A E q) and (B q F) admissible]`.

The positive case is Physlib's statement translated to `sixJSym`; the zero-spin cases are handled
by the closed form `sixJSym_zero_left` moved into place by the tetrahedral symmetries.

## Main results

* `PhyslibAlpha.Sl2.sixJSym_orth_all`: orthogonality of the 6j symbols, for all spins.
* `PhyslibAlpha.Sl2.sixJSym_sq_orth`: the diagonal case, `Σ_x (x + 1) {B A x; E F q}²`.
* `PhyslibAlpha.Sl2.sixJSym_perm`: the tetrahedral symmetry in the explicit form used here.
* `PhyslibAlpha.Sl2.triad_of_sixJSym_ne_zero`: a nonzero 6j symbol has four admissible triads.
-/

@[expose] public section

open Finset

namespace PhyslibAlpha.Sl2

/-! ## Tetrahedral symmetry and the triads of a nonzero 6j symbol -/

/-- Edge labels of the dual tetrahedron of `{j₁ j₂ j₃; j₄ j₅ j₆}`, as `sixJSymEdge` indexes them. -/
def edgeM (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Fin 4 → Fin 4 → ℕ :=
  ![![0, j₁, j₂, j₃], ![j₁, 0, j₆, j₅], ![j₂, j₆, 0, j₄], ![j₃, j₅, j₄, 0]]

/-- The same labels as a function on `Sym2 (Fin 4)`. -/
def edgeFn (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Sym2 (Fin 4) → ℕ :=
  Sym2.lift ⟨edgeM j₁ j₂ j₃ j₄ j₅ j₆, by intro i k; fin_cases i <;> fin_cases k <;> rfl⟩

/-- **Tetrahedral symmetry, explicit form**: relabelling the four triads by `σ` does not change
the 6j symbol. -/
lemma sixJSym_perm (σ : Equiv.Perm (Fin 4)) (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 0) (σ 1)) (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 0) (σ 2))
      (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 0) (σ 3)) (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 2) (σ 3))
      (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 1) (σ 3)) (edgeM j₁ j₂ j₃ j₄ j₅ j₆ (σ 1) (σ 2)) =
      sixJSym j₁ j₂ j₃ j₄ j₅ j₆ :=
  sixJSymEdge_comp_map σ (edgeFn j₁ j₂ j₃ j₄ j₅ j₆)

/-- The permutation of `Fin 4` given by a vector (bijectivity by `decide`). -/
noncomputable def permOf (v : Fin 4 → Fin 4) (h : Function.Bijective v) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective v h

/-- The triad `(j₁ j₅ j₆)` moved to the front (`σ = (0 1)`). -/
lemma sixJSym_v1 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₆ j₅ j₄ j₃ j₂ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![1, 0, 2, 3] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- The triad `(j₄ j₂ j₆)` moved to the front (`σ = (0 2)`). -/
lemma sixJSym_v2 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₆ j₂ j₄ j₃ j₅ j₁ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![2, 1, 0, 3] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- The triad `(j₄ j₅ j₃)` moved to the front (`σ = (0 3)`). -/
lemma sixJSym_v3 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₅ j₄ j₃ j₂ j₁ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![3, 1, 2, 0] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- Exchange of the two columns: `{j₄ j₅ j₃; j₁ j₂ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}`. -/
lemma sixJSym_flip (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₄ j₅ j₃ j₁ j₂ j₆ = sixJSym j₁ j₂ j₃ j₄ j₅ j₆ := by
  have := sixJSym_perm (permOf ![3, 2, 1, 0] (by decide)) j₁ j₂ j₃ j₄ j₅ j₆
  simpa [permOf, edgeM] using this

/-- A `sixJTerm` vanishes unless all four 3j symbols are admissible. -/
lemma sixJTerm_eq_zero {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} {m : Fin 6 → ℤ}
    (h : ¬ (Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) ∧ Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5) ∧
      Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5) ∧ Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2))) :
    sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m = 0 := by
  simp only [sixJTerm]
  by_cases h1 : Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2)
  · by_cases h2 : Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5)
    · by_cases h3 : Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5)
      · have h4 : ¬ Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2) := fun h4 => h ⟨h1, h2, h3, h4⟩
        simp [threeJ_of_not h4]
      · simp [threeJ_of_not h3]
    · simp [threeJ_of_not h2]
  · simp [threeJ_of_not h1]

/-- A nonzero 6j symbol has four admissible triads: integer perimeters and the triangle
inequalities of its first triad. -/
lemma triads_of_sixJSym_ne_zero {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}
    (h : sixJSym j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0) :
    (j₁ + j₂ + j₃) % 2 = 0 ∧ (j₁ + j₅ + j₆) % 2 = 0 ∧ (j₄ + j₂ + j₆) % 2 = 0 ∧
      (j₄ + j₅ + j₃) % 2 = 0 ∧ j₃ ≤ j₁ + j₂ ∧ j₁ ≤ j₂ + j₃ ∧ j₂ ≤ j₁ + j₃ := by
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_contra hc
  apply hm
  apply sixJTerm_eq_zero
  rintro ⟨h1, h2, h3, h4⟩
  apply hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, t1, t2, t3, p1⟩ := h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, p2⟩ := h2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, p3⟩ := h3
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, p4⟩ := h4
  exact ⟨p1, p2, p3, p4, t1, t2, t3⟩

/-- A nonzero 6j symbol has four admissible triads. -/
lemma triad_of_sixJSym_ne_zero {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : sixJSym j₁ j₂ j₃ j₄ j₅ j₆ ≠ 0) :
    Triad j₁ j₂ j₃ ∧ Triad j₁ j₅ j₆ ∧ Triad j₄ j₂ j₆ ∧ Triad j₄ j₅ j₃ := by
  have h0 := triads_of_sixJSym_ne_zero h
  have h1 := triads_of_sixJSym_ne_zero (show sixJSym j₁ j₆ j₅ j₄ j₃ j₂ ≠ 0 by rwa [sixJSym_v1])
  have h2 := triads_of_sixJSym_ne_zero (show sixJSym j₆ j₂ j₄ j₃ j₅ j₁ ≠ 0 by rwa [sixJSym_v2])
  have h3 := triads_of_sixJSym_ne_zero (show sixJSym j₅ j₄ j₃ j₂ j₁ j₆ ≠ 0 by rwa [sixJSym_v3])
  unfold Triad
  omega

/-! ## Orthogonality for positive spins, translated from Physlib -/

/-- Only `x = a + b - 2k` with `k ≤ min a b` can satisfy the triangle rule for `(a b x)`, so a sum
over `x ∈ [0, a + b]` of terms vanishing off that set reindexes to a sum over `k`. -/
lemma sum_range_eq_sum_fin (a b : ℕ) (F : ℕ → ℝ) (hF : ∀ x, ¬ Triad a b x → F x = 0) :
    ∑ x ∈ range (a + b + 1), F x = ∑ k : Fin (min a b + 1), F (a + b - 2 * k) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => F (a + b - 2 * k)) (min a b + 1)]
  exact sum_range_triad a b F hF

/-- **6j orthogonality** (doubled units), translated from Physlib's `sum_sixJ_mul_sixJ`:
`Σ_x (x+1)(q+1) {B A x; E F q}{B A x; E F r} = δ_{qr} [(A E q), (B q F) admissible]`, for
`B, E > 0`. -/
theorem sixJSym_orth {B A E F q r : ℕ} (hB : 0 < B) (hE : 0 < E) :
    ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym B A x E F q * sixJSym B A x E F r) =
      if q = r ∧ Triad A E q ∧ Triad B q F then 1 else 0 := by
  have hBA : 0 < B + A := by omega
  have hAE : 0 < A + E := by omega
  -- if `q` is not an admissible label, every term vanishes
  by_cases hq : Triad A E q ∧ Triad B q F
  swap
  · rw [ite_eq_right (fun h => hq ⟨h.2.1, h.2.2⟩)]
    refine sum_eq_zero fun x _ => ?_
    have h0 : sixJSym B A x E F q = 0 := by
      by_contra h
      obtain ⟨-, T2, T3, -⟩ := triad_of_sixJSym_ne_zero h
      exact hq ⟨by unfold Triad at *; omega, by unfold Triad at *; omega⟩
    rw [h0]; ring
  by_cases hr : Triad A E r ∧ Triad B r F
  swap
  · rw [ite_eq_right (show ¬(q = r ∧ Triad A E q ∧ Triad B q F) from fun h => by
      obtain ⟨rfl, h1, h2⟩ := h
      exact hr ⟨h1, h2⟩)]
    refine sum_eq_zero fun x _ => ?_
    have h0 : sixJSym B A x E F r = 0 := by
      by_contra h
      obtain ⟨-, T2, T3, -⟩ := triad_of_sixJSym_ne_zero h
      exact hr ⟨by unfold Triad at *; omega, by unfold Triad at *; omega⟩
    rw [h0]; ring
  obtain ⟨⟨q0, q1, q2, q3⟩, ⟨q4, q5, q6, q7⟩⟩ := hq
  obtain ⟨⟨r0, r1, r2, r3⟩, ⟨r4, r5, r6, r7⟩⟩ := hr
  have hPhys := sum_sixJ_mul_sixJ (a := B) (b := A) (c := E) hBA hAE hB hE
    (K := (B + A + E - F) / 2)
    (k₃ := ⟨(A + E - q) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩)
    (k₃' := ⟨(A + E - r) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩)
    (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega)
    (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega)
  have hrhs : (if (⟨(A + E - q) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨by omega, by omega⟩)⟩ :
      Fin (min A E + 1)) = ⟨(A + E - r) / 2, Nat.lt_succ_iff.mpr (Nat.le_min.mpr
        ⟨by omega, by omega⟩)⟩ then (1 : ℝ) else 0) =
      if q = r ∧ Triad A E q ∧ Triad B q F then 1 else 0 := by
    by_cases hqr : q = r
    · subst hqr
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, ⟨q0, q1, q2, q3⟩, ⟨q4, q5, q6, q7⟩⟩]
    · rw [ite_eq_right (fun h => hqr (by have := congrArg Fin.val h; simp only at this; omega)),
        ite_eq_right (fun h => hqr h.1)]
  rw [← hrhs, ← hPhys, sum_range_eq_sum_fin B A]
  · refine sum_congr rfl fun k₁ _ => ?_
    have hk₁ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁.isLt)
    by_cases hA : ValidA B A E ((B + A + E - F) / 2) k₁
    · rw [sixJ_eq_sixJSym hBA hAE hB hE hA (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;>
          omega),
        sixJ_eq_sixJSym hBA hAE hB hE hA (by unfold ValidB; refine ⟨?_, ?_, ?_⟩ <;> simp only <;>
          omega)]
      simp only
      obtain ⟨a1, a2, a3⟩ := hA
      rw [show B + A + E - 2 * ((B + A + E - F) / 2) = F by omega,
        show A + E - 2 * ((A + E - q) / 2) = q by omega,
        show A + E - 2 * ((A + E - r) / 2) = r by omega]
      push_cast
      ring
    · rw [show sixJSym B A (B + A - 2 * (k₁ : ℕ)) E F q = 0 by
        by_contra h
        obtain ⟨-, -, -, T4⟩ := triad_of_sixJSym_ne_zero h
        exact hA (by unfold Triad at T4; unfold ValidA; refine ⟨?_, ?_, ?_⟩ <;> omega)]
      unfold sixJ
      rw [ite_eq_right (fun h => hA h.1)]
      ring
  · intro x hx
    have h0 : sixJSym B A x E F q = 0 := by
      by_contra h
      exact hx (triad_of_sixJSym_ne_zero h).1
    rw [h0]; ring

/-! ## Orthogonality for all spins -/

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
`Σ_x (x + 1) {B A x; E F q}² = [Triad A E q ∧ Triad B q F] / (q + 1)`. -/
theorem sixJSym_sq_orth (B A E F q : ℕ) :
    ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 =
      if Triad A E q ∧ Triad B q F then 1 / ((q : ℝ) + 1) else 0 := by
  have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
  -- from the version with the extra factor `(q + 1)`
  have of_orth : (∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
      (sixJSym B A x E F q * sixJSym B A x E F q) =
        if Triad A E q ∧ Triad B q F then 1 else 0) →
      ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 =
        if Triad A E q ∧ Triad B q F then 1 / ((q : ℝ) + 1) else 0 := by
    intro h
    have h' : ((q : ℝ) + 1) * ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 =
        if Triad A E q ∧ Triad B q F then 1 else 0 := by
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
      have : ∀ x, sixJSym B A x 0 F q = sixJSym 0 F x B A q :=
        fun x => (sixJSym_flip _ _ _ _ _ _).symm
      simp only [this, sixJSym_zero_left]
      rw [sum_sq_single _ F A q _ _ (by rw [← pow_mul, mul_comm, pow_mul]; norm_num)]
      by_cases h : F < B + A + 1 ∧ q = A ∧ Triad F A B
      · obtain ⟨h1, rfl, h3⟩ := h
        rw [ite_eq_left ⟨h1, rfl, h3⟩, ite_eq_left (by unfold Triad at h3 ⊢; omega)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (by unfold Triad at h' ⊢; omega))]
  · have hB0 : B = 0 := by omega
    subst hB0
    simp only [sixJSym_zero_left]
    rw [sum_sq_single _ A F q _ _ (by rw [← pow_mul, mul_comm, pow_mul]; norm_num)]
    by_cases h : A < 0 + A + 1 ∧ q = F ∧ Triad A F E
    · obtain ⟨-, rfl, h3⟩ := h
      rw [ite_eq_left ⟨by omega, rfl, h3⟩, ite_eq_left (by unfold Triad at h3 ⊢; omega)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (by unfold Triad at h' ⊢; omega))]

/-- **6j orthogonality for all spins** (doubled units):
`Σ_x (x+1)(q+1) {B A x; E F q}{B A x; E F r} = δ_{qr} [(A E q), (B q F) admissible]`.
For `B, E > 0` this is `sixJSym_orth`; the diagonal is `sixJSym_sq_orth`; off the diagonal a zero
`B` or `E` forces `q = r` by the triangle rule. -/
theorem sixJSym_orth_all (B A E F q r : ℕ) :
    ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym B A x E F q * sixJSym B A x E F r) =
      if q = r ∧ Triad A E q ∧ Triad B q F then 1 else 0 := by
  by_cases hBE : 0 < B ∧ 0 < E
  · exact sixJSym_orth hBE.1 hBE.2
  by_cases hqr : q = r
  · subst hqr
    have hq : ((q : ℝ) + 1) ≠ 0 := by positivity
    rw [show ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym B A x E F q * sixJSym B A x E F q) =
        ((q : ℝ) + 1) * ∑ x ∈ range (B + A + 1), ((x : ℝ) + 1) * (sixJSym B A x E F q) ^ 2 by
      rw [mul_sum]; exact sum_congr rfl fun x _ => by ring, sixJSym_sq_orth]
    by_cases ht : Triad A E q ∧ Triad B q F
    · rw [ite_eq_left ht, ite_eq_left ⟨rfl, ht⟩]; field_simp
    · rw [ite_eq_right ht, ite_eq_right (fun h => ht h.2)]; ring
  · rw [ite_eq_right (fun h => hqr h.1)]
    refine sum_eq_zero fun x _ => ?_
    by_cases h1 : sixJSym B A x E F q = 0
    · rw [h1]; ring
    by_cases h2 : sixJSym B A x E F r = 0
    · rw [h2]; ring
    exfalso
    obtain ⟨-, a2, a3, -⟩ := triad_of_sixJSym_ne_zero h1
    obtain ⟨-, b2, b3, -⟩ := triad_of_sixJSym_ne_zero h2
    unfold Triad at a2 a3 b2 b3
    omega

end PhyslibAlpha.Sl2
