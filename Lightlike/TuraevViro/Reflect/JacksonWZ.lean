import Mathlib

/-!
# A telescoping certificate for the terminating very-well-poised `₆φ₅` sum

With `q`-Pochhammer symbols `pk z q k = (z; q)_k` and
`T x k = (1 - a q^{2k}) / (1 - a) · (a, b, c, 1/x; q)_k / (q, aq/b, aq/c, aqx; q)_k · (aqx/(bc))^k`,
the difference `T (q x) k - ρ x · T x k` telescopes in `k`: it equals `G x (k+1) - G x k` for an
explicit `G` that carries no pole. Summing over `k = 0, …, n+1` at `x = q^n` gives the recurrence
`S (n+1) = ρ (n) S n`, and by induction on `n` Jackson's sum `jackson_sum`. The identity holds for
generic `x`; all denominators that occur are hypotheses.

The summation is the terminating very-well-poised `₆φ₅` sum, DLMF §17.7(iii), equation (17.7.16)
(`jacksonRhs` is its right side). The proof here is a direct check of the telescoping identity
(found by computer algebra and verified here); it does not follow a published derivation.

The hypotheses `JHyp` of the first version require nonvanishing up to index `N + 2`. The proof only
touches indices up to `N`, so `JHypT` states exactly that, and `jackson_sum` is kept as its
corollary. `JHypT` still fails when a numerator and a denominator vanish together at index `N`
(the removable case), which is not covered here.

## Main results

* `jackson_sumT`: for `JHypT q a b c N` and `n ≤ N`, the sum of `Tj q a b c (q ^ n) k` over
  `k ≤ n` equals `jacksonRhs q a b c n`.
* `jackson_sum`: the same under the stronger `JHyp q a b c N`.

## References

* DLMF §17.7(iii), equation (17.7.16).
-/

namespace Lightlike.TV.Refl

/-- The `q`-Pochhammer symbol `(z; q)_k`. -/
def pk (z q : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => pk z q k * (1 - z * q ^ k)

/-- Shifting the argument of a `q`-Pochhammer symbol down by `q`. -/
lemma pk_shift {q : ℂ} (hq : q ≠ 0) (z : ℂ) (j : ℕ) :
    pk (z / q) q (j + 1) = (1 - z / q) * pk z q j := by
  induction j with
  | zero => simp [pk]
  | succ j ih =>
    rw [pk, ih, pk]
    have : z / q * q ^ (j + 1) = z * q ^ j := by field_simp; ring
    rw [this]; ring

/-- Multiplying the argument of a `q`-Pochhammer symbol by `q`. -/
lemma pk_mul_q (z q : ℂ) (k : ℕ) :
    pk (z * q) q k * (1 - z) = pk z q k * (1 - z * q ^ k) := by
  induction k with
  | zero => simp [pk]
  | succ k ih =>
    rw [pk, pk]
    have : z * q * q ^ k = z * q ^ (k + 1) := by ring
    rw [this]
    calc pk (z * q) q k * (1 - z * q ^ (k + 1)) * (1 - z)
        = (pk (z * q) q k * (1 - z)) * (1 - z * q ^ (k + 1)) := by ring
      _ = _ := by rw [ih]

/-- The summand of the terminating very-well-poised `₆φ₅` sum. -/
noncomputable def Tj (q a b c x : ℂ) (k : ℕ) : ℂ :=
  (1 - a * q ^ (2 * k)) / (1 - a) *
    (pk a q k * pk b q k * pk c q k * pk x⁻¹ q k) /
      (pk q q k * pk (a * q / b) q k * pk (a * q / c) q k * pk (a * q * x) q k) *
    (a * q * x / (b * c)) ^ k

/-- The ratio of consecutive Jackson sums. -/
noncomputable def rhoJ (q a b c x : ℂ) : ℂ :=
  (1 - a * q * x) * (1 - a * q * x / (b * c)) / ((1 - a * q * x / b) * (1 - a * q * x / c))

/-- The pole-free telescoping partner of `Tj`. -/
noncomputable def Gj (q a b c x : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 =>
    (1 - a * q * x) / ((1 - a * q * x / b) * (1 - a * q * x / c)) *
      ((1 - q ^ (m + 1)) * (1 - a * q ^ (m + 1) / b) * (1 - a * q ^ (m + 1) / c) / (1 - a)) *
      (pk a q (m + 1) * pk b q (m + 1) * pk c q (m + 1) * pk x⁻¹ q m) /
        (pk q q (m + 1) * pk (a * q / b) q (m + 1) * pk (a * q / c) q (m + 1) *
          pk (a * q * x) q (m + 1)) * (a * q * x / (b * c)) ^ (m + 1)

/-- The first step of the telescoping identity. -/
lemma wz_zero {q a b c x : ℂ} (hq : q ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : x ≠ 0) (ha : 1 - a ≠ 0)
    (h1 : 1 - a * q * x ≠ 0) (h2 : 1 - a * q * x / b ≠ 0) (h3 : 1 - a * q * x / c ≠ 0)
    (h4 : 1 - q ≠ 0) (h5 : 1 - a * q / b ≠ 0) (h6 : 1 - a * q / c ≠ 0)
    (h7 : 1 - a * q * x * q ≠ 0) :
    Tj q a b c (q * x) 0 - rhoJ q a b c x * Tj q a b c x 0 = Gj q a b c x 1 - Gj q a b c x 0 := by
  have h2c : b - a * q * x ≠ 0 := by
    intro e; apply h2; rw [show 1 - a * q * x / b = (b - a * q * x) / b by field_simp, e, zero_div]
  have h3c : c - a * q * x ≠ 0 := by
    intro e; apply h3; rw [show 1 - a * q * x / c = (c - a * q * x) / c by field_simp, e, zero_div]
  have h5c : b - a * q ≠ 0 := by
    intro e; apply h5; rw [show 1 - a * q / b = (b - a * q) / b by field_simp, e, zero_div]
  have h6c : c - a * q ≠ 0 := by
    intro e; apply h6; rw [show 1 - a * q / c = (c - a * q) / c by field_simp, e, zero_div]
  simp only [Tj, rhoJ, Gj, pk]
  simp
  field_simp
  ring

/-- A `q`-Pochhammer symbol is nonzero when none of its factors vanishes. -/
lemma pk_ne_zero (z q : ℂ) (n : ℕ) (h : ∀ i < n, 1 - z * q ^ i ≠ 0) : pk z q n ≠ 0 := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    rw [pk]
    exact mul_ne_zero (ih fun i hi => h i (by omega)) (h n (by omega))

/-- Clearing the denominator `b` in a nonvanishing factor. -/
lemma clr {b : ℂ} (hb : b ≠ 0) (u v : ℂ) (h : 1 - u / b * v ≠ 0) : b - u * v ≠ 0 := by
  intro e; apply h
  rw [show 1 - u / b * v = (b - u * v) / b by field_simp, e, zero_div]

/-- Clearing the denominator `b` in a nonvanishing factor of the form `1 - t / b`. -/
lemma clr' {b : ℂ} (hb : b ≠ 0) (t : ℂ) (h : 1 - t / b ≠ 0) : b - t ≠ 0 := by
  intro e; apply h
  rw [show 1 - t / b = (b - t) / b by field_simp, e, zero_div]

set_option maxHeartbeats 400000 in
set_option maxRecDepth 20000 in
/-- The rational identity of the general telescoping step, in the form in which the step meets
it: `A, B, C, X, Wj` and the four Pochhammer values `P1'` to `P4'` are the common factor, and the
other denominators are written out. -/
lemma wz_goal {q a b c x m A B C X Wj : ℂ}
    (hq : q ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : x ≠ 0) (ha : 1 - a ≠ 0)
    (h1 : 1 - a * q * x ≠ 0) (h2 : 1 - a * q * x / b ≠ 0) (h3 : 1 - a * q * x / c ≠ 0)
    (f1 : 1 - q * m ≠ 0) (f1' : 1 - q * (m * q) ≠ 0)
    (f2 : 1 - a * q / b * m ≠ 0) (f2' : 1 - a * q / b * (m * q) ≠ 0)
    (f3 : 1 - a * q / c * m ≠ 0) (f3' : 1 - a * q / c * (m * q) ≠ 0)
    (f4 : 1 - a * q * x * m ≠ 0) (f4' : 1 - a * q * x * (m * q) ≠ 0)
    (P1' P2' P3' P4' : ℂ) (hP1 : P1' ≠ 0) (hP2 : P2' ≠ 0) (hP3 : P3' ≠ 0) (hP4 : P4' ≠ 0) :
    (1 - a * (q ^ 0 * q * q * (m ^ 0 * m * m))) / (1 - a) *
            (A * (1 - a * m) * (B * (1 - b * m)) * (C * (1 - c * m)) * ((1 - x⁻¹ / q) * X)) /
          (P1' * (1 - q * m) * (P2' * (1 - a * q / b * m)) * (P3' * (1 - a * q / c * m)) *
            (P4' * (1 - a * q * x * m) * (1 - a * q * x * (m * q)) / (1 - a * q * x))) *
        (Wj * m * (a * q * (q * x) / (b * c))) -
      (1 - a * q * x) * (1 - a * q * x / (b * c)) / ((1 - a * q * x / b) * (1 - a * q * x / c)) *
        ((1 - a * (q ^ 0 * q * q * (m ^ 0 * m * m))) / (1 - a) *
              (A * (1 - a * m) * (B * (1 - b * m)) * (C * (1 - c * m)) * (X * (1 - x⁻¹ * m))) /
            (P1' * (1 - q * m) * (P2' * (1 - a * q / b * m)) * (P3' * (1 - a * q / c * m)) *
              (P4' * (1 - a * q * x * m))) *
          (Wj * (a * q * x / (b * c)))) =
    (1 - a * q * x) / ((1 - a * q * x / b) * (1 - a * q * x / c)) *
              ((1 - m * q * q) * (1 - a * (m * q * q) / b) * (1 - a * (m * q * q) / c) / (1 - a)) *
            (A * (1 - a * m) * (1 - a * (m * q)) * (B * (1 - b * m) * (1 - b * (m * q))) *
                (C * (1 - c * m) * (1 - c * (m * q))) *
              (X * (1 - x⁻¹ * m))) /
          (P1' * (1 - q * m) * (1 - q * (m * q)) * (P2' * (1 - a * q / b * m) * (1 - a * q / b * (m * q))) *
              (P3' * (1 - a * q / c * m) * (1 - a * q / c * (m * q))) *
            (P4' * (1 - a * q * x * m) * (1 - a * q * x * (m * q)))) *
        (Wj * (a * q * x / (b * c)) * (a * q * x / (b * c))) -
      (1 - a * q * x) / ((1 - a * q * x / b) * (1 - a * q * x / c)) *
              ((1 - m * q) * (1 - a * (m * q) / b) * (1 - a * (m * q) / c) / (1 - a)) *
            (A * (1 - a * m) * (B * (1 - b * m)) * (C * (1 - c * m)) * X) /
          (P1' * (1 - q * m) * (P2' * (1 - a * q / b * m)) * (P3' * (1 - a * q / c * m)) *
            (P4' * (1 - a * q * x * m))) *
        (Wj * (a * q * x / (b * c))) := by
  obtain ⟨β, rfl⟩ : ∃ β, b = β⁻¹ := ⟨b⁻¹, (inv_inv b).symm⟩
  obtain ⟨γ, rfl⟩ : ∃ γ, c = γ⁻¹ := ⟨c⁻¹, (inv_inv c).symm⟩
  simp only [← mul_inv, div_inv_eq_mul, ne_eq, inv_eq_zero] at *
  generalize hA : 1 - a = D0 at ha ⊢
  generalize hP : 1 - a * q * x = P at h1 ⊢
  generalize hPb : 1 - a * q * x * β = Pb at h2 ⊢
  generalize hPc : 1 - a * q * x * γ = Pc at h3 ⊢
  generalize hD1 : 1 - q * m = D1 at f1 ⊢
  generalize hE1 : 1 - q * (m * q) = E1 at f1' ⊢
  generalize hD2 : 1 - a * q * β * m = D2 at f2 ⊢
  generalize hE2 : 1 - a * q * β * (m * q) = E2 at f2' ⊢
  generalize hD3 : 1 - a * q * γ * m = D3 at f3 ⊢
  generalize hE3 : 1 - a * q * γ * (m * q) = E3 at f3' ⊢
  generalize hD4 : 1 - a * q * x * m = D4 at f4 ⊢
  generalize hE4 : 1 - a * q * x * (m * q) = E4 at f4' ⊢
  field_simp
  subst hA hP hPb hPc hD1 hD2 hD3 hD4 hE1 hE2 hE3 hE4
  ring

set_option maxHeartbeats 400000 in
set_option maxRecDepth 20000 in
/-- The general step of the telescoping identity. -/
lemma wz_succ {q a b c x : ℂ} (j : ℕ) (hq : q ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : x ≠ 0)
    (ha : 1 - a ≠ 0) (h1 : 1 - a * q * x ≠ 0) (h2 : 1 - a * q * x / b ≠ 0)
    (h3 : 1 - a * q * x / c ≠ 0)
    (hP1 : ∀ i < j + 2, 1 - q * q ^ i ≠ 0) (hP2 : ∀ i < j + 2, 1 - a * q / b * q ^ i ≠ 0)
    (hP3 : ∀ i < j + 2, 1 - a * q / c * q ^ i ≠ 0) (hP4 : ∀ i < j + 2, 1 - a * q * x * q ^ i ≠ 0) :
    Tj q a b c (q * x) (j + 1) - rhoJ q a b c x * Tj q a b c x (j + 1) =
      Gj q a b c x (j + 2) - Gj q a b c x (j + 1) := by
  have P1 := pk_ne_zero q q j fun i hi => hP1 i (by omega)
  have P2 := pk_ne_zero (a * q / b) q j fun i hi => hP2 i (by omega)
  have P3 := pk_ne_zero (a * q / c) q j fun i hi => hP3 i (by omega)
  have P4 := pk_ne_zero (a * q * x) q j fun i hi => hP4 i (by omega)
  have f1 := hP1 j (by omega); have f1' := hP1 (j + 1) (by omega)
  have f2 := hP2 j (by omega); have f2' := hP2 (j + 1) (by omega)
  have f3 := hP3 j (by omega); have f3' := hP3 (j + 1) (by omega)
  have f4 := hP4 j (by omega); have f4' := hP4 (j + 1) (by omega)
  have g2 := clr hb (a * q) _ f2; have g2' := clr hb (a * q) _ f2'
  have g3 := clr hc (a * q) _ f3; have g3' := clr hc (a * q) _ f3'
  have g2c := clr' hb _ h2; have g3c := clr' hc _ h3
  have hsh : pk (q * x)⁻¹ q (j + 1) = (1 - x⁻¹ / q) * pk x⁻¹ q j := by
    rw [show (q * x)⁻¹ = x⁻¹ / q by rw [mul_inv]; ring]
    exact pk_shift hq _ j
  have hmq : ∀ m : ℕ, pk (a * q * (q * x)) q m * (1 - a * q * x) =
      pk (a * q * x) q m * (1 - a * q * x * q ^ m) := by
    intro m
    have := pk_mul_q (a * q * x) q m
    rw [show a * q * (q * x) = a * q * x * q by ring]
    exact this
  have hD : ∀ m : ℕ, pk (a * q * (q * x)) q m =
      pk (a * q * x) q m * (1 - a * q * x * q ^ m) / (1 - a * q * x) := by
    intro m; rw [eq_div_iff h1]; exact hmq m
  have hq2 : q ^ (2 * (j + 1)) = q ^ 2 * (q ^ j) ^ 2 := by ring
  simp only [Tj, Gj, rhoJ]
  rw [hsh, hD, hq2]
  have hW : (a * q * (q * x) / (b * c)) ^ j = (a * q * x / (b * c)) ^ j * q ^ j := by
    rw [show a * q * (q * x) / (b * c) = a * q * x / (b * c) * q by ring, mul_pow]
  simp only [pk, pow_succ]
  rw [hW]
  generalize (a * q * x / (b * c)) ^ j = Wj
  generalize pk a q j = A
  generalize pk b q j = B
  generalize pk c q j = C
  generalize pk x⁻¹ q j = X
  generalize pk q q j = P1' at P1 ⊢
  generalize pk (a * q / b) q j = P2' at P2 ⊢
  generalize pk (a * q / c) q j = P3' at P3 ⊢
  generalize pk (a * q * x) q j = P4' at P4 ⊢
  rw [pow_succ] at f1' f2' f3' f4'
  generalize q ^ j = m at f1 f1' f2 f2' f3 f3' f4 f4' ⊢
  exact wz_goal hq hb hc hx ha h1 h2 h3 f1 f1' f2 f2' f3 f3' f4 f4' P1' P2' P3' P4' P1 P2 P3 P4

/-- The sum over `k < N + 1` of the telescoping differences, from the one-step identities. -/
lemma wz_sum {q a b c x : ℂ} (N : ℕ)
    (h0 : Tj q a b c (q * x) 0 - rhoJ q a b c x * Tj q a b c x 0 =
      Gj q a b c x 1 - Gj q a b c x 0)
    (hs : ∀ j < N, Tj q a b c (q * x) (j + 1) - rhoJ q a b c x * Tj q a b c x (j + 1) =
      Gj q a b c x (j + 2) - Gj q a b c x (j + 1)) :
    ∑ k ∈ Finset.range (N + 1), (Tj q a b c (q * x) k - rhoJ q a b c x * Tj q a b c x k) =
      Gj q a b c x (N + 1) - Gj q a b c x 0 := by
  rw [← Finset.sum_range_sub (fun k => Gj q a b c x k) (N + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rcases k with _ | j
  · exact h0
  · exact hs j (by have := Finset.mem_range.1 hk; omega)

/-- The nonvanishing conditions under which Jackson's sum is proved for `n ≤ N`. -/
def JHyp (q a b c : ℂ) (N : ℕ) : Prop :=
  q ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ 1 - a ≠ 0 ∧
    (∀ i ≤ N + 2, 1 - q * q ^ i ≠ 0) ∧ (∀ i ≤ N + 2, 1 - a * q / b * q ^ i ≠ 0) ∧
    (∀ i ≤ N + 2, 1 - a * q / c * q ^ i ≠ 0) ∧
    (∀ n ≤ N, ∀ i ≤ N + 2, 1 - a * q * q ^ n * q ^ i ≠ 0) ∧
    (∀ n ≤ N, 1 - a * q * q ^ n / b ≠ 0 ∧ 1 - a * q * q ^ n / c ≠ 0)

/-- The nonvanishing conditions that the proof of Jackson's sum for `n ≤ N` uses: the indices the
telescoping touches are at most `N` (not `N + 2`), and the outer index `n` is below `N`. They hold
in more cases than `JHyp`, for instance when `aq/b` is a power of `q` with an exponent larger than
`N`; they still fail when a numerator and a denominator both vanish at index `N`. -/
def JHypT (q a b c : ℂ) (N : ℕ) : Prop :=
  q ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ 1 - a ≠ 0 ∧
    (∀ i ≤ N, 1 - q * q ^ i ≠ 0) ∧ (∀ i ≤ N, 1 - a * q / b * q ^ i ≠ 0) ∧
    (∀ i ≤ N, 1 - a * q / c * q ^ i ≠ 0) ∧
    (∀ n < N, ∀ i ≤ N, 1 - a * q * q ^ n * q ^ i ≠ 0) ∧
    (∀ n < N, 1 - a * q * q ^ n / b ≠ 0 ∧ 1 - a * q * q ^ n / c ≠ 0)

/-- Every hypothesis of `JHypT` is one of `JHyp`. -/
lemma JHyp.toT {q a b c : ℂ} {N : ℕ} (h : JHyp q a b c N) : JHypT q a b c N := by
  obtain ⟨hq, hb, hc, ha, hP1, hP2, hP3, hP4, hP5⟩ := h
  exact ⟨hq, hb, hc, ha, fun i hi => hP1 i (by omega), fun i hi => hP2 i (by omega),
    fun i hi => hP3 i (by omega), fun n hn i hi => hP4 n (by omega) i (by omega),
    fun n hn => hP5 n (by omega)⟩

/-- The right side of Jackson's sum. -/
noncomputable def jacksonRhs (q a b c : ℂ) (n : ℕ) : ℂ :=
  pk (a * q) q n * pk (a * q / (b * c)) q n / (pk (a * q / b) q n * pk (a * q / c) q n)

/-- The Pochhammer symbol `(q^{-n}; q)_{n+1}` vanishes. -/
lemma pk_inv_pow_zero {q : ℂ} (hq : q ≠ 0) (n : ℕ) : pk (q ^ n)⁻¹ q (n + 1) = 0 := by
  rw [pk, mul_comm]
  have : (q ^ n)⁻¹ * q ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero n hq)
  rw [this]; simp

/-- One step of Jackson's sum under the sharper hypotheses `JHypT`: the sum for `n + 1` is `ρ`
times the sum for `n`. -/
lemma jackson_stepT {q a b c : ℂ} {N : ℕ} (h : JHypT q a b c N) {n : ℕ} (hn : n + 1 ≤ N) :
    ∑ k ∈ Finset.range (n + 2), Tj q a b c (q ^ (n + 1)) k =
      rhoJ q a b c (q ^ n) * ∑ k ∈ Finset.range (n + 1), Tj q a b c (q ^ n) k := by
  obtain ⟨hq, hb, hc, ha, hP1, hP2, hP3, hP4, hP5⟩ := h
  have hx : q ^ n ≠ 0 := pow_ne_zero n hq
  have hqn : q ^ (n + 1) = q * q ^ n := by ring
  have key := wz_sum (q := q) (a := a) (b := b) (c := c) (x := q ^ n) (n + 1)
    (wz_zero hq hb hc hx ha
      (by simpa using hP4 n (by omega) 0 (by omega))
      (hP5 n (by omega)).1 (hP5 n (by omega)).2
      (by simpa using hP1 0 (by omega)) (by simpa using hP2 0 (by omega))
      (by simpa using hP3 0 (by omega)) (by have := hP4 n (by omega) 1 (by omega); simpa using this))
    (fun j hj => wz_succ j hq hb hc hx ha
      (by simpa using hP4 n (by omega) 0 (by omega))
      (hP5 n (by omega)).1 (hP5 n (by omega)).2
      (fun i hi => hP1 i (by omega)) (fun i hi => hP2 i (by omega))
      (fun i hi => hP3 i (by omega)) (fun i hi => hP4 n (by omega) i (by omega)))
  have hG : Gj q a b c (q ^ n) (n + 1 + 1) = 0 := by
    simp [Gj, pk_inv_pow_zero hq n]
  have hT : Tj q a b c (q ^ n) (n + 1) = 0 := by
    simp [Tj, pk_inv_pow_zero hq n]
  have hG0 : Gj q a b c (q ^ n) 0 = 0 := rfl
  rw [hG, hG0, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  have K : ∑ k ∈ Finset.range (n + 1 + 1), Tj q a b c (q * q ^ n) k =
      rhoJ q a b c (q ^ n) * ∑ k ∈ Finset.range (n + 1 + 1), Tj q a b c (q ^ n) k := by
    linear_combination key
  rw [show Finset.range (n + 2) = Finset.range (n + 1 + 1) from rfl, hqn, K,
    Finset.sum_range_succ (fun k => Tj q a b c (q ^ n) k) (n + 1), hT, add_zero]

/-- **Jackson's sum** under the sharper hypotheses `JHypT`: the terminating very-well-poised `₆φ₅`
sum, with `q^n` the number of terms. -/
theorem jackson_sumT {q a b c : ℂ} {N : ℕ} (h : JHypT q a b c N) :
    ∀ n ≤ N, ∑ k ∈ Finset.range (n + 1), Tj q a b c (q ^ n) k = jacksonRhs q a b c n := by
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨hq, hb, hc, ha, -⟩ := h
    simp [Tj, jacksonRhs, pk, ha]
  | succ n ih =>
    intro hn
    rw [jackson_stepT h hn, ih (by omega)]
    obtain ⟨hq, hb, hc, ha, hP1, hP2, hP3, hP4, hP5⟩ := h
    have P2 := pk_ne_zero (a * q / b) q n fun i hi => hP2 i (by omega)
    have P3 := pk_ne_zero (a * q / c) q n fun i hi => hP3 i (by omega)
    have h2 := (hP5 n (by omega)).1
    have h3 := (hP5 n (by omega)).2
    have h2' : 1 - a * q / b * q ^ n ≠ 0 := by
      intro e; apply h2; rw [← e]; ring
    have h3' : 1 - a * q / c * q ^ n ≠ 0 := by
      intro e; apply h3; rw [← e]; ring
    simp only [rhoJ, jacksonRhs, pk]
    field_simp
    try ring

/-- One step of Jackson's sum: the sum for `n + 1` is `ρ` times the sum for `n`. -/
lemma jackson_step {q a b c : ℂ} {N : ℕ} (h : JHyp q a b c N) {n : ℕ} (hn : n + 1 ≤ N) :
    ∑ k ∈ Finset.range (n + 2), Tj q a b c (q ^ (n + 1)) k =
      rhoJ q a b c (q ^ n) * ∑ k ∈ Finset.range (n + 1), Tj q a b c (q ^ n) k :=
  jackson_stepT h.toT hn

/-- **Jackson's sum**: the terminating very-well-poised `₆φ₅` sum, with `q^n` the number of terms. -/
theorem jackson_sum {q a b c : ℂ} {N : ℕ} (h : JHyp q a b c N) :
    ∀ n ≤ N, ∑ k ∈ Finset.range (n + 1), Tj q a b c (q ^ n) k = jacksonRhs q a b c n :=
  jackson_sumT h.toT

end Lightlike.TV.Refl
