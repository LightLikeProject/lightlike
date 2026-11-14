import Lightlike.Asymptotics.HalfSixJ
import Lightlike.Asymptotics.RacahBE
import Lightlike.Asymptotics.Assembly

/-!
# Racah's formula for the 6j symbol

`sixJSym_eq_racahW`: Physlib's 6j symbol `sixJSym`, defined as a sum over magnetic quantum
numbers of products of four 3j symbols, equals Racah's single-sum expression `racahW` for all
spins (doubled units).

The proof is a strong induction on the sum of the six spins.
* Inadmissible symbols vanish on both sides.
* A symbol with a zero spin is `sixJSym_zero_left_eq_racahW` after a tetrahedral symmetry.
* Otherwise the Biedenharn–Elliott identity with one spin `½` holds for `sixJSym`
  (`Lightlike.Pentagon.biedenharnElliott`) and for `racahW` (`racahW_be_half`). It expresses
  `{p q r; f b c}` times the spin-½ symbol `{p q r; r−1 1 p−1}` through symbols with a spin `½`
  (`sixJSym_one_left_eq_racahW`) and symbols `{c p−1 x; r−1 f q}` of smaller total spin.
* The spin-½ factor is nonzero when `q < p + r` (`racahW_be_factor_ne_zero`). Every admissible
  triad of positive spins has an edge with this property, and a column swap moves it to the
  middle.

At even doubled spins `racahW` is the integer-spin expression `racahDelta J * racahSum J` of
`Assembly.lean`, so `racahFormula` proves `RacahFormula`. The Ponzano–Regge formula then rests
only on the asymptotics of Racah's sum (`ponzanoReggeFormula_of_racahSumAsymptotics`).
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.Asymptotics

/-! ## Nonvanishing of the spin-½ symbols -/

/-- `racahW {½ a a+½; e d d+½}` (triangle parametrisation of `sixJSym_half_plus`) is nonzero. -/
lemma racahW_half_plus_ne_zero (u v w : ℕ) :
    racahW 1 (u + w) (u + w + 1) (u + v + 1) (v + w) (v + w + 1) ≠ 0 := by
  have hA : Adm6 1 (u + w) (u + w + 1) (u + v + 1) (v + w) (v + w + 1) := by
    unfold Adm6 Tri; omega
  rw [racahW_of_adm hA, rsum_eq_single (u + v + w + 1) 2 0 (by simp [faceD]; omega)
      (by simp [quadD]; omega) (quadD_nonneg _ _ _ _ _ _),
    rterm_eq_of ![v, u, 0, 0] ![0, w, 1] (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega)]
  have tp : ∀ x y z : ℕ, 0 < triD x y z := fun x y z => Real.sqrt_pos.mpr (triSq_pos x y z)
  exact mul_ne_zero (mul_pos (mul_pos (mul_pos (tp _ _ _) (tp _ _ _)) (tp _ _ _)) (tp _ _ _)).ne'
    (div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
      (mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => by positivity)
        (prod_ne_zero_iff.mpr fun i _ => by positivity)))

/-- `racahW {½ a a−½; e d d+½}` (triangle parametrisation of `sixJSym_half_minus`) is
nonzero. -/
lemma racahW_half_minus_ne_zero (u v w : ℕ) :
    racahW 1 (u + w + 1) (u + w) (u + v) (v + w) (v + w + 1) ≠ 0 := by
  have hA : Adm6 1 (u + w + 1) (u + w) (u + v) (v + w) (v + w + 1) := by
    unfold Adm6 Tri; omega
  rw [racahW_of_adm hA, rsum_eq_single (u + v + w + 1) 2 0 (by simp [faceD]; omega)
      (by simp [quadD]; omega) (quadD_nonneg _ _ _ _ _ _),
    rterm_eq_of ![v, u, 0, 1] ![0, w, 0] (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega)]
  have tp : ∀ x y z : ℕ, 0 < triD x y z := fun x y z => Real.sqrt_pos.mpr (triSq_pos x y z)
  exact mul_ne_zero (mul_pos (mul_pos (mul_pos (tp _ _ _) (tp _ _ _)) (tp _ _ _)) (tp _ _ _)).ne'
    (div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity))
      (mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => by positivity)
        (prod_ne_zero_iff.mpr fun i _ => by positivity)))

/-- An admissible `racahW` symbol with spins `½` and `j₆ = j₅ + ½` is nonzero. -/
lemma racahW_one_left_succ_ne_zero {j₂ j₃ j₄ j₅ : ℕ} (hA : Adm6 1 j₂ j₃ j₄ j₅ (j₅ + 1)) :
    racahW 1 j₂ j₃ j₄ j₅ (j₅ + 1) ≠ 0 := by
  obtain ⟨h1, -, h3, h4⟩ := hA
  unfold Tri at h1 h3 h4
  rcases (by omega : j₃ = j₂ + 1 ∨ j₂ = j₃ + 1) with rfl | rfl
  · obtain ⟨u, v, w, rfl, rfl, rfl⟩ : ∃ u v w, j₂ = u + w ∧ j₄ = u + v + 1 ∧ j₅ = v + w :=
      ⟨(j₂ + j₄ - 1 - j₅) / 2, (j₅ + j₄ - 1 - j₂) / 2, (j₂ + j₅ + 1 - j₄) / 2, by omega,
        by omega, by omega⟩
    exact racahW_half_plus_ne_zero u v w
  · obtain ⟨u, v, w, rfl, rfl, rfl⟩ : ∃ u v w, j₃ = u + w ∧ j₄ = u + v ∧ j₅ = v + w :=
      ⟨(j₃ + j₄ - j₅) / 2, (j₄ + j₅ - j₃) / 2, (j₃ + j₅ - j₄) / 2, by omega, by omega, by omega⟩
    exact racahW_half_minus_ne_zero u v w

/-- An admissible `racahW` symbol with a spin `½` in the first place is nonzero: its Racah sum
has a single term. -/
theorem racahW_one_left_ne_zero {j₂ j₃ j₄ j₅ j₆ : ℕ} (hA : Adm6 1 j₂ j₃ j₄ j₅ j₆) :
    racahW 1 j₂ j₃ j₄ j₅ j₆ ≠ 0 := by
  have h2 := hA.2.1
  unfold Tri at h2
  rcases (by omega : j₆ = j₅ + 1 ∨ j₅ = j₆ + 1) with rfl | rfl
  · exact racahW_one_left_succ_ne_zero hA
  · rw [← racahW_swap23]
    exact racahW_one_left_succ_ne_zero ((adm6_swap23 1 j₃ j₂ j₄ j₆ (j₆ + 1)).1 hA)

/-- The spin-½ factor `{p q r; r−1 1 p−1}` of the Biedenharn–Elliott step is nonzero when the
triad `(p q r)` is not stretched at `q`. -/
lemma racahW_be_factor_ne_zero {p q r : ℕ} (hT : Tri p q r) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hq : q ≠ p + r) : racahW p q r (r - 1) 1 (p - 1) ≠ 0 := by
  rw [← racahW_flipswap p q r (r - 1) 1 (p - 1)]
  exact racahW_one_left_ne_zero (by unfold Adm6 Tri at *; omega)

/-! ## Transport along the tetrahedral symmetries -/

/-- The statement `sixJSym = racahW` is invariant under swapping the first two columns. -/
lemma eq_racahW_swap12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₂ j₁ j₃ j₅ j₄ j₆ = racahW j₂ j₁ j₃ j₅ j₄ j₆ ↔
      sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  rw [sixJSym_swap₁₂ j₁ j₂ j₃ j₄ j₅ j₆, racahW_swap12]

/-- The statement `sixJSym = racahW` is invariant under swapping the last two columns. -/
lemma eq_racahW_swap23 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₃ j₂ j₄ j₆ j₅ = racahW j₁ j₃ j₂ j₄ j₆ j₅ ↔
      sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  rw [sixJSym_swap₂₃ j₁ j₂ j₃ j₄ j₅ j₆, racahW_swap23]

/-- The statement `sixJSym = racahW` is invariant under exchanging upper and lower spins in the
first two columns. -/
lemma eq_racahW_flip12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₄ j₅ j₃ j₁ j₂ j₆ = racahW j₄ j₅ j₃ j₁ j₂ j₆ ↔
      sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  rw [sixJSym_flip₁₂ j₁ j₂ j₃ j₄ j₅ j₆, racahW_flip12]

/-- Racah's formula with a spin `½` in the fifth place, from `sixJSym_one_left_eq_racahW`. -/
lemma sixJSym_eq_racahW_five (j₁ j₂ j₃ j₄ j₆ : ℕ) :
    sixJSym j₁ j₂ j₃ j₄ 1 j₆ = racahW j₁ j₂ j₃ j₄ 1 j₆ :=
  (eq_racahW_flip12 j₁ j₂ j₃ j₄ 1 j₆).1
    ((eq_racahW_swap12 j₄ 1 j₃ j₁ j₂ j₆).1 (sixJSym_one_left_eq_racahW j₄ j₃ j₂ j₁ j₆))

/-! ## The induction -/

/-- **The Biedenharn–Elliott step.** If Racah's formula holds for all symbols of smaller total
spin, it holds for an admissible `{p q r; f b c}` with `p, r, b ≥ ½` and `q < p + r`. -/
lemma sixJSym_eq_racahW_step {p q r f b c : ℕ}
    (ih : ∀ k₁ k₂ k₃ k₄ k₅ k₆ : ℕ, k₁ + k₂ + k₃ + k₄ + k₅ + k₆ < p + q + r + f + b + c →
      sixJSym k₁ k₂ k₃ k₄ k₅ k₆ = racahW k₁ k₂ k₃ k₄ k₅ k₆)
    (hA : Adm6 p q r f b c) (hp : 1 ≤ p) (hr : 1 ≤ r) (hb : 1 ≤ b) (hq : q ≠ p + r) :
    sixJSym p q r f b c = racahW p q r f b c := by
  have hL : beLHS 1 b c (p - 1) (r - 1) f p q r =
      ∑ x ∈ range (1 + b + 1), wTerm 1 b c (p - 1) (r - 1) f p q r x := by
    unfold beLHS
    refine sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    rw [wTerm, sixJSym_one_left_eq_racahW, sixJSym_eq_racahW_five (r - 1) f x b r,
      ih c (p - 1) x (r - 1) f q (by omega)]
  have hBE := biedenharnElliott 1 b c (p - 1) (r - 1) f p q r
  rw [hL, sum_eq_add (b + 1) (b - 1) (by omega)] at hBE
  · unfold beRHS at hBE
    rw [← racahW_be_half hA hp hr hb, sixJSym_eq_racahW_five p q r (r - 1) (p - 1)] at hBE
    exact (mul_left_cancel₀ (racahW_be_factor_ne_zero hA.1 hp hr hq) hBE).symm
  · intro x _ hx
    rw [wTerm, racahW_of_not (j₁ := 1) (j₂ := b) (j₃ := x)
      (fun h => by obtain ⟨h1, -⟩ := h; unfold Tri at h1; omega)]
    ring
  · exact fun h => absurd (mem_range.mpr (by omega)) h
  · exact fun h => absurd (mem_range.mpr (by omega)) h

/-- **Racah's formula**: Physlib's 6j symbol equals Racah's single-sum expression `racahW` for
all spins (doubled units),

  `{j₁ j₂ j₃; j₄ j₅ j₆} = Δ(j₁j₂j₃) Δ(j₁j₅j₆) Δ(j₄j₂j₆) Δ(j₄j₅j₃)
      Σ_t (−1)^t (t+1)! / (∏ᵢ (t − Aᵢ)! ∏ₖ (Bₖ − t)!)`

for admissible spins, and both sides vanish otherwise. -/
theorem sixJSym_eq_racahW (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  suffices h : ∀ n, ∀ j₁ j₂ j₃ j₄ j₅ j₆ : ℕ, j₁ + j₂ + j₃ + j₄ + j₅ + j₆ = n →
      sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ from h _ _ _ _ _ _ _ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j₁ j₂ j₃ j₄ j₅ j₆ hn
  have ih' : ∀ k₁ k₂ k₃ k₄ k₅ k₆ : ℕ, k₁ + k₂ + k₃ + k₄ + k₅ + k₆ < n →
      sixJSym k₁ k₂ k₃ k₄ k₅ k₆ = racahW k₁ k₂ k₃ k₄ k₅ k₆ :=
    fun k₁ k₂ k₃ k₄ k₅ k₆ hk => ih _ hk _ _ _ _ _ _ rfl
  by_cases hA : Adm6 j₁ j₂ j₃ j₄ j₅ j₆
  swap
  · rw [racahW_of_not hA]
    by_contra h
    exact hA (tri_of_sixJSym_ne_zero h)
  -- a zero spin, moved to the first place
  by_cases h1 : j₁ = 0
  · subst h1
    exact sixJSym_zero_left_eq_racahW _ _ _ _ _
  by_cases h2 : j₂ = 0
  · subst h2
    exact (eq_racahW_swap12 j₁ 0 j₃ j₄ j₅ j₆).1 (sixJSym_zero_left_eq_racahW _ _ _ _ _)
  by_cases h3 : j₃ = 0
  · subst h3
    exact (eq_racahW_swap23 j₁ j₂ 0 j₄ j₅ j₆).1
      ((eq_racahW_swap12 j₁ 0 j₂ j₄ j₆ j₅).1 (sixJSym_zero_left_eq_racahW _ _ _ _ _))
  by_cases h4 : j₄ = 0
  · subst h4
    exact (eq_racahW_flip12 j₁ j₂ j₃ 0 j₅ j₆).1 (sixJSym_zero_left_eq_racahW _ _ _ _ _)
  by_cases h5 : j₅ = 0
  · subst h5
    exact (eq_racahW_flip12 j₁ j₂ j₃ j₄ 0 j₆).1
      ((eq_racahW_swap12 j₄ 0 j₃ j₁ j₂ j₆).1 (sixJSym_zero_left_eq_racahW _ _ _ _ _))
  by_cases h6 : j₆ = 0
  · subst h6
    exact (eq_racahW_swap23 j₁ j₂ j₃ j₄ j₅ 0).1 ((eq_racahW_flip12 j₁ j₃ j₂ j₄ 0 j₅).1
      ((eq_racahW_swap12 j₄ 0 j₂ j₁ j₃ j₅).1 (sixJSym_zero_left_eq_racahW _ _ _ _ _)))
  -- all spins positive: the Biedenharn–Elliott step at a non-stretched edge of `(j₁ j₂ j₃)`
  by_cases hq : j₂ = j₁ + j₃
  · exact (eq_racahW_swap12 j₁ j₂ j₃ j₄ j₅ j₆).1
      (sixJSym_eq_racahW_step (fun k₁ k₂ k₃ k₄ k₅ k₆ hk => ih' k₁ k₂ k₃ k₄ k₅ k₆ (by omega))
        ((adm6_swap12 j₁ j₂ j₃ j₄ j₅ j₆).2 hA) (by omega) (by omega) (by omega) (by omega))
  · exact sixJSym_eq_racahW_step (fun k₁ k₂ k₃ k₄ k₅ k₆ hk => ih' k₁ k₂ k₃ k₄ k₅ k₆ (by omega))
      hA (by omega) (by omega) (by omega) hq

/-! ## Integer spins -/

/-- At even doubled spins the triangle coefficient `triD` is `triadDelta` of `Assembly.lean`. -/
lemma triD_two_mul (a b c : ℕ) : triD (2 * a) (2 * b) (2 * c) = triadDelta a b c := by
  unfold triD triSq triadDelta
  rw [show (2 * a + 2 * b - 2 * c) / 2 = a + b - c by omega,
    show (2 * a + 2 * c - 2 * b) / 2 = a + c - b by omega,
    show (2 * b + 2 * c - 2 * a) / 2 = b + c - a by omega,
    show (2 * a + 2 * b + 2 * c) / 2 = a + b + c by omega]

/-- At even doubled spins the halved face sums `faceD` are the face sums `faceN`. -/
lemma faceD_two_mul (J : Fin 6 → ℕ) :
    faceD (2 * J 0) (2 * J 1) (2 * J 2) (2 * J 3) (2 * J 4) (2 * J 5) = fun i => (faceN J i : ℤ) := by
  funext i
  fin_cases i <;> simp [faceD, faceN] <;> omega

/-- At even doubled spins the halved quad sums `quadD` are the quad sums `quadN`. -/
lemma quadD_two_mul (J : Fin 6 → ℕ) :
    quadD (2 * J 0) (2 * J 1) (2 * J 2) (2 * J 3) (2 * J 4) (2 * J 5) = fun k => (quadN J k : ℤ) := by
  funext k
  fin_cases k <;> simp [quadD, quadN] <;> omega

/-- **Racah's formula** at integer spins, `RacahFormula` of `Assembly.lean`:
`{J₀ J₁ J₂; J₃ J₄ J₅} = racahDelta J * racahSum J` for four triangular faces. -/
theorem racahFormula : RacahFormula := by
  intro J h₁ h₂ h₃ h₄
  have hA : Adm6 (2 * J 0) (2 * J 1) (2 * J 2) (2 * J 3) (2 * J 4) (2 * J 5) := by
    unfold PR.IsTriad at h₁ h₂ h₃ h₄
    unfold Adm6 Tri
    omega
  rw [sixJSym_eq_racahW, racahW_of_adm hA, triD_two_mul, triD_two_mul, triD_two_mul,
    triD_two_mul, faceD_two_mul, quadD_two_mul, ← racahDelta]
  congr 1
  rw [← sum_range_rterm_eq_rsum (N := quadN J 0 + 1) (fun k => by positivity) 0 (by simp)]
  refine sum_congr rfl fun t _ => ?_
  rw [rterm]; ring

/-- **The Ponzano–Regge formula from the asymptotics of Racah's sum**: with Racah's formula
proven (`racahFormula`), `PR.PonzanoReggeFormula` follows from `RacahSumAsymptotics` alone. -/
theorem ponzanoReggeFormula_of_racahSumAsymptotics (hS : RacahSumAsymptotics) :
    PR.PonzanoReggeFormula :=
  ponzanoReggeFormula_of racahFormula hS

end Lightlike.Asymptotics
