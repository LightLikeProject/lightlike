import Lightlike.Asymptotics.RacahSum
import Lightlike.PonzanoRegge.BEZero

/-!
# Racah's expression for the 6j symbol in doubled units

`racahW j₁ … j₆` is Racah's single-sum expression for `{j₁ j₂ j₃; j₄ j₅ j₆}` with spins in
doubled units (as Physlib's `sixJSym` takes them): zero unless the four triads are admissible,
and otherwise

  `Δ(j₁j₂j₃) Δ(j₁j₅j₆) Δ(j₄j₂j₆) Δ(j₄j₅j₃) · Σ_t (−1)^t (t+1)! / (∏ᵢ (t − Aᵢ)! ∏ₖ (Bₖ − t)!)`,

with `Δ(xyz)² = ((x+y−z)/2)! ((x−y+z)/2)! ((−x+y+z)/2)! / ((x+y+z)/2 + 1)!` (`triSq`), `Aᵢ` the
four face sums and `Bₖ` the three sums of four edges avoiding an opposite pair (all halved).

This file proves that `racahW` has the tetrahedral symmetry of the 6j symbol (`racahW_swap12`,
`racahW_swap23`, `racahW_flip12`) and agrees with Physlib's `sixJSym` when one spin is zero
(`sixJSym_zero_left_eq_racahW`). The Biedenharn–Elliott identity with one spin `½` for
`racahW` is in `RacahBE.lean`; together they give Racah's formula (`Racah.lean`).
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.Asymptotics

/-! ## Triangle coefficients -/

/-- The squared triangle coefficient in doubled units:
`Δ(xyz)² = ((x+y−z)/2)! ((x+z−y)/2)! ((y+z−x)/2)! / ((x+y+z)/2 + 1)!`. -/
noncomputable def triSq (x y z : ℕ) : ℝ :=
  (((x + y - z) / 2).factorial * ((x + z - y) / 2).factorial * ((y + z - x) / 2).factorial : ℝ) /
    ((x + y + z) / 2 + 1).factorial

/-- The triangle coefficient `Δ(xyz) = √(triSq x y z)` in doubled units. -/
noncomputable def triD (x y z : ℕ) : ℝ := √(triSq x y z)

lemma triSq_pos (x y z : ℕ) : 0 < triSq x y z := by unfold triSq; positivity

lemma triD_mul_self (x y z : ℕ) : triD x y z * triD x y z = triSq x y z :=
  Real.mul_self_sqrt (triSq_pos x y z).le

lemma triSq_swap12 (x y z : ℕ) : triSq y x z = triSq x y z := by
  unfold triSq
  rw [Nat.add_comm y x]
  ring

lemma triSq_swap23 (x y z : ℕ) : triSq x z y = triSq x y z := by
  unfold triSq
  rw [Nat.add_comm z y, show x + z + y = x + y + z by ring]
  ring

lemma triD_swap12 (x y z : ℕ) : triD y x z = triD x y z := by
  unfold triD; rw [triSq_swap12]

lemma triD_swap23 (x y z : ℕ) : triD x z y = triD x y z := by
  unfold triD; rw [triSq_swap23]

lemma triD_cycle (x y z : ℕ) : triD y z x = triD x y z := by
  rw [triD_swap12 z y x, triD_swap23 z x y, triD_swap12 x z y, triD_swap23 x y z]

lemma triD_swap13 (x y z : ℕ) : triD z y x = triD x y z := by
  rw [triD_swap12 y z x, triD_cycle]

/-- `triSq` in the triangle parametrisation `x = b + c`, `y = a + c`, `z = a + b`. -/
lemma triSq_eq {x y z : ℕ} (a b c : ℕ) (hx : x = b + c) (hy : y = a + c) (hz : z = a + b) :
    triSq x y z = ((c.factorial * b.factorial * a.factorial : ℕ) : ℝ) / (a + b + c + 1).factorial := by
  subst hx hy hz
  unfold triSq
  rw [show (b + c + (a + c) - (a + b)) / 2 = c by omega, show (b + c + (a + b) - (a + c)) / 2 = b by omega,
    show (a + c + (a + b) - (b + c)) / 2 = a by omega,
    show (b + c + (a + c) + (a + b)) / 2 = a + b + c by omega]
  push_cast
  ring

/-! ## Racah's expression -/

/-- The four face sums of `{j₁ j₂ j₃; j₄ j₅ j₆}`, halved: the triads `(j₁j₂j₃)`, `(j₁j₅j₆)`,
`(j₄j₂j₆)`, `(j₄j₅j₃)`. -/
def faceD (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Fin 4 → ℤ :=
  ![(((j₁ + j₂ + j₃) / 2 : ℕ) : ℤ), (((j₁ + j₅ + j₆) / 2 : ℕ) : ℤ), (((j₄ + j₂ + j₆) / 2 : ℕ) : ℤ),
    (((j₄ + j₅ + j₃) / 2 : ℕ) : ℤ)]

/-- The three sums of four edges avoiding an opposite pair, halved. -/
def quadD (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Fin 3 → ℤ :=
  ![(((j₁ + j₂ + j₄ + j₅) / 2 : ℕ) : ℤ), (((j₂ + j₃ + j₅ + j₆) / 2 : ℕ) : ℤ),
    (((j₃ + j₁ + j₆ + j₄) / 2 : ℕ) : ℤ)]

lemma faceD_nonneg (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (i : Fin 4) : 0 ≤ faceD j₁ j₂ j₃ j₄ j₅ j₆ i := by
  fin_cases i <;> simp [faceD] <;> omega

lemma quadD_nonneg (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (k : Fin 3) : 0 ≤ quadD j₁ j₂ j₃ j₄ j₅ j₆ k := by
  fin_cases k <;> simp [quadD] <;> omega

/-- The four triads of `{j₁ j₂ j₃; j₄ j₅ j₆}` are admissible (doubled units). -/
def Adm6 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Prop :=
  Tri j₁ j₂ j₃ ∧ Tri j₁ j₅ j₆ ∧ Tri j₄ j₂ j₆ ∧ Tri j₄ j₅ j₃

instance (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : Decidable (Adm6 j₁ j₂ j₃ j₄ j₅ j₆) := by
  unfold Adm6; infer_instance

/-- **Racah's expression** for `{j₁ j₂ j₃; j₄ j₅ j₆}` in doubled units: the four triangle
coefficients times Racah's alternating sum, and zero unless the four triads are admissible. -/
noncomputable def racahW (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) : ℝ :=
  if Adm6 j₁ j₂ j₃ j₄ j₅ j₆ then
    triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃ *
      rsum (faceD j₁ j₂ j₃ j₄ j₅ j₆) (quadD j₁ j₂ j₃ j₄ j₅ j₆)
  else 0

lemma racahW_of_adm {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : Adm6 j₁ j₂ j₃ j₄ j₅ j₆) :
    racahW j₁ j₂ j₃ j₄ j₅ j₆ = triD j₁ j₂ j₃ * triD j₁ j₅ j₆ * triD j₄ j₂ j₆ * triD j₄ j₅ j₃ *
      rsum (faceD j₁ j₂ j₃ j₄ j₅ j₆) (quadD j₁ j₂ j₃ j₄ j₅ j₆) := by
  rw [racahW, ite_eq_left h]

lemma racahW_of_not {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : ¬Adm6 j₁ j₂ j₃ j₄ j₅ j₆) :
    racahW j₁ j₂ j₃ j₄ j₅ j₆ = 0 := by
  rw [racahW, ite_eq_right h]

/-! ## Tools for Racah's sum -/

/-- `rsum` is unchanged when the faces and the quads are relabelled. -/
lemma rsum_eq_of_perm {A A' : Fin 4 → ℤ} {B B' : Fin 3 → ℤ} (σ : Equiv.Perm (Fin 4))
    (τ : Equiv.Perm (Fin 3)) (hA : ∀ i, A i = A' (σ i)) (hB : ∀ k, B k = B' (τ k)) :
    rsum A B = rsum A' B' := by
  rw [show A = A' ∘ σ from funext hA, show B = B' ∘ τ from funext hB, rsum_comp]

/-- When some face sum and some quad sum coincide, Racah's sum has the single term `t = Aᵢ = Bₖ`. -/
lemma rsum_eq_single {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} (t : ℕ) (i : Fin 4) (k : Fin 3)
    (hA : A i = t) (hBk : B k = t) (hB : ∀ k, 0 ≤ B k) : rsum A B = rterm A B t := by
  unfold rsum
  rw [sum_eq_single t]
  · intro u _ hu
    rcases lt_or_gt_of_ne hu with h | h
    · exact rterm_eq_zero_of_lt i (by omega)
    · exact rterm_eq_zero_of_gt k (by omega)
  · intro ht
    exfalso
    apply ht
    rw [mem_range]
    have := single_le_sum (f := B) (fun k _ => hB k) (mem_univ k)
    omega

/-- A term of Racah's sum with all factorial arguments nonnegative. -/
lemma rterm_eq_of {A : Fin 4 → ℤ} {B : Fin 3 → ℤ} {t : ℕ} (a : Fin 4 → ℕ) (b : Fin 3 → ℕ)
    (ha : ∀ i, (t : ℤ) - A i = a i) (hb : ∀ k, B k - t = b k) :
    rterm A B t = (-1) ^ t * ((t + 1).factorial : ℝ) /
      ((∏ i, ((a i).factorial : ℝ)) * ∏ k, ((b k).factorial : ℝ)) := by
  unfold rterm
  simp only [ha, hb, invFact_natCast, prod_inv_distrib]
  rw [div_eq_mul_inv, mul_inv]

/-! ## Tetrahedral symmetry -/

lemma adm6_swap12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    Adm6 j₂ j₁ j₃ j₅ j₄ j₆ ↔ Adm6 j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold Adm6 Tri; constructor <;> intro h <;> omega

lemma adm6_swap23 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    Adm6 j₁ j₃ j₂ j₄ j₆ j₅ ↔ Adm6 j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold Adm6 Tri; constructor <;> intro h <;> omega

lemma adm6_flip12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    Adm6 j₄ j₅ j₃ j₁ j₂ j₆ ↔ Adm6 j₁ j₂ j₃ j₄ j₅ j₆ := by
  unfold Adm6 Tri; constructor <;> intro h <;> omega

/-- `{j₂ j₁ j₃; j₅ j₄ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}` for `racahW`. -/
lemma racahW_swap12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahW j₂ j₁ j₃ j₅ j₄ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  by_cases h : Adm6 j₁ j₂ j₃ j₄ j₅ j₆
  · rw [racahW_of_adm h, racahW_of_adm ((adm6_swap12 ..).2 h), triD_swap12 j₂, triD_swap12 j₂ j₄,
      triD_swap12 j₅ j₁, triD_swap12 j₅ j₄,
      rsum_eq_of_perm (permOf ![0, 2, 1, 3] (by decide)) (Equiv.ofBijective ![0, 2, 1] (by decide))
        (A' := faceD j₁ j₂ j₃ j₄ j₅ j₆) (B' := quadD j₁ j₂ j₃ j₄ j₅ j₆)
        (by intro i; fin_cases i <;> simp [faceD, permOf] <;> omega)
        (by intro k; fin_cases k <;> simp [quadD, Equiv.ofBijective_apply] <;> omega)]
    ring
  · rw [racahW_of_not h, racahW_of_not (fun h' => h ((adm6_swap12 ..).1 h'))]

/-- `{j₁ j₃ j₂; j₄ j₆ j₅} = {j₁ j₂ j₃; j₄ j₅ j₆}` for `racahW`. -/
lemma racahW_swap23 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahW j₁ j₃ j₂ j₄ j₆ j₅ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  by_cases h : Adm6 j₁ j₂ j₃ j₄ j₅ j₆
  · rw [racahW_of_adm h, racahW_of_adm ((adm6_swap23 ..).2 h), triD_swap23 j₁ j₂,
      triD_swap23 j₁ j₅, triD_swap23 j₄ j₅ j₃, triD_swap23 j₄ j₂ j₆,
      rsum_eq_of_perm (permOf ![0, 1, 3, 2] (by decide)) (Equiv.ofBijective ![2, 1, 0] (by decide))
        (A' := faceD j₁ j₂ j₃ j₄ j₅ j₆) (B' := quadD j₁ j₂ j₃ j₄ j₅ j₆)
        (by intro i; fin_cases i <;> simp [faceD, permOf] <;> omega)
        (by intro k; fin_cases k <;> simp [quadD, Equiv.ofBijective_apply] <;> omega)]
    ring
  · rw [racahW_of_not h, racahW_of_not (fun h' => h ((adm6_swap23 ..).1 h'))]

/-- `{j₄ j₅ j₃; j₁ j₂ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}` for `racahW`. -/
lemma racahW_flip12 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahW j₄ j₅ j₃ j₁ j₂ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  by_cases h : Adm6 j₁ j₂ j₃ j₄ j₅ j₆
  · rw [racahW_of_adm h, racahW_of_adm ((adm6_flip12 ..).2 h),
      rsum_eq_of_perm (permOf ![3, 2, 1, 0] (by decide)) (Equiv.refl (Fin 3))
        (A' := faceD j₁ j₂ j₃ j₄ j₅ j₆) (B' := quadD j₁ j₂ j₃ j₄ j₅ j₆)
        (by intro i; fin_cases i <;> simp [faceD, permOf])
        (by intro k; fin_cases k <;> simp [quadD] <;> omega)]
    ring
  · rw [racahW_of_not h, racahW_of_not (fun h' => h ((adm6_flip12 ..).1 h'))]

/-- `{j₅ j₄ j₃; j₂ j₁ j₆} = {j₁ j₂ j₃; j₄ j₅ j₆}` for `racahW`. -/
lemma racahW_flipswap (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahW j₅ j₄ j₃ j₂ j₁ j₆ = racahW j₁ j₂ j₃ j₄ j₅ j₆ := by
  rw [racahW_swap12 j₄ j₅ j₃ j₁ j₂ j₆, racahW_flip12]

/-! ## A zero spin -/

/-- **`racahW` with a zero spin** has the closed form of `sixJSym_zero_left`. -/
theorem racahW_zero_left (j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahW 0 j₂ j₃ j₄ j₅ j₆ =
      if j₃ = j₂ ∧ j₆ = j₅ ∧ Tri j₂ j₅ j₄ then
        (-1) ^ ((j₂ + j₅ + j₄) / 2) / (Real.sqrt ((j₂ : ℝ) + 1) * Real.sqrt ((j₅ : ℝ) + 1))
      else 0 := by
  have hiff : Adm6 0 j₂ j₃ j₄ j₅ j₆ ↔ j₃ = j₂ ∧ j₆ = j₅ ∧ Tri j₂ j₅ j₄ := by
    unfold Adm6 Tri; constructor <;> intro h <;> omega
  by_cases h : j₃ = j₂ ∧ j₆ = j₅ ∧ Tri j₂ j₅ j₄
  swap
  · rw [ite_eq_right h, racahW_of_not (fun h' => h (hiff.1 h'))]
  rw [ite_eq_left h, racahW_of_adm (hiff.2 h)]
  obtain ⟨h3, h6, hT⟩ := h
  rw [h3, h6]
  obtain ⟨α, β, γ, rfl, rfl, rfl⟩ : ∃ α β γ : ℕ, j₂ = α + β ∧ j₅ = α + γ ∧ j₄ = β + γ :=
    ⟨(j₂ + j₅ - j₄) / 2, (j₂ + j₄ - j₅) / 2, (j₄ + j₅ - j₂) / 2, by unfold Tri at hT; omega,
      by unfold Tri at hT; omega, by unfold Tri at hT; omega⟩
  have h0 : ∀ j : ℕ, triD 0 j j = 1 / Real.sqrt ((j : ℝ) + 1) := by
    intro j
    have : triSq 0 j j = 1 / ((j : ℝ) + 1) := by
      rw [triSq_eq j 0 0 (by ring) (by ring) (by ring)]
      simp only [add_zero, Nat.factorial_zero, mul_one, one_mul]
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    rw [triD, this, one_div, Real.sqrt_inv, one_div]
  have hT : triD (β + γ) (α + β) (α + γ) * triD (β + γ) (α + γ) (α + β) =
      ((γ.factorial * β.factorial * α.factorial : ℕ) : ℝ) / (α + β + γ + 1).factorial := by
    rw [triD_swap23 (β + γ) (α + γ), triD_mul_self, triSq_eq α β γ (by ring) (by ring) (by ring)]
  have hS : rsum (faceD 0 (α + β) (α + β) (β + γ) (α + γ) (α + γ))
      (quadD 0 (α + β) (α + β) (β + γ) (α + γ) (α + γ)) =
      (-1) ^ (α + β + γ) * ((α + β + γ + 1).factorial : ℝ) /
        ((γ.factorial * β.factorial * α.factorial : ℕ) : ℝ) := by
    rw [rsum_eq_single (α + β + γ) 2 0 (by simp [faceD]; omega) (by simp [quadD]; omega)
      (quadD_nonneg _ _ _ _ _ _), rterm_eq_of ![γ, β, 0, 0] ![0, α, 0]
      (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega)]
    simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.factorial_zero,
      Nat.cast_one, mul_one, one_mul, Nat.cast_mul]
  rw [h0, h0, mul_assoc _ (triD (β + γ) (α + β) (α + γ)), hT, hS,
    show (α + β + (α + γ) + (β + γ)) / 2 = α + β + γ by omega]
  have : (0 : ℝ) < ((γ.factorial * β.factorial * α.factorial : ℕ) : ℝ) := by positivity
  field_simp

/-- Physlib's 6j symbol with a zero spin agrees with Racah's expression `racahW`. -/
theorem sixJSym_zero_left_eq_racahW (j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym 0 j₂ j₃ j₄ j₅ j₆ = racahW 0 j₂ j₃ j₄ j₅ j₆ := by
  rw [sixJSym_zero_left, racahW_zero_left]

end Lightlike.Asymptotics
