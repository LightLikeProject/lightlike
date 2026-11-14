import Lightlike.Asymptotics.RacahW
import Lightlike.Recoupling.Intertwiner

/-!
# The 6j symbol with one spin ½

This file proves that Physlib's `sixJSym` agrees with Racah's expression `racahW` whenever one
spin is `½` (doubled spin `1`): `sixJSym_one_left_eq_racahW`. Together with the spin-0 case
(`sixJSym_zero_left_eq_racahW`) and the Biedenharn–Elliott identity with one spin `½` for `racahW`
(`racahW_be_half`), this is the input of the induction proving Racah's formula (`Racah.lean`).

The proof evaluates the change-of-channel identity for 4-valent intertwiners
(`fourJ_eq_sum_fourRecoupling`) at stretched projections. With `j₁ = ½`, `m₁ = ½` and
`m₃ = j₃`, only the channel `l = j₃ + ½` survives, and each intertwiner component is a single
product of two 3j symbols with one stretched projection, which have a closed form
(`threeJ_stretched`). Solving for the 6j symbol and comparing with `racahW` is an identity
between factorials.
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon Lightlike.Recoupling

namespace Lightlike.Asymptotics

/-! ## 3j symbols with a stretched projection -/

/-- The projection factor `√(((j − m)/2)! ((j + m)/2)!)` of a 3j symbol in doubled units. -/
noncomputable def projD (j : ℕ) (m : ℤ) : ℝ :=
  √(((((j : ℤ) - m) / 2).toNat.factorial : ℝ) * ((((j : ℤ) + m) / 2).toNat.factorial : ℝ))

/-- The projection factor is even in `m`. -/
lemma projD_neg (j : ℕ) (m : ℤ) : projD j (-m) = projD j m := by
  unfold projD
  rw [show (j : ℤ) - -m = j + m by ring, show (j : ℤ) + -m = j - m by ring, mul_comm]

/-- The product of the projection factors at `m` and `−m` is `((j−m)/2)! ((j+m)/2)!`. -/
lemma projD_mul_neg {j : ℕ} {m : ℤ} (x y : ℕ) (hx : (j : ℤ) - m = 2 * x)
    (hy : (j : ℤ) + m = 2 * y) :
    projD j m * projD j (-m) = (x.factorial : ℝ) * (y.factorial : ℝ) := by
  rw [projD_neg, projD, Real.mul_self_sqrt (by positivity),
    show (((j : ℤ) - m) / 2).toNat = x by omega, show (((j : ℤ) + m) / 2).toNat = y by omega]

/-- The projection factor is positive. -/
lemma projD_pos (j : ℕ) (m : ℤ) : 0 < projD j m := by
  unfold projD; positivity

/-- Racah's formula for the 3j symbol, with the square root split into a triangle coefficient and
three projection factors. -/
lemma threeJ_eq_of_adm {j₁ j₂ j₃ : ℕ} {m₁ m₂ m₃ : ℤ} (h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      (-1) ^ (reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 2 0 + reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 1 1) *
        (triD j₁ j₂ j₃ * projD j₁ m₁ * projD j₂ m₂ * projD j₃ m₃) *
        sixSum 0 ((reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 1 0 : ℤ) - reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 0 1)
          ((reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 2 1 : ℤ) - reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 0 0)
          (reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 0 2) (reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 1 0)
          (reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 2 1) := by
  rw [threeJ, ite_eq_left h, threeJR, reggeJ_row_sum h]
  congr 2
  simp only [Fin.prod_univ_three, reggeJ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  unfold triD triSq projD
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity)]
  congr 1
  ring

/-- Racah's six-factorial sum when the range of summation is the single point `z = 0`. -/
lemma sixSum_single {a₂ a₃ b₁ b₂ b₃ : ℤ} (a b c d : ℕ) (h₂ : a₂ = -a) (h₃ : a₃ = -b)
    (h₄ : b₁ = c) (h₅ : b₂ = 0) (h₆ : b₃ = d) :
    sixSum 0 a₂ a₃ b₁ b₂ b₃ =
      ((a.factorial : ℝ) * b.factorial * c.factorial * d.factorial)⁻¹ := by
  subst h₂ h₃ h₄ h₅ h₆
  unfold sixSum
  rw [finsum_eq_single _ 0]
  · simp [sixTerm, invFact]
    ring
  · intro z hz
    unfold sixTerm
    rcases lt_or_gt_of_ne hz with h | h
    · rw [invFact_of_neg (u := z - 0) (by omega)]; ring
    · rw [invFact_of_neg (u := 0 - z) (by omega)]; ring

/-- **The 3j symbol with a stretched first projection** `m₁ = j₁` (doubled units):
`(j₁ j₂ j₃; j₁ m₂ m₃) = (−1)^(j₁ + (j₂−m₂)/2) Δ(j₁j₂j₃) ∏ᵢ √(((jᵢ−mᵢ)/2)! ((jᵢ+mᵢ)/2)!) /
(r₀₁! r₀₂! r₂₁! r₂₂!)`, with `r₀₁ = (j₁+j₃−j₂)/2`, `r₀₂ = (j₁+j₂−j₃)/2`, `r₂₁ = (j₂+m₂)/2`,
`r₂₂ = (j₃+m₃)/2`. -/
theorem threeJ_stretched {j₁ j₂ j₃ : ℕ} {m₁ m₂ m₃ : ℤ} (r₀₁ r₀₂ r₁₁ r₂₁ r₂₂ : ℕ)
    (hT : Tri j₁ j₂ j₃) (hm₁ : m₁ = j₁) (hs : m₁ + m₂ + m₃ = 0) (h01 : j₁ + j₃ = j₂ + 2 * r₀₁)
    (h02 : j₁ + j₂ = j₃ + 2 * r₀₂) (h11 : (j₂ : ℤ) - m₂ = 2 * r₁₁) (h21 : (j₂ : ℤ) + m₂ = 2 * r₂₁)
    (h22 : (j₃ : ℤ) + m₃ = 2 * r₂₂) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = (-1) ^ (j₁ + r₁₁) *
      (triD j₁ j₂ j₃ * projD j₁ m₁ * projD j₂ m₂ * projD j₃ m₃) /
        ((r₀₁.factorial : ℝ) * r₀₂.factorial * r₂₁.factorial * r₂₂.factorial) := by
  unfold Tri at hT
  have h : Adm3 j₁ j₂ j₃ m₁ m₂ m₃ := by omega
  rw [threeJ_eq_of_adm h, sixSum_single r₀₁ r₂₂ r₀₂ r₂₁ (by simp [reggeJ]; omega)
    (by simp [reggeJ]; omega) (by simp [reggeJ]; omega) (by simp [reggeJ]; omega)
    (by simp [reggeJ]; omega),
    show reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 2 0 + reggeJ j₁ j₂ j₃ m₁ m₂ m₃ 1 1 = j₁ + r₁₁ by
      simp [reggeJ]; omega]
  ring

/-! ## Intertwiner components as single products -/

/-- A component of the `(j₁ j₂)(j₃ j₄)` intertwiner is a single product of two 3j symbols: the
internal projection is fixed to `μ = −m₁ − m₂`. -/
lemma fourJ_eq {j₁ j₂ j₃ j₄ k : ℕ} {m₁ m₂ m₃ m₄ : ℤ} (μ ν : ℤ) (n : ℕ) (hμ : m₁ + m₂ + μ = 0)
    (hν : μ + ν = 0) (hn : (k : ℤ) - μ = 2 * n) :
    fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ = √((k : ℝ) + 1) *
      ((-1) ^ n * threeJ j₁ j₂ k m₁ m₂ μ * threeJ k j₃ j₄ ν m₃ m₄) := by
  unfold fourJ
  congr 1
  rw [sum_eq_single μ]
  · rw [show ((k : ℤ) - μ) / 2 = (n : ℤ) by omega, zpow_natCast, show -μ = ν by omega]
  · intro x _ hx
    rw [threeJ_of_not (fun h => hx (by obtain ⟨h0, -⟩ := h; omega))]
    ring
  · intro hμk
    rw [threeJ_of_not (fun h => hμk (by
      obtain ⟨-, -, -, -, -, h5, h6, -⟩ := h
      exact mem_Icc.mpr ⟨h5, h6⟩))]
    ring

/-! ## The spin-½ 6j symbols -/

/-- The 6j symbol `{½ a a+½; e d d+½}` in the triangle parametrisation `a = u + w`,
`e = u + v + ½`, `d = v + w` (doubled units), by the intertwiner identity at stretched
projections. -/
theorem sixJSym_half_plus (u v w : ℕ) :
    sixJSym 1 (u + w) (u + w + 1) (u + v + 1) (v + w) (v + w + 1) =
      racahW 1 (u + w) (u + w + 1) (u + v + 1) (v + w) (v + w + 1) := by
  have hrec := fourJ_eq_sum_fourRecoupling 1 (u + w) (v + w) (u + v + 1) (u + w + 1) 1
    (-((u : ℤ) + w)) ((v : ℤ) + w) ((u : ℤ) - v - 1)
  rw [sum_eq_single_of_mem (v + w + 1) (mem_range.mpr (by omega))] at hrec
  on_goal 2 =>
    intro l hl hne
    have hl' : l ≤ v + w := by rw [mem_range] at hl; omega
    apply mul_eq_zero_of_right
    unfold fourJ
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro μ _
    rw [threeJ_of_not (fun h => by obtain ⟨h0, -, -, -, -, h5, -⟩ := h; omega)]
    ring
  rw [fourJ_eq (m₁ := 1) (m₂ := -((u : ℤ) + w)) (k := u + w + 1) ((u : ℤ) + w - 1)
      (1 - (u : ℤ) - w) 1 (by omega) (by omega) (by omega),
    fourJ_eq (m₁ := 1) (m₂ := (v : ℤ) + w) (k := v + w + 1) (-1 - (v : ℤ) - w) (1 + (v : ℤ) + w)
      (v + w + 1) (by omega) (by omega) (by omega),
    ← threeJ_cycle (u + w + 1) (v + w) (u + v + 1) (1 - (u : ℤ) - w) ((v : ℤ) + w)
      ((u : ℤ) - v - 1),
    threeJ_stretched (j₁ := 1) (j₂ := u + w) (j₃ := u + w + 1) (m₁ := 1) (m₂ := -((u : ℤ) + w))
      (m₃ := (u : ℤ) + w - 1) 1 0 (u + w) 0 (u + w) (by unfold Tri; omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    threeJ_stretched (j₁ := v + w) (j₂ := u + v + 1) (j₃ := u + w + 1) (m₁ := (v : ℤ) + w)
      (m₂ := (u : ℤ) - v - 1) (m₃ := 1 - (u : ℤ) - w) w v (v + 1) u 1 (by unfold Tri; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    threeJ_stretched (j₁ := 1) (j₂ := v + w) (j₃ := v + w + 1) (m₁ := 1) (m₂ := (v : ℤ) + w)
      (m₃ := -1 - (v : ℤ) - w) 1 0 0 (v + w) 0 (by unfold Tri; omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    threeJ_stretched (j₁ := v + w + 1) (j₂ := u + w) (j₃ := u + v + 1) (m₁ := 1 + (v : ℤ) + w)
      (m₂ := -((u : ℤ) + w)) (m₃ := (u : ℤ) - v - 1) (v + 1) w (u + w) 0 u (by unfold Tri; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] at hrec
  unfold fourRecoupling at hrec
  rw [triD_swap13 (u + v + 1) (u + w) (v + w + 1), triD_swap12 (u + v + 1) (v + w) (u + w + 1),
    Real.sqrt_mul (by positivity)] at hrec
  have hA : Adm6 1 (u + w) (u + w + 1) (u + v + 1) (v + w) (v + w + 1) := by
    unfold Adm6 Tri; omega
  rw [racahW_of_adm hA, rsum_eq_single (u + v + w + 1) 2 0 (by simp [faceD]; omega)
      (by simp [quadD]; omega) (quadD_nonneg _ _ _ _ _ _),
    rterm_eq_of ![v, u, 0, 0] ![0, w, 1] (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega)]
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, mul_one, one_mul] at hrec ⊢
  -- squares of the atoms that do not cancel
  have hT2 : triD 1 (v + w) (v + w + 1) * triD 1 (v + w) (v + w + 1) =
      ((v + w).factorial : ℝ) / (v + w + 1 + 1).factorial := by
    rw [triD_mul_self, triSq_eq (v + w) 1 0 (by omega) (by omega) (by omega),
      show v + w + 1 + 0 + 1 = v + w + 1 + 1 by ring]
    simp only [Nat.factorial_zero, Nat.factorial_one, one_mul]
  have hT3 : triD (u + v + 1) (u + w) (v + w + 1) * triD (u + v + 1) (u + w) (v + w + 1) =
      (u.factorial * (v + 1).factorial * w.factorial : ℝ) / (u + v + w + 1 + 1).factorial := by
    rw [triD_mul_self, triSq_eq w (v + 1) u (by omega) (by omega) (by omega),
      show w + (v + 1) + u + 1 = u + v + w + 1 + 1 by ring]
    push_cast; ring
  have hS2 : √(((v + w + 1 : ℕ) : ℝ) + 1) * √(((v + w + 1 : ℕ) : ℝ) + 1) =
      ((v + w + 1 : ℕ) : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have hPd : projD (v + w + 1) (-1 - (v : ℤ) - w) * projD (v + w + 1) (1 + (v : ℤ) + w) =
      ((v + w + 1).factorial : ℝ) := by
    have h := projD_mul_neg (j := v + w + 1) (m := -1 - (v : ℤ) - w) (v + w + 1) 0 (by omega)
      (by omega)
    rw [show -(-1 - (v : ℤ) - w) = 1 + v + w by ring] at h
    rw [h, Nat.factorial_zero, Nat.cast_one, mul_one]
  have hPk : projD (u + w + 1) ((u : ℤ) + w - 1) * projD (u + w + 1) (1 - (u : ℤ) - w) =
      ((u + w).factorial : ℝ) := by
    have h := projD_mul_neg (j := u + w + 1) (m := (u : ℤ) + w - 1) 1 (u + w) (by omega)
      (by omega)
    rw [show -((u : ℤ) + w - 1) = 1 - u - w by ring] at h
    rw [h, Nat.factorial_one, Nat.cast_one, one_mul]
  -- positivity of the atoms
  have tp : ∀ x y z : ℕ, 0 < triD x y z := fun x y z => Real.sqrt_pos.mpr (triSq_pos x y z)
  have hT2p := tp 1 (v + w) (v + w + 1)
  have hT3p := tp (u + v + 1) (u + w) (v + w + 1)
  have hP1p := projD_pos 1 1
  have hPap := projD_pos (u + w) (-((u : ℤ) + w))
  have hPdp := projD_pos (v + w) ((v : ℤ) + w)
  have hPep := projD_pos (u + v + 1) ((u : ℤ) - v - 1)
  have hPd1p := projD_pos (v + w + 1) (-1 - (v : ℤ) - w)
  have hPd2p := projD_pos (v + w + 1) (1 + (v : ℤ) + w)
  have hS1p : 0 < √(((u + w + 1 : ℕ) : ℝ) + 1) := by positivity
  have hS2p : 0 < √(((v + w + 1 : ℕ) : ℝ) + 1) := by positivity
  have hσ : ∀ n : ℕ, ((-1 : ℝ) ^ n) ≠ 0 := fun n => pow_ne_zero _ (by norm_num)
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by positivity
  -- the sign and factorial identity left after cancelling the common atoms
  have hsign : (-1 : ℝ) ^ (u + v + w + 1) * (-1) ^ ((u + w + (v + w) + (u + w + 1) + (v + w + 1)) / 2) *
      (-1) ^ (v + w + 1) * (-1) ^ (1 + 0) * (-1) ^ (v + w + 1 + (u + w)) =
      (-1) ^ 1 * (-1) ^ (1 + (u + w)) * (-1) ^ (v + w + (v + 1)) := by
    simp only [← pow_add]
    exact neg_one_pow_eq_of_mod (by omega)
  have hcore : (-1 : ℝ) ^ (u + v + w + 1) *
      (-1) ^ ((u + w + (v + w) + (u + w + 1) + (v + w + 1)) / 2) * (-1) ^ (v + w + 1) *
      (-1) ^ (1 + 0) * (-1) ^ (v + w + 1 + (u + w)) * ((u + v + w + 1 + 1).factorial : ℝ) /
      ((v.factorial * u.factorial * w.factorial : ℝ) * (v + w).factorial *
        ((v + 1).factorial * w.factorial * u.factorial)) *
      (((v + w).factorial : ℝ) / (v + w + 1 + 1).factorial *
        ((u.factorial * (v + 1).factorial * w.factorial : ℝ) / (u + v + w + 1 + 1).factorial) *
        (((v + w + 1 : ℕ) : ℝ) + 1) * ((v + w + 1).factorial : ℝ)) =
      (-1) ^ 1 * (-1) ^ (1 + (u + w)) * (-1) ^ (v + w + (v + 1)) /
        (((u + w).factorial : ℝ) * (w.factorial * v.factorial * u.factorial)) *
        ((u + w).factorial : ℝ) := by
    rw [hsign, Nat.factorial_succ (v + w + 1)]
    have := hf (v + w + 1); have := hf (u + v + w + 1 + 1); have := hf (v + 1)
    have := hf (v + w); have := hf (u + w); have := hf u; have := hf v; have := hf w
    push_cast
    field_simp
  have hQ : triD 1 (v + w) (v + w + 1) * triD 1 (v + w) (v + w + 1) *
      (triD (u + v + 1) (u + w) (v + w + 1) * triD (u + v + 1) (u + w) (v + w + 1)) *
      (√(((v + w + 1 : ℕ) : ℝ) + 1) * √(((v + w + 1 : ℕ) : ℝ) + 1)) *
      (projD (v + w + 1) (-1 - (v : ℤ) - w) * projD (v + w + 1) (1 + (v : ℤ) + w)) =
      ((v + w).factorial : ℝ) / (v + w + 1 + 1).factorial *
        ((u.factorial * (v + 1).factorial * w.factorial : ℝ) / (u + v + w + 1 + 1).factorial) *
        (((v + w + 1 : ℕ) : ℝ) + 1) * ((v + w + 1).factorial : ℝ) := by
    rw [hT2, hT3, hS2, hPd]
  set T1 := triD 1 (u + w) (u + w + 1)
  set T2 := triD 1 (v + w) (v + w + 1)
  set T3 := triD (u + v + 1) (u + w) (v + w + 1)
  set T4 := triD (u + v + 1) (v + w) (u + w + 1)
  set P1 := projD 1 1
  set Pa := projD (u + w) (-((u : ℤ) + w))
  set Pd := projD (v + w) ((v : ℤ) + w)
  set Pe := projD (u + v + 1) ((u : ℤ) - v - 1)
  set Pk1 := projD (u + w + 1) ((u : ℤ) + w - 1)
  set Pk2 := projD (u + w + 1) (1 - (u : ℤ) - w)
  set Pd1 := projD (v + w + 1) (-1 - (v : ℤ) - w)
  set Pd2 := projD (v + w + 1) (1 + (v : ℤ) + w)
  set S1 := √(((u + w + 1 : ℕ) : ℝ) + 1)
  set S2 := √(((v + w + 1 : ℕ) : ℝ) + 1)
  have hZ : (-1 : ℝ) ^ ((u + w + (v + w) + (u + w + 1) + (v + w + 1)) / 2) * (S1 * S2) *
      (S2 * ((-1) ^ (v + w + 1) * ((-1) ^ (1 + 0) * (T2 * P1 * Pd * Pd1) / ((v + w).factorial : ℝ)) *
        ((-1) ^ (v + w + 1 + (u + w)) * (T3 * Pd2 * Pa * Pe) /
          (((v + 1).factorial : ℝ) * w.factorial * u.factorial)))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hσ _) (mul_pos hS1p hS2p).ne') (mul_ne_zero hS2p.ne'
      (mul_ne_zero (mul_ne_zero (hσ _) (div_ne_zero (mul_ne_zero (hσ _)
        (mul_pos (mul_pos (mul_pos hT2p hP1p) hPdp) hPd1p).ne') (hf _)))
        (div_ne_zero (mul_ne_zero (hσ _) (mul_pos (mul_pos (mul_pos hT3p hPd2p) hPap) hPep).ne')
          (mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _)))))
  apply mul_right_cancel₀ hZ
  linear_combination -hrec - ((T1 * T4 * S1 * P1 * Pa * Pd * Pe *
      ((-1 : ℝ) ^ (u + v + w + 1) * (-1) ^ ((u + w + (v + w) + (u + w + 1) + (v + w + 1)) / 2) *
        (-1) ^ (v + w + 1) * (-1) ^ (1 + 0) * (-1) ^ (v + w + 1 + (u + w)) *
        ((u + v + w + 1 + 1).factorial : ℝ) / ((v.factorial * u.factorial * w.factorial : ℝ) *
          (v + w).factorial * ((v + 1).factorial * w.factorial * u.factorial)))) * hQ +
    (T1 * T4 * S1 * P1 * Pa * Pd * Pe) * hcore -
    (T1 * T4 * S1 * P1 * Pa * Pd * Pe * ((-1 : ℝ) ^ 1 * (-1) ^ (1 + (u + w)) *
      (-1) ^ (v + w + (v + 1)) / (((u + w).factorial : ℝ) * (w.factorial * v.factorial *
        u.factorial)))) * hPk)

/-- The 6j symbol `{½ a a−½; e d d+½}` in the triangle parametrisation `a = u + w + ½`,
`e = u + v`, `d = v + w` (doubled units), by the intertwiner identity at stretched
projections. -/
theorem sixJSym_half_minus (u v w : ℕ) :
    sixJSym 1 (u + w + 1) (u + w) (u + v) (v + w) (v + w + 1) =
      racahW 1 (u + w + 1) (u + w) (u + v) (v + w) (v + w + 1) := by
  have hrec := fourJ_eq_sum_fourRecoupling 1 (u + w + 1) (v + w) (u + v) (u + w) 1
    (-((u : ℤ) + w + 1)) ((v : ℤ) + w) ((u : ℤ) - v)
  rw [sum_eq_single_of_mem (v + w + 1) (mem_range.mpr (by omega))] at hrec
  on_goal 2 =>
    intro l hl hne
    have hl' : l ≤ v + w := by rw [mem_range] at hl; omega
    apply mul_eq_zero_of_right
    unfold fourJ
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro μ _
    rw [threeJ_of_not (fun h => by obtain ⟨h0, -, -, -, -, h5, -⟩ := h; omega)]
    ring
  rw [fourJ_eq (m₁ := 1) (m₂ := -((u : ℤ) + w + 1)) (k := u + w) ((u : ℤ) + w)
      (-((u : ℤ) + w)) 0 (by omega) (by omega) (by omega),
    fourJ_eq (m₁ := 1) (m₂ := (v : ℤ) + w) (k := v + w + 1) (-1 - (v : ℤ) - w) (1 + (v : ℤ) + w)
      (v + w + 1) (by omega) (by omega) (by omega),
    ← threeJ_cycle (u + w) (v + w) (u + v) (-((u : ℤ) + w)) ((v : ℤ) + w) ((u : ℤ) - v),
    threeJ_stretched (j₁ := 1) (j₂ := u + w + 1) (j₃ := u + w) (m₁ := 1)
      (m₂ := -((u : ℤ) + w + 1)) (m₃ := (u : ℤ) + w) 0 1 (u + w + 1) 0 (u + w)
      (by unfold Tri; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega),
    threeJ_stretched (j₁ := v + w) (j₂ := u + v) (j₃ := u + w) (m₁ := (v : ℤ) + w)
      (m₂ := (u : ℤ) - v) (m₃ := -((u : ℤ) + w)) w v v u 0 (by unfold Tri; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    threeJ_stretched (j₁ := 1) (j₂ := v + w) (j₃ := v + w + 1) (m₁ := 1) (m₂ := (v : ℤ) + w)
      (m₃ := -1 - (v : ℤ) - w) 1 0 0 (v + w) 0 (by unfold Tri; omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega),
    threeJ_stretched (j₁ := v + w + 1) (j₂ := u + w + 1) (j₃ := u + v) (m₁ := 1 + (v : ℤ) + w)
      (m₂ := -((u : ℤ) + w + 1)) (m₃ := (u : ℤ) - v) v (w + 1) (u + w + 1) 0 u
      (by unfold Tri; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)] at hrec
  unfold fourRecoupling at hrec
  rw [triD_swap13 (u + v) (u + w + 1) (v + w + 1), triD_swap12 (u + v) (v + w) (u + w),
    Real.sqrt_mul (by positivity)] at hrec
  have hA : Adm6 1 (u + w + 1) (u + w) (u + v) (v + w) (v + w + 1) := by
    unfold Adm6 Tri; omega
  rw [racahW_of_adm hA, rsum_eq_single (u + v + w + 1) 2 0 (by simp [faceD]; omega)
      (by simp [quadD]; omega) (quadD_nonneg _ _ _ _ _ _),
    rterm_eq_of ![v, u, 0, 1] ![0, w, 0] (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega)]
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, mul_one, one_mul] at hrec ⊢
  -- squares of the atoms that do not cancel
  have hT2 : triD 1 (v + w) (v + w + 1) * triD 1 (v + w) (v + w + 1) =
      ((v + w).factorial : ℝ) / (v + w + 1 + 1).factorial := by
    rw [triD_mul_self, triSq_eq (v + w) 1 0 (by omega) (by omega) (by omega),
      show v + w + 1 + 0 + 1 = v + w + 1 + 1 by ring]
    simp only [Nat.factorial_zero, Nat.factorial_one, one_mul]
  have hT3 : triD (u + v) (u + w + 1) (v + w + 1) * triD (u + v) (u + w + 1) (v + w + 1) =
      (u.factorial * v.factorial * (w + 1).factorial : ℝ) / (u + v + w + 1 + 1).factorial := by
    rw [triD_mul_self, triSq_eq (w + 1) v u (by omega) (by omega) (by omega),
      show w + 1 + v + u + 1 = u + v + w + 1 + 1 by ring]
    push_cast; ring
  have hS2 : √(((v + w + 1 : ℕ) : ℝ) + 1) * √(((v + w + 1 : ℕ) : ℝ) + 1) =
      ((v + w + 1 : ℕ) : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have hPd : projD (v + w + 1) (-1 - (v : ℤ) - w) * projD (v + w + 1) (1 + (v : ℤ) + w) =
      ((v + w + 1).factorial : ℝ) := by
    have h := projD_mul_neg (j := v + w + 1) (m := -1 - (v : ℤ) - w) (v + w + 1) 0 (by omega)
      (by omega)
    rw [show -(-1 - (v : ℤ) - w) = 1 + v + w by ring] at h
    rw [h, Nat.factorial_zero, Nat.cast_one, mul_one]
  have hPk : projD (u + w) ((u : ℤ) + w) * projD (u + w) (-((u : ℤ) + w)) =
      ((u + w).factorial : ℝ) := by
    rw [projD_mul_neg (j := u + w) (m := (u : ℤ) + w) 0 (u + w) (by omega) (by omega),
      Nat.factorial_zero, Nat.cast_one, one_mul]
  -- positivity of the atoms
  have tp : ∀ x y z : ℕ, 0 < triD x y z := fun x y z => Real.sqrt_pos.mpr (triSq_pos x y z)
  have hT2p := tp 1 (v + w) (v + w + 1)
  have hT3p := tp (u + v) (u + w + 1) (v + w + 1)
  have hP1p := projD_pos 1 1
  have hPap := projD_pos (u + w + 1) (-((u : ℤ) + w + 1))
  have hPdp := projD_pos (v + w) ((v : ℤ) + w)
  have hPep := projD_pos (u + v) ((u : ℤ) - v)
  have hPd1p := projD_pos (v + w + 1) (-1 - (v : ℤ) - w)
  have hPd2p := projD_pos (v + w + 1) (1 + (v : ℤ) + w)
  have hS1p : 0 < √(((u + w : ℕ) : ℝ) + 1) := by positivity
  have hS2p : 0 < √(((v + w + 1 : ℕ) : ℝ) + 1) := by positivity
  have hσ : ∀ n : ℕ, ((-1 : ℝ) ^ n) ≠ 0 := fun n => pow_ne_zero _ (by norm_num)
  have hf : ∀ n : ℕ, (n.factorial : ℝ) ≠ 0 := fun n => by positivity
  -- the sign and factorial identity left after cancelling the common atoms
  have hsign : (-1 : ℝ) ^ (u + v + w + 1) *
      (-1) ^ ((u + w + 1 + (v + w) + (u + w) + (v + w + 1)) / 2) *
      (-1) ^ (v + w + 1) * (-1) ^ (1 + 0) * (-1) ^ (v + w + 1 + (u + w + 1)) =
      (-1) ^ 0 * (-1) ^ (1 + (u + w + 1)) * (-1) ^ (v + w + v) := by
    simp only [← pow_add]
    exact neg_one_pow_eq_of_mod (by omega)
  have hcore : (-1 : ℝ) ^ (u + v + w + 1) *
      (-1) ^ ((u + w + 1 + (v + w) + (u + w) + (v + w + 1)) / 2) * (-1) ^ (v + w + 1) *
      (-1) ^ (1 + 0) * (-1) ^ (v + w + 1 + (u + w + 1)) * ((u + v + w + 1 + 1).factorial : ℝ) /
      ((v.factorial * u.factorial * w.factorial : ℝ) * (v + w).factorial *
        (v.factorial * (w + 1).factorial * u.factorial)) *
      (((v + w).factorial : ℝ) / (v + w + 1 + 1).factorial *
        ((u.factorial * v.factorial * (w + 1).factorial : ℝ) / (u + v + w + 1 + 1).factorial) *
        (((v + w + 1 : ℕ) : ℝ) + 1) * ((v + w + 1).factorial : ℝ)) =
      (-1) ^ 0 * (-1) ^ (1 + (u + w + 1)) * (-1) ^ (v + w + v) /
        (((u + w).factorial : ℝ) * (w.factorial * v.factorial * u.factorial)) *
        ((u + w).factorial : ℝ) := by
    rw [hsign, Nat.factorial_succ (v + w + 1)]
    have := hf (v + w + 1); have := hf (u + v + w + 1 + 1); have := hf (w + 1)
    have := hf (v + w); have := hf (u + w); have := hf u; have := hf v; have := hf w
    push_cast
    field_simp
  have hQ : triD 1 (v + w) (v + w + 1) * triD 1 (v + w) (v + w + 1) *
      (triD (u + v) (u + w + 1) (v + w + 1) * triD (u + v) (u + w + 1) (v + w + 1)) *
      (√(((v + w + 1 : ℕ) : ℝ) + 1) * √(((v + w + 1 : ℕ) : ℝ) + 1)) *
      (projD (v + w + 1) (-1 - (v : ℤ) - w) * projD (v + w + 1) (1 + (v : ℤ) + w)) =
      ((v + w).factorial : ℝ) / (v + w + 1 + 1).factorial *
        ((u.factorial * v.factorial * (w + 1).factorial : ℝ) / (u + v + w + 1 + 1).factorial) *
        (((v + w + 1 : ℕ) : ℝ) + 1) * ((v + w + 1).factorial : ℝ) := by
    rw [hT2, hT3, hS2, hPd]
  set T1 := triD 1 (u + w + 1) (u + w)
  set T2 := triD 1 (v + w) (v + w + 1)
  set T3 := triD (u + v) (u + w + 1) (v + w + 1)
  set T4 := triD (u + v) (v + w) (u + w)
  set P1 := projD 1 1
  set Pa := projD (u + w + 1) (-((u : ℤ) + w + 1))
  set Pd := projD (v + w) ((v : ℤ) + w)
  set Pe := projD (u + v) ((u : ℤ) - v)
  set Pk1 := projD (u + w) ((u : ℤ) + w)
  set Pk2 := projD (u + w) (-((u : ℤ) + w))
  set Pd1 := projD (v + w + 1) (-1 - (v : ℤ) - w)
  set Pd2 := projD (v + w + 1) (1 + (v : ℤ) + w)
  set S1 := √(((u + w : ℕ) : ℝ) + 1)
  set S2 := √(((v + w + 1 : ℕ) : ℝ) + 1)
  have hZ : (-1 : ℝ) ^ ((u + w + 1 + (v + w) + (u + w) + (v + w + 1)) / 2) * (S1 * S2) *
      (S2 * ((-1) ^ (v + w + 1) * ((-1) ^ (1 + 0) * (T2 * P1 * Pd * Pd1) / ((v + w).factorial : ℝ)) *
        ((-1) ^ (v + w + 1 + (u + w + 1)) * (T3 * Pd2 * Pa * Pe) /
          ((v.factorial : ℝ) * (w + 1).factorial * u.factorial)))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (hσ _) (mul_pos hS1p hS2p).ne') (mul_ne_zero hS2p.ne'
      (mul_ne_zero (mul_ne_zero (hσ _) (div_ne_zero (mul_ne_zero (hσ _)
        (mul_pos (mul_pos (mul_pos hT2p hP1p) hPdp) hPd1p).ne') (hf _)))
        (div_ne_zero (mul_ne_zero (hσ _) (mul_pos (mul_pos (mul_pos hT3p hPd2p) hPap) hPep).ne')
          (mul_ne_zero (mul_ne_zero (hf _) (hf _)) (hf _)))))
  apply mul_right_cancel₀ hZ
  linear_combination -hrec -
    (T1 * T4 * S1 * P1 * Pa * Pd * Pe * ((-1 : ℝ) ^ (u + v + w + 1) *
      (-1) ^ ((u + w + 1 + (v + w) + (u + w) + (v + w + 1)) / 2) * (-1) ^ (v + w + 1) *
      (-1) ^ (1 + 0) * (-1) ^ (v + w + 1 + (u + w + 1)) * ((u + v + w + 1 + 1).factorial : ℝ) /
      ((v.factorial * u.factorial * w.factorial : ℝ) * (v + w).factorial *
        (v.factorial * (w + 1).factorial * u.factorial)))) * hQ -
    (T1 * T4 * S1 * P1 * Pa * Pd * Pe) * hcore +
    (T1 * T4 * S1 * P1 * Pa * Pd * Pe * ((-1 : ℝ) ^ 0 * (-1) ^ (1 + (u + w + 1)) *
      (-1) ^ (v + w + v) / (((u + w).factorial : ℝ) * (w.factorial * v.factorial *
        u.factorial)))) * hPk

/-- The spin-½ 6j symbols with `j₆ = j₅ + ½` agree with `racahW`: the two cases `j₃ = j₂ ± ½`
are `sixJSym_half_plus` and `sixJSym_half_minus` after solving the triangle conditions for
`u, v, w`. -/
lemma sixJSym_one_left_succ {j₂ j₃ j₄ j₅ : ℕ} (hA : Adm6 1 j₂ j₃ j₄ j₅ (j₅ + 1)) :
    sixJSym 1 j₂ j₃ j₄ j₅ (j₅ + 1) = racahW 1 j₂ j₃ j₄ j₅ (j₅ + 1) := by
  obtain ⟨h1, -, h3, h4⟩ := hA
  unfold Tri at h1 h3 h4
  rcases (by omega : j₃ = j₂ + 1 ∨ j₂ = j₃ + 1) with rfl | rfl
  · obtain ⟨u, v, w, rfl, rfl, rfl⟩ : ∃ u v w, j₂ = u + w ∧ j₄ = u + v + 1 ∧ j₅ = v + w :=
      ⟨(j₂ + j₄ - 1 - j₅) / 2, (j₅ + j₄ - 1 - j₂) / 2, (j₂ + j₅ + 1 - j₄) / 2, by omega,
        by omega, by omega⟩
    exact sixJSym_half_plus u v w
  · obtain ⟨u, v, w, rfl, rfl, rfl⟩ : ∃ u v w, j₃ = u + w ∧ j₄ = u + v ∧ j₅ = v + w :=
      ⟨(j₃ + j₄ - j₅) / 2, (j₄ + j₅ - j₃) / 2, (j₃ + j₅ - j₄) / 2, by omega, by omega, by omega⟩
    exact sixJSym_half_minus u v w

/-- **Racah's formula with one spin ½**: Physlib's 6j symbol `{½ j₂ j₃; j₄ j₅ j₆}` equals
Racah's single-sum expression `racahW` (doubled units), for all spins. -/
theorem sixJSym_one_left_eq_racahW (j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym 1 j₂ j₃ j₄ j₅ j₆ = racahW 1 j₂ j₃ j₄ j₅ j₆ := by
  by_cases hA : Adm6 1 j₂ j₃ j₄ j₅ j₆
  · have h2 := hA.2.1
    unfold Tri at h2
    rcases (by omega : j₆ = j₅ + 1 ∨ j₅ = j₆ + 1) with rfl | rfl
    · exact sixJSym_one_left_succ hA
    · rw [← sixJSym_swap₂₃, ← racahW_swap23]
      exact sixJSym_one_left_succ ((adm6_swap23 1 j₃ j₂ j₄ j₆ (j₆ + 1)).1 hA)
  · rw [racahW_of_not hA]
    by_contra h
    exact hA (tri_of_sixJSym_ne_zero h)

end Lightlike.Asymptotics
