import Lightlike.Asymptotics.RacahW

/-!
# The Biedenharn–Elliott identity with one spin ½ for Racah's expression

`racahW_be_half` is the Biedenharn–Elliott identity `BE(1, b, c, p−1, r−1, f, p, q, r)` (doubled
units, so the spin `a = ½`) for Racah's expression `racahW` in place of Physlib's `sixJSym`:

  `W{p q r; r−1 1 p−1} · W{p q r; f b c} = Σ_{x = b ± 1} (−1)^{(…+x)/2} (x+1)
      W{1 b x; c p−1 p} · W{c p−1 x; r−1 f q} · W{r−1 f x; b 1 r}`.

All spin-½ factors are single-term Racah sums (`sigma_half_plus`, `sigma_half_minus`,
`sigma_half_K`); after the triangle coefficients cancel, the identity is the contiguous relation
`rsum_contiguous` of Racah's sum. `Racah.lean` uses it, together with the same identity for
`sixJSym` (`Lightlike.Pentagon.biedenharnElliott`), to prove Racah's formula by induction on the total
spin.
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.Asymptotics

/-! ## The spin-½ Racah sums -/

/-- The Racah sum of `W{1 b b+1; c p−1 p}` (one term), times a triangle coefficient. -/
lemma sigma_half_plus {b c p : ℕ} (h : Tri p b c) (hβ : b + 2 ≤ c + p) :
    triSq c (p - 1) (b + 1) *
        rsum (faceD 1 b (b + 1) c (p - 1) p) (quadD 1 b (b + 1) c (p - 1) p) =
      (-1) ^ ((p + b + c) / 2) * ((((b + c - p) / 2 + 1 : ℕ)) : ℝ) := by
  obtain ⟨α, β, γ, rfl, rfl, rfl⟩ : ∃ α β γ : ℕ, p = α + β + 1 ∧ b = α + γ ∧ c = β + 1 + γ :=
    ⟨(p + b - c) / 2, (p + c - b) / 2 - 1, (b + c - p) / 2, by unfold Tri at h; omega,
      by unfold Tri at h; omega, by unfold Tri at h; omega⟩
  rw [triSq_eq α (γ + 1) β (by ring) (by omega) (by ring),
    rsum_eq_single (α + β + 1 + γ) 2 0 (by simp [faceD]; omega) (by simp [quadD]; omega)
      (quadD_nonneg _ _ _ _ _ _),
    rterm_eq_of ![β, γ, 0, 0] ![0, α, 1] (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega),
    show (α + β + 1 + (α + γ) + (β + 1 + γ)) / 2 = α + β + 1 + γ by omega,
    show (α + γ + (β + 1 + γ) - (α + β + 1)) / 2 + 1 = γ + 1 by omega,
    show α + (γ + 1) + β + 1 = α + β + 1 + γ + 1 by ring]
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, mul_one, one_mul, Nat.cast_mul]
  rw [Nat.factorial_succ γ]
  have : (0 : ℝ) < (α + β + 1 + γ + 1).factorial := by positivity
  have : (0 : ℝ) < β.factorial := by positivity
  have : (0 : ℝ) < γ.factorial := by positivity
  have : (0 : ℝ) < α.factorial := by positivity
  push_cast
  field_simp

/-- The Racah sum of `W{1 b b−1; c p−1 p}` (one term), times a triangle coefficient. -/
lemma sigma_half_minus {b c p : ℕ} (h : Tri p b c) (hb : 1 ≤ b) (hα : c + 2 ≤ p + b) :
    triSq c (p - 1) (b - 1) *
        rsum (faceD 1 b (b - 1) c (p - 1) p) (quadD 1 b (b - 1) c (p - 1) p) =
      (-1) ^ ((p + b + c) / 2) * ((((p + b + c) / 2 + 1 : ℕ)) : ℝ) := by
  obtain ⟨α, β, γ, rfl, rfl, rfl⟩ : ∃ α β γ : ℕ, p = α + 1 + β ∧ b = α + 1 + γ ∧ c = β + γ :=
    ⟨(p + b - c) / 2 - 1, (p + c - b) / 2, (b + c - p) / 2, by unfold Tri at h; omega,
      by unfold Tri at h; omega, by unfold Tri at h; omega⟩
  rw [triSq_eq α γ β (by ring) (by omega) (by omega),
    rsum_eq_single (α + 1 + β + γ) 2 0 (by simp [faceD]; omega) (by simp [quadD]; omega)
      (quadD_nonneg _ _ _ _ _ _),
    rterm_eq_of ![β, γ, 0, 1] ![0, α, 0] (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega),
    show (α + 1 + β + (α + 1 + γ) + (β + γ)) / 2 = α + 1 + β + γ by omega,
    show α + γ + β + 1 = α + 1 + β + γ by ring]
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, mul_one, one_mul, Nat.cast_mul]
  rw [Nat.factorial_succ (α + 1 + β + γ)]
  have : (0 : ℝ) < (α + 1 + β + γ).factorial := by positivity
  have : (0 : ℝ) < β.factorial := by positivity
  have : (0 : ℝ) < γ.factorial := by positivity
  have : (0 : ℝ) < α.factorial := by positivity
  push_cast
  field_simp

/-- The Racah sum of `W{p q r; r−1 1 p−1}` (one term), times a triangle coefficient. -/
lemma sigma_half_K {p q r : ℕ} (h : Tri p q r) (hv : q + 2 ≤ p + r) :
    triSq p q r * rsum (faceD p q r (r - 1) 1 (p - 1)) (quadD p q r (r - 1) 1 (p - 1)) =
      (-1) ^ ((p + q + r) / 2) * ((((p + r - q) / 2 : ℕ)) : ℝ) := by
  obtain ⟨u, v, w, rfl, rfl, rfl⟩ : ∃ u v w : ℕ, p = u + v + 1 ∧ q = u + w ∧ r = v + 1 + w :=
    ⟨(p + q - r) / 2, (p + r - q) / 2 - 1, (q + r - p) / 2, by unfold Tri at h; omega,
      by unfold Tri at h; omega, by unfold Tri at h; omega⟩
  rw [triSq_eq w (v + 1) u (by ring) (by ring) (by ring),
    rsum_eq_single (u + v + 1 + w) 0 0 (by simp [faceD]; omega) (by simp [quadD]; omega)
      (quadD_nonneg _ _ _ _ _ _),
    rterm_eq_of ![0, w, 1, u] ![0, 0, v] (by intro i; fin_cases i <;> simp [faceD] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD] <;> omega),
    show (u + v + 1 + (u + w) + (v + 1 + w)) / 2 = u + v + 1 + w by omega,
    show (u + v + 1 + (v + 1 + w) - (u + w)) / 2 = v + 1 by omega,
    show w + (v + 1) + u + 1 = u + v + 1 + w + 1 by ring]
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, mul_one, one_mul, Nat.cast_mul]
  rw [Nat.factorial_succ v]
  have : (0 : ℝ) < (u + v + 1 + w + 1).factorial := by positivity
  have : (0 : ℝ) < u.factorial := by positivity
  have : (0 : ℝ) < v.factorial := by positivity
  have : (0 : ℝ) < w.factorial := by positivity
  push_cast
  field_simp

/-! ## The identity -/

/-- A term of the Biedenharn–Elliott sum with `racahW` in place of `sixJSym` (as `beTerm`). -/
noncomputable def wTerm (a b c d e f p q r x : ℕ) : ℝ :=
  (-1 : ℝ) ^ ((a + b + c + d + e + f + p + q + r + x) / 2) * ((x : ℝ) + 1) *
    (racahW a b x c d p * racahW c d x e f q * racahW e f x b a r)

/-- The triangle coefficients common to both sides of `racahW_be_half`. -/
noncomputable def beC (p q r f b c : ℕ) : ℝ :=
  triD p 1 (p - 1) * triD (r - 1) q (p - 1) * triD (r - 1) 1 r * triD p b c * triD f q c *
    triD f b r

/-- Racah's sum with the shift of the `+` term of `rsum_contiguous`. -/
noncomputable def rsumP (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) : ℝ :=
  rsum ![A 0 - 1, A 1, A 2, A 3] ![B 0, B 1, B 2 - 1]

/-- Racah's sum with the shift of the `−` term of `rsum_contiguous`. -/
noncomputable def rsumM (A : Fin 4 → ℤ) (B : Fin 3 → ℤ) : ℝ :=
  rsum ![A 0 - 1, A 1 - 1, A 2, A 3 - 1] ![B 0 - 1, B 1 - 1, B 2 - 1]

/-- Racah's sum of an admissible symbol is balanced. -/
lemma faceD_sum_eq_quadD_sum {p q r f b c : ℕ} (hT : Adm6 p q r f b c) :
    ∑ i, faceD p q r f b c i = ∑ k, quadD p q r f b c k := by
  unfold Adm6 Tri at hT
  simp [faceD, quadD, Fin.sum_univ_four, Fin.sum_univ_three]
  omega

/-- The left side: `W{p q r; r−1 1 p−1} W{p q r; f b c} = C (−1)^{s₁} v₁ σ_T`. -/
lemma be_half_lhs {p q r f b c : ℕ} (hT : Adm6 p q r f b c) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    racahW p q r (r - 1) 1 (p - 1) * racahW p q r f b c =
      beC p q r f b c * ((-1) ^ ((p + q + r) / 2) * ((((p + r - q) / 2 : ℕ)) : ℝ)) *
        rsum (faceD p q r f b c) (quadD p q r f b c) := by
  have t1 : Tri p q r := hT.1
  by_cases hv : q + 2 ≤ p + r
  · have hK : Adm6 p q r (r - 1) 1 (p - 1) := by
      unfold Adm6 Tri at *; omega
    rw [racahW_of_adm hK, racahW_of_adm hT, ← sigma_half_K t1 hv, ← triD_mul_self p q r, beC]
    ring
  · have hK : ¬Adm6 p q r (r - 1) 1 (p - 1) := by
      unfold Adm6 Tri at *; omega
    have h0 : (p + r - q) / 2 = 0 := by unfold Tri at t1; omega
    rw [racahW_of_not hK, h0]
    simp

/-- The `x = b + 1` term, times `b + 1`. -/
lemma be_half_plus {p q r f b c : ℕ} (hT : Adm6 p q r f b c) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    ((b : ℝ) + 1) * wTerm 1 b c (p - 1) (r - 1) f p q r (b + 1) =
      beC p q r f b c * (-1) ^ ((p + q + r) / 2) *
        (((((b + c - p) / 2 + 1 : ℕ)) : ℝ) * ((((b + f - r) / 2 + 1 : ℕ)) : ℝ)) *
        rsumP (faceD p q r f b c) (quadD p q r f b c) := by
  obtain ⟨t1, t2, t3, t4⟩ := hT
  by_cases hc : b + 2 ≤ c + p ∧ b + 2 ≤ f + r ∧ q + 2 ≤ p + r
  swap
  · have hN : ¬Adm6 c (p - 1) (b + 1) (r - 1) f q := by
      unfold Adm6 Tri at *; omega
    have h0 : rsumP (faceD p q r f b c) (quadD p q r f b c) = 0 := by
      unfold rsumP
      unfold Tri at t1 t2 t3 t4
      by_cases h1 : b + 2 ≤ c + p
      · by_cases h2 : b + 2 ≤ f + r
        · exact rsum_eq_zero_of_lt 2 2 (by simp [faceD, quadD]; omega)
        · exact rsum_eq_zero_of_lt 1 2 (by simp [faceD, quadD]; omega)
      · exact rsum_eq_zero_of_lt 3 2 (by simp [faceD, quadD]; omega)
    rw [wTerm, racahW_of_not hN, h0]
    simp
  obtain ⟨hβ2, hβ4, hv⟩ := hc
  have h1 : Adm6 1 b (b + 1) c (p - 1) p := by unfold Adm6 Tri at *; omega
  have h2 : Adm6 c (p - 1) (b + 1) (r - 1) f q := by unfold Adm6 Tri at *; omega
  have h3 : Adm6 1 b (b + 1) f (r - 1) r := by unfold Adm6 Tri at *; omega
  have t4' : Tri r b f := by unfold Tri at *; omega
  have e1 : triSq 1 b (b + 1) = 1 / (((b : ℝ) + 1) * ((b : ℝ) + 2)) := by
    rw [triSq_eq b 1 0 (by ring) (by ring) (by ring)]
    simp only [Nat.factorial_zero, Nat.factorial_one, add_zero, one_mul, mul_one]
    rw [show b + 1 + 1 = (b + 1) + 1 by ring, Nat.factorial_succ (b + 1), Nat.factorial_succ b]
    have : (0 : ℝ) < b.factorial := by positivity
    push_cast
    field_simp
    ring
  have e4 : rsum (faceD c (p - 1) (b + 1) (r - 1) f q) (quadD c (p - 1) (b + 1) (r - 1) f q) =
      rsumP (faceD p q r f b c) (quadD p q r f b c) := by
    unfold rsumP
    unfold Tri at t1 t2 t3 t4
    exact rsum_eq_of_perm (permOf ![1, 2, 0, 3] (by decide))
      (Equiv.ofBijective ![2, 0, 1] (by decide))
      (by intro i; fin_cases i <;> simp [faceD, permOf] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD, Equiv.ofBijective_apply] <;> omega)
  have hsign : (-1 : ℝ) ^ ((1 + b + c + (p - 1) + (r - 1) + f + p + q + r + (b + 1)) / 2) *
      ((-1) ^ ((p + b + c) / 2) * (-1) ^ ((r + b + f) / 2)) = (-1) ^ ((p + q + r) / 2) := by
    rw [← pow_add, ← pow_add]
    unfold Tri at t1 t2 t3 t4
    exact neg_one_pow_eq_of_mod (by omega)
  calc ((b : ℝ) + 1) * wTerm 1 b c (p - 1) (r - 1) f p q r (b + 1)
      = (-1 : ℝ) ^ ((1 + b + c + (p - 1) + (r - 1) + f + p + q + r + (b + 1)) / 2) *
          (((b : ℝ) + 1) * (((b + 1 : ℕ) : ℝ) + 1)) * beC p q r f b c * triSq 1 b (b + 1) *
          (triSq c (p - 1) (b + 1) *
            rsum (faceD 1 b (b + 1) c (p - 1) p) (quadD 1 b (b + 1) c (p - 1) p)) *
          (triSq f (r - 1) (b + 1) *
            rsum (faceD 1 b (b + 1) f (r - 1) r) (quadD 1 b (b + 1) f (r - 1) r)) *
          rsum (faceD c (p - 1) (b + 1) (r - 1) f q) (quadD c (p - 1) (b + 1) (r - 1) f q) := by
        rw [wTerm, racahW_flipswap 1 b (b + 1) f (r - 1) r, racahW_of_adm h1, racahW_of_adm h2,
          racahW_of_adm h3, triD_cycle p 1 (p - 1), triD_swap13 p b c, ← triD_cycle c f q,
          triD_swap23 (r - 1) q (p - 1), triD_swap12 (r - 1) 1 r, triD_swap12 f (r - 1) (b + 1),
          ← triD_mul_self 1 b (b + 1), ← triD_mul_self c (p - 1) (b + 1),
          ← triD_mul_self f (r - 1) (b + 1), beC]
        ring
    _ = (-1 : ℝ) ^ ((1 + b + c + (p - 1) + (r - 1) + f + p + q + r + (b + 1)) / 2) *
          (((b : ℝ) + 1) * (((b + 1 : ℕ) : ℝ) + 1)) * beC p q r f b c *
          (1 / (((b : ℝ) + 1) * ((b : ℝ) + 2))) *
          ((-1) ^ ((p + b + c) / 2) * ((((b + c - p) / 2 + 1 : ℕ)) : ℝ)) *
          ((-1) ^ ((r + b + f) / 2) * ((((b + f - r) / 2 + 1 : ℕ)) : ℝ)) *
          rsumP (faceD p q r f b c) (quadD p q r f b c) := by
        rw [e1, sigma_half_plus t2 hβ2, sigma_half_plus t4' hβ4, e4]
    _ = _ := by
        rw [← hsign]
        push_cast
        field_simp
        ring

/-- The `x = b − 1` term, times `b + 1`. -/
lemma be_half_minus {p q r f b c : ℕ} (hT : Adm6 p q r f b c) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hb : 1 ≤ b) :
    ((b : ℝ) + 1) * wTerm 1 b c (p - 1) (r - 1) f p q r (b - 1) =
      -(beC p q r f b c * (-1) ^ ((p + q + r) / 2) *
        (((((p + b + c) / 2 + 1 : ℕ)) : ℝ) * ((((r + b + f) / 2 + 1 : ℕ)) : ℝ)) *
        rsumM (faceD p q r f b c) (quadD p q r f b c)) := by
  obtain ⟨t1, t2, t3, t4⟩ := hT
  by_cases hc : c + 2 ≤ p + b ∧ f + 2 ≤ b + r ∧ q + 2 ≤ p + r
  swap
  · have hN : ¬Adm6 c (p - 1) (b - 1) (r - 1) f q := by
      unfold Adm6 Tri at *; omega
    have h0 : rsumM (faceD p q r f b c) (quadD p q r f b c) = 0 := by
      unfold rsumM
      unfold Tri at t1 t2 t3 t4
      by_cases h1 : c + 2 ≤ p + b
      · by_cases h2 : f + 2 ≤ b + r
        · exact rsum_eq_zero_of_lt 2 2 (by simp [faceD, quadD]; omega)
        · exact rsum_eq_zero_of_lt 2 1 (by simp [faceD, quadD]; omega)
      · exact rsum_eq_zero_of_lt 2 0 (by simp [faceD, quadD]; omega)
    rw [wTerm, racahW_of_not hN, h0]
    simp
  obtain ⟨hα2, hγ4, hv⟩ := hc
  have h1 : Adm6 1 b (b - 1) c (p - 1) p := by unfold Adm6 Tri at *; omega
  have h2 : Adm6 c (p - 1) (b - 1) (r - 1) f q := by unfold Adm6 Tri at *; omega
  have h3 : Adm6 1 b (b - 1) f (r - 1) r := by unfold Adm6 Tri at *; omega
  have t4' : Tri r b f := by unfold Tri at *; omega
  have hγ4' : f + 2 ≤ r + b := by omega
  obtain ⟨b, rfl⟩ : ∃ b' : ℕ, b = b' + 1 := ⟨b - 1, by omega⟩
  have e1 : triSq 1 (b + 1) (b + 1 - 1) = 1 / (((b : ℝ) + 1) * ((b : ℝ) + 2)) := by
    rw [triSq_eq b 0 1 (by ring) (by ring) (by omega)]
    simp only [Nat.factorial_zero, Nat.factorial_one, add_zero, one_mul, mul_one]
    rw [show b + 0 + 1 + 1 = (b + 1) + 1 by ring, Nat.factorial_succ (b + 1), Nat.factorial_succ b]
    have : (0 : ℝ) < b.factorial := by positivity
    push_cast
    field_simp
    ring
  have e4 : rsum (faceD c (p - 1) (b + 1 - 1) (r - 1) f q)
      (quadD c (p - 1) (b + 1 - 1) (r - 1) f q) =
      rsumM (faceD p q r f (b + 1) c) (quadD p q r f (b + 1) c) := by
    unfold rsumM
    unfold Tri at t1 t2 t3 t4
    exact rsum_eq_of_perm (permOf ![1, 2, 0, 3] (by decide))
      (Equiv.ofBijective ![2, 0, 1] (by decide))
      (by intro i; fin_cases i <;> simp [faceD, permOf] <;> omega)
      (by intro k; fin_cases k <;> simp [quadD, Equiv.ofBijective_apply] <;> omega)
  have hsign : (-1 : ℝ) ^ ((1 + (b + 1) + c + (p - 1) + (r - 1) + f + p + q + r + (b + 1 - 1)) / 2) *
      ((-1) ^ ((p + (b + 1) + c) / 2) * (-1) ^ ((r + (b + 1) + f) / 2)) =
        -(-1) ^ ((p + q + r) / 2) := by
    rw [← pow_add, ← pow_add, show -(-1 : ℝ) ^ ((p + q + r) / 2) = (-1) ^ ((p + q + r) / 2 + 1) by
      ring]
    unfold Tri at t1 t2 t3 t4
    exact neg_one_pow_eq_of_mod (by omega)
  calc ((((b + 1 : ℕ) : ℝ)) + 1) * wTerm 1 (b + 1) c (p - 1) (r - 1) f p q r (b + 1 - 1)
      = (-1 : ℝ) ^ ((1 + (b + 1) + c + (p - 1) + (r - 1) + f + p + q + r + (b + 1 - 1)) / 2) *
          ((((b + 1 : ℕ) : ℝ) + 1) * (((b + 1 - 1 : ℕ) : ℝ) + 1)) * beC p q r f (b + 1) c *
          triSq 1 (b + 1) (b + 1 - 1) *
          (triSq c (p - 1) (b + 1 - 1) * rsum (faceD 1 (b + 1) (b + 1 - 1) c (p - 1) p)
            (quadD 1 (b + 1) (b + 1 - 1) c (p - 1) p)) *
          (triSq f (r - 1) (b + 1 - 1) * rsum (faceD 1 (b + 1) (b + 1 - 1) f (r - 1) r)
            (quadD 1 (b + 1) (b + 1 - 1) f (r - 1) r)) *
          rsum (faceD c (p - 1) (b + 1 - 1) (r - 1) f q)
            (quadD c (p - 1) (b + 1 - 1) (r - 1) f q) := by
        rw [wTerm, racahW_flipswap 1 (b + 1) (b + 1 - 1) f (r - 1) r, racahW_of_adm h1,
          racahW_of_adm h2, racahW_of_adm h3, triD_cycle p 1 (p - 1), triD_swap13 p (b + 1) c,
          ← triD_cycle c f q, triD_swap23 (r - 1) q (p - 1), triD_swap12 (r - 1) 1 r,
          triD_swap12 f (r - 1) (b + 1 - 1), ← triD_mul_self 1 (b + 1) (b + 1 - 1),
          ← triD_mul_self c (p - 1) (b + 1 - 1), ← triD_mul_self f (r - 1) (b + 1 - 1), beC]
        ring
    _ = (-1 : ℝ) ^ ((1 + (b + 1) + c + (p - 1) + (r - 1) + f + p + q + r + (b + 1 - 1)) / 2) *
          ((((b + 1 : ℕ) : ℝ) + 1) * (((b + 1 - 1 : ℕ) : ℝ) + 1)) * beC p q r f (b + 1) c *
          (1 / (((b : ℝ) + 1) * ((b : ℝ) + 2))) *
          ((-1) ^ ((p + (b + 1) + c) / 2) * ((((p + (b + 1) + c) / 2 + 1 : ℕ)) : ℝ)) *
          ((-1) ^ ((r + (b + 1) + f) / 2) * ((((r + (b + 1) + f) / 2 + 1 : ℕ)) : ℝ)) *
          rsumM (faceD p q r f (b + 1) c) (quadD p q r f (b + 1) c) := by
        rw [e1, sigma_half_minus t2 (by omega) hα2, sigma_half_minus t4' (by omega) hγ4', e4]
    _ = _ := by
        rw [show -(beC p q r f (b + 1) c * (-1) ^ ((p + q + r) / 2) *
            (((((p + (b + 1) + c) / 2 + 1 : ℕ)) : ℝ) * ((((r + (b + 1) + f) / 2 + 1 : ℕ)) : ℝ)) *
            rsumM (faceD p q r f (b + 1) c) (quadD p q r f (b + 1) c)) =
            beC p q r f (b + 1) c * -(-1) ^ ((p + q + r) / 2) *
            (((((p + (b + 1) + c) / 2 + 1 : ℕ)) : ℝ) * ((((r + (b + 1) + f) / 2 + 1 : ℕ)) : ℝ)) *
            rsumM (faceD p q r f (b + 1) c) (quadD p q r f (b + 1) c) by ring, ← hsign,
          show b + 1 - 1 = b by omega]
        push_cast
        have hb1 : ((b : ℝ) + 1 + 1) * ((b : ℝ) + 1) * (1 / (((b : ℝ) + 1) * ((b : ℝ) + 2))) = 1 := by
          field_simp
          ring
        linear_combination ((-1 : ℝ) ^ ((1 + (b + 1) + c + (p - 1) + (r - 1) + f + p + q + r + b) / 2) *
          beC p q r f (b + 1) c *
          ((-1) ^ ((p + (b + 1) + c) / 2) * ((((p + (b + 1) + c) / 2 : ℕ) : ℝ) + 1)) *
          ((-1) ^ ((r + (b + 1) + f) / 2) * ((((r + (b + 1) + f) / 2 : ℕ) : ℝ) + 1)) *
          rsumM (faceD p q r f (b + 1) c) (quadD p q r f (b + 1) c)) * hb1

/-- **Biedenharn–Elliott with one spin ½ for Racah's expression** (doubled units):
`BE(1, b, c, p−1, r−1, f, p, q, r)` with `racahW` in place of `sixJSym`. The two terms are
`x = b ± 1`; all other `x` violate the triangle rule in `(1 b x)`. -/
theorem racahW_be_half {p q r f b c : ℕ} (hT : Adm6 p q r f b c) (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hb : 1 ≤ b) :
    racahW p q r (r - 1) 1 (p - 1) * racahW p q r f b c =
      wTerm 1 b c (p - 1) (r - 1) f p q r (b + 1) +
        wTerm 1 b c (p - 1) (r - 1) f p q r (b - 1) := by
  have hB : ∀ k, 1 ≤ quadD p q r f b c k := by
    intro k; fin_cases k <;> simp [quadD] <;> omega
  have hc := rsum_contiguous (faceD p q r f b c) (quadD p q r f b c)
    (faceD_sum_eq_quadD_sum hT) (faceD_nonneg _ _ _ _ _ _) hB
  obtain ⟨t1, t2, t3, t4⟩ := id hT
  unfold Tri at t1 t2 t3 t4
  have k1 : quadD p q r f b c 0 + quadD p q r f b c 1 - faceD p q r f b c 0 -
      faceD p q r f b c 2 + 1 = (b : ℤ) + 1 := by simp [faceD, quadD]; omega
  have k2 : quadD p q r f b c 2 - faceD p q r f b c 2 = (((p + r - q) / 2 : ℕ) : ℤ) := by
    simp [faceD, quadD]; omega
  have k3 : quadD p q r f b c 0 - faceD p q r f b c 0 + 1 = (((b + f - r) / 2 + 1 : ℕ) : ℤ) := by
    simp [faceD, quadD]; omega
  have k4 : quadD p q r f b c 1 - faceD p q r f b c 0 + 1 = (((b + c - p) / 2 + 1 : ℕ) : ℤ) := by
    simp [faceD, quadD]; omega
  have k5 : faceD p q r f b c 1 + 1 = (((p + b + c) / 2 + 1 : ℕ) : ℤ) := by
    simp [faceD]
  have k6 : faceD p q r f b c 3 + 1 = (((r + b + f) / 2 + 1 : ℕ) : ℤ) := by
    simp [faceD]; omega
  rw [k1, k2, k3, k4, k5, k6] at hc
  apply mul_left_cancel₀ (show ((b : ℝ) + 1) ≠ 0 by positivity)
  rw [mul_add, be_half_plus hT hp hr, be_half_minus hT hp hr hb, be_half_lhs hT hp hr]
  unfold rsumP rsumM
  simp only [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add,
    Nat.cast_one] at hc ⊢
  linear_combination (beC p q r f b c * (-1) ^ ((p + q + r) / 2)) * hc

end Lightlike.Asymptotics
