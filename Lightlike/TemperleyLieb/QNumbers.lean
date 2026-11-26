import Mathlib
import Lightlike.TemperleyLieb.Kappa

/-!
# Quantum integers and the closed form of the vertex norm

With `[n] = (q^n - q^{-n}) / (q - q^{-1})` (`qb q n`) and `[n]! = ∏ [j]` (`qfac q n`) one has `chebD (loopVal q) n =
(-1)^n [n+1]`, `sCoef q a = -[a-1]/[a]`, `lamRec q a b i = -[a+b-i+1] [i] / ([a] [b])` and
`kapRec q a b i = (-1)^i [a+b-i+1]! [i]! [a-i]! [b-i]! / ([a]! [b]! [a+b-2i+1]!)` (= `θ(a,b,c)/Δ_c`, Kauffman–Lins).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- The quantum integer `[n] = (q^n - q^{-n}) / (q - q^{-1})`. -/
noncomputable def qb (q : kˣ) (n : ℕ) : k :=
  (((q : k) ^ n - ((q : k)⁻¹) ^ n)) / ((q : k) - (q : k)⁻¹)

/-- The quantum factorial. -/
noncomputable def qfac (q : kˣ) : ℕ → k
  | 0 => 1
  | n + 1 => qfac q n * qb q (n + 1)

/-- `loopVal q = -(q + q⁻¹)` with the field inverse. -/
lemma loopVal_eq (q : kˣ) : loopVal q = -((q : k) + (q : k)⁻¹) := by
  simp only [loopVal, Units.val_inv_eq_inv_val]; ring

/-- `[0] = 0`. -/
@[simp] lemma qb_zero (q : kˣ) : qb q 0 = 0 := by simp [qb]

/-- `[1] = 1` when `q - q⁻¹ ≠ 0`. -/
lemma qb_one (q : kˣ) (hD : (q : k) - (q : k)⁻¹ ≠ 0) : qb q 1 = 1 := by
  simp only [qb, pow_one]; exact div_self hD

/-- The recursion `[n+2] = (q + q⁻¹) [n+1] - [n]`. -/
lemma qb_succ_succ (q : kˣ) (n : ℕ) :
    qb q (n + 2) = ((q : k) + (q : k)⁻¹) * qb q (n + 1) - qb q n := by
  have hq : (q : k) ≠ 0 := q.ne_zero
  simp only [qb]
  rw [mul_div_assoc', ← sub_div]
  congr 1
  have hw : (q : k) * (q : k)⁻¹ = 1 := mul_inv_cancel₀ hq
  linear_combination (-(((q : k) ^ n - ((q : k)⁻¹) ^ n))) * hw

/-- `chebD (loopVal q) n = (-1)^n [n+1]`. -/
theorem chebD_eq_qb (q : kˣ) (hD : (q : k) - (q : k)⁻¹ ≠ 0) (n : ℕ) :
    chebD (loopVal q) n = (-1) ^ n * qb q (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [chebD, qb_one q hD]
    · have h2 : qb q 2 = (q : k) + (q : k)⁻¹ := by
        have := qb_succ_succ q 0
        simpa [qb_one q hD] using this
      simp [chebD, h2, loopVal_eq]
    · rw [chebD_succ_succ, ih (n + 1) (by omega), ih n (by omega), qb_succ_succ q (n + 1), loopVal_eq]
      ring

/-- `[n] = (q^n - (q^n)⁻¹) / (q - q⁻¹)`. -/
lemma qb_eq (q : kˣ) (n : ℕ) : qb q n = (((q : k) ^ n) - ((q : k) ^ n)⁻¹) / ((q : k) - (q : k)⁻¹) := by
  simp [qb, inv_pow]

/-- The coefficient `s_a = d_{a-2}/d_{a-1} = -[a-1]/[a]`. -/
theorem sCoef_eq (q : kˣ) (hD : (q : k) - (q : k)⁻¹ ≠ 0) (α : ℕ) :
    sCoef q (α + 1) = -qb q α / qb q (α + 1) := by
  rcases α with _ | α
  · simp [sCoef]
  · simp only [sCoef, show 2 ≤ α + 1 + 1 by omega, if_true, chebD_eq_qb q hD]
    rw [show α + 1 + 1 - 2 = α by omega, show α + 1 + 1 - 1 = α + 1 by omega]
    rw [pow_succ]
    have h : ((-1 : k) ^ α) ≠ 0 := pow_ne_zero _ (by simp)
    field_simp

/-- The pure field identity behind `lamRec_eq`. -/
lemma lam_identity (q u v z : k) (hq : q ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hz : z ≠ 0)
    (hD : q ^ 2 - 1 ≠ 0) (h1 : u ^ 2 - 1 ≠ 0) (h2 : v ^ 2 - 1 ≠ 0)
    (h3 : u ^ 2 * q ^ 2 - 1 ≠ 0) (h4 : v ^ 2 * q ^ 2 - 1 ≠ 0) :
    -(((u * v * q ^ 2 / z) - (u * v * q ^ 2 / z)⁻¹) / (q - q⁻¹)) * (((z * q) - (z * q)⁻¹) / (q - q⁻¹)) /
        ((((u * q) - (u * q)⁻¹) / (q - q⁻¹)) * (((v * q) - (v * q)⁻¹) / (q - q⁻¹))) =
      -(q + q⁻¹) + ((u - u⁻¹) / (q - q⁻¹)) / (((u * q) - (u * q)⁻¹) / (q - q⁻¹)) +
        ((v - v⁻¹) / (q - q⁻¹)) / (((v * q) - (v * q)⁻¹) / (q - q⁻¹)) +
        (-((u - u⁻¹) / (q - q⁻¹)) / (((u * q) - (u * q)⁻¹) / (q - q⁻¹))) *
          (-((v - v⁻¹) / (q - q⁻¹)) / (((v * q) - (v * q)⁻¹) / (q - q⁻¹))) *
          (-(((u * v * q / z) - (u * v * q / z)⁻¹) / (q - q⁻¹)) * (((z) - (z)⁻¹) / (q - q⁻¹)) /
            ((((u) - (u)⁻¹) / (q - q⁻¹)) * (((v) - (v)⁻¹) / (q - q⁻¹)))) := by
  field_simp
  ring

/-- `[j] ≠ 0` when `q^{2j} ≠ 1`. -/
lemma qb_ne (q : kˣ) (hD : (q : k) - (q : k)⁻¹ ≠ 0) (j : ℕ) (h : (q : k) ^ (2 * j) ≠ 1) : qb q j ≠ 0 := by
  have hq : (q : k) ≠ 0 := q.ne_zero
  rw [qb_eq]
  refine div_ne_zero ?_ hD
  have hqj : (q : k) ^ j ≠ 0 := pow_ne_zero _ hq
  intro h0
  apply h
  field_simp at h0
  rw [pow_mul']
  linear_combination h0

/-- The vertex eigenvalue in closed form: `lamRec a b i = -[a+b-i+1][i]/([a][b])`. -/
theorem lamRec_eq (q : kˣ) : ∀ (i a b : ℕ), i ≤ a → i ≤ b →
    (∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) →
    lamRec q a b i = -qb q (a + b - i + 1) * qb q i / (qb q a * qb q b) := by
  intro i
  induction i with
  | zero => intro a b _ _ _; simp [lamRec]
  | succ i ih =>
    intro a b hia hib hq2
    obtain ⟨α, rfl⟩ : ∃ α, a = α + 1 := ⟨a - 1, by omega⟩
    obtain ⟨β, rfl⟩ : ∃ β, b = β + 1 := ⟨b - 1, by omega⟩
    have hq : (q : k) ≠ 0 := q.ne_zero
    have hD2 : (q : k) ^ 2 - 1 ≠ 0 := by
      have := hq2 1 le_rfl (by omega); simpa [sub_eq_zero] using this
    have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
      intro h
      apply hD2
      field_simp at h
      linear_combination h
    simp only [lamRec, sCoef_eq q hD, loopVal_eq, Nat.add_sub_cancel]
    have hnz : ∀ j, 1 ≤ j → j ≤ α + β + 3 → qb q j ≠ 0 := fun j h1 h2 => qb_ne q hD j (hq2 j h1 (by omega))
    obtain ⟨m, hm⟩ : ∃ m, α + β = m + i := ⟨α + β - i, by omega⟩
    have e1 : α + 1 + (β + 1) - (i + 1) + 1 = m + 2 := by omega
    have e2 : α + β - i + 1 = m + 1 := by omega
    rw [e1]
    by_cases hα0 : α = 0
    · subst hα0
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [lamRec, qb_zero, zero_mul, zero_div, mul_zero, sub_zero, neg_zero, add_zero, zero_add]
      have hmβ : m = β := by omega
      subst hmβ
      have hb1 : qb q (m + 1) ≠ 0 := hnz _ (by omega) (by omega)
      rw [qb_one q hD, qb_succ_succ q m]
      field_simp
      ring
    by_cases hβ0 : β = 0
    · subst hβ0
      have hi0 : i = 0 := by omega
      subst hi0
      have hmα : m = α := by omega
      subst hmα
      have ha1 : qb q (m + 1) ≠ 0 := hnz _ (by omega) (by omega)
      simp only [lamRec, qb_zero, zero_mul, zero_div, mul_zero, div_zero, neg_zero, sub_zero, add_zero, zero_add]
      rw [qb_one q hD, qb_succ_succ q m]
      field_simp
      ring
    rw [ih α β (by omega) (by omega) (fun j h1 h2 => hq2 j h1 (by omega)), e2]
    have hmq : (q : k) ^ m = (q : k) ^ α * (q : k) ^ β / (q : k) ^ i := by
      have : (q : k) ^ (α + β) = (q : k) ^ m * (q : k) ^ i := by rw [hm, pow_add]
      rw [pow_add] at this
      field_simp
      linear_combination -this
    have hu1 : ((q : k) ^ α) ^ 2 - 1 ≠ 0 := by
      have := hq2 α (by omega) (by omega)
      rw [pow_mul'] at this; exact sub_ne_zero.mpr this
    have hv1 : ((q : k) ^ β) ^ 2 - 1 ≠ 0 := by
      have := hq2 β (by omega) (by omega)
      rw [pow_mul'] at this; exact sub_ne_zero.mpr this
    have hu2 : ((q : k) ^ α) ^ 2 * (q : k) ^ 2 - 1 ≠ 0 := by
      have := hq2 (α + 1) (by omega) (by omega)
      rw [show (q : k) ^ (2 * (α + 1)) = ((q : k) ^ α) ^ 2 * (q : k) ^ 2 by ring] at this
      exact sub_ne_zero.mpr this
    have hv2 : ((q : k) ^ β) ^ 2 * (q : k) ^ 2 - 1 ≠ 0 := by
      have := hq2 (β + 1) (by omega) (by omega)
      rw [show (q : k) ^ (2 * (β + 1)) = ((q : k) ^ β) ^ 2 * (q : k) ^ 2 by ring] at this
      exact sub_ne_zero.mpr this
    have hz : (q : k) ^ i ≠ 0 := pow_ne_zero _ hq
    have hu : (q : k) ^ α ≠ 0 := pow_ne_zero _ hq
    have hv : (q : k) ^ β ≠ 0 := pow_ne_zero _ hq
    simp only [qb_eq, pow_succ, hmq, show (q : k) ^ 2 = q * q by ring]
    generalize (q : k) ^ α = u at *
    generalize (q : k) ^ β = v at *
    generalize (q : k) ^ i = z at *
    have key := lam_identity (q : k) u v z hq hu hv hz hD2 hu1 hv1 hu2 hv2
    have e1 : u * v / z * q = u * v * q / z := by ring
    have e2 : u * v / z * q * q = u * v * q ^ 2 / z := by ring
    rw [e2, e1]
    linear_combination -key

/-- The quantum factorial does not vanish below the first zero. -/
lemma qfac_ne (q : kˣ) (N : ℕ) (hnz : ∀ j, 1 ≤ j → j ≤ N → qb q j ≠ 0) : ∀ n, n ≤ N → qfac q n ≠ 0 := by
  intro n
  induction n with
  | zero => intro _; simp [qfac]
  | succ n ih =>
    intro hn
    simp only [qfac]
    exact mul_ne_zero (ih (by omega)) (hnz (n + 1) (by omega) hn)

/-- **The norm of the vertex in closed form** (Kauffman–Lins `θ(a,b,c)/Δ_c`, `c = a + b - 2i`):
`kapRec a b i = (-1)^i [a+b-i+1]! [i]! [a-i]! [b-i]! / ([a]! [b]! [a+b-2i+1]!)`. -/
theorem kapRec_eq (q : kˣ) : ∀ (i a b : ℕ), i ≤ a → i ≤ b →
    (∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) →
    kapRec q a b i = (-1) ^ i * qfac q (a + b - i + 1) * qfac q i * qfac q (a - i) * qfac q (b - i) /
      (qfac q a * qfac q b * qfac q (a + b - 2 * i + 1)) := by
  intro i
  induction i with
  | zero =>
    intro a b _ _ hq2
    have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
      have := hq2 1 le_rfl (by omega)
      intro h; apply this
      have hq : (q : k) ≠ 0 := q.ne_zero
      field_simp at h
      linear_combination h
    have hnz : ∀ j, 1 ≤ j → j ≤ a + b + 1 → qb q j ≠ 0 := fun j h1 h2 => qb_ne q hD j (hq2 j h1 h2)
    have h1 := qfac_ne q (a + b + 1) hnz a (by omega)
    have h2 := qfac_ne q (a + b + 1) hnz b (by omega)
    have h3 := qfac_ne q (a + b + 1) hnz (a + b + 1) le_rfl
    have h0 : qfac q 0 = 1 := rfl
    simp only [kapRec, Nat.sub_zero, mul_zero, pow_zero, one_mul, h0, mul_one]
    field_simp
  | succ i ih =>
    intro a b hia hib hq2
    obtain ⟨α, rfl⟩ : ∃ α, a = α + 1 := ⟨a - 1, by omega⟩
    obtain ⟨β, rfl⟩ : ∃ β, b = β + 1 := ⟨b - 1, by omega⟩
    have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
      have := hq2 1 le_rfl (by omega)
      intro h; apply this
      have hq : (q : k) ≠ 0 := q.ne_zero
      field_simp at h
      linear_combination h
    have hnz : ∀ j, 1 ≤ j → j ≤ α + β + 3 → qb q j ≠ 0 := fun j h1 h2 => qb_ne q hD j (hq2 j h1 (by omega))
    obtain ⟨m, hm⟩ : ∃ m, α + β = m + i := ⟨α + β - i, by omega⟩
    have hlam := lamRec_eq q (i + 1) (α + 1) (β + 1) hia hib hq2
    have hih := ih α β (by omega) (by omega) (fun j h1 h2 => hq2 j h1 (by omega))
    simp only [kapRec, Nat.add_sub_cancel] at hih ⊢
    rw [hlam, hih]
    have e1 : α + 1 + (β + 1) - (i + 1) + 1 = m + 2 := by omega
    have e2 : α + β - i + 1 = m + 1 := by omega
    have e3 : α + 1 + (β + 1) - 2 * (i + 1) + 1 = α + β - 2 * i + 1 := by omega
    have e4 : α + 1 - (i + 1) = α - i := by omega
    have e5 : β + 1 - (i + 1) = β - i := by omega
    rw [e1, e3, e4, e5, e2]
    have n1 := qfac_ne q (α + β + 3) hnz α (by omega)
    have n2 := qfac_ne q (α + β + 3) hnz β (by omega)
    have n3 := qfac_ne q (α + β + 3) hnz (α + β - 2 * i + 1) (by omega)
    have n4 := hnz (α + 1) (by omega) (by omega)
    have n5 := hnz (β + 1) (by omega) (by omega)
    have n6 : qfac q (α + 1) = qfac q α * qb q (α + 1) := rfl
    have n7 : qfac q (β + 1) = qfac q β * qb q (β + 1) := rfl
    have n8 : qfac q (m + 2) = qfac q (m + 1) * qb q (m + 2) := rfl
    have n9 : qfac q (i + 1) = qfac q i * qb q (i + 1) := rfl
    rw [n6, n7, n8, n9]
    field_simp
    ring

/-- **The vertex norm in closed form**: `p_c (nestCap Q nestCup) p_c = K(a,b,i) · p_c` with `K = θ/Δ_c`. -/
theorem vertex_norm_closed (q : kˣ) (i a b : ℕ) (hia : i ≤ a) (hib : i ≤ b)
    (hq2 : ∀ j, 1 ≤ j → j ≤ a + b + 1 → (q : k) ^ (2 * j) ≠ 1) :
    jwAt q 0 (a + b - 2 * i) * (nestCap q (a - i) i * Qab q a b * nestCup q (a - i) i) *
        jwAt q 0 (a + b - 2 * i) =
      ((-1) ^ i * qfac q (a + b - i + 1) * qfac q i * qfac q (a - i) * qfac q (b - i) /
        (qfac q a * qfac q b * qfac q (a + b - 2 * i + 1))) • jwAt q 0 (a + b - 2 * i) := by
  have hD : (q : k) - (q : k)⁻¹ ≠ 0 := by
    have := hq2 1 le_rfl (by omega)
    intro h; apply this
    have hq : (q : k) ≠ 0 := q.ne_zero
    field_simp at h
    linear_combination h
  have hd : ∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0 := by
    intro j hj
    rw [chebD_eq_qb q hD]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) (qb_ne q hD (j + 1) (hq2 (j + 1) (by omega) (by omega)))
  rw [vertex_norm_value q i a b hia hib hd, kapRec_eq q i a b hia hib hq2]

end Lightlike.TemperleyLieb
