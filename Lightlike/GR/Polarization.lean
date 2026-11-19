import Lightlike.GR.SpinorHelicity

/-!
# Polarization vectors of massless vector bosons in spinor-helicity form

Elvang-Huang (2.49)–(2.50) and Exercise 2.10(c): for a null momentum `p = −|p]⟨p|` and a reference spinor
`q`, the polarization vectors in bispinor form are `(ε₊(p; q))_{aḃ} = (√2/⟨qp⟩) |p]⟨q|` and
`(ε₋(p; q))_{aḃ} = (√2/[qp]) |q]⟨p|` (`epsPlus`, `epsMinus`).

* transversality `p · ε± = 0` and `ε±² = 0` (`mdot_epsPlus`, …), the normalization `ε₊ · ε₋ = −1`
  (`mdot_epsPlus_epsMinus`);
* **gauge invariance of the reference spinor**: changing `q` shifts `ε₊` by a multiple of `p`
  (`epsPlus_sub_epsPlus`, Elvang-Huang p. 17 and Exercise 2.10(d));
* **the completeness relation** `ε₊^μ ε₋^ν + ε₋^μ ε₊^ν = −(η^{μν} − (p^μ q^ν + q^μ p^ν)/(p·q))` with the
  reference momentum `q = −|q]⟨q|` (`completeness_eps`).

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, §2.4: (2.49), p. 16, (2.50) and the
  discussion of the reference spinor and the Ward identity, p. 17; Exercise 2.10, p. 17.
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

/-- `p · q` of two rank-one bispinors: `mdot (momOf (a bᵀ)) (momOf (c dᵀ)) = ½ ⟨b d⟩ [a c]`. -/
lemma mdot_momOf_vecMulVec (a b c d : Fin 2 → ℂ) :
    mdot (momOf (vecMulVec a b)) (momOf (vecMulVec c d)) = (1 / 2) * angleBr b d * squareBr a c := by
  simp only [mdot, momOf, vecMulVec_apply, angleBr_eq, squareBr_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

lemma momOf_smul (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : momOf (c • M) = c • momOf M := by
  funext μ
  fin_cases μ <;> simp [momOf] <;> ring

/-- The positive-helicity polarization vector `(ε₊(p; q))_{aḃ} = (√2/⟨qp⟩) |p]⟨q|` (Elvang-Huang (2.49),
Exercise 2.10(c)); `l, lt` are `|p], ⟨p|` and `ltq` is `⟨q|`. -/
def epsPlus (l lt ltq : Fin 2 → ℂ) : Fin 4 → ℂ :=
  momOf ((((Real.sqrt 2 : ℝ) : ℂ) / angleBr ltq lt) • vecMulVec l ltq)

/-- The negative-helicity polarization vector `(ε₋(p; q))_{aḃ} = (√2/[qp]) |q]⟨p|`; `lq` is `|q]`. -/
def epsMinus (l lt lq : Fin 2 → ℂ) : Fin 4 → ℂ :=
  momOf ((((Real.sqrt 2 : ℝ) : ℂ) / squareBr lq l) • vecMulVec lq lt)

lemma nullMom_eq_momOf (l lt : Fin 2 → ℂ) : nullMom l lt = (-1 : ℂ) • momOf (vecMulVec l lt) := by
  rw [nullMom, ← momOf_smul]; congr 1; ext i j; simp [vecMulVec_apply]

/-- **Transversality** `p · ε₊ = 0`. -/
theorem mdot_epsPlus (l lt ltq : Fin 2 → ℂ) : mdot (nullMom l lt) (epsPlus l lt ltq) = 0 := by
  rw [nullMom_eq_momOf, epsPlus, momOf_smul]
  have hm : ∀ (a b : ℂ) (u v : Fin 4 → ℂ), mdot (a • u) (b • v) = a * b * mdot u v := by
    intro a b u v; simp only [mdot, Pi.smul_apply, smul_eq_mul]; ring
  rw [hm, mdot_momOf_vecMulVec]
  have : squareBr l l = 0 := by rw [squareBr_eq]; ring
  rw [this]; ring

/-- **Transversality** `p · ε₋ = 0`. -/
theorem mdot_epsMinus (l lt lq : Fin 2 → ℂ) : mdot (nullMom l lt) (epsMinus l lt lq) = 0 := by
  rw [nullMom_eq_momOf, epsMinus, momOf_smul]
  have hm : ∀ (a b : ℂ) (u v : Fin 4 → ℂ), mdot (a • u) (b • v) = a * b * mdot u v := by
    intro a b u v; simp only [mdot, Pi.smul_apply, smul_eq_mul]; ring
  rw [hm, mdot_momOf_vecMulVec]
  have : angleBr lt lt = 0 := by rw [angleBr_eq]; ring
  rw [this]; ring

lemma sqrt_two_sq_complex : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  have : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  exact_mod_cast this

lemma mdot_smul_smul (a b : ℂ) (u v : Fin 4 → ℂ) : mdot (a • u) (b • v) = a * b * mdot u v := by
  simp only [mdot, Pi.smul_apply, smul_eq_mul]; ring

/-- `ε₊` is null. -/
theorem mdot_epsPlus_self (l lt ltq : Fin 2 → ℂ) : mdot (epsPlus l lt ltq) (epsPlus l lt ltq) = 0 := by
  rw [epsPlus, momOf_smul, mdot_smul_smul, mdot_momOf_vecMulVec]
  have : squareBr l l = 0 := by rw [squareBr_eq]; ring
  rw [this]; ring

/-- **The normalization** `ε₊(p; q) · ε₋(p; q) = −1`. -/
theorem mdot_epsPlus_epsMinus (l lt lq ltq : Fin 2 → ℂ) (h1 : angleBr ltq lt ≠ 0)
    (h2 : squareBr lq l ≠ 0) : mdot (epsPlus l lt ltq) (epsMinus l lt lq) = -1 := by
  rw [epsPlus, epsMinus, momOf_smul, momOf_smul, mdot_smul_smul, mdot_momOf_vecMulVec,
    squareBr_antisymm l lq]
  field_simp
  rw [sqrt_two_sq_complex]

lemma momOf_sub (M N : Matrix (Fin 2) (Fin 2) ℂ) : momOf (M - N) = momOf M - momOf N := by
  funext μ
  fin_cases μ <;> simp [momOf] <;> ring

/-- The Schouten identity for angle spinors as vectors: `⟨qp⟩ q' − ⟨q'p⟩ q = ⟨q q'⟩ p`. -/
lemma schouten_vec (lt ltq ltq' : Fin 2 → ℂ) :
    angleBr ltq lt • ltq' - angleBr ltq' lt • ltq = angleBr ltq ltq' • lt := by
  funext a
  fin_cases a <;> simp [angleBr_eq] <;> ring

/-- **The reference spinor is a gauge choice** (Elvang-Huang p. 17 and Exercise 2.10(d)): changing `q` to `q'`
shifts `ε₊` by a multiple of `p`, `ε₊(p; q') − ε₊(p; q) = −√2 ⟨q q'⟩/(⟨qp⟩⟨q'p⟩) p`. -/
theorem epsPlus_sub_epsPlus (l lt ltq ltq' : Fin 2 → ℂ) (h1 : angleBr ltq lt ≠ 0)
    (h2 : angleBr ltq' lt ≠ 0) :
    epsPlus l lt ltq' - epsPlus l lt ltq =
      (-((Real.sqrt 2 : ℝ) : ℂ) * angleBr ltq ltq' / (angleBr ltq lt * angleBr ltq' lt)) •
        nullMom l lt := by
  have hv : (1 / angleBr ltq' lt) • ltq' - (1 / angleBr ltq lt) • ltq =
      (angleBr ltq ltq' / (angleBr ltq lt * angleBr ltq' lt)) • lt := by
    have key := schouten_vec lt ltq ltq'
    funext a
    have ha := congrFun key a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢
    field_simp
    linear_combination ha
  have hvm : ∀ (c : ℂ) (x : Fin 2 → ℂ), vecMulVec l (c • x) = c • vecMulVec l x := by
    intro c x; ext i j; simp [vecMulVec_apply]; ring
  have hvs : ∀ (x y : Fin 2 → ℂ), vecMulVec l (x - y) = vecMulVec l x - vecMulVec l y := by
    intro x y; ext i j; simp [vecMulVec_apply]; ring
  rw [epsPlus, epsPlus, ← momOf_sub, nullMom_eq_momOf, smul_smul, ← momOf_smul]
  congr 1
  rw [show (((Real.sqrt 2 : ℝ) : ℂ) / angleBr ltq' lt) • vecMulVec l ltq' -
      (((Real.sqrt 2 : ℝ) : ℂ) / angleBr ltq lt) • vecMulVec l ltq =
      ((Real.sqrt 2 : ℝ) : ℂ) • vecMulVec l ((1 / angleBr ltq' lt) • ltq' - (1 / angleBr ltq lt) • ltq) by
    rw [hvs, hvm, hvm, smul_sub, smul_smul, smul_smul]; congr 1 <;> congr 1 <;> ring]
  rw [hv, hvm, smul_smul]
  congr 1
  ring

/-- **The completeness relation** for the two helicities with the same reference momentum
`q = −|q]⟨q|`: `ε₊^μ ε₋^ν + ε₋^μ ε₊^ν = −(η^{μν} − (p^μ q^ν + q^μ p^ν)/(p · q))` (mostly-plus `η`). -/
theorem completeness_eps (l lt lq ltq : Fin 2 → ℂ) (h1 : angleBr ltq lt ≠ 0)
    (h2 : squareBr lq l ≠ 0) (μ ν : Fin 4) :
    epsPlus l lt ltq μ * epsMinus l lt lq ν + epsMinus l lt lq μ * epsPlus l lt ltq ν =
      -((if μ = ν then (if μ = 0 then -1 else 1) else 0) -
        (nullMom l lt μ * nullMom lq ltq ν + nullMom lq ltq μ * nullMom l lt ν) /
          mdot (nullMom l lt) (nullMom lq ltq)) := by
  set A := angleBr ltq lt
  set B := squareBr lq l
  have hpq : mdot (nullMom l lt) (nullMom lq ltq) = A * B / 2 := by
    rw [nullMom_eq_momOf, nullMom_eq_momOf, mdot_smul_smul, mdot_momOf_vecMulVec,
      angleBr_antisymm lt ltq, squareBr_antisymm l lq]
    ring
  -- the polynomial identity behind completeness
  have key : momOf (vecMulVec l ltq) μ * momOf (vecMulVec lq lt) ν +
      momOf (vecMulVec lq lt) μ * momOf (vecMulVec l ltq) ν =
      -(A * B / 2) * (if μ = ν then (if μ = 0 then -1 else 1) else 0) +
        (momOf (vecMulVec l lt) μ * momOf (vecMulVec lq ltq) ν +
          momOf (vecMulVec lq ltq) μ * momOf (vecMulVec l lt) ν) := by
    simp only [A, B, angleBr_eq, squareBr_eq]
    fin_cases μ <;> fin_cases ν <;>
      (simp [momOf, vecMulVec_apply]; ring_nf; try simp only [inv_pow, I_sq, inv_neg, inv_one]; try ring)
  rw [hpq, epsPlus, epsMinus, momOf_smul, momOf_smul, nullMom_eq_momOf, nullMom_eq_momOf]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hs := sqrt_two_sq_complex
  have hAB : A * B ≠ 0 := mul_ne_zero h1 h2
  apply mul_left_cancel₀ hAB
  have hA : A * A⁻¹ = 1 := mul_inv_cancel₀ h1
  have hB : B * B⁻¹ = 1 := mul_inv_cancel₀ h2
  have hAB2 : (A * B / 2) * (A * B / 2)⁻¹ = 1 := mul_inv_cancel₀ (div_ne_zero hAB two_ne_zero)
  simp only [div_eq_mul_inv]
  set m1 := momOf (vecMulVec l ltq)
  set m2 := momOf (vecMulVec lq lt)
  set P := momOf (vecMulVec l lt)
  set Q := momOf (vecMulVec lq ltq)
  set η : ℂ := if μ = ν then (if μ = 0 then -1 else 1) else 0
  have key' : m1 μ * m2 ν + m2 μ * m1 ν = -(A * B * 2⁻¹) * η + (P μ * Q ν + Q μ * P ν) := by
    rw [key]; ring
  linear_combination ((A * A⁻¹) * (B * B⁻¹) * (m1 μ * m2 ν + m2 μ * m1 ν)) * hs +
    (2 * (B * B⁻¹) * (m1 μ * m2 ν + m2 μ * m1 ν)) * hA + (2 * (m1 μ * m2 ν + m2 μ * m1 ν)) * hB +
    2 * key' - (2 * (P μ * Q ν + Q μ * P ν)) * hAB2

end Lightlike.SpinorHelicity
