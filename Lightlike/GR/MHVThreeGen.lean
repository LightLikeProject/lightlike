import Lightlike.GR.MHVTrue

/-!
# The three-gluon Feynman amplitudes for any helicities, from momentum conservation alone

For conserved three-point spinor kinematics the colour-ordered Feynman amplitude with the polarizations (2.49)-(2.50)
(common references `|q]` for negative and `⟨q'|` for positive legs) is
`A[1⁻2⁻3⁺] = ⟨12⟩ [q3]²/([q1][q2])` and `A[1⁺2⁺3⁻] = [12] ⟨q'3⟩²/(⟨q'1⟩⟨q'2⟩)`. On the kinematics with all angle
brackets zero (the anti-MHV three-point kinematics), `A[1⁺2⁺3⁻] = [12]³/([23][31])`.
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

/-- Auxiliary statement `ppm_alg` for the true MHV amplitudes. -/
lemma ppm_alg (s y0 y1 y2 x2 u0 u1 s01 : ℂ) (r2 : s * s = 2) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hx2 : x2 ≠ 0)
    (c1 : y0 * u0 + y1 * u1 + y2 * x2 = 0) :
    -s * (s / y0 * (s / y1) * (1 / 2 * 0 * s01) * (s / x2 * -1 * (1 / 2 * -y0 * u0)) +
      s / y1 * (s / x2) * (1 / 2 * y2 * -u1) * (s / y0 * -1 * (1 / 2 * y1 * s01)) +
      s / x2 * (s / y0) * (1 / 2 * -y2 * u0) *
        -(s / y1 * -1 * (1 / 2 * y0 * -s01) + s / y1 * -1 * (1 / 2 * y1 * 0))) = s01 * y2 ^ 2 / (y0 * y1) := by
  field_simp
  linear_combination (s01 * y2 * (s * s) / 2 + 3 * s01 * y2 - 8 * s01 * y2) * c1 +
    (s01 * y2 * (-(y0 * u0 + y1 * u1 + y2 * x2) / 2 - (4 + (s * s - 2)) * (y0 * u0 + y1 * u1))) * r2

/-- Auxiliary statement `bgAmplitude_three_ppm_gen` for the true MHV amplitudes. -/
theorem bgAmplitude_three_ppm_gen (l lt : Fin 3 → Fin 2 → ℂ) (h : Conserved3 l lt) (qs qa : Fin 2 → ℂ)
    (p e : ℕ → Fin 4 → ℂ) (hp0 : p 0 = nullMom (l 0) (lt 0)) (hp1 : p 1 = nullMom (l 1) (lt 1))
    (he0 : e 0 = epsPlus (l 0) (lt 0) qa) (he1 : e 1 = epsPlus (l 1) (lt 1) qa)
    (he2 : e 2 = epsMinus (l 2) (lt 2) qs)
    (hy0 : angleBr qa (lt 0) ≠ 0) (hy1 : angleBr qa (lt 1) ≠ 0) (hx2 : squareBr qs (l 2) ≠ 0) :
    bgAmplitude 0 p e = squareBr (l 0) (l 1) * angleBr qa (lt 2) ^ 2 / (angleBr qa (lt 0) * angleBr qa (lt 1)) := by
  rw [bgAmplitude_three, he0, he1, he2, hp0, hp1]
  simp only [epsMinus, epsPlus, nullMom_eq_momOf_smul, mdot_neg_right, mdot_add_right, mdot_momOf_smul_vec]
  have hs : ∀ u v : Fin 2 → ℂ, squareBr u v = -squareBr v u := fun u v => squareBr_antisymm u v
  have ha : ∀ u v : Fin 2 → ℂ, angleBr u v = -angleBr v u := fun u v => angleBr_antisymm u v
  have z1 : angleBr qa qa = 0 := by rw [angleBr_eq]; ring
  have z2 : squareBr (l 1) (l 1) = 0 := by rw [squareBr_eq]; ring
  have r2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have := sqrt_two_sq_complex; rw [sq] at this; exact this
  have c1 := contract_conserved3 h qa qs
  rw [hs (l 0) qs, hs (l 1) qs, hs (l 2) qs] at c1
  rw [hs (l 1) qs, hs (l 1) (l 0), ha (lt 2) qa, z1, z2]
  have key := ppm_alg (((Real.sqrt 2 : ℝ)) : ℂ) (angleBr qa (lt 0)) (angleBr qa (lt 1)) (angleBr qa (lt 2))
    (squareBr qs (l 2)) (squareBr qs (l 0)) (squareBr qs (l 1)) (squareBr (l 0) (l 1)) r2 hy0 hy1 hx2
    (by linear_combination (-1 : ℂ) * c1)
  rw [← key]
  ring

/-- Algebra of the three-point amplitude `[+ − +]`. -/
lemma pmp_alg (s a0 a1 a2 x0 x1 x2 b01 b20 : ℂ) (r2 : s * s = 2) (ha0 : a0 ≠ 0) (ha2 : a2 ≠ 0) (hx1 : x1 ≠ 0)
    (c1 : a0 * x0 + a1 * x1 + a2 * x2 = 0) (c2 : a1 * b01 = a2 * b20) :
    -s * (s / a0 * (s / x1) * (1 / 2 * a1 * -x0) * (s / a2 * -1 * (1 / 2 * a0 * b20)) +
      s / x1 * (s / a2) * (1 / 2 * -a1 * x2) * (s / a0 * -1 * (1 / 2 * a1 * b01))) =
        b20 * a1 ^ 2 / (a2 * a0) := by
  have s4 : s ^ 4 = 4 := by rw [show s ^ 4 = (s * s) * (s * s) by ring, r2]; norm_num
  field_simp
  ring_nf
  rw [s4]
  linear_combination (-4 * a1 * b20) * c1 + (-4 * a1 * x2) * c2

/-- **The three-gluon true amplitude `[1⁺ 2⁻ 3⁺]`** from momentum conservation:
`[31] ⟨q'2⟩² / (⟨q'3⟩⟨q'1⟩)` (the cyclic rotation of `bgAmplitude_three_ppm_gen`). -/
theorem bgAmplitude_three_pmp_gen (l lt : Fin 3 → Fin 2 → ℂ) (h : Conserved3 l lt) (qs qa : Fin 2 → ℂ)
    (p e : ℕ → Fin 4 → ℂ) (hp0 : p 0 = nullMom (l 0) (lt 0)) (hp1 : p 1 = nullMom (l 1) (lt 1))
    (he0 : e 0 = epsPlus (l 0) (lt 0) qa) (he1 : e 1 = epsMinus (l 1) (lt 1) qs)
    (he2 : e 2 = epsPlus (l 2) (lt 2) qa)
    (hy0 : angleBr qa (lt 0) ≠ 0) (hx1 : squareBr qs (l 1) ≠ 0) (hy2 : angleBr qa (lt 2) ≠ 0) :
    bgAmplitude 0 p e = squareBr (l 2) (l 0) * angleBr qa (lt 1) ^ 2 / (angleBr qa (lt 2) * angleBr qa (lt 0)) := by
  rw [bgAmplitude_three, he0, he1, he2, hp0, hp1]
  simp only [epsMinus, epsPlus, nullMom_eq_momOf_smul, mdot_neg_right, mdot_add_right, mdot_momOf_smul_vec]
  have hs : ∀ u v : Fin 2 → ℂ, squareBr u v = -squareBr v u := fun u v => squareBr_antisymm u v
  have z1 : angleBr qa qa = 0 := by rw [angleBr_eq]; ring
  have z2 : angleBr (lt 1) (lt 1) = 0 := by rw [angleBr_eq]; ring
  have r2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have := sqrt_two_sq_complex; rw [sq] at this; exact this
  have c1 := contract_conserved3 h qa qs
  have c2 := contract_conserved3 h qa (l 0)
  have z0 : squareBr (l 0) (l 0) = 0 := by rw [squareBr_eq]; ring
  rw [hs (l 0) qs, hs (l 1) qs, hs (l 2) qs] at c1
  rw [z0] at c2
  have h01 := hs (l 0) (l 1)
  rw [hs (l 0) qs, angleBr_antisymm (lt 1) qa, z1]
  have key := pmp_alg (((Real.sqrt 2 : ℝ)) : ℂ) (angleBr qa (lt 0)) (angleBr qa (lt 1)) (angleBr qa (lt 2))
    (squareBr qs (l 0)) (squareBr qs (l 1)) (squareBr qs (l 2)) (squareBr (l 0) (l 1)) (squareBr (l 2) (l 0)) r2
    hy0 hy2 hx1 (by linear_combination (-1 : ℂ) * c1) (by linear_combination (angleBr qa (lt 1)) * h01 - c2)
  rw [← key]
  ring

/-- Auxiliary statement `mmp_alg1` for the true MHV amplitudes. -/
lemma mmp_alg1 (s a0 a1 x0 x1 x2 y b01 : ℂ) (r2 : s * s = 2) (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy : y ≠ 0)
    (c1 : a0 * x0 + a1 * x1 = y * x2) :
    -s * (s / x1 * (s / y) * (1 / 2 * a1 * x2) * (s / x0 * -1 * (1 / 2 * b01 * x1)) +
        s / y * (s / x0) * (1 / 2 * -a0 * -x2) * -(s / x1 * -1 * (1 / 2 * -b01 * x0))) =
        b01 * x2 ^ 2 / (x0 * x1) := by
  field_simp
  linear_combination (b01 * x2 * (s * s) / 2 + 3 * b01 * x2) * c1 +
    (x2 * b01 * (a1 * x1 + a0 * x0) * (s * s + 3 / 2) + x2 ^ 2 * b01 * y / 2) * r2

/-- Auxiliary statement `bgAmplitude_three_mmp_gen` for the true MHV amplitudes. -/
theorem bgAmplitude_three_mmp_gen (l lt : Fin 3 → Fin 2 → ℂ) (h : Conserved3 l lt) (qs qa : Fin 2 → ℂ)
    (p e : ℕ → Fin 4 → ℂ) (hp0 : p 0 = nullMom (l 0) (lt 0)) (hp1 : p 1 = nullMom (l 1) (lt 1))
    (he0 : e 0 = epsMinus (l 0) (lt 0) qs) (he1 : e 1 = epsMinus (l 1) (lt 1) qs)
    (he2 : e 2 = epsPlus (l 2) (lt 2) qa)
    (hq0 : squareBr qs (l 0) ≠ 0) (hq1 : squareBr qs (l 1) ≠ 0) (hqa : angleBr qa (lt 2) ≠ 0) :
    bgAmplitude 0 p e = angleBr (lt 0) (lt 1) * squareBr qs (l 2) ^ 2 / (squareBr qs (l 0) * squareBr qs (l 1)) := by
  rw [bgAmplitude_three, he0, he1, he2, hp0, hp1]
  simp only [epsMinus, epsPlus, nullMom_eq_momOf_smul, mdot_neg_right, mdot_add_right, mdot_momOf_smul_vec]
  have hs : ∀ u v : Fin 2 → ℂ, squareBr u v = -squareBr v u := fun u v => squareBr_antisymm u v
  have ha : ∀ u v : Fin 2 → ℂ, angleBr u v = -angleBr v u := fun u v => angleBr_antisymm u v
  have z1 : squareBr qs qs = 0 := by rw [squareBr_eq]; ring
  have z2 : angleBr (lt 1) (lt 1) = 0 := by rw [angleBr_eq]; ring
  have r2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have := sqrt_two_sq_complex; rw [sq] at this; exact this
  have c1 := contract_conserved3 h qa qs
  rw [hs (l 0) qs, hs (l 1) qs, hs (l 2) qs, ha qa (lt 0), ha qa (lt 1)] at c1
  rw [hs (l 2) qs, ha qa (lt 0), ha (lt 1) (lt 0), z1, z2]
  have key := mmp_alg1 (((Real.sqrt 2 : ℝ)) : ℂ) (angleBr (lt 0) qa) (angleBr (lt 1) qa) (squareBr qs (l 0))
    (squareBr qs (l 1)) (squareBr qs (l 2)) (angleBr qa (lt 2)) (angleBr (lt 0) (lt 1)) r2 hq0 hq1 hqa
    (by linear_combination c1)
  rw [← key]
  ring

/-- **A complex null vector is `nullMom` of spinors.** -/
theorem exists_nullMom_of_null (P : Fin 4 → ℂ) (hP : mdot P P = 0) : ∃ l lt : Fin 2 → ℂ, P = nullMom l lt := by
  have hdet : momBispinor P 0 0 * momBispinor P 1 1 = momBispinor P 0 1 * momBispinor P 1 0 := by
    simp only [momBispinor, mdot] at *
    simp [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] at *
    linear_combination (-1 : ℂ) * hP + (P 2 ^ 2) * Complex.I_sq
  set M := momBispinor P with hM
  have hP' : P = momOf M := (momOf_momBispinor P).symm
  suffices h : ∃ l lt : Fin 2 → ℂ, M = -vecMulVec l lt by
    obtain ⟨l, lt, h⟩ := h
    exact ⟨l, lt, by rw [hP', h, nullMom]⟩
  by_cases h00 : M 0 0 = 0
  · by_cases h01 : M 0 1 = 0
    · refine ⟨![0, 1], ![-M 1 0, -M 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, h00, h01]
    · have h10 : M 1 0 = 0 := by
        rw [h00, zero_mul] at hdet
        exact (mul_eq_zero.1 hdet.symm).resolve_left h01
      refine ⟨![1, M 1 1 / M 0 1], ![0, -M 0 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, h00, h10] <;> field_simp
  · refine ⟨![1, M 1 0 / M 0 0], ![-M 0 0, -M 0 1], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply] <;> field_simp <;> linear_combination hdet

/-- The Schouten identity for square spinors as vectors: `[q l] q' − [q' l] q = [q q'] l`. -/
lemma schouten_vec_square (l lq lq' : Fin 2 → ℂ) :
    squareBr lq l • lq' - squareBr lq' l • lq = squareBr lq lq' • l := by
  funext a
  fin_cases a <;> simp [squareBr_eq] <;> ring

/-- **The reference spinor of `ε₋` is a gauge choice**: `ε₋(p; q') − ε₋(p; q) = −√2 [q q']/([q p][q' p]) p`. -/
theorem epsMinus_sub_epsMinus (l lt lq lq' : Fin 2 → ℂ) (h1 : squareBr lq l ≠ 0) (h2 : squareBr lq' l ≠ 0) :
    epsMinus l lt lq' - epsMinus l lt lq =
      (-((Real.sqrt 2 : ℝ) : ℂ) * squareBr lq lq' / (squareBr lq l * squareBr lq' l)) • nullMom l lt := by
  have hv : (1 / squareBr lq' l) • lq' - (1 / squareBr lq l) • lq =
      (squareBr lq lq' / (squareBr lq l * squareBr lq' l)) • l := by
    have key := schouten_vec_square l lq lq'
    funext a
    have ha := congrFun key a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢
    field_simp
    linear_combination ha
  have hvm : ∀ (c : ℂ) (x : Fin 2 → ℂ), vecMulVec (c • x) lt = c • vecMulVec x lt := by
    intro c x; ext i j; simp [vecMulVec_apply]; ring
  have hvs : ∀ (x y : Fin 2 → ℂ), vecMulVec (x - y) lt = vecMulVec x lt - vecMulVec y lt := by
    intro x y; ext i j; simp [vecMulVec_apply]; ring
  rw [epsMinus, epsMinus, ← momOf_sub, nullMom_eq_momOf, smul_smul, ← momOf_smul]
  congr 1
  rw [show (((Real.sqrt 2 : ℝ) : ℂ) / squareBr lq' l) • vecMulVec lq' lt -
      (((Real.sqrt 2 : ℝ) : ℂ) / squareBr lq l) • vecMulVec lq lt =
      ((Real.sqrt 2 : ℝ) : ℂ) • vecMulVec ((1 / squareBr lq' l) • lq' - (1 / squareBr lq l) • lq) lt by
    rw [hvs, hvm, hvm, smul_sub, smul_smul, smul_smul]; congr 1 <;> congr 1 <;> ring]
  rw [hv, hvm, smul_smul]
  congr 1
  ring

end Lightlike.SpinorHelicity
