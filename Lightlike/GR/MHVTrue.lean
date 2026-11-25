import Lightlike.GR.ColourOrderedFeynman
import Lightlike.GR.ThreePointAmplitude
import Lightlike.GR.FeynmanWard

/-!
# The true three-gluon MHV amplitude from the Feynman rules

The colour-ordered amplitude `bgAmplitude` evaluated on spinor kinematics with the polarization vectors
`epsMinus`, `epsPlus` of Elvang-Huang (2.49)-(2.50). For three gluons `1⁻ 2⁻ 3⁺` with a common reference square
spinor `|q]` for the negative legs and `⟨q'|` for the positive leg, momentum conservation gives
`A₃ = ⟨12⟩³ / (⟨23⟩⟨31⟩)` (Elvang-Huang (2.77)), the base case of the BCFW recursion for the true amplitudes.
-/

open Matrix Complex

noncomputable section

namespace Lightlike.SpinorHelicity

/-- Auxiliary statement `mdot_momOf_smul_vec` for the true three-gluon amplitude. -/
lemma mdot_momOf_smul_vec (c d : ℂ) (a b a' b' : Fin 2 → ℂ) :
    mdot (momOf (c • vecMulVec a b)) (momOf (d • vecMulVec a' b')) =
      c * d * ((1 / 2) * angleBr b b' * squareBr a a') := by
  rw [momOf_smul, momOf_smul, mdot_smul_smul, mdot_momOf_vecMulVec]

/-- Auxiliary statement `nullMom_eq_momOf_smul` for the true three-gluon amplitude. -/
lemma nullMom_eq_momOf_smul (l lt : Fin 2 → ℂ) : nullMom l lt = momOf ((-1 : ℂ) • vecMulVec l lt) := by
  rw [nullMom, neg_one_smul]

/-- The algebra of the three-point amplitude. -/
lemma three_alg (s a0 a1 x0 x1 x2 y b01 b12 b20 : ℂ) (r2 : s * s = 2) (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0)
    (hy : y ≠ 0) (h12 : b12 ≠ 0) (h20 : b20 ≠ 0)
    (c1 : a0 * x0 + a1 * x1 = y * x2) (c2 : b12 * x2 = b01 * x0) (c3 : b20 * x2 = b01 * x1) :
    -s * (s / x1 * (s / y) * (1 / 2 * a1 * x2) * (s / x0 * -1 * (1 / 2 * b01 * x1)) +
        s / y * (s / x0) * (1 / 2 * -a0 * -x2) * -(s / x1 * -1 * (1 / 2 * -b01 * x0))) =
      b01 ^ 3 / (b12 * b20) := by
  have s1 : -s * (s / x1 * (s / y) * (1 / 2 * a1 * x2) * (s / x0 * -1 * (1 / 2 * b01 * x1)) +
        s / y * (s / x0) * (1 / 2 * -a0 * -x2) * -(s / x1 * -1 * (1 / 2 * -b01 * x0))) =
        b01 * x2 ^ 2 / (x0 * x1) := by
    field_simp
    linear_combination (b01 * x2 * (s * s) / 2 + 3 * b01 * x2) * c1 +
      (x2 * b01 * (a1 * x1 + a0 * x0) * (s * s + 3 / 2) + x2 ^ 2 * b01 * y / 2) * r2
  rw [s1]
  field_simp
  linear_combination (b01 * b20 * x2) * c2 + (b01 * b01 * x0) * c3

/-- Auxiliary statement `bgAmplitude_three_mmp` for the true three-gluon amplitude. -/
theorem bgAmplitude_three_mmp (l lt : Fin 3 → Fin 2 → ℂ) (h : Conserved3 l lt) (qs qa : Fin 2 → ℂ)
    (p e : ℕ → Fin 4 → ℂ) (hp0 : p 0 = nullMom (l 0) (lt 0)) (hp1 : p 1 = nullMom (l 1) (lt 1))
    (he0 : e 0 = epsMinus (l 0) (lt 0) qs) (he1 : e 1 = epsMinus (l 1) (lt 1) qs)
    (he2 : e 2 = epsPlus (l 2) (lt 2) qa)
    (hq0 : squareBr qs (l 0) ≠ 0) (hq1 : squareBr qs (l 1) ≠ 0) (hqa : angleBr qa (lt 2) ≠ 0)
    (a12 : angleBr (lt 1) (lt 2) ≠ 0) (a20 : angleBr (lt 2) (lt 0) ≠ 0) :
    bgAmplitude 0 p e = angleBr (lt 0) (lt 1) ^ 3 / (angleBr (lt 1) (lt 2) * angleBr (lt 2) (lt 0)) := by
  rw [bgAmplitude_three, he0, he1, he2, hp0, hp1]
  simp only [epsMinus, epsPlus, nullMom_eq_momOf_smul, mdot_neg_right, mdot_add_right, mdot_momOf_smul_vec]
  have hs : ∀ u v : Fin 2 → ℂ, squareBr u v = -squareBr v u := fun u v => squareBr_antisymm u v
  have ha : ∀ u v : Fin 2 → ℂ, angleBr u v = -angleBr v u := fun u v => angleBr_antisymm u v
  have z1 : squareBr qs qs = 0 := by rw [squareBr_eq]; ring
  have z2 : angleBr (lt 1) (lt 1) = 0 := by rw [angleBr_eq]; ring
  have r2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have := sqrt_two_sq_complex; rw [sq] at this; exact this
  have c1 := contract_conserved3 h qa qs
  have c2 := contract_conserved3 h (lt 1) qs
  have c3 := contract_conserved3 h (lt 0) qs
  have z3 : angleBr (lt 0) (lt 0) = 0 := by rw [angleBr_eq]; ring
  rw [hs (l 0) qs, hs (l 1) qs, hs (l 2) qs, ha qa (lt 0), ha qa (lt 1)] at c1
  rw [hs (l 0) qs, hs (l 1) qs, hs (l 2) qs, ha (lt 1) (lt 0), z2] at c2
  rw [hs (l 0) qs, hs (l 1) qs, hs (l 2) qs, ha (lt 0) (lt 2), z3] at c3
  rw [hs (l 2) qs, ha qa (lt 0), ha (lt 1) (lt 0), z1, z2]
  have key := three_alg (((Real.sqrt 2 : ℝ)) : ℂ) (angleBr (lt 0) qa) (angleBr (lt 1) qa) (squareBr qs (l 0))
    (squareBr qs (l 1)) (squareBr qs (l 2)) (angleBr qa (lt 2)) (angleBr (lt 0) (lt 1)) (angleBr (lt 1) (lt 2))
    (angleBr (lt 2) (lt 0)) r2 hq0 hq1 hqa a12 a20 (by linear_combination c1) (by linear_combination (-1 : ℂ) * c2) (by linear_combination c3)
  rw [← key]
  ring

/-- Auxiliary statement `bgAmplitude_three_mpm` for the true three-gluon amplitude. -/
theorem bgAmplitude_three_mpm (l lt : Fin 3 → Fin 2 → ℂ) (h : Conserved3 l lt) (qs qa : Fin 2 → ℂ)
    (p e : ℕ → Fin 4 → ℂ) (hp0 : p 0 = nullMom (l 0) (lt 0)) (hp1 : p 1 = nullMom (l 1) (lt 1))
    (hp2 : p 2 = nullMom (l 2) (lt 2))
    (he0 : e 0 = epsMinus (l 0) (lt 0) qs) (he1 : e 1 = epsPlus (l 1) (lt 1) qa)
    (he2 : e 2 = epsMinus (l 2) (lt 2) qs)
    (hq2 : squareBr qs (l 2) ≠ 0) (hq0 : squareBr qs (l 0) ≠ 0) (hqa : angleBr qa (lt 1) ≠ 0)
    (a01 : angleBr (lt 0) (lt 1) ≠ 0) (a12 : angleBr (lt 1) (lt 2) ≠ 0) :
    bgAmplitude 0 p e = angleBr (lt 2) (lt 0) ^ 3 / (angleBr (lt 0) (lt 1) * angleBr (lt 1) (lt 2)) := by
  have hsum := (conserved3_iff l lt).1 h
  have hcons : momRange p 0 2 = 0 := by
    have : momRange p 0 2 = p 0 + p 1 + p 2 := by
      simp [momRange, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, add_assoc]
    rw [this, hp0, hp1, hp2]; exact hsum
  have hprop : ∀ d, 1 ≤ d → d ≤ 0 → mdot (momRange p 0 d) (momRange p 0 d) ≠ 0 := fun d h1 h2 => by omega
  have hcons1 : momRange (rotLabels p 2) 0 2 = 0 := by
    have : momRange (rotLabels p 2) 0 2 = p 1 + p 2 + p 0 := by
      simp [momRange, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, rotLabels, add_assoc]
    rw [this]; rw [← hcons]; simp [momRange, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, add_assoc]; abel
  have r1 := bgAmplitude_rotLabels 0 p e hcons (fun d h1 h2 => by omega)
  have r2 := bgAmplitude_rotLabels 0 (rotLabels p (0 + 2)) (rotLabels e (0 + 2)) hcons1 (fun d h1 h2 => by omega)
  rw [← r1, ← r2]
  have key := bgAmplitude_three_mmp (fun k => ![l 2, l 0, l 1] k) (fun k => ![lt 2, lt 0, lt 1] k) ?_ qs qa
    (rotLabels (rotLabels p 2) 2) (rotLabels (rotLabels e 2) 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · intro a b
    have := h a b
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination this
  · simpa [rotLabels] using hp2
  · simpa [rotLabels] using hp0
  · simpa [rotLabels] using he2
  · simpa [rotLabels] using he0
  · simpa [rotLabels] using he1
  · simpa using hq2
  · simpa using hq0
  · simpa using hqa
  · simpa using a01
  · simpa using a12

end Lightlike.SpinorHelicity
