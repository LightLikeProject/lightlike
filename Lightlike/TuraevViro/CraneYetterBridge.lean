import Mathlib
import Lightlike.TuraevViro.CraneYetter
import Lightlike.TuraevViro.QSixJ

/-!
# The Kauffman–Lins nets of the Crane–Yetter state sum and the quantum 6j symbol

The Crane–Yetter vertex and tetrahedron weights (`CraneYetter.lean`) are written with the Kauffman–Lins evaluations
`tlTet` and `tlTheta`; the q-orthogonality and the q-Biedenharn–Elliott identity of the library are stated for the
quantum 6j symbol `qSixJ` (square-root normalised). `qSixJ_eq_tlTet` relates them:

`{A D E; C B F}_q = Tet[A B E; C D F] / √|θ(A, D, E) θ(B, C, E) θ(A, B, F) θ(C, D, F)|`

at `q = e^{iπ/r}`, for all colours (both sides vanish off the admissible ones). The two sides have the same Racah sum
(`qRacahSum_eq_tet`); the twelve q-factorials of the prefactor of `tlTet` are those of the four triads
(`tet_pre_eq`), and `|θ|` is `[s+1]! [s-x]! [s-y]! [s-z]! / ([x]! [y]! [z]!)` (`tlTheta_abs`). The product of the four
theta nets takes both signs, so the absolute value is needed.
-/

open Finset Lightlike.Pentagon

namespace Lightlike.TV

/-- The square-root identity behind `qSixJ = Tet / √|θθθθ|`. -/
lemma sqrt_bridge {X₁ X₂ X₃ X₄ F₁ F₂ F₃ F₄ Q : ℝ} (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₃ : 0 < X₃) (hX₄ : 0 < X₄)
    (hF₁ : 0 < F₁) (hF₂ : 0 < F₂) (hF₃ : 0 < F₃) (hF₄ : 0 < F₄) (hQ : 0 < Q) :
    √(X₁ / F₁) * √(X₂ / F₂) * √(X₃ / F₃) * √(X₄ / F₄) =
      X₁ * X₂ * X₃ * X₄ / Q / √(F₁ * X₁ * (F₂ * X₂) * (F₃ * X₃) * (F₄ * X₄) / Q ^ 2) := by
  have hR : 0 < √(F₁ * X₁ * (F₂ * X₂) * (F₃ * X₃) * (F₄ * X₄) / Q ^ 2) := Real.sqrt_pos.mpr (by positivity)
  refine (sq_eq_sq₀ (by positivity) (by positivity)).mp ?_
  rw [div_pow, Real.sq_sqrt (by positivity), mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- A Racah sum over a `range` is the sum over the box `max aᵢ ≤ z ≤ min bⱼ` (generic in the face and pair sums). -/
lemma racah_box (r N a₁ a₂ a₃ a₄ b₁ b₂ b₃ : ℕ) (hN : min (min b₁ b₂) b₃ ≤ N) :
    ∑ z ∈ range (N + 1), qRacahTerm r a₁ a₃ a₄ a₂ b₃ b₁ b₂ z =
      ∑ z ∈ Icc (max (max a₁ a₂) (max a₃ a₄)) (min (min b₁ b₂) b₃),
        (-1) ^ z * qfact r (z + 1) /
          ((∏ i : Fin 4, qfact r (z - ![a₁, a₂, a₃, a₄] i)) * ∏ j : Fin 3, qfact r (![b₁, b₂, b₃] j - z)) := by
  symm
  rw [← sum_subset (s₁ := Icc (max (max a₁ a₂) (max a₃ a₄)) (min (min b₁ b₂) b₃)) (s₂ := range (N + 1))
      (fun z hz => by
        simp only [mem_Icc, max_le_iff, le_min_iff] at hz
        exact mem_range.mpr (by have := min_le_left (min b₁ b₂) b₃; have := min_le_left b₁ b₂; omega))
      (fun z _ hz => ?_)]
  swap
  · simp only [mem_Icc, max_le_iff, le_min_iff, not_and_or, not_le] at hz
    unfold qRacahTerm invQFact
    rcases hz with ((h | h) | (h | h)) | ((h | h) | h)
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (z : ℤ) - (a₁ : ℤ) by omega)]; ring
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (z : ℤ) - (a₂ : ℤ) by omega)]; ring
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (z : ℤ) - (a₃ : ℤ) by omega)]; ring
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (z : ℤ) - (a₄ : ℤ) by omega)]; ring
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (b₁ : ℤ) - (z : ℤ) by omega)]; ring
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (b₂ : ℤ) - (z : ℤ) by omega)]; ring
    · rw [if_neg (show ¬ (0 : ℤ) ≤ (b₃ : ℤ) - (z : ℤ) by omega)]; ring
  refine sum_congr rfl fun z hz => ?_
  simp only [mem_Icc, max_le_iff, le_min_iff] at hz
  unfold qRacahTerm invQFact
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
    if_pos (by omega), if_pos (by omega),
    show ((z : ℤ) - (a₁ : ℤ)).toNat = z - a₁ by omega, show ((z : ℤ) - (a₂ : ℤ)).toNat = z - a₂ by omega,
    show ((z : ℤ) - (a₃ : ℤ)).toNat = z - a₃ by omega, show ((z : ℤ) - (a₄ : ℤ)).toNat = z - a₄ by omega,
    show ((b₁ : ℤ) - (z : ℤ)).toNat = b₁ - z by omega, show ((b₂ : ℤ) - (z : ℤ)).toNat = b₂ - z by omega,
    show ((b₃ : ℤ) - (z : ℤ)).toNat = b₃ - z by omega]
  field_simp

/-- **The Racah sums agree**: the sum of `qSixJ` (over a `range`, with reciprocal q-factorials of integers) is the sum of
`tlTet` (over the box `max aᵢ ≤ z ≤ min bⱼ`). -/
lemma qRacahSum_eq_tet (r A B E C D F : ℕ) :
    qRacahSum r A D E C B F =
      ∑ z ∈ Icc (max (max ((A + D + E) / 2) ((B + C + E) / 2)) (max ((A + B + F) / 2) ((C + D + F) / 2)))
          (min (min ((B + D + E + F) / 2) ((A + C + E + F) / 2)) ((A + B + C + D) / 2)),
        (-1) ^ z * qfact r (z + 1) /
          ((∏ i : Fin 4, qfact r (z - ![(A + D + E) / 2, (B + C + E) / 2, (A + B + F) / 2, (C + D + F) / 2] i)) *
            ∏ j : Fin 3, qfact r (![(B + D + E + F) / 2, (A + C + E + F) / 2, (A + B + C + D) / 2] j - z)) := by
  unfold qRacahSum
  rw [show C + B + E = B + C + E by ring, show A + D + C + B = A + B + C + D by ring,
    show D + E + B + F = B + D + E + F by ring, show E + A + F + C = A + C + E + F by ring]
  exact racah_box r _ _ _ _ _ _ _ _ (by omega)

/-- `|θ(x, y, z)| = [s+1]! [s-x]! [s-y]! [s-z]! / ([x]! [y]! [z]!)`, `s = (x+y+z)/2`, on an admissible triad. -/
lemma tlTheta_abs {r x y z : ℕ} (hr : 2 ≤ r) (h : qAdm r x y z) :
    |tlTheta r x y z| = qfact r ((x + y + z) / 2 + 1) *
      (qfact r ((x + y + z) / 2 - x) * qfact r ((x + y + z) / 2 - y) * qfact r ((x + y + z) / 2 - z)) /
        (qfact r x * qfact r y * qfact r z) := by
  have h' := h
  unfold qAdm Tri at h'
  unfold tlTheta
  rw [if_pos h, show (x + y - z) / 2 = (x + y + z) / 2 - z by omega, show (y + z - x) / 2 = (x + y + z) / 2 - x by omega,
    show (x + z - y) / 2 = (x + y + z) / 2 - y by omega]
  have p : ∀ n, n < r → 0 < qfact r n := fun n hn => qfact_pos hr hn
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (p _ (by omega)), abs_of_pos (p _ (by omega)), abs_of_pos (p _ (by omega)), abs_of_pos (p _ (by omega)),
    abs_of_pos (mul_pos (mul_pos (p _ (by omega)) (p _ (by omega))) (p _ (by omega)))]
  ring

/-- The twelve q-factorials of the prefactor of `tlTet` are the twelve of the four triads. -/
lemma tet_pre_eq {r A B E C D F : ℕ} (h1 : qAdm r A D E) (h2 : qAdm r B C E) (h3 : qAdm r A B F) (h4 : qAdm r C D F) :
    (∏ i : Fin 4, ∏ j : Fin 3, qfact r (![(B + D + E + F) / 2, (A + C + E + F) / 2, (A + B + C + D) / 2] j -
        ![(A + D + E) / 2, (B + C + E) / 2, (A + B + F) / 2, (C + D + F) / 2] i)) =
      (qfact r ((A + D + E) / 2 - A) * qfact r ((A + D + E) / 2 - D) * qfact r ((A + D + E) / 2 - E)) *
      (qfact r ((A + B + F) / 2 - A) * qfact r ((A + B + F) / 2 - B) * qfact r ((A + B + F) / 2 - F)) *
      (qfact r ((C + D + F) / 2 - C) * qfact r ((C + D + F) / 2 - D) * qfact r ((C + D + F) / 2 - F)) *
      (qfact r ((B + C + E) / 2 - B) * qfact r ((B + C + E) / 2 - C) * qfact r ((B + C + E) / 2 - E)) := by
  unfold qAdm Tri at h1 h2 h3 h4
  obtain ⟨s₁, hs₁⟩ : ∃ s, A + D + E = 2 * s := ⟨(A + D + E) / 2, by omega⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s, B + C + E = 2 * s := ⟨(B + C + E) / 2, by omega⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s, A + B + F = 2 * s := ⟨(A + B + F) / 2, by omega⟩
  obtain ⟨s₄, hs₄⟩ : ∃ s, C + D + F = 2 * s := ⟨(C + D + F) / 2, by omega⟩
  have q₁ : (A + D + E) / 2 = s₁ := by omega
  have q₂ : (B + C + E) / 2 = s₂ := by omega
  have q₃ : (A + B + F) / 2 = s₃ := by omega
  have q₄ : (C + D + F) / 2 = s₄ := by omega
  have b₁ : (B + D + E + F) / 2 = s₁ + s₃ - A := by omega
  have b₂ : (A + C + E + F) / 2 = s₁ + s₄ - D := by omega
  have b₃ : (A + B + C + D) / 2 = s₁ + s₂ - E := by omega
  simp only [Fin.prod_univ_four, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, q₁, q₂, q₃, q₄, b₁, b₂, b₃]
  have l₁ : A ≤ s₁ ∧ D ≤ s₁ ∧ E ≤ s₁ := by omega
  have l₂ : B ≤ s₂ ∧ C ≤ s₂ ∧ E ≤ s₂ := by omega
  have l₃ : A ≤ s₃ ∧ B ≤ s₃ ∧ F ≤ s₃ := by omega
  have l₄ : C ≤ s₄ ∧ D ≤ s₄ ∧ F ≤ s₄ := by omega
  clear h1 h2 h3 h4 q₁ q₂ q₃ q₄ b₁ b₂ b₃
  have e0 : s₁ + s₃ - A - s₁ = s₃ - A := by omega
  have e1 : s₁ + s₄ - D - s₁ = s₄ - D := by omega
  have e2 : s₁ + s₂ - E - s₁ = s₂ - E := by omega
  have e3 : s₁ + s₃ - A - s₂ = s₄ - C := by omega
  have e4 : s₁ + s₄ - D - s₂ = s₃ - B := by omega
  have e5 : s₁ + s₂ - E - s₂ = s₁ - E := by omega
  have e6 : s₁ + s₃ - A - s₃ = s₁ - A := by omega
  have e7 : s₁ + s₄ - D - s₃ = s₂ - B := by omega
  have e8 : s₁ + s₂ - E - s₃ = s₄ - F := by omega
  have e9 : s₁ + s₃ - A - s₄ = s₂ - C := by omega
  have e10 : s₁ + s₄ - D - s₄ = s₁ - D := by omega
  have e11 : s₁ + s₂ - E - s₄ = s₃ - F := by omega
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  ring

/-- The product of the four `|θ|` over the square of the six edge factorials. -/
lemma theta_prod_eq {X₁ X₂ X₃ X₄ F₁ F₂ F₃ F₄ a b c d e f : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) :
    F₁ * X₁ / (a * d * e) * (F₄ * X₄ / (b * c * e)) * (F₂ * X₂ / (a * b * f)) * (F₃ * X₃ / (c * d * f)) =
      F₁ * X₁ * (F₂ * X₂) * (F₃ * X₃) * (F₄ * X₄) / (a * b * c * d * e * f) ^ 2 := by
  field_simp

/-- **The quantum 6j symbol from the Kauffman–Lins nets**: `{A D E; C B F}_q = Tet[A B E; C D F] / √|θθθθ|`, with the
four theta nets of the triads `(A, D, E)`, `(B, C, E)`, `(A, B, F)`, `(C, D, F)` of the tetrahedron (both sides vanish
off the admissible colourings). The product of the four theta nets takes both signs. -/
theorem qSixJ_eq_tlTet {r : ℕ} (hr : 2 ≤ r) (A B E C D F : ℕ) :
    qSixJ r A D E C B F =
      tlTet r A B E C D F / √|tlTheta r A D E * tlTheta r B C E * tlTheta r A B F * tlTheta r C D F| := by
  by_cases h : qAdm r A D E ∧ qAdm r B C E ∧ qAdm r A B F ∧ qAdm r C D F
  swap
  · have hS : ¬ (qAdm r A D E ∧ qAdm r A B F ∧ qAdm r C D F ∧ qAdm r C B E) := fun ⟨a, b, c, d⟩ =>
      h ⟨a, qAdm_swap12 d, b, c⟩
    unfold qSixJ tlTet
    rw [if_neg hS, if_neg h, zero_div]
  obtain ⟨h1, h2, h3, h4⟩ := h
  have g1 := h1; have g2 := h2; have g3 := h3; have g4 := h4
  unfold qAdm Tri at g1 g2 g3 g4
  have p : ∀ n, n < r → 0 < qfact r n := fun n hn => qfact_pos hr hn
  unfold qSixJ tlTet
  rw [if_pos ⟨h1, h3, h4, qAdm_swap12 h2⟩, if_pos ⟨h1, h2, h3, h4⟩, qRacahSum_eq_tet, tet_pre_eq h1 h2 h3 h4,
    abs_mul, abs_mul, abs_mul, tlTheta_abs hr h1, tlTheta_abs hr h2, tlTheta_abs hr h3, tlTheta_abs hr h4]
  unfold qDelta
  rw [show C + B + E = B + C + E by ring]
  rw [mul_comm (qfact r ((B + C + E) / 2 - C)) (qfact r ((B + C + E) / 2 - B))]
  have hX₁ : 0 < qfact r ((A + D + E) / 2 - A) * qfact r ((A + D + E) / 2 - D) * qfact r ((A + D + E) / 2 - E) := mul_pos (mul_pos (p _ (by omega)) (p _ (by omega))) (p _ (by omega))
  have hX₂ : 0 < qfact r ((A + B + F) / 2 - A) * qfact r ((A + B + F) / 2 - B) * qfact r ((A + B + F) / 2 - F) := mul_pos (mul_pos (p _ (by omega)) (p _ (by omega))) (p _ (by omega))
  have hX₃ : 0 < qfact r ((C + D + F) / 2 - C) * qfact r ((C + D + F) / 2 - D) * qfact r ((C + D + F) / 2 - F) := mul_pos (mul_pos (p _ (by omega)) (p _ (by omega))) (p _ (by omega))
  have hX₄ : 0 < qfact r ((B + C + E) / 2 - B) * qfact r ((B + C + E) / 2 - C) * qfact r ((B + C + E) / 2 - E) := mul_pos (mul_pos (p _ (by omega)) (p _ (by omega))) (p _ (by omega))
  have hF₁ : 0 < qfact r ((A + D + E) / 2 + 1) := p _ (by omega)
  have hF₂ : 0 < qfact r ((A + B + F) / 2 + 1) := p _ (by omega)
  have hF₃ : 0 < qfact r ((C + D + F) / 2 + 1) := p _ (by omega)
  have hF₄ : 0 < qfact r ((B + C + E) / 2 + 1) := p _ (by omega)
  have hA := p A (by omega); have hB := p B (by omega); have hC := p C (by omega)
  have hD := p D (by omega); have hE := p E (by omega); have hFF := p F (by omega)
  have key := sqrt_bridge hX₁ hX₂ hX₃ hX₄ hF₁ hF₂ hF₃ hF₄ (Q := qfact r A * qfact r B * qfact r C * qfact r D * qfact r E * qfact r F) (by positivity)
  rw [theta_prod_eq hA.ne' hB.ne' hC.ne' hD.ne' hE.ne' hFF.ne', key]
  ring

end Lightlike.TV
