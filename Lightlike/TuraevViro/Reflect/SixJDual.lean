import Lightlike.TuraevViro.Reflect.SixJOrth

/-!
# The recurrence and orthogonality in the dual colour

The q-Racah sum is symmetric under permuting its four `α` arguments. Exchanging `j₂ ↔ j₅` and the
third with the sixth colour permutes them, so the sum `Sj` in the sixth colour (third colour fixed)
is the sum in the third colour of the tetrahedron with `j₂, j₅` exchanged. The recurrence and the
off-diagonal orthogonality of `SixJOrth` therefore hold in the sixth colour as well.
-/


namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- `SR` is symmetric under exchanging `a₁ ↔ a₂` together with `a₃ ↔ a₄`. -/
lemma SR_swap (r : ℕ) (a1 a2 a3 a4 b1 b2 b3 : ℤ) :
    SR r a1 a2 a3 a4 b1 b2 b3 = SR r a2 a1 a4 a3 b1 b2 b3 := by
  unfold SR
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold qRacahTerm
  ring

/-- The sum with third and sixth colour exchanged: `Sj` of the tetrahedron with `j₂, j₅` exchanged. -/
lemma Sj_dual (r j1 j2 j4 j5 q x : ℕ) :
    Sj r j1 j2 j4 j5 q (x : ℤ) = Sj r j1 j5 j4 j2 x (q : ℤ) := by
  unfold Sj
  rw [SR_swap]
  congr 1 <;> ring_nf

/-- **Orthogonality in the sixth colour**: for third colours `x ≠ x'`, the sums over the admissible
sixth colours `q₀, q₀+2, …, q₀+2n` are orthogonal for the weight `jOmega` of the exchanged
tetrahedron. Same hypotheses as `sixj_offdiag`. -/
theorem sixj_offdiag_dual {r : ℕ} (hr : 2 ≤ r) (j1 j2 j4 j5 q0 n : ℕ)
    (hadm : ∀ k ≤ n, qAdm r j1 j5 (q0 + 2 * k) ∧ qAdm r j4 j2 (q0 + 2 * k))
    (hlo : (q0 : ℤ) < (j1 : ℤ) - j5 + 2 ∨ (q0 : ℤ) < (j5 : ℤ) - j1 + 2 ∨
      (q0 : ℤ) < (j4 : ℤ) - j2 + 2 ∨ (q0 : ℤ) < (j2 : ℤ) - j4 + 2)
    (hhi : (j1 : ℤ) + j5 < (q0 + 2 * n : ℕ) + 2 ∨ (j4 : ℤ) + j2 < (q0 + 2 * n : ℕ) + 2 ∨
      (2 * r : ℤ) - 2 ≤ (j1 : ℤ) + j5 + ((q0 + 2 * n : ℕ) + 2) ∨
      (2 * r : ℤ) - 2 ≤ (j4 : ℤ) + j2 + ((q0 + 2 * n : ℕ) + 2))
    {x x' : ℕ} (hq1 : qAdm r j1 j2 x) (hq2 : qAdm r j4 j5 x)
    (hq1' : qAdm r j1 j2 x') (hq2' : qAdm r j4 j5 x') (hxr : x + 1 < r) (hxr' : x' + 1 < r)
    (hne : x ≠ x') :
    ∑ k ∈ range (n + 1), jOmega r j1 j5 j4 j2 (q0 + 2 * k) *
      Sj r j1 j2 j4 j5 (q0 + 2 * k) (x : ℤ) * Sj r j1 j2 j4 j5 (q0 + 2 * k) (x' : ℤ) = 0 := by
  have h := sixj_offdiag hr j1 j5 j4 j2 q0 n hadm hlo hhi hq1 hq2 hq1' hq2' hxr hxr' hne
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Sj_dual r j1 j2 j4 j5 (q0 + 2 * k) x, Sj_dual r j1 j2 j4 j5 (q0 + 2 * k) x']

end Lightlike.TV.Refl
