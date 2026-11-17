import Lightlike.Spacetime.Lorentzian

/-!
# Convexity of the future timelike cone of a Lorentzian form

For a Lorentzian form `B` on a vector space `V` and a timelike vector `X`, the set of vectors `v`
with `B(v, v) < 0` and `B(v, X) < 0` (the future timelike cone determined by `X`) is convex
(`convex_futureTimelike`). In a Lorentz frame, `B(v, w) = -v⁰ w⁰ + Σ vⁱ wⁱ`; two timelike vectors
`u, w` have `B(u, w) < 0` exactly when their time components have the same sign, and `B(u, X) < 0`
says that the time component of `u` has the sign of the time component of `X`.

## References

* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1 (the cone of
  timelike vectors has two convex components).

The comparison with the source at a location is pending.
-/

namespace Lightlike

open Finset

/-- Euclidean Cauchy–Schwarz, strict: if `Σ uᵢ² < a²` and `Σ wᵢ² < b²` then
`|Σ uᵢ wᵢ| < |a b|`. -/
lemma abs_sum_mul_lt {m : ℕ} (u w : Fin m → ℝ) (a b : ℝ) (hu : ∑ i, u i ^ 2 < a ^ 2)
    (hw : ∑ i, w i ^ 2 < b ^ 2) : |∑ i, u i * w i| < |a * b| := by
  have h0u : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h0w : 0 ≤ ∑ i, w i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : (∑ i, u i * w i) ^ 2 ≤ (∑ i, u i ^ 2) * ∑ i, w i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have : (∑ i, u i * w i) ^ 2 < (a * b) ^ 2 := by
    rw [mul_pow]
    nlinarith
  exact sq_lt_sq.1 this

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {n : ℕ} {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- In a frame the form is `-v⁰ w⁰ + Σ vⁱ wⁱ`. -/
lemma IsLorentzianForm.apply_eq_succ {m : ℕ} (e : Module.Basis (Fin (m + 1)) ℝ V)
    (he : ∀ i j, B (e i) (e j) = eta (m + 1) i j) (v w : V) :
    B v w = -(e.repr v 0 * e.repr w 0) + ∑ i : Fin m, e.repr v i.succ * e.repr w i.succ := by
  rw [IsLorentzianForm.apply_eq_sum e he, Fin.sum_univ_succ]
  simp [etaDiag]

/-- **Two timelike vectors of the same future cone have negative product**: for a Lorentzian form,
`B(u, u) < 0`, `B(w, w) < 0`, `B(X, X) < 0`, `B(u, X) < 0`, `B(w, X) < 0` give `B(u, w) < 0`. -/
theorem IsLorentzianForm.neg_of_futureTimelike (h : IsLorentzianForm n B) {u w X : V}
    (hX : B X X < 0) (hu : B u u < 0) (hw : B w w < 0) (hu' : B u X < 0) (hw' : B w X < 0) :
    B u w < 0 := by
  obtain ⟨e, he⟩ := h
  rcases n with _ | m
  · rw [IsLorentzianForm.apply_eq_sum e he] at hu
    simp at hu
  · rw [IsLorentzianForm.apply_eq_succ e he] at hX hu hw hu' hw' ⊢
    set u0 := e.repr u 0
    set w0 := e.repr w 0
    set X0 := e.repr X 0
    have sq : ∀ v : V, B v v < 0 → ∑ i : Fin m, e.repr v i.succ ^ 2 < e.repr v 0 ^ 2 := by
      intro v hv
      rw [IsLorentzianForm.apply_eq_succ e he] at hv
      simpa [sq] using (by linarith : ∑ i : Fin m, e.repr v i.succ * e.repr v i.succ <
        e.repr v 0 * e.repr v 0)
    have hsu := sq u (by rwa [IsLorentzianForm.apply_eq_succ e he])
    have hsw := sq w (by rwa [IsLorentzianForm.apply_eq_succ e he])
    have hsX := sq X (by rwa [IsLorentzianForm.apply_eq_succ e he])
    have pos : ∀ v : V, (∑ i : Fin m, e.repr v i.succ ^ 2 < e.repr v 0 ^ 2) →
        -(e.repr v 0 * X0) + ∑ i : Fin m, e.repr v i.succ * e.repr X i.succ < 0 →
        0 < e.repr v 0 * X0 := by
      intro v hv hvX
      have := abs_sum_mul_lt (fun i : Fin m => e.repr v i.succ) (fun i => e.repr X i.succ)
        (e.repr v 0) X0 hv hsX
      by_contra hneg
      push Not at hneg
      rw [abs_of_nonpos hneg] at this
      have := (abs_lt.1 this).1
      linarith
    have p1 := pos u hsu hu'
    have p2 := pos w hsw hw'
    have hx0 : 0 < X0 ^ 2 := by
      have : 0 ≤ ∑ i : Fin m, e.repr X i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      linarith
    have p3 : 0 < u0 * w0 := by
      have : 0 < (u0 * X0) * (w0 * X0) := mul_pos p1 p2
      have e2 : (u0 * X0) * (w0 * X0) = (u0 * w0) * X0 ^ 2 := by ring
      rw [e2] at this
      by_contra hc
      push Not at hc
      have := mul_nonpos_of_nonpos_of_nonneg hc hx0.le
      linarith
    have := abs_sum_mul_lt (fun i : Fin m => e.repr u i.succ) (fun i => e.repr w i.succ) u0 w0 hsu hsw
    rw [abs_of_pos p3] at this
    have := (abs_lt.1 this).2
    linarith

/-- The future timelike cone `{v | B v v < 0 ∧ B v X < 0}` of a Lorentzian form is convex. -/
theorem IsLorentzianForm.convex_futureTimelike (h : IsLorentzianForm n B) {X : V} (hX : B X X < 0) :
    Convex ℝ {v : V | B v v < 0 ∧ B v X < 0} := by
  intro u hu w hw a b ha hb hab
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hw1, hw2⟩ := hw
  have huw := h.neg_of_futureTimelike hX hu1 hw1 hu2 hw2
  have hsymm : B w u = B u w := h.symm w u
  refine ⟨?_, ?_⟩
  · simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, hsymm]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this
      simpa using hw1
    · have t1 := mul_neg_of_pos_of_neg (mul_pos ha' ha') hu1
      have t2 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hb) huw.le
      have t3 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb hb) hw1.le
      nlinarith
  · simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this
      simpa using hw2
    · nlinarith [mul_nonneg ha hb]

end Lightlike
