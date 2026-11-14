import Lightlike.Asymptotics.Saddle

/-!
# The phase of Racah's sum on the closed upper half-plane

The phase `phase l` of Racah's sum (`Saddle.lean`) is built from principal logarithms of `x`,
`x − Aᵢ` and `Bₖ − x`, where `Aᵢ` are the four face sums and `Bₖ` the three quadrilateral sums of
the edge lengths. On the open upper half-plane `Bₖ − z` lies in the lower half-plane, and
`log (Bₖ − z) = log (z − Bₖ) − iπ`. Substituting this gives the *continued phase*

  `phaseC A B z = g z − Σᵢ g (z − Aᵢ) + Σₖ g (z − Bₖ) − 2πi z + iπ Σₖ Bₖ`,  `g w = w log w`,

which equals `phase l` on the open upper half-plane (`phase_eq_phaseC`) but, unlike `phase l`,
extends continuously to the real axis from above. Its imaginary part on the real axis is the
piecewise-linear function `bdry A B` (`im_phaseC_ofReal`).

This is the first step of the steepest-descent proof of `RacahSumAsymptotics`. The descent paths of
`phaseC` keep `Im phaseC` constant and end on the real axis; where they can end is decided by the
**real-axis lemma** proven here. With `A_max = maxᵢ Aᵢ < B_min = minₖ Bₖ` and all `Aᵢ > 0`:

* `bdry = π u` on `[A_max, B_min]` (`bdry_mid`);
* `bdry ≥ π A_max` on `(−∞, A_max]`, strictly decreasing wherever it exceeds `π A_max`
  (`bdry_ge_left`, `bdry_strictAnti_left`);
* `bdry ≤ π B_min` on `[B_min, ∞)`, strictly decreasing wherever it is below `π B_min`
  (`bdry_le_right`, `bdry_strictAnti_right`).

So every level above `π A_max` is taken at most once on `(−∞, A_max]`, and every level below
`π B_min` at most once on `[B_min, ∞)` (`bdry_injOn_left`, `bdry_injOn_right`).

The parameters are kept general (`A : Fin 4 → ℝ`, `B : Fin 3 → ℝ`); for a tetrahedron they are
`faceSum l` and `quadSum l`, and `IsEuclid l` supplies the hypotheses `0 < Aᵢ < Bₖ`.
-/

open Complex
open scoped Real

namespace Lightlike.Asymptotics

/-- `g w = w log w` with the principal logarithm (so `g 0 = 0`). -/
noncomputable def xlog (w : ℂ) : ℂ := w * log w

/-- The continued phase `g z − Σᵢ g (z − Aᵢ) + Σₖ g (z − Bₖ) − 2πi z + iπ Σₖ Bₖ`, with
`g w = w log w`. It equals Racah's phase on the open upper half-plane (`phase_eq_phaseC`). -/
noncomputable def phaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  xlog z - ∑ i, xlog (z - A i) + ∑ k, xlog (z - B k) - 2 * π * I * z + π * I * ∑ k, (B k : ℂ)

/-- Crossing the cut: `log (−w) = log w − iπ` for `w` in the open upper half-plane. -/
lemma log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) : log (-w) = log w - π * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos hw]

/-- On the open upper half-plane the continued phase is Racah's phase. -/
theorem phase_eq_phaseC (l : Fin 6 → ℝ) {z : ℂ} (hz : 0 < z.im) :
    phase l z = phaseC (faceSum l) (quadSum l) z := by
  have hB : ∀ k, log ((quadSum l k : ℂ) - z) = log (z - quadSum l k) - π * I := fun k => by
    rw [show (quadSum l k : ℂ) - z = -(z - quadSum l k) by ring]
    exact log_neg_of_im_pos (by simpa using hz)
  simp only [phase, phaseC, xlog, hB, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-! ## Boundary values on the real axis -/

/-- `Im g u = π min(u, 0)` for real `u` (the principal argument of a negative real is `π`). -/
lemma im_xlog_ofReal (u : ℝ) : (xlog u).im = π * min u 0 := by
  rcases le_or_gt 0 u with h | h
  · rw [min_eq_right h, mul_zero, xlog, ← ofReal_log h, ← ofReal_mul, ofReal_im]
  · rw [min_eq_left h.le, xlog, mul_im, ofReal_re, ofReal_im, log_im, arg_ofReal_of_neg h]
    ring

/-- The boundary values of `Im phaseC` on the real axis:
`π (min(u,0) − Σᵢ min(u − Aᵢ, 0) + Σₖ min(u − Bₖ, 0) − 2u + Σₖ Bₖ)`. -/
noncomputable def bdry (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (u : ℝ) : ℝ :=
  π * (min u 0 - ∑ i, min (u - A i) 0 + ∑ k, min (u - B k) 0 - 2 * u + ∑ k, B k)

/-- On the real axis, `Im phaseC = bdry`. -/
theorem im_phaseC_ofReal (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (u : ℝ) :
    (phaseC A B u).im = bdry A B u := by
  have h1 : ∀ c : ℝ, (xlog ((u : ℂ) - c)).im = π * min (u - c) 0 := fun c => by
    rw [← ofReal_sub]; exact im_xlog_ofReal _
  simp only [phaseC, bdry, Fin.sum_univ_four, Fin.sum_univ_three, sub_im, add_im, h1,
    im_xlog_ofReal]
  simp
  ring

/-! ## The real-axis lemma -/

section RealAxis

variable {A : Fin 4 → ℝ} {B : Fin 3 → ℝ}

lemma min_sub_zero_eq (x y : ℝ) : min (x - y) 0 = -max (y - x) 0 := by
  simp only [min_def, max_def]; split_ifs <;> linarith

/-- `bdry` left of every `Bₖ`: `π (min(u,0) + u + Σᵢ max(Aᵢ − u, 0))`. -/
lemma bdry_of_le {u : ℝ} (hu : ∀ k, u ≤ B k) :
    bdry A B u = π * (min u 0 + u + ∑ i, max (A i - u) 0) := by
  have h2 : ∀ k, min (u - B k) 0 = u - B k := fun k => min_eq_left (by linarith [hu k])
  unfold bdry
  simp only [h2]
  simp only [min_sub_zero_eq u, Finset.sum_neg_distrib, Fin.sum_univ_three]
  ring

/-- `bdry` right of every `Aᵢ` (and of `0`): `π (Σₖ Bₖ − 2u − Σₖ max(Bₖ − u, 0))`. -/
lemma bdry_of_ge {u : ℝ} (hu : ∀ i, A i ≤ u) (hu0 : 0 ≤ u) :
    bdry A B u = π * (∑ k, B k - 2 * u - ∑ k, max (B k - u) 0) := by
  have h1 : ∀ i, min (u - A i) 0 = 0 := fun i => min_eq_right (by linarith [hu i])
  unfold bdry
  simp only [h1, min_eq_right hu0]
  simp only [min_sub_zero_eq u, Finset.sum_const_zero, Finset.sum_neg_distrib]
  ring

variable (hA : ∀ i, 0 < A i) (hAB : ∀ i k, A i < B k)
include hA hAB

omit hAB in
/-- **Middle piece.** `bdry u = π u` for `A_max ≤ u ≤ B_min`. -/
theorem bdry_mid {i₀ : Fin 4} {k₀ : Fin 3} (hi₀ : ∀ i, A i ≤ A i₀) (hk₀ : ∀ k, B k₀ ≤ B k)
    {u : ℝ} (h1 : A i₀ ≤ u) (h2 : u ≤ B k₀) : bdry A B u = π * u := by
  rw [bdry_of_ge (fun i => (hi₀ i).trans h1) ((hA i₀).le.trans h1)]
  have h3 : ∀ k, max (B k - u) 0 = B k - u := fun k => max_eq_left (by linarith [hk₀ k])
  simp only [h3, Fin.sum_univ_three]
  ring

/-- **Left piece, lower bound.** `π Aᵢ₀ ≤ bdry u` for `u ≤ Aᵢ₀`, for any face sum `Aᵢ₀`; it is
used with `Aᵢ₀ = A_max`. -/
theorem bdry_ge_left {i₀ : Fin 4} {u : ℝ} (hu : u ≤ A i₀) :
    π * A i₀ ≤ bdry A B u := by
  rw [bdry_of_le (fun k => hu.trans (hAB i₀ k).le)]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  have hs : max (A i₀ - u) 0 ≤ ∑ i, max (A i - u) 0 :=
    Finset.single_le_sum (f := fun i => max (A i - u) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_univ i₀)
  rcases le_or_gt 0 u with h0 | h0
  · rw [min_eq_right h0]
    linarith [le_max_left (A i₀ - u) 0]
  · rw [min_eq_left h0.le]
    have he : ∀ i, max (A i - u) 0 = A i - u := fun i => max_eq_left (by linarith [hA i])
    have hA' : A i₀ ≤ ∑ i, A i :=
      Finset.single_le_sum (f := A) (fun i _ => (hA i).le) (Finset.mem_univ i₀)
    simp only [he, Fin.sum_univ_four] at hA' ⊢
    linarith

/-- **Left piece, strict decrease.** On `(−∞, Aᵢ₀]`, `bdry` is strictly decreasing at every
point where it exceeds `π Aᵢ₀` (any face sum `Aᵢ₀`; used with `A_max`). -/
theorem bdry_strictAnti_left {i₀ : Fin 4} {u v : ℝ} (huv : u < v)
    (hv : v ≤ A i₀) (hlev : π * A i₀ < bdry A B v) : bdry A B v < bdry A B u := by
  have hB : ∀ w, w ≤ A i₀ → ∀ k, w ≤ B k := fun w hw k => hw.trans (hAB i₀ k).le
  rw [bdry_of_le (hB v hv)] at hlev ⊢
  rw [bdry_of_le (hB u (huv.le.trans hv))]
  have hlev' := lt_of_mul_lt_mul_left hlev Real.pi_pos.le
  refine mul_lt_mul_of_pos_left ?_ Real.pi_pos
  rcases lt_or_ge v 0 with hv0 | hv0
  · -- both negative: every term is linear, slope `−2`
    have he : ∀ w, w < 0 → ∀ i, max (A i - w) 0 = A i - w := fun w hw i =>
      max_eq_left (by linarith [hA i])
    simp only [he u (huv.trans hv0), he v hv0, min_eq_left (huv.trans hv0).le, min_eq_left hv0.le,
      Fin.sum_univ_four]
    linarith
  rcases lt_or_ge u 0 with hu0 | hu0
  · -- `u < 0 ≤ v`: the left value is `Σ A − 2u`, the right one is at most `Σ A`
    have he : ∀ i, max (A i - u) 0 = A i - u := fun i => max_eq_left (by linarith [hA i])
    have hs : A i₀ - max (A i₀ - v) 0 ≤ ∑ i, (A i - max (A i - v) 0) :=
      Finset.single_le_sum (f := fun i => A i - max (A i - v) 0)
        (fun i _ => sub_nonneg.2 (max_le (by linarith) (hA i).le)) (Finset.mem_univ i₀)
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ A i₀ - v)] at hs
    simp only [he, min_eq_left hu0.le, min_eq_right hv0, Fin.sum_univ_four] at hs ⊢
    linarith
  · -- `0 ≤ u < v`: a second face sum lies above `v`, giving slope at most `−1`
    rw [min_eq_right hv0] at hlev'
    rw [min_eq_right hu0, min_eq_right hv0]
    obtain ⟨i₁, hi₁, hvi₁⟩ : ∃ i₁, i₁ ≠ i₀ ∧ v < A i₁ := by
      by_contra hno
      simp only [not_exists, not_and, not_lt] at hno
      have hsum : ∑ i, max (A i - v) 0 = max (A i₀ - v) 0 := by
        refine Finset.sum_eq_single i₀ (fun i _ hi => max_eq_right (by linarith [hno i hi]))
          (fun h => absurd (Finset.mem_univ i₀) h)
      rw [hsum, max_eq_left (by linarith : (0 : ℝ) ≤ A i₀ - v)] at hlev'
      linarith
    set d : Fin 4 → ℝ := fun i => max (A i - u) 0 - max (A i - v) 0 with hd
    have hdnn : ∀ i ∈ Finset.univ, 0 ≤ d i := fun i _ =>
      sub_nonneg.2 (max_le_max (by linarith) le_rfl)
    have hd0 : d i₀ = v - u := by
      simp only [hd, max_eq_left (by linarith : (0 : ℝ) ≤ A i₀ - u),
        max_eq_left (by linarith : (0 : ℝ) ≤ A i₀ - v)]; ring
    have hd1 : d i₁ = v - u := by
      simp only [hd, max_eq_left (by linarith : (0 : ℝ) ≤ A i₁ - u),
        max_eq_left (by linarith : (0 : ℝ) ≤ A i₁ - v)]; ring
    have hs := Finset.add_le_sum hdnn (Finset.mem_univ i₀) (Finset.mem_univ i₁) hi₁.symm
    have hsplit : ∑ i, d i = ∑ i, max (A i - u) 0 - ∑ i, max (A i - v) 0 := by
      simp only [hd, Finset.sum_sub_distrib]
    linarith

/-- **Right piece, upper bound.** `bdry u ≤ π Bₖ₀` for `u ≥ Bₖ₀`, for any quadrilateral sum
`Bₖ₀`; it is used with `Bₖ₀ = B_min`. -/
theorem bdry_le_right {k₀ : Fin 3} {u : ℝ} (hu : B k₀ ≤ u) :
    bdry A B u ≤ π * B k₀ := by
  rw [bdry_of_ge (fun i => (hAB i k₀).le.trans hu) ((hA 0).le.trans ((hAB 0 k₀).le.trans hu))]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  have hs : max (B k₀ - u) 0 - (B k₀ - u) ≤ ∑ k, (max (B k - u) 0 - (B k - u)) :=
    Finset.single_le_sum (f := fun k => max (B k - u) 0 - (B k - u))
      (fun k _ => sub_nonneg.2 (le_max_left _ _)) (Finset.mem_univ k₀)
  rw [max_eq_right (by linarith : B k₀ - u ≤ 0)] at hs
  simp only [Fin.sum_univ_three] at hs ⊢
  linarith

/-- **Right piece, strict decrease.** On `[Bₖ₀, ∞)`, `bdry` is strictly decreasing at every
point where it is below `π Bₖ₀` (any quadrilateral sum `Bₖ₀`; used with `B_min`). -/
theorem bdry_strictAnti_right {k₀ : Fin 3} {u v : ℝ} (hu : B k₀ ≤ u)
    (huv : u < v) (hlev : bdry A B u < π * B k₀) : bdry A B v < bdry A B u := by
  have hge : ∀ w, B k₀ ≤ w → ∀ i, A i ≤ w := fun w hw i => (hAB i k₀).le.trans hw
  have h0 : ∀ w, B k₀ ≤ w → 0 ≤ w := fun w hw => (hA 0).le.trans (hge w hw 0)
  rw [bdry_of_ge (hge u hu) (h0 u hu)] at hlev ⊢
  rw [bdry_of_ge (hge v (hu.trans huv.le)) (h0 v (hu.trans huv.le))]
  have hlev' := lt_of_mul_lt_mul_left hlev Real.pi_pos.le
  refine mul_lt_mul_of_pos_left ?_ Real.pi_pos
  -- each `max (B k − u) 0 − max (B k − v) 0` lies in `[0, v − u]`; at most one is nonzero
  have hlo : ∀ k, max (B k - v) 0 ≤ max (B k - u) 0 := fun k => max_le_max (by linarith) le_rfl
  have hhi : ∀ k, max (B k - u) 0 ≤ max (B k - v) 0 + (v - u) := fun k => by
    simp only [max_def]; split_ifs <;> linarith
  have hz : ∀ k, B k ≤ u → max (B k - u) 0 = 0 := fun k hk => max_eq_right (by linarith)
  have hp : ∀ k, u < B k → max (B k - u) 0 = B k - u := fun k hk => max_eq_left (by linarith)
  -- below `π B_min`, a second quadrilateral sum lies at or left of `u`
  obtain ⟨k₂, hk₂, hk₂u⟩ : ∃ k₂, k₂ ≠ k₀ ∧ B k₂ ≤ u := by
    by_contra hno
    simp only [not_exists, not_and, not_le] at hno
    have hsum : ∑ k, (max (B k - u) 0 - (B k - u)) = u - B k₀ := by
      rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [hp k (hno k hk)]; ring)
        (fun h => absurd (Finset.mem_univ k₀) h), hz k₀ hu]
      ring
    simp only [Finset.sum_sub_distrib, Fin.sum_univ_three] at hsum hlev'
    linarith
  set d : Fin 3 → ℝ := fun k => max (B k - u) 0 - max (B k - v) 0 with hd
  have hd0 : d k₀ = 0 := by
    simp only [hd, hz k₀ hu, max_eq_right (by linarith : B k₀ - v ≤ 0)]; ring
  have hd2 : d k₂ = 0 := by
    simp only [hd, hz k₂ hk₂u, max_eq_right (by linarith : B k₂ - v ≤ 0)]; ring
  have hsum : ∑ k, d k = ∑ k ∈ (Finset.univ.erase k₀).erase k₂, d k := by
    rw [Finset.sum_erase _ hd2, Finset.sum_erase _ hd0]
  have hcard : ((Finset.univ.erase k₀).erase k₂).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hk₂, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hle := Finset.sum_le_card_nsmul ((Finset.univ.erase k₀).erase k₂) d (v - u)
    (fun k _ => by simp only [hd]; linarith [hhi k])
  rw [hcard, one_nsmul, ← hsum] at hle
  have hsplit : ∑ k, d k = ∑ k, max (B k - u) 0 - ∑ k, max (B k - v) 0 := by
    simp only [hd, Finset.sum_sub_distrib]
  linarith

/-- Every level above `π Aᵢ₀` is taken at most once on `(−∞, Aᵢ₀]`. -/
theorem bdry_injOn_left {i₀ : Fin 4} {u v : ℝ} (hu : u ≤ A i₀)
    (hv : v ≤ A i₀) (hlev : π * A i₀ < bdry A B u) (huv : bdry A B u = bdry A B v) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · exact absurd huv (bdry_strictAnti_left hA hAB h hv (huv ▸ hlev)).ne'
  · exact h
  · exact absurd huv (bdry_strictAnti_left hA hAB h hu hlev).ne

/-- Every level below `π Bₖ₀` is taken at most once on `[Bₖ₀, ∞)`. -/
theorem bdry_injOn_right {k₀ : Fin 3} {u v : ℝ} (hu : B k₀ ≤ u)
    (hv : B k₀ ≤ v) (hlev : bdry A B u < π * B k₀) (huv : bdry A B u = bdry A B v) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · exact absurd huv (bdry_strictAnti_right hA hAB hu h hlev).ne'
  · exact h
  · exact absurd huv (bdry_strictAnti_right hA hAB hv h (huv ▸ hlev)).ne

/-- A level above `π B_min` is taken only left of `A_max`. -/
theorem lt_of_bdry_gt {i₀ : Fin 4} {k₀ : Fin 3} (hi₀ : ∀ i, A i ≤ A i₀) (hk₀ : ∀ k, B k₀ ≤ B k)
    {u : ℝ} (hlev : π * B k₀ < bdry A B u) : u < A i₀ := by
  by_contra h
  rw [not_lt] at h
  rcases le_or_gt u (B k₀) with h2 | h2
  · rw [bdry_mid hA hi₀ hk₀ h h2] at hlev
    linarith [mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]
  · linarith [bdry_le_right hA hAB h2.le]

/-- A level below `π A_max` is taken only right of `B_min`. -/
theorem gt_of_bdry_lt {i₀ : Fin 4} {k₀ : Fin 3} (hi₀ : ∀ i, A i ≤ A i₀) (hk₀ : ∀ k, B k₀ ≤ B k)
    {u : ℝ} (hlev : bdry A B u < π * A i₀) : B k₀ < u := by
  by_contra h
  rw [not_lt] at h
  rcases le_or_gt (A i₀) u with h2 | h2
  · rw [bdry_mid hA hi₀ hk₀ h2 h] at hlev
    linarith [mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]
  · linarith [bdry_ge_left hA hAB h2.le]

end RealAxis

/-! ## Continuity on the closed upper half-plane -/

/-- `‖log w‖ ≤ |log ‖w‖| + π`. -/
lemma norm_log_le (w : ℂ) : ‖log w‖ ≤ |Real.log ‖w‖| + π := by
  refine (norm_le_abs_re_add_abs_im _).trans ?_
  rw [log_re, log_im]
  linarith [abs_arg_le_pi w]

/-- `g w = w log w` is continuous at `0` (where `g 0 = 0`). -/
lemma continuousAt_xlog_zero : ContinuousAt xlog 0 := by
  have hb : Continuous fun w : ℂ => |‖w‖ * Real.log ‖w‖| + π * ‖w‖ := by fun_prop
  have ht : Filter.Tendsto (fun w : ℂ => |‖w‖ * Real.log ‖w‖| + π * ‖w‖) (nhds 0) (nhds 0) := by
    simpa using hb.tendsto 0
  rw [ContinuousAt, show xlog 0 = 0 by simp [xlog]]
  refine squeeze_zero_norm (fun w => ?_) ht
  rw [xlog, norm_mul]
  calc ‖w‖ * ‖log w‖ ≤ ‖w‖ * (|Real.log ‖w‖| + π) :=
        mul_le_mul_of_nonneg_left (norm_log_le w) (norm_nonneg w)
    _ = |‖w‖ * Real.log ‖w‖| + π * ‖w‖ := by
        rw [abs_mul, abs_of_nonneg (norm_nonneg w)]; ring

/-- `g w = w log w` is continuous on the closed upper half-plane (the principal logarithm is
continuous there from above, including on the negative real axis). -/
lemma continuousOn_xlog : ContinuousOn xlog {z : ℂ | 0 ≤ z.im} := by
  intro w hw
  rcases eq_or_ne w 0 with rfl | hw0
  · exact continuousAt_xlog_zero.continuousWithinAt
  by_cases hs : w ∈ slitPlane
  · exact (continuousAt_id.mul (continuousAt_clog hs)).continuousWithinAt
  · rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hs
    have hre : w.re < 0 := lt_of_le_of_ne hs.1 fun h => hw0 (Complex.ext h hs.2)
    exact continuousWithinAt_id.mul (continuousWithinAt_log_of_re_neg_of_im_zero hre hs.2)

/-- The continued phase is continuous on the closed upper half-plane. -/
theorem continuousOn_phaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) :
    ContinuousOn (phaseC A B) {z : ℂ | 0 ≤ z.im} := by
  have hsh : ∀ c : ℝ, ContinuousOn (fun z : ℂ => xlog (z - c)) {z : ℂ | 0 ≤ z.im} := fun c =>
    continuousOn_xlog.comp (continuousOn_id.sub continuousOn_const) fun z hz => by
      simpa using hz
  unfold phaseC
  refine ((((continuousOn_xlog.sub (continuousOn_finsetSum _ fun i _ => hsh (A i))).add
    (continuousOn_finsetSum _ fun k _ => hsh (B k))).sub ?_).add continuousOn_const)
  exact continuousOn_const.mul continuousOn_id

/-! ## The derivative on the open upper half-plane -/

/-- The derivative of the continued phase, `log z − Σᵢ log (z − Aᵢ) + Σₖ log (z − Bₖ) − 2πi`. -/
noncomputable def dphaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) (z : ℂ) : ℂ :=
  log z - ∑ i, log (z - A i) + ∑ k, log (z - B k) - 2 * π * I

lemma hasDerivAt_xlog {w : ℂ} (hw : w ∈ slitPlane) : HasDerivAt xlog (log w + 1) w := by
  have h := (hasDerivAt_id w).mul (hasDerivAt_log hw)
  rw [id, one_mul, mul_inv_cancel₀ (slitPlane_ne_zero hw)] at h
  exact h

lemma mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inr hz.ne')

lemma mem_slitPlane_sub {z : ℂ} (hz : 0 < z.im) (c : ℝ) : z - c ∈ slitPlane :=
  mem_slitPlane_of_im_pos (by simpa using hz)

/-- The continued phase is holomorphic on the open upper half-plane, with derivative `dphaseC`. -/
theorem hasDerivAt_phaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (phaseC A B) (dphaseC A B z) z := by
  have hsh : ∀ c : ℝ, HasDerivAt (fun z : ℂ => xlog (z - c)) (log (z - c) + 1) z := fun c => by
    exact (hasDerivAt_xlog (mem_slitPlane_sub hz c)).comp_sub_const z (c : ℂ)
  have h := ((((hasDerivAt_xlog (mem_slitPlane_of_im_pos hz)).sub
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hsh (A i))).add
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hsh (B k))).sub
    ((hasDerivAt_id z).const_mul (2 * π * I))).add_const (π * I * ∑ k, (B k : ℂ))
  convert h using 1
  · ext w; simp [phaseC]
  · simp only [dphaseC, Fin.sum_univ_four, Fin.sum_univ_three]; ring

/-- On the open upper half-plane, `dphaseC` is the derivative `dphase` of Racah's phase. -/
theorem dphase_eq_dphaseC (l : Fin 6 → ℝ) {z : ℂ} (hz : 0 < z.im) :
    dphase l z = dphaseC (faceSum l) (quadSum l) z := by
  have hB : ∀ k, log ((quadSum l k : ℂ) - z) = log (z - quadSum l k) - π * I := fun k => by
    rw [show (quadSum l k : ℂ) - z = -(z - quadSum l k) by ring]
    exact log_neg_of_im_pos (by simpa using hz)
  simp only [dphase, dphaseC, hB, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- The saddle point is a critical point of the continued phase. -/
theorem IsEuclid.dphaseC_saddle {l : Fin 6 → ℝ} (h : IsEuclid l) :
    dphaseC (faceSum l) (quadSum l) (saddle l) = 0 := by
  rw [← dphase_eq_dphaseC l h.saddle_im_pos, h.dphase_saddle]

/-- `exp ψ'(z) = z ∏ₖ (z − Bₖ) / ∏ᵢ (z − Aᵢ)` on the open upper half-plane. -/
theorem exp_dphaseC (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {z : ℂ} (hz : 0 < z.im) :
    exp (dphaseC A B z) = z * (∏ k, (z - B k)) / ∏ i, (z - A i) := by
  have hne : ∀ c : ℝ, z - c ≠ 0 := fun c => slitPlane_ne_zero (mem_slitPlane_sub hz c)
  have hz0 : z ≠ 0 := slitPlane_ne_zero (mem_slitPlane_of_im_pos hz)
  rw [dphaseC, exp_sub, exp_add, exp_sub, exp_sum, exp_sum, exp_two_pi_mul_I, div_one,
    exp_log hz0, Finset.prod_congr rfl fun i _ => exp_log (hne (A i)),
    Finset.prod_congr rfl fun k _ => exp_log (hne (B k))]
  ring

/-! ## A lower bound for `|ψ'|` away from the saddle -/

/-- `min(1, |eʷ − 1|/2) ≤ |w|`. -/
lemma min_le_norm_of_exp (w : ℂ) : min 1 (‖exp w - 1‖ / 2) ≤ ‖w‖ := by
  rcases le_or_gt ‖w‖ 1 with h | h
  · exact (min_le_right _ _).trans (by linarith [norm_exp_sub_one_le h])
  · exact (min_le_left _ _).trans h.le

/-- The saddle quadratic factors over its two conjugate roots. -/
lemma qpoly_eq_mul {l : Fin 6 → ℝ} (hv : 0 ≤ vol2l l) (ha : qa l ≠ 0) (z : ℂ) :
    (qa l : ℂ) * z ^ 2 + qb l * z + qc l =
      qa l * (z - saddle l) * (z - (starRingEnd ℂ) (saddle l)) := by
  have hqa : (qa l : ℂ) ≠ 0 := ofReal_ne_zero.2 ha
  have h1 : saddle l + (starRingEnd ℂ) (saddle l) = -qb l / qa l := by
    rw [add_conj, saddle_re]; push_cast; field_simp
  have h2 : saddle l * (starRingEnd ℂ) (saddle l) = qc l / qa l := by
    have h := normSq_saddle_sub hv ha 0
    rw [ofReal_zero, sub_zero, saddleQ_eq] at h
    rw [mul_conj, h]; push_cast; ring
  have e1 : (qb l : ℂ) = -(qa l) * (saddle l + (starRingEnd ℂ) (saddle l)) := by
    rw [h1]; field_simp
  have e2 : (qc l : ℂ) = qa l * (saddle l * (starRingEnd ℂ) (saddle l)) := by
    rw [h2]; field_simp
  rw [e1, e2]; ring

/-- `z ∏ₖ (z − Bₖ) − ∏ᵢ (z − Aᵢ) = −(qa z² + qb z + qc)` for the face and quadrilateral sums. -/
lemma prod_sub_prod_eq (l : Fin 6 → ℝ) (z : ℂ) :
    z * ∏ k, (z - quadSum l k) - ∏ i, (z - faceSum l i) = -((qa l : ℂ) * z ^ 2 + qb l * z + qc l) := by
  simp only [Fin.prod_univ_three, Fin.prod_univ_four, qa, qb, qc, faceSum_zero, faceSum_one,
    faceSum_two, faceSum_three, quadSum_zero, quadSum_one, quadSum_two]
  push_cast; ring

/-- **No critical point off the saddle.** On the open upper half-plane,
`|ψ'(z)| ≥ min(1, qa |z − x₊| Im x₊ / (2 |∏ᵢ (z − Aᵢ)|))`, `x₊ = saddle l`. -/
theorem IsEuclid.norm_dphaseC_ge {l : Fin 6 → ℝ} (h : IsEuclid l) {z : ℂ} (hz : 0 < z.im) :
    min 1 (qa l * ‖z - saddle l‖ * (saddle l).im / (2 * ‖∏ i, (z - faceSum l i)‖)) ≤
      ‖dphaseC (faceSum l) (quadSum l) z‖ := by
  have hP : ∏ i, (z - faceSum l i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => slitPlane_ne_zero (mem_slitPlane_sub hz _)
  have hPn : 0 < ‖∏ i, (z - faceSum l i)‖ := norm_pos_iff.2 hP
  have hqa := h.qa_pos
  have hexp : exp (dphaseC (faceSum l) (quadSum l) z) - 1 =
      -((qa l : ℂ) * (z - saddle l) * (z - (starRingEnd ℂ) (saddle l))) /
        ∏ i, (z - faceSum l i) := by
    rw [exp_dphaseC _ _ hz, div_sub_one hP, prod_sub_prod_eq, qpoly_eq_mul h.vol2_pos.le hqa.ne',
      neg_div]
  have hconj : (saddle l).im ≤ ‖z - (starRingEnd ℂ) (saddle l)‖ := by
    refine le_trans ?_ ((le_abs_self _).trans (abs_im_le_norm _))
    simp only [sub_im, conj_im]
    linarith
  have hnorm : qa l * ‖z - saddle l‖ * (saddle l).im / ‖∏ i, (z - faceSum l i)‖ ≤
      ‖exp (dphaseC (faceSum l) (quadSum l) z) - 1‖ := by
    rw [hexp, norm_div, norm_neg, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hqa.le]
    gcongr
  refine le_trans ?_ (min_le_norm_of_exp _)
  refine min_le_min_left _ ?_
  rw [div_mul_eq_div_div_swap]
  exact div_le_div_of_nonneg_right hnorm (by norm_num)

/-! ## The continued phase at infinity -/

/-- Points of the segment from `z` to `z − c` (`c` real) have the imaginary part of `z` and lie
within `|c|` of `z`. -/
lemma segment_sub_ofReal {z w : ℂ} {c : ℝ} (hw : w ∈ segment ℝ z (z - c)) :
    w.im = z.im ∧ ‖w - z‖ ≤ |c| := by
  rw [segment_eq_image'] at hw
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hw
  beta_reduce
  have e : z + θ • (z - c - z) - z = -((θ * c : ℝ) : ℂ) := by
    rw [real_smul]; push_cast; ring
  refine ⟨?_, ?_⟩
  · have e' : z + θ • (z - c - z) = z + -((θ * c : ℝ) : ℂ) := by rw [← e]; ring
    rw [e', add_im, neg_im, ofReal_im, neg_zero, add_zero]
  · rw [e, norm_neg, norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg c) h1

/-- **Second-order Taylor bound for `w log w`** along a real shift, in the open upper half-plane:
`|g(z − c) − g(z) + c g'(z)| ≤ c² / (|z| − |c|)`, where `g'(z) = log z + 1`. -/
theorem norm_xlog_sub_le {z : ℂ} (hz : 0 < z.im) {c : ℝ} (hc : |c| < ‖z‖) :
    ‖xlog (z - c) - xlog z + c * (log z + 1)‖ ≤ c ^ 2 / (‖z‖ - |c|) := by
  set S := segment ℝ z (z - c)
  have hS : Convex ℝ S := convex_segment _ _
  have hzS : z ∈ S := left_mem_segment _ _ _
  have hcS : z - c ∈ S := right_mem_segment _ _ _
  have hd : 0 < ‖z‖ - |c| := sub_pos.2 hc
  have hpos : ∀ w ∈ S, 0 < w.im := fun w hw => (segment_sub_ofReal hw).1 ▸ hz
  have hlow : ∀ w ∈ S, ‖z‖ - |c| ≤ ‖w‖ := fun w hw => by
    have h1 := (segment_sub_ofReal hw).2
    have h2 := norm_sub_norm_le z w
    rw [norm_sub_rev] at h2
    linarith
  have hlog : ∀ w ∈ S, ‖log w - log z‖ ≤ |c| / (‖z‖ - |c|) := fun w hw => by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := log)
      (f' := fun v => v⁻¹) (C := 1 / (‖z‖ - |c|))
      (fun v hv => (hasDerivAt_log (mem_slitPlane_of_im_pos (hpos v hv))).hasDerivWithinAt)
      (fun v hv => by
        simp only [norm_inv, one_div]
        exact inv_anti₀ hd (hlow v hv)) hS hzS hw
    calc ‖log w - log z‖ ≤ 1 / (‖z‖ - |c|) * ‖w - z‖ := h
      _ ≤ 1 / (‖z‖ - |c|) * |c| := by gcongr; exact (segment_sub_ofReal hw).2
      _ = |c| / (‖z‖ - |c|) := by ring
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w => xlog w - w * (log z + 1)) (f' := fun w => log w - log z)
    (C := |c| / (‖z‖ - |c|))
    (fun w hw => by
      have := ((hasDerivAt_xlog (mem_slitPlane_of_im_pos (hpos w hw))).sub
        ((hasDerivAt_id' w).mul_const (log z + 1))).hasDerivWithinAt (s := S)
      convert this using 1
      ring)
    hlog hS hzS hcS
  have e : xlog (z - c) - xlog z + c * (log z + 1) =
      (xlog (z - c) - (z - c) * (log z + 1)) - (xlog z - z * (log z + 1)) := by ring
  rw [e]
  calc _ ≤ |c| / (‖z‖ - |c|) * ‖z - c - z‖ := h
    _ = c ^ 2 / (‖z‖ - |c|) := by
        rw [show z - (c : ℂ) - z = -(c : ℂ) by ring, norm_neg, norm_real, Real.norm_eq_abs,
          ← sq_abs c]
        ring

/-- **The continued phase at infinity.** If the face and quadrilateral sums balance,
`Σᵢ Aᵢ = Σₖ Bₖ` (as they do for a tetrahedron: each edge lies in two faces and two
quadrilaterals), then on the open upper half-plane
`|ψ(z) + 2πiz − πi Σₖ Bₖ| ≤ 2 (Σᵢ Aᵢ² + Σₖ Bₖ²) / |z|` once `|z| ≥ 2|Aᵢ|, 2|Bₖ|`. -/
theorem norm_phaseC_add_le {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hbal : ∑ i, A i = ∑ k, B k)
    {z : ℂ} (hz : 0 < z.im) (hA : ∀ i, 2 * |A i| ≤ ‖z‖) (hB : ∀ k, 2 * |B k| ≤ ‖z‖) :
    ‖phaseC A B z + 2 * π * I * z - π * I * ∑ k, (B k : ℂ)‖ ≤
      2 * (∑ i, A i ^ 2 + ∑ k, B k ^ 2) / ‖z‖ := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 (slitPlane_ne_zero (mem_slitPlane_of_im_pos hz))
  set E : ℝ → ℂ := fun c => xlog (z - c) - xlog z + c * (log z + 1) with hE
  have hEb : ∀ c : ℝ, 2 * |c| ≤ ‖z‖ → ‖E c‖ ≤ 2 * c ^ 2 / ‖z‖ := fun c hc => by
    have hlt : |c| < ‖z‖ := by linarith [abs_nonneg c]
    refine (norm_xlog_sub_le hz hlt).trans ?_
    rw [show 2 * c ^ 2 / ‖z‖ = c ^ 2 / (‖z‖ / 2) by field_simp]
    exact div_le_div_of_nonneg_left (sq_nonneg c) (half_pos hz0) (by linarith)
  have hb : (∑ i, (A i : ℂ)) = ∑ k, (B k : ℂ) := by exact_mod_cast hbal
  have key : phaseC A B z + 2 * π * I * z - π * I * ∑ k, (B k : ℂ) =
      ∑ k, E (B k) - ∑ i, E (A i) := by
    simp only [hE, phaseC, Fin.sum_univ_four, Fin.sum_univ_three] at hb ⊢
    linear_combination (log z + 1) * hb
  rw [key]
  calc ‖∑ k, E (B k) - ∑ i, E (A i)‖ ≤ ∑ k, ‖E (B k)‖ + ∑ i, ‖E (A i)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    _ ≤ ∑ k, 2 * B k ^ 2 / ‖z‖ + ∑ i, 2 * A i ^ 2 / ‖z‖ :=
        add_le_add (Finset.sum_le_sum fun k _ => hEb _ (hB k))
          (Finset.sum_le_sum fun i _ => hEb _ (hA i))
    _ = 2 * (∑ i, A i ^ 2 + ∑ k, B k ^ 2) / ‖z‖ := by
        simp only [Fin.sum_univ_four, Fin.sum_univ_three]; ring

/-- The face and quadrilateral sums of a tetrahedron balance: both add up to twice the total
edge length. -/
lemma sum_faceSum_eq_sum_quadSum (l : Fin 6 → ℝ) : ∑ i, faceSum l i = ∑ k, quadSum l k := by
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, faceSum_zero, faceSum_one, faceSum_two,
    faceSum_three, quadSum_zero, quadSum_one, quadSum_two]
  ring

end Lightlike.Asymptotics
