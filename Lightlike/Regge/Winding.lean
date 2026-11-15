import Mathlib

/-!
# Wedges around a point that do not overlap add up to a full turn

Seen from an interior point of an edge, the tetrahedra around the edge are wedges in the plane
perpendicular to it. This file contains the planar part of the proof that, in a triangulation of a
region of space, the dihedral angles around an interior edge add up to `2π`.

Directions in the plane are given by angles `α ∈ ℝ`. The open wedge spanned by the directions `α`
and `β` consists of the directions `τ` with `(cos τ, sin τ)` a positive combination of
`(cos α, sin α)` and `(cos β, sin β)` (`InWedge α β τ`).

## Main result

* `sum_arccos_cos_eq_two_pi`: let `α 0, …, α n` be directions, `n ≥ 1`, with `α n` the same
  direction as `α 0`, no two consecutive ones parallel, and the open wedges between consecutive
  directions pairwise disjoint. Then the angles between consecutive directions,
  `arccos (cos (α (i+1) - α i))`, add up to `2π`.
* `exists_lift_of_pos`: under the same hypotheses, with the first wedge turning positively, the
  directions lift to angles `A 0 < A 1 < ⋯ < A n = A 0 + 2π` with steps less than `π`. The
  Lorentzian full turn (`Lightlike/Regge/Lorentzian/Angle.lean`) counts light rays along this lift.

The proof: no overlap forces all wedges to turn the same way (two neighbours turning opposite ways
overlap next to their common direction). The angles then add up to `2π m` with `m ≥ 1`, because
the directions close up, and `m ≥ 2` would make some direction lie in two wedges
(`winding_core`).
-/

open Real Finset

namespace Lightlike.Regge

/-- The direction `τ` lies strictly inside the angle spanned by the directions `α` and `β`:
`(cos τ, sin τ)` is a positive combination of `(cos α, sin α)` and `(cos β, sin β)`. -/
def InWedge (α β τ : ℝ) : Prop :=
  ∃ l m : ℝ, 0 < l ∧ 0 < m ∧ cos τ = l * cos α + m * cos β ∧ sin τ = l * sin α + m * sin β

/-- The wedge between `α` and `β` is the wedge between `β` and `α`. -/
theorem InWedge.symm {α β τ : ℝ} (h : InWedge α β τ) : InWedge β α τ := by
  obtain ⟨l, m, hl, hm, hc, hs⟩ := h
  exact ⟨m, l, hm, hl, by rw [hc]; ring, by rw [hs]; ring⟩

/-- Wedges depend only on the directions, i.e. on cosines and sines. -/
theorem InWedge.congr {α β τ α' β' τ' : ℝ} (h : InWedge α β τ)
    (hα : cos α = cos α' ∧ sin α = sin α') (hβ : cos β = cos β' ∧ sin β = sin β')
    (hτ : cos τ = cos τ' ∧ sin τ = sin τ') : InWedge α' β' τ' := by
  obtain ⟨l, m, hl, hm, hc, hs⟩ := h
  exact ⟨l, m, hl, hm, by rw [← hτ.1, ← hα.1, ← hβ.1, hc], by rw [← hτ.2, ← hα.2, ← hβ.2, hs]⟩

/-- Reflecting all directions reflects the wedge. -/
theorem InWedge.neg {α β τ : ℝ} (h : InWedge α β τ) : InWedge (-α) (-β) (-τ) := by
  obtain ⟨l, m, hl, hm, hc, hs⟩ := h
  refine ⟨l, m, hl, hm, ?_, ?_⟩
  · simp only [cos_neg]
    exact hc
  · simp only [sin_neg]
    rw [hs]
    ring

/-- A direction strictly between `A` and `A + φ`, for `0 < φ < π`, lies in their open wedge. -/
theorem inWedge_of_mem_Ioo {A φ τ : ℝ} (hφ : 0 < φ) (hφπ : φ < π) (h1 : A < τ)
    (h2 : τ < A + φ) : InWedge A (A + φ) τ := by
  obtain ⟨u, rfl⟩ : ∃ u, τ = A + u := ⟨τ - A, by ring⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ hφπ
  refine ⟨sin (φ - u) / sin φ, sin u / sin φ,
    div_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)) hs,
    div_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)) hs, ?_, ?_⟩
  · field_simp
    simp only [cos_add, sin_sub]
    ring
  · field_simp
    simp only [sin_add, sin_sub]
    ring

/-- **Winding once.** Let `A 0 < A 1 < ⋯ < A n` (`n ≥ 1`) increase by less than `π` at each step
and end in the direction they started from. If the open wedges `(A i, A (i+1))` are pairwise
disjoint as sets of directions, then `A n - A 0 = 2π`: the wedges go around exactly once. -/
theorem winding_core {n : ℕ} (hn : 0 < n) (A : ℕ → ℝ)
    (hstep : ∀ i < n, A i < A (i + 1) ∧ A (i + 1) < A i + π) (hclose : cos (A n - A 0) = 1)
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, InWedge (A i) (A (i + 1)) τ →
      ¬ InWedge (A j) (A (j + 1)) τ) :
    A n - A 0 = 2 * π := by
  have hmono : ∀ j ≤ n, ∀ i < j, A i < A j := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      have hs := (hstep j (by omega)).1
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact (ih (by omega) i h).trans hs
      · rw [h]
        exact hs
  obtain ⟨m, hm⟩ := (cos_eq_one_iff _).mp hclose
  have hpos : 0 < A n - A 0 := sub_pos.mpr (hmono n le_rfl 0 hn)
  have hm0 : (0 : ℝ) < m := by nlinarith [pi_pos]
  have hm1 : (1 : ℤ) ≤ m := by
    have : (0 : ℤ) < m := by exact_mod_cast hm0
    omega
  have hm2 : m < 2 := by
    by_contra hge
    have hge' : (2 : ℝ) ≤ m := by exact_mod_cast not_lt.mp hge
    have h4 : A 0 + 4 * π ≤ A n := by nlinarith [pi_pos]
    have h01 := hstep 0 hn
    obtain ⟨τ, hτ, hτn⟩ := (Set.Ioo_infinite h01.1).exists_notMem_finset
      ((range (n + 1)).image fun k => A k - 2 * π)
    have hτk : ∀ k ≤ n, A k ≠ τ + 2 * π := by
      intro k hk heq
      exact hτn (mem_image.mpr ⟨k, mem_range.mpr (by omega), by rw [heq]; ring⟩)
    have hP : ∃ k, τ + 2 * π < A k := ⟨n, by linarith [hτ.2, pi_pos]⟩
    set k₀ := Nat.find hP with hk₀_def
    have hk₀ : τ + 2 * π < A k₀ := Nat.find_spec hP
    have hk₀n : k₀ ≤ n := Nat.find_min' hP (by linarith [hτ.2, pi_pos])
    have hk₀0 : k₀ ≠ 0 := by
      intro h0
      rw [h0] at hk₀
      linarith [hτ.1, pi_pos]
    have hj : ¬ τ + 2 * π < A (k₀ - 1) := Nat.find_min hP (by omega)
    have hj' : A (k₀ - 1) < τ + 2 * π :=
      lt_of_le_of_ne (not_lt.mp hj) (hτk (k₀ - 1) (by omega))
    have hj0 : k₀ - 1 ≠ 0 := by
      intro h0
      rw [show k₀ = 1 by omega] at hk₀
      linarith [hτ.1]
    have hsj := hstep (k₀ - 1) (by omega)
    rw [show k₀ - 1 + 1 = k₀ by omega] at hsj
    have w0 : InWedge (A 0) (A 1) τ := by
      have := inWedge_of_mem_Ioo (A := A 0) (φ := A 1 - A 0) (by linarith) (by linarith) hτ.1
        (by linarith [hτ.2])
      rwa [show A 0 + (A 1 - A 0) = A 1 by ring] at this
    have wj : InWedge (A (k₀ - 1)) (A (k₀ - 1 + 1)) τ := by
      rw [show k₀ - 1 + 1 = k₀ by omega]
      have := inWedge_of_mem_Ioo (A := A (k₀ - 1)) (φ := A k₀ - A (k₀ - 1)) (by linarith)
        (by linarith) hj' (by linarith)
      rw [show A (k₀ - 1) + (A k₀ - A (k₀ - 1)) = A k₀ by ring] at this
      exact this.congr ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨cos_add_two_pi τ, sin_add_two_pi τ⟩
    exact hdisj 0 hn (k₀ - 1) (by omega) (Ne.symm hj0) τ w0 wj
  have : m = 1 := by omega
  rw [← hm, this]
  push_cast
  ring

/-- **Lifting the directions once around.** Under the hypotheses of `sum_arccos_cos_eq_two_pi`,
with the first step turning positively (`sin (α 1 - α 0) > 0`), there are angles `A k` pointing in
the directions `α k` that increase by less than `π` at each step and by exactly `2π` in total. -/
theorem exists_lift_of_pos {n : ℕ} (hn : 0 < n) (α : ℕ → ℝ)
    (hnd : ∀ i < n, sin (α (i + 1) - α i) ≠ 0)
    (hclose : cos (α n) = cos (α 0) ∧ sin (α n) = sin (α 0))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, InWedge (α i) (α (i + 1)) τ →
      ¬ InWedge (α j) (α (j + 1)) τ)
    (h0 : 0 < sin (α 1 - α 0)) :
    ∃ A : ℕ → ℝ, (∀ k, cos (A k) = cos (α k) ∧ sin (A k) = sin (α k)) ∧
      (∀ i < n, A i < A (i + 1) ∧ A (i + 1) < A i + π) ∧ A n - A 0 = 2 * π := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- the turning angle of step `i`, reduced to `(-π, π]`
  set φ : ℕ → ℝ := fun i => toIocMod h2π (-π) (α (i + 1) - α i) with hφ_def
  have hφmem : ∀ i, -π < φ i ∧ φ i ≤ π := by
    intro i
    have := toIocMod_mem_Ioc h2π (-π) (α (i + 1) - α i)
    exact ⟨this.1, by linarith [this.2]⟩
  have hφeq : ∀ i, α i + φ i = α (i + 1) - (toIocDiv h2π (-π) (α (i + 1) - α i) : ℝ) * (2 * π) :=
    by
    intro i
    simp only [hφ_def, ← self_sub_toIocDiv_zsmul h2π (-π) (α (i + 1) - α i), zsmul_eq_mul]
    ring
  have hrot : ∀ i, cos (α i + φ i) = cos (α (i + 1)) ∧ sin (α i + φ i) = sin (α (i + 1)) := by
    intro i
    rw [hφeq]
    exact ⟨cos_sub_int_mul_two_pi _ _, sin_sub_int_mul_two_pi _ _⟩
  have hcs : ∀ i, cos (φ i) = cos (α (i + 1) - α i) ∧ sin (φ i) = sin (α (i + 1) - α i) := by
    intro i
    have : φ i = α (i + 1) - α i - (toIocDiv h2π (-π) (α (i + 1) - α i) : ℝ) * (2 * π) := by
      linarith [hφeq i]
    rw [this]
    exact ⟨cos_sub_int_mul_two_pi _ _, sin_sub_int_mul_two_pi _ _⟩
  -- directions `α i - φ i`-style: going back from `α (i+1)` by `φ i` gives `α i`
  have hback : ∀ i, cos (α (i + 1) - φ i) = cos (α i) ∧ sin (α (i + 1) - φ i) = sin (α i) := by
    intro i
    have : α (i + 1) - φ i = α i + (toIocDiv h2π (-π) (α (i + 1) - α i) : ℝ) * (2 * π) := by
      linarith [hφeq i]
    rw [this]
    exact ⟨cos_add_int_mul_two_pi _ _, sin_add_int_mul_two_pi _ _⟩
  -- for `i < n`, `φ i ∈ (-π, 0) ∪ (0, π)`
  have hφne : ∀ i < n, φ i ≠ 0 ∧ φ i ≠ π := by
    intro i hi
    constructor
    · intro h
      apply hnd i hi
      rw [← (hcs i).2, h, sin_zero]
    · intro h
      apply hnd i hi
      rw [← (hcs i).2, h, sin_pi]
  -- consecutive steps turn the same way
  have hcons : ∀ i, i + 1 < n → 0 < φ i → 0 < φ (i + 1) := by
    intro i hi hpos
    by_contra hneg
    have hneg' : φ (i + 1) < 0 :=
      lt_of_le_of_ne (not_lt.mp hneg) (hφne (i + 1) hi).1
    set B := α (i + 1)
    set ψ := φ (i + 1)
    have hψ := hφmem (i + 1)
    have hφi := hφmem i
    have hφi' : φ i < π := lt_of_le_of_ne hφi.2 (hφne i (by omega)).2
    set δ := min (φ i) (-ψ) / 2 with hδ
    have hδ1 : δ < φ i := by
      have := min_le_left (φ i) (-ψ)
      have : 0 < min (φ i) (-ψ) := lt_min hpos (by linarith)
      linarith
    have hδ2 : δ < -ψ := by
      have := min_le_right (φ i) (-ψ)
      have : 0 < min (φ i) (-ψ) := lt_min hpos (by linarith)
      linarith
    have hδ0 : 0 < δ := by
      have : 0 < min (φ i) (-ψ) := lt_min hpos (by linarith)
      linarith
    have wi : InWedge (α i) (α (i + 1)) (B - δ) := by
      have := inWedge_of_mem_Ioo (A := B - φ i) (φ := φ i) (τ := B - δ) hpos hφi' (by linarith) (by linarith)
      exact this.congr (hback i) ⟨by rw [show B - φ i + φ i = B by ring],
        by rw [show B - φ i + φ i = B by ring]⟩ ⟨rfl, rfl⟩
    have wi1 : InWedge (α (i + 1)) (α (i + 1 + 1)) (B - δ) := by
      have := inWedge_of_mem_Ioo (A := B + ψ) (φ := -ψ) (τ := B - δ) (by linarith) (by linarith) (by linarith)
        (by linarith)
      exact this.symm.congr ⟨by rw [show B + ψ + -ψ = B by ring],
        by rw [show B + ψ + -ψ = B by ring]⟩ (hrot (i + 1)) ⟨rfl, rfl⟩
    exact hdisj i (by omega) (i + 1) hi (by omega) _ wi wi1
  have hφ0 : 0 < φ 0 := by
    rcases lt_or_ge 0 (φ 0) with h | h
    · exact h
    · exfalso
      have hm := hφmem 0
      have : sin (φ 0) ≤ 0 := by
        rcases eq_or_lt_of_le h with h' | h'
        · rw [h', sin_zero]
        · exact (sin_neg_of_neg_of_neg_pi_lt h' hm.1).le
      rw [(hcs 0).2] at this
      simp only [zero_add] at this
      linarith
  have hφpos : ∀ i < n, 0 < φ i := by
    intro i
    induction i with
    | zero => intro _; exact hφ0
    | succ i ih => intro hi; exact hcons i hi (ih (by omega))
  -- the cumulative angles
  set A : ℕ → ℝ := fun k => α 0 + ∑ i ∈ range k, φ i with hA_def
  have hAstep : ∀ k, A (k + 1) = A k + φ k := by
    intro k
    simp only [hA_def, sum_range_succ]
    ring
  have hAdir : ∀ k, cos (A k) = cos (α k) ∧ sin (A k) = sin (α k) := by
    intro k
    induction k with
    | zero => simp [hA_def]
    | succ k ih =>
      rw [hAstep, ← (hrot k).1, ← (hrot k).2]
      simp only [cos_add, sin_add, ih.1, ih.2, and_self]
  have hAst : ∀ i < n, A i < A (i + 1) ∧ A (i + 1) < A i + π := fun i hi =>
    ⟨by rw [hAstep]; linarith [hφpos i hi],
      by rw [hAstep]; linarith [lt_of_le_of_ne (hφmem i).2 (hφne i hi).2]⟩
  have hw := winding_core hn A hAst
    (by
      rw [cos_sub, (hAdir n).1, (hAdir n).2, (hAdir 0).1, (hAdir 0).2, hclose.1, hclose.2]
      simpa only [sq] using cos_sq_add_sin_sq (α 0))
    (fun i hi j hj hij τ h1 h2 => hdisj i hi j hj hij τ
      (h1.congr (hAdir i) (hAdir (i + 1)) ⟨rfl, rfl⟩) (h2.congr (hAdir j) (hAdir (j + 1)) ⟨rfl, rfl⟩))
  exact ⟨A, hAdir, hAst, hw⟩

/-- The first step turns positively: the case of `sum_arccos_cos_eq_two_pi` with
`sin (α 1 - α 0) > 0`. -/
theorem sum_arccos_cos_eq_two_pi_of_pos {n : ℕ} (hn : 0 < n) (α : ℕ → ℝ)
    (hnd : ∀ i < n, sin (α (i + 1) - α i) ≠ 0)
    (hclose : cos (α n) = cos (α 0) ∧ sin (α n) = sin (α 0))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, InWedge (α i) (α (i + 1)) τ →
      ¬ InWedge (α j) (α (j + 1)) τ)
    (h0 : 0 < sin (α 1 - α 0)) :
    ∑ i ∈ range n, arccos (cos (α (i + 1) - α i)) = 2 * π := by
  obtain ⟨A, hAdir, hAst, hw⟩ := exists_lift_of_pos hn α hnd hclose hdisj h0
  have harc : ∀ i < n, arccos (cos (α (i + 1) - α i)) = A (i + 1) - A i := by
    intro i hi
    rw [show cos (α (i + 1) - α i) = cos (A (i + 1) - A i) by
        rw [cos_sub, cos_sub, (hAdir i).1, (hAdir i).2, (hAdir (i + 1)).1, (hAdir (i + 1)).2],
      arccos_cos (by linarith [(hAst i hi).1]) (by linarith [(hAst i hi).2])]
  rw [sum_congr rfl fun i hi => harc i (mem_range.mp hi), sum_range_sub (fun k => A k)]
  exact hw

/-- **Non-overlapping wedges around a point add up to a full turn.** Let `α 0, …, α n` (`n ≥ 1`)
be directions in the plane with `α n` the same direction as `α 0`, no two consecutive ones
parallel (`sin (α (i+1) - α i) ≠ 0`), and the open wedges between consecutive directions pairwise
disjoint. Then the angles `arccos (cos (α (i+1) - α i))` between consecutive directions add up to
`2π`. -/
theorem sum_arccos_cos_eq_two_pi {n : ℕ} (hn : 0 < n) (α : ℕ → ℝ)
    (hnd : ∀ i < n, sin (α (i + 1) - α i) ≠ 0)
    (hclose : cos (α n) = cos (α 0) ∧ sin (α n) = sin (α 0))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, InWedge (α i) (α (i + 1)) τ →
      ¬ InWedge (α j) (α (j + 1)) τ) :
    ∑ i ∈ range n, arccos (cos (α (i + 1) - α i)) = 2 * π := by
  rcases lt_or_gt_of_ne (hnd 0 hn) with hneg | hpos
  · -- reflect: apply the positive case to `-α`
    have h := sum_arccos_cos_eq_two_pi_of_pos hn (fun i => -α i)
      (fun i hi => by
        rw [show -α (i + 1) - -α i = -(α (i + 1) - α i) by ring, sin_neg, neg_ne_zero]
        exact hnd i hi)
      (by simp only [cos_neg, sin_neg, hclose.1, hclose.2, and_self])
      (fun i hi j hj hij τ h1 h2 => by
        have := hdisj i hi j hj hij (-τ)
          (by simpa using h1.neg) (by simpa using h2.neg)
        exact this)
      (by rw [show -α (0 + 1) - -α 0 = -(α 1 - α 0) by simp; ring, sin_neg]; linarith)
    have e : ∀ i, arccos (cos (-α (i + 1) - -α i)) = arccos (cos (α (i + 1) - α i)) := fun i => by
      rw [show -α (i + 1) - -α i = -(α (i + 1) - α i) by ring, cos_neg]
    rw [← sum_congr rfl fun i _ => e i]
    exact h
  · exact sum_arccos_cos_eq_two_pi_of_pos hn α hnd hclose hdisj (by simpa using hpos)

end Lightlike.Regge
