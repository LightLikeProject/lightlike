import Mathlib.Analysis.ODE.ExistUnique

/-!
# Global solutions of ODEs with a globally Lipschitz right-hand side

For `f : ℝ → E → E` on a real Banach space `E`, Lipschitz in `x` with one constant `K` for all `t ∈ [a, b]` and
continuous in `t`, the initial value problem `y' = f(t, y)`, `y a = x₀` has a solution on the whole interval `[a, b]`
(`exists_solution_Icc_of_lipschitz`), and it is unique (`eqOn_of_lipschitz`). This covers the linear equations
`y' = M(t) y` with `M` continuous, among them the parallel transport equation of a connection along a path.

The existence glues the local solutions of Mathlib's Picard–Lindelöf theorem
(`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) on steps of a fixed length: with the bound `B` of
`‖f(t, 0)‖`, the right-hand side grows at most linearly, `‖f(t, x)‖ ≤ B + K ‖x‖`, so the length of a step does not
depend on the initial value. The uniqueness is Mathlib's `ODE_solution_unique_of_mem_Icc_right` (Gronwall).
`Lightlike.Gauge.eq_zero_of_linear_ode` is the uniqueness for `y' = A(t) y` on `ℝᵐ` with zero initial value.
-/

open Set Metric Filter Topology
open scoped NNReal

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Gluing two solutions** on adjacent closed intervals `[a, T]` and `[T, T']` that agree at `T`. -/
lemma hasDerivWithinAt_Icc_piecewise {f g : ℝ → E} {D : ℝ → E} {a T T' : ℝ} (haT : a ≤ T) (hTT' : T ≤ T')
    (hf : ∀ t ∈ Icc a T, HasDerivWithinAt f (D t) (Icc a T) t)
    (hg : ∀ t ∈ Icc T T', HasDerivWithinAt g (D t) (Icc T T') t) (hfg : f T = g T) :
    ∀ t ∈ Icc a T', HasDerivWithinAt (fun s => if s ≤ T then f s else g s) (D t) (Icc a T') t := by
  intro t ht
  have hzf : ∀ s ∈ Icc a T, (fun s => if s ≤ T then f s else g s) s = f s := fun s hs => by
    simp only [ite_eq_left hs.2]
  have hzg : ∀ s ∈ Icc T T', (fun s => if s ≤ T then f s else g s) s = g s := fun s hs => by
    rcases eq_or_lt_of_le hs.1 with h | h
    · simp only [← h, le_refl, ite_true, hfg]
    · simp only [ite_eq_right (not_le.2 h)]
  rcases lt_trichotomy t T with h | h | h
  · have hmem : Icc a T ∈ 𝓝[Icc a T'] t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds h)) fun s hs => ⟨hs.1.1, hs.2.le⟩
    exact ((hf t ⟨ht.1, h.le⟩).congr hzf (hzf t ⟨ht.1, h.le⟩)).mono_of_mem_nhdsWithin hmem
  · subst h
    rw [← Icc_union_Icc_eq_Icc haT hTT']
    exact ((hf t ⟨ht.1, le_rfl⟩).congr hzf (hzf t ⟨ht.1, le_rfl⟩)).union
      ((hg t ⟨le_rfl, ht.2⟩).congr hzg (hzg t ⟨le_rfl, ht.2⟩))
  · have hmem : Icc T T' ∈ 𝓝[Icc a T'] t :=
      mem_of_superset (inter_mem_nhdsWithin _ (Ioi_mem_nhds h)) fun s hs => ⟨hs.2.le, hs.1.2⟩
    exact ((hg t ⟨h.le, ht.2⟩).congr hzg (hzg t ⟨h.le, ht.2⟩)).mono_of_mem_nhdsWithin hmem

variable [CompleteSpace E]

/-- **One step**: on an interval `[s, s']` of length at most `1 / (2 (B + K + 1))`, where `‖f(t, 0)‖ ≤ B`, the
equation `y' = f(t, y)` has a solution from every initial value at `s`. -/
lemma exists_solution_step {f : ℝ → E → E} {K : ℝ≥0} {B s s' : ℝ} (hss : s ≤ s')
    (hL : ∀ t ∈ Icc s s', LipschitzWith K (f t)) (hc : ∀ x, ContinuousOn (fun t => f t x) (Icc s s'))
    (hB : ∀ t ∈ Icc s s', ‖f t 0‖ ≤ B) (hlen : (s' - s) * (2 * (B + K + 1)) ≤ 1) (x₀ : E) :
    ∃ y : ℝ → E, y s = x₀ ∧ ∀ t ∈ Icc s s', HasDerivWithinAt y (f t (y t)) (Icc s s') t := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s ⟨le_rfl, hss⟩)
  have hK0 : (0 : ℝ) ≤ K := K.2
  set R : ℝ≥0 := ⟨‖x₀‖ + 1, by positivity⟩ with hR
  set L : ℝ≥0 := ⟨B + K * (2 * ‖x₀‖ + 1), by positivity⟩ with hLdef
  have hRc : (R : ℝ) = ‖x₀‖ + 1 := rfl
  have hLc : (L : ℝ) = B + K * (2 * ‖x₀‖ + 1) := rfl
  have hP : IsPicardLindelof f (⟨s, le_rfl, hss⟩ : Icc s s') x₀ R 0 L K := by
    refine ⟨fun t ht => (hL t ht).lipschitzOnWith, fun x _ => hc x, fun t ht x hx => ?_, ?_⟩
    · have hx' : ‖x‖ ≤ 2 * ‖x₀‖ + 1 := by
        have := norm_le_of_mem_closedBall hx
        rw [hRc] at this
        linarith
      have h1 : ‖f t x - f t 0‖ ≤ K * ‖x - 0‖ := by
        simpa [dist_eq_norm] using (hL t ht).dist_le_mul x 0
      have h2 : ‖f t x‖ ≤ ‖f t 0‖ + K * ‖x‖ := by
        have := norm_le_insert' (f t x) (f t 0)
        rw [sub_zero] at h1
        linarith [norm_sub_rev (f t x) (f t 0)]
      rw [hLc]
      nlinarith [hB t ht]
    · rw [hLc, hRc, NNReal.coe_zero, sub_zero]
      show (B + K * (2 * ‖x₀‖ + 1)) * max (s' - s) (s - s) ≤ ‖x₀‖ + 1
      rw [sub_self, max_eq_left (by linarith)]
      have h3 : (s' - s) * (B + K) ≤ 1 / 2 := by nlinarith
      have h4 : (s' - s) * K ≤ 1 / 2 := by nlinarith
      nlinarith [norm_nonneg x₀]
  exact hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- **Global existence** for a right-hand side that is Lipschitz in `x` with one constant on `[a, b]` and continuous in
`t`: the solution of `y' = f(t, y)`, `y a = x₀`, exists on the whole interval `[a, b]`. -/
theorem exists_solution_Icc_of_lipschitz {f : ℝ → E → E} {K : ℝ≥0} {a b : ℝ} (hab : a ≤ b)
    (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t)) (hc : ∀ x, ContinuousOn (fun t => f t x) (Icc a b)) (x₀ : E) :
    ∃ y : ℝ → E, y a = x₀ ∧ ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc 0)
  have hB' : ∀ t ∈ Icc a b, ‖f t 0‖ ≤ |B| := fun t ht => (hB t ht).trans (le_abs_self B)
  have hK0 : (0 : ℝ) ≤ K := K.2
  set h : ℝ := 1 / (2 * (|B| + K + 1)) with hh
  have hpos : 0 < 2 * (|B| + K + 1) := by positivity
  have hh0 : 0 < h := by positivity
  have hstep : h * (2 * (|B| + K + 1)) = 1 := by rw [hh]; field_simp
  have key : ∀ n : ℕ, ∃ y : ℝ → E, y a = x₀ ∧ ∀ t ∈ Icc a (min (a + (n + 1) * h) b),
      HasDerivWithinAt y (f t (y t)) (Icc a (min (a + (n + 1) * h) b)) t := by
    intro n
    induction n with
    | zero =>
      have hsub : Icc a (min (a + ((0 : ℕ) + 1) * h) b) ⊆ Icc a b := Icc_subset_Icc_right (min_le_right _ _)
      refine exists_solution_step (le_min (by push_cast; linarith) hab) (fun t ht => hL t (hsub ht))
        (fun x => (hc x).mono hsub) (fun t ht => hB' t (hsub ht)) ?_ x₀
      have : min (a + ((0 : ℕ) + 1) * h) b - a ≤ h := by
        have := min_le_left (a + ((0 : ℕ) + 1) * h) b
        push_cast at this ⊢
        linarith
      nlinarith
    | succ n ih =>
      obtain ⟨y, hy0, hy⟩ := ih
      set T := min (a + ((n : ℕ) + 1) * h) b with hT
      set T' := min (a + (((n + 1 : ℕ) : ℝ) + 1) * h) b with hT'
      have haT : a ≤ T := le_min (by nlinarith [n.cast_nonneg (α := ℝ)]) hab
      have hTT' : T ≤ T' := by
        refine min_le_min_right _ ?_
        push_cast
        nlinarith
      have hlen : T' - T ≤ h := by
        rcases le_total (a + ((n : ℕ) + 1) * h) b with hle | hle
        · have h1 : T = a + ((n : ℕ) + 1) * h := min_eq_left hle
          have h2 : T' ≤ a + (((n + 1 : ℕ) : ℝ) + 1) * h := min_le_left _ _
          push_cast at h1 h2
          linarith
        · have h1 : T = b := min_eq_right hle
          have h2 : T' ≤ b := min_le_right _ _
          linarith
      have hsub : Icc T T' ⊆ Icc a b := Icc_subset_Icc haT (min_le_right _ _)
      obtain ⟨z, hz0, hz⟩ := exists_solution_step hTT' (fun t ht => hL t (hsub ht)) (fun x => (hc x).mono hsub)
        (fun t ht => hB' t (hsub ht)) (by nlinarith) (y T)
      refine ⟨fun s => if s ≤ T then y s else z s, by simp only [ite_eq_left haT, hy0], ?_⟩
      refine hasDerivWithinAt_Icc_piecewise (D := fun t => f t (if t ≤ T then y t else z t)) haT hTT'
        (fun t ht => ?_) (fun t ht => ?_) hz0.symm
      · simp only [ite_eq_left ht.2]
        exact hy t ht
      · rcases eq_or_lt_of_le ht.1 with he | hlt
        · simp only [← he, le_refl, ite_true, ← hz0]
          exact hz T ⟨le_rfl, hTT'⟩
        · simp only [ite_eq_right (not_le.2 hlt)]
          exact hz t ht
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / h)
  obtain ⟨y, hy0, hy⟩ := key n
  have hmin : min (a + (n + 1) * h) b = b := by
    refine min_eq_right ?_
    have := (div_lt_iff₀ hh0).1 hn
    nlinarith
  rw [hmin] at hy
  exact ⟨y, hy0, hy⟩

omit [CompleteSpace E] in
/-- **Uniqueness**: two solutions of `y' = f(t, y)` on `[a, b]`, for `f` Lipschitz in `x` with one constant, that agree
at `a` agree on `[a, b]`. -/
theorem eqOn_of_lipschitz {f : ℝ → E → E} {K : ℝ≥0} {a b : ℝ} (hL : ∀ t ∈ Icc a b, LipschitzWith K (f t))
    {y z : ℝ → E} (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (f t (z t)) (Icc a b) t) (h0 : y a = z a) :
    EqOn y z (Icc a b) := by
  have hmem : ∀ t ∈ Ico a b, Icc a b ∈ 𝓝[Ici t] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t ht => (hL t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (fun t ht => (hy t ht).continuousWithinAt)
    (fun t ht => (hy t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (hmem t ht)) (fun _ _ => mem_univ _)
    (fun t ht => (hz t ht).continuousWithinAt)
    (fun t ht => (hz t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (hmem t ht)) (fun _ _ => mem_univ _) h0

end Lightlike.ODE
