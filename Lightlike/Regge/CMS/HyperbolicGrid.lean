import Mathlib
import Lightlike.Regge.CMS.GridExample
import Lightlike.Regge.CMS.Hyperbolic

/-!
# The grid example on the hyperbolic plane: a non-zero curvature integral

On the flat metric the integral term of the grid bound is `0`. For the hyperbolic plane
`dx² + e^{2x} dy²` (scalar curvature `-2`) the same grid satisfies every hypothesis of the
convergence theorem, and the integral over the interior triangles is strictly negative, so the
bound is not a statement about a vanishing term.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- The interior region of the `m × m` grid of mesh `h`: the union of the triangles with all three
corners interior vertices. -/
def gInterior (m : ℕ) (h : ℝ) : Set (Fin 2 → ℝ) :=
  ⋃ t ∈ Finset.univ.filter (fun t : GT m => cornersIn gC (gV m) t = 3), cell (gP h) gC t

theorem gInterior_subset {m : ℕ} {h : ℝ} (hh : 0 < h) :
    gInterior m h ⊆ Icc (0 : Fin 2 → ℝ) (fun _ => h * m) :=
  iUnion₂_subset fun t _ => grid_in_box hh t

theorem measurableSet_gInterior (m : ℕ) (h : ℝ) : MeasurableSet (gInterior m h) :=
  MeasurableSet.biUnion (Finset.countable_toSet _) fun _ _ => measurableSet_tri _ _ _

theorem cornersIn_eq_three {m : ℕ} {t : GT m} :
    cornersIn gC (gV m) t = 3 ↔ ∀ k, gC t k ∈ gV m := by
  unfold cornersIn
  constructor
  · intro h k
    by_contra hk
    have : (Finset.univ.filter fun k : Fin 3 => gC t k ∈ gV m).card < Finset.univ.card :=
      Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => hk
        (by simpa using hsub (Finset.mem_univ k))⟩
    simp at this; omega
  · intro h
    have : (Finset.univ.filter fun k : Fin 3 => gC t k ∈ gV m) = Finset.univ := by
      ext k; simp [h k]
    rw [this]; simp

/-- Every triangle of the grid has area `h² / 2`. -/
theorem grid_cell_volume {m : ℕ} {h : ℝ} (hh : 0 < h) (t : GT m) :
    volume.real (cell (gP h) gC t) = h ^ 2 / 2 := by
  obtain ⟨i, j, b⟩ := t
  rw [cell, Measure.real, volume_tri]
  have : ∀ x : ℝ, 0 ≤ x → ENNReal.toReal (ENNReal.ofReal x) = x := fun x hx =>
    ENNReal.toReal_ofReal hx
  cases b
  · have e : det2 (gP h (gC (i, j, false) 1) - gP h (gC (i, j, false) 0))
        (gP h (gC (i, j, false) 2) - gP h (gC (i, j, false) 0)) = h ^ 2 := by
      simp [gC, gP, det2]; ring
    rw [e, abs_of_pos (by positivity), this _ (by positivity)]
  · have e : det2 (gP h (gC (i, j, true) 1) - gP h (gC (i, j, true) 0))
        (gP h (gC (i, j, true) 2) - gP h (gC (i, j, true) 0)) = h ^ 2 := by
      simp [gC, gP, det2]; ring
    rw [e, abs_of_pos (by positivity), this _ (by positivity)]

/-- The interior region of the `m × m` grid contains at least `2 (m - 2)²` triangles. -/
theorem grid_interior_card_ge (m : ℕ) [NeZero m] :
    2 * (m - 2) ^ 2 ≤ (Finset.univ.filter fun t : GT m => cornersIn gC (gV m) t = 3).card := by
  have key : ∀ (a b : Fin (m - 2)) (c : Bool),
      ((⟨a + 1, by omega⟩ : Fin m), (⟨b + 1, by omega⟩ : Fin m), c) ∈
        Finset.univ.filter fun t : GT m => cornersIn gC (gV m) t = 3 := by
    intro a b c
    have := a.isLt; have := b.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cornersIn_eq_three]
    intro k
    cases c <;> fin_cases k <;> simp [gC, mem_gV] <;> omega
  have hc : (Finset.univ : Finset (Fin (m - 2) × Fin (m - 2) × Bool)).card = 2 * (m - 2) ^ 2 := by
    simp; ring
  rw [← hc]
  refine Finset.card_le_card_of_injOn
    (fun x : Fin (m - 2) × Fin (m - 2) × Bool =>
      ((⟨x.1 + 1, by have := x.1.isLt; omega⟩ : Fin m),
        (⟨x.2.1 + 1, by have := x.2.1.isLt; omega⟩ : Fin m), x.2.2))
    (fun x _ => key x.1 x.2.1 x.2.2) ?_
  rintro ⟨a, b, c⟩ _ ⟨a', b', c'⟩ _ h
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp [Fin.ext_iff, h3]; omega

/-- The area of the interior region is at least `(m - 2)² h²`. -/
theorem gInterior_volume_ge {m : ℕ} [NeZero m] {h : ℝ} (hh : 0 < h) :
    ((m - 2 : ℕ) : ℝ) ^ 2 * h ^ 2 ≤ volume.real (gInterior m h) := by
  unfold gInterior
  rw [measureReal_biUnion_finset₀
    (fun t _ t' _ hne => grid_disjoint hh t t' hne)
    (fun t _ => (measurableSet_tri _ _ _).nullMeasurableSet)
    (fun t _ => by rw [cell, volume_tri]; exact ENNReal.ofReal_ne_top)]
  rw [Finset.sum_congr rfl fun t _ => grid_cell_volume hh t, Finset.sum_const, nsmul_eq_mul]
  have := grid_interior_card_ge m
  have h2 : (2 : ℝ) * ((m - 2 : ℕ) : ℝ) ^ 2 ≤ ((Finset.univ.filter fun t : GT m =>
      cornersIn gC (gV m) t = 3).card : ℝ) := by exact_mod_cast this
  nlinarith [sq_nonneg h, pow_pos hh 2]

/-- The integrand of the grid bound for `hypMetric` and the weight `1` is `-e^{x₀}`. -/
theorem hyp_integrand (x : Fin 2 → ℝ) :
    (fun _ : Fin 2 → ℝ => (1 : ℝ)) x * (scalarCurvature hypMetric x / 2 * √(hypMetric x).det) =
      -exp (x 0) := by
  have hd : (hypMetric x).det = exp (x 0) ^ 2 := by
    simp [hypMetric, Matrix.det_diagonal, hypD, Fin.prod_univ_two, ← exp_nat_mul]
  rw [scalar_hyp, hd, Real.sqrt_sq (exp_pos _).le]
  ring

/-- **Non-zero integral.** On the `m × m` grid of mesh `h`, the curvature integral of the
hyperbolic plane over the interior triangles is `≤ -(m - 2)² h² < 0` for `m ≥ 3`. -/
theorem hyp_integral_neg {m : ℕ} [NeZero m] (hm : 3 ≤ m) {h : ℝ} (hh : 0 < h) :
    ∫ x in gInterior m h, (fun _ : Fin 2 → ℝ => (1 : ℝ)) x *
        (scalarCurvature hypMetric x / 2 * √(hypMetric x).det) ≤ -(((m - 2 : ℕ) : ℝ) ^ 2 * h ^ 2) := by
  have hK := gInterior_subset (m := m) hh
  have hfin : volume (gInterior m h) < ⊤ :=
    lt_of_le_of_lt (measure_mono hK) (by rw [Real.volume_Icc_pi]; simp)
  have hint : IntegrableOn (fun x : Fin 2 → ℝ => -exp (x 0)) (gInterior m h) := by
    have : ContinuousOn (fun x : Fin 2 → ℝ => -exp (x 0)) (Icc 0 (fun _ => h * m)) := by fun_prop
    exact (this.integrableOn_Icc).mono_set hK
  simp only [hyp_integrand]
  have hle : ∫ x in gInterior m h, -exp (x 0) ≤ ∫ x in gInterior m h, (-1 : ℝ) := by
    refine setIntegral_mono_on hint (integrableOn_const hfin.ne) (measurableSet_gInterior m h) ?_
    intro x hx
    have : 0 ≤ x 0 := (hK hx).1 0
    have := Real.add_one_le_exp (x 0)
    linarith
  have : ∫ x in gInterior m h, (-1 : ℝ) = -volume.real (gInterior m h) := by
    simp [Measure.real]
  linarith [gInterior_volume_ge (m := m) hh]

/-- **The grid bound on the hyperbolic plane** for `3 × 3` squares, with a strictly negative
integral term for every admissible `h`. -/
theorem hyp_grid_bound :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → h ≤ 1 →
      |∑ v ∈ gV 3, (fun _ : Fin 2 → ℝ => (1 : ℝ)) (gP h v) *
          (2 * π - ∑ j : ZMod 6, triAngle
            (dist hypMetric univ (gP h v) (gP h (gnb v j)) ^ 2)
            (dist hypMetric univ (gP h v) (gP h (gnb v (j + 1))) ^ 2)
            (dist hypMetric univ (gP h (gnb v j)) (gP h (gnb v (j + 1))) ^ 2)) -
        ∫ x in gInterior 3 h, (fun _ : Fin 2 → ℝ => (1 : ℝ)) x *
          (scalarCurvature hypMetric x / 2 * √(hypMetric x).det)| ≤ C * h ∧
      ∫ x in gInterior 3 h, (fun _ : Fin 2 → ℝ => (1 : ℝ)) x *
          (scalarCurvature hypMetric x / 2 * √(hypMetric x).det) < 0 := by
  obtain ⟨C, h₀, hh₀, hmain⟩ := grid_triangulation_bound_of isRiemMetric_hyp
  refine ⟨C, h₀, hh₀, fun h hh a b => ⟨hmain h hh a b, ?_⟩⟩
  have := hyp_integral_neg (m := 3) (le_refl 3) hh
  refine lt_of_le_of_lt this ?_
  have : (0 : ℝ) < ((3 - 2 : ℕ) : ℝ) ^ 2 * h ^ 2 := by norm_num; positivity
  linarith

end Lightlike.CMS
