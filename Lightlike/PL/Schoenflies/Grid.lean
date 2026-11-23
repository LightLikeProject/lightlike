import Mathlib

/-!
# Grid squares around a compact set

Row G3-188, milestone PL5 (third pass), item 5b, route A (exhaustion of the inner region by polygons).
A compact set `C` inside an open set `U` of the plane is covered by finitely many closed grid squares of a
small mesh `δ` that meet `C`, and the slightly inflated squares (`box`, inflation `δ/4`) still lie in `U`.
The inflation is what makes the boundary of the union free of pinch points later on.

* `cell δ q`, `box δ ε q`: the closed grid square of mesh `δ` with lower-left corner `δ q`, and its
  inflation by `ε`.
* `exists_grid_cover`: the finite cover by squares meeting `C`.
-/

namespace Lightlike.PL.Schoenflies

open Set Metric

/-- The closed grid square of mesh `δ` with lower-left corner `(q.1 δ, q.2 δ)`. -/
def cell (δ : ℝ) (q : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Icc ((q.1 : ℝ) * δ) (((q.1 : ℝ) + 1) * δ) ×ˢ Icc ((q.2 : ℝ) * δ) (((q.2 : ℝ) + 1) * δ)

/-- The grid square `cell δ q` inflated by `ε` on every side. -/
def box (δ ε : ℝ) (q : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Icc ((q.1 : ℝ) * δ - ε) (((q.1 : ℝ) + 1) * δ + ε) ×ˢ
    Icc ((q.2 : ℝ) * δ - ε) (((q.2 : ℝ) + 1) * δ + ε)

lemma cell_subset_box {δ ε : ℝ} (hε : 0 ≤ ε) (q : ℤ × ℤ) : cell δ q ⊆ box δ ε q := by
  rintro ⟨x, y⟩ ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Every point lies in the grid square of its floors. -/
lemma mem_cell_floor {δ : ℝ} (hδ : 0 < δ) (c : ℝ × ℝ) : c ∈ cell δ (⌊c.1 / δ⌋, ⌊c.2 / δ⌋) := by
  have h1 := Int.floor_le (c.1 / δ)
  have h2 := Int.lt_floor_add_one (c.1 / δ)
  have h3 := Int.floor_le (c.2 / δ)
  have h4 := Int.lt_floor_add_one (c.2 / δ)
  rw [le_div_iff₀ hδ] at h1 h3
  rw [div_lt_iff₀ hδ] at h2 h4
  exact ⟨⟨h1, h2.le⟩, ⟨h3, h4.le⟩⟩

/-- A point of an inflated square is within `δ + ε` of every point of the square. -/
lemma dist_le_of_mem_box {δ ε : ℝ} {q : ℤ × ℤ} {z c : ℝ × ℝ} (hz : z ∈ box δ ε q)
    (hc : c ∈ cell δ q) : dist z c ≤ δ + ε := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  obtain ⟨⟨k1, k2⟩, ⟨k3, k4⟩⟩ := hc
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  refine max_le ?_ ?_
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- **Finite grid cover.** A compact `C` inside an open `U` is covered by finitely many closed grid squares of
some mesh `δ`, each meeting `C`, whose inflations by `δ / 4` lie in `U`. -/
theorem exists_grid_cover {C U : Set (ℝ × ℝ)} (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Finset (ℤ × ℤ), C ⊆ ⋃ q ∈ F, cell δ q ∧
      (∀ q ∈ F, (cell δ q ∩ C).Nonempty) ∧ ∀ q ∈ F, box δ (δ / 4) q ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hC.exists_cthickening_subset_open hU hCU
  set δ : ℝ := r / 2 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : ℝ × ℝ)
  have hfin : {q : ℤ × ℤ | (cell δ q ∩ C).Nonempty}.Finite := by
    refine Set.Finite.subset ((Set.finite_Icc (⌊-R / δ - 1⌋) ⌈R / δ⌉).prod
      (Set.finite_Icc (⌊-R / δ - 1⌋) ⌈R / δ⌉)) ?_
    rintro q ⟨c, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hcC⟩
    have hb := hR hcC
    rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_le, abs_le] at hb
    obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := hb
    have e1 : (q.1 : ℝ) ≤ R / δ := by rw [le_div_iff₀ hδ]; linarith
    have e2 : (q.2 : ℝ) ≤ R / δ := by rw [le_div_iff₀ hδ]; linarith
    have e3 : -R / δ - 1 ≤ (q.1 : ℝ) := by
      have : -R ≤ ((q.1 : ℝ) + 1) * δ := by linarith
      have h := (div_le_iff₀ hδ).2 (show -R ≤ ((q.1 : ℝ) + 1) * δ from this)
      linarith
    have e4 : -R / δ - 1 ≤ (q.2 : ℝ) := by
      have : -R ≤ ((q.2 : ℝ) + 1) * δ := by linarith
      have h := (div_le_iff₀ hδ).2 (show -R ≤ ((q.2 : ℝ) + 1) * δ from this)
      linarith
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have := Int.floor_le (-R / δ - 1); exact_mod_cast this.trans e3
    · exact Int.cast_le.1 (e1.trans (Int.le_ceil _))
    · have := Int.floor_le (-R / δ - 1); exact_mod_cast this.trans e4
    · exact Int.cast_le.1 (e2.trans (Int.le_ceil _))
  refine ⟨δ, hδ, hfin.toFinset, ?_, ?_, ?_⟩
  · intro c hc
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨(⌊c.1 / δ⌋, ⌊c.2 / δ⌋), ⟨c, mem_cell_floor hδ c, hc⟩, mem_cell_floor hδ c⟩
  · intro q hq
    exact (Set.Finite.mem_toFinset hfin).1 hq
  · intro q hq z hz
    obtain ⟨c, hcq, hcC⟩ := (Set.Finite.mem_toFinset hfin).1 hq
    apply hrU
    refine Metric.mem_cthickening_of_dist_le z c r C hcC ?_
    have := dist_le_of_mem_box hz hcq
    rw [hδdef] at this
    linarith

end Lightlike.PL.Schoenflies
