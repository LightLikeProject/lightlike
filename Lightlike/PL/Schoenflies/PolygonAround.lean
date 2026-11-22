import Lightlike.PL.Schoenflies.CarrierBox
import Lightlike.PL.Schoenflies.PolygonScale
import Lightlike.PL.Schoenflies.Grid
import Lightlike.PL.Schoenflies.LatticePoly

/-!
# A simple polygon around a compact connected set inside an open set

Row G3-188, milestone PL5 (third pass), item 5b, route A.  For a nonempty compact connected `C` inside an
open `U ⊆ ℝ²` there is a simple polygon `p` with `p.carrier ⊆ U` and `C` inside the class of crossing parity
`1` of `p` (the bounded component, by `Polygon.polygon_jordan`).  The polygon is the rescaling, by
`h = δ / 4`, of the boundary polygon of the lattice squares coming from `exists_grid_cover`.

* `smul_cell_mem_openBoxU`: a point of a grid square, in units of `δ / 4`, lies in the open inflated square.
* `smul_closedBoxU_subset_box`: the rescaled closed inflated square is the geometric `box δ (δ/4) q`.
* `exists_simple_polygon_around`: the theorem.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- A point of the grid square `cell δ q`, in units of `δ / 4`, lies in the open inflated square. -/
lemma smul_cell_mem_openBoxU {δ : ℝ} (hδ : 0 < δ) {q : ℤ × ℤ} {w : ℝ × ℝ} (hw : w ∈ cell δ q) :
    (δ / 4)⁻¹ • w ∈ openBoxU q := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hw
  have key : ∀ a : ℝ, (δ / 4)⁻¹ * a = 4 * (a / δ) := by
    intro a; field_simp
  have e1 : (q.1 : ℝ) ≤ w.1 / δ := by rw [le_div_iff₀ hδ]; exact h1
  have e2 : w.1 / δ ≤ (q.1 : ℝ) + 1 := by rw [div_le_iff₀ hδ]; exact h2
  have e3 : (q.2 : ℝ) ≤ w.2 / δ := by rw [le_div_iff₀ hδ]; exact h3
  have e4 : w.2 / δ ≤ (q.2 : ℝ) + 1 := by rw [div_le_iff₀ hδ]; exact h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, key] <;> linarith

/-- The rescaled closed inflated square lies in the geometric inflated square. -/
lemma smul_closedBoxU_subset_box {δ : ℝ} (hδ : 0 < δ) (q : ℤ × ℤ) {c : ℝ × ℝ}
    (hc : c ∈ closedBoxU q) : (δ / 4) • c ∈ box δ (δ / 4) q := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hh : 0 ≤ δ / 4 := by positivity
  have m1 := mul_le_mul_of_nonneg_left h1 hh
  have m2 := mul_le_mul_of_nonneg_left h2 hh
  have m3 := mul_le_mul_of_nonneg_left h3 hh
  have m4 := mul_le_mul_of_nonneg_left h4 hh
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith

/-- **A simple polygon around a compact connected set.**  A nonempty compact connected `C` inside an open
`U ⊆ ℝ²` lies in the crossing-parity-`1` class of a simple polygon whose carrier is contained in `U`. -/
theorem exists_simple_polygon_around {C U : Set (ℝ × ℝ)} (hC : IsCompact C) (hCc : IsPreconnected C)
    (hne : C.Nonempty) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ (n : ℕ) (p : Polygon n), p.IsSimple ∧ p.carrier ⊆ U ∧
      ∀ z ∈ C, z ∉ p.carrier ∧ p.parity z = 1 := by
  obtain ⟨δ, hδ, F, hcov, hmeet, hbox⟩ := exists_grid_cover hC hU hCU
  obtain ⟨z0, hz0⟩ := hne
  have hF : F.Nonempty := by
    obtain ⟨q, hq, -⟩ := Set.mem_iUnion₂.1 (hcov hz0)
    exact ⟨q, hq⟩
  set h : ℝ := δ / 4 with hhdef
  have hpos : 0 < h := by positivity
  have hne' : h ≠ 0 := hpos.ne'
  set C' : Set (ℝ × ℝ) := (fun z => h⁻¹ • z) '' C with hC'
  have hC'c : IsPreconnected C' := hCc.image _ (continuous_const_smul _).continuousOn
  have hCF : C' ⊆ ⋃ q ∈ F, openBoxU q := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨q, hq, hwq⟩ := Set.mem_iUnion₂.1 (hcov hw)
    exact Set.mem_iUnion₂.2 ⟨q, hq, smul_cell_mem_openBoxU hδ hwq⟩
  have hmeet' : ∀ q ∈ F, (C' ∩ openBoxU q).Nonempty := by
    intro q hq
    obtain ⟨w, hwq, hwC⟩ := hmeet q hq
    exact ⟨_, ⟨w, hwC, rfl⟩, smul_cell_mem_openBoxU hδ hwq⟩
  obtain ⟨n, v, hn, hv, hadj, hsimp, hC'p⟩ := exists_polygon_inside_connected F hF hC'c hCF hmeet'
  refine ⟨n, fun i => h • latticePoly v i, smul_isSimple hsimp hne', ?_, ?_⟩
  · intro z hz
    rw [carrier_smul] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    obtain ⟨q, hq, hcq⟩ := Set.mem_iUnion₂.1 (carrier_subset_closedBox hadj hc)
    exact hbox q hq (smul_closedBoxU_subset_box hδ q hcq)
  · intro z hz
    have hzC' : h⁻¹ • z ∈ C' := ⟨z, hz, rfl⟩
    obtain ⟨hnot, hpar⟩ := hC'p _ hzC'
    refine ⟨?_, ?_⟩
    · rw [carrier_smul]
      rintro ⟨c, hc, hcz⟩
      apply hnot
      have : h⁻¹ • z = c := by rw [← hcz, inv_smul_smul₀ hne']
      rw [this]; exact hc
    · have := parity_smul (latticePoly v) hpos (h⁻¹ • z)
      rw [smul_inv_smul₀ hne'] at this
      rw [this]; exact hpar

end Lightlike.PL.Schoenflies
