import Lightlike.Rows.G2_008.Existence

/-!
# Positivity of the extended functional (row G2-008)

The extended functional `lamL` is positive (`lamL_nonneg`): a nonnegative continuous function is
uniformly approximated by cylindrical functions `G`, which are `≥ -ε`, and `lam` of such a function
is `≥ -ε` because the bonding maps are surjective and the `μ i` are probability measures.
-/

noncomputable section

open MeasureTheory Set

namespace Lightlike.Rows.G2_008

namespace InvSystem

variable {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
variable (S : InvSystem ι X)
variable [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
variable [Nonempty ι] [IsDirectedOrder ι] [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
variable (hS : ∀ {i j : ι} (h : i ≤ j), Function.Surjective (S.f h))
variable {μ : ∀ i, Measure (X i)} (hμ : S.IsConsistent μ) (hp : ∀ i, IsProbabilityMeasure (μ i))

include hS hμ hp in
/-- A cylindrical function bounded below by `-ε` has `lamL ≥ -ε`. -/
lemma lamL_cyl_ge (i : ι) (φ : C(X i, ℝ)) {ε : ℝ} (h : ∀ x, -ε ≤ S.cyl i φ x) :
    -ε ≤ S.lamL hS hμ hp (S.cyl i φ) := by
  rw [S.lamL_cyl hS hμ hp]
  have := hp i
  have hb : ∀ y, -ε ≤ φ y := by
    intro y
    obtain ⟨x, rfl⟩ := S.proj_surjective hS i y
    simpa using h x
  have := integral_mono (μ := μ i) (integrable_const (-ε)) (integrable_cont hp φ) hb
  simpa using this

include hS hμ hp in
/-- **Positivity**: `lamL F ≥ 0` for `F ≥ 0`. -/
lemma lamL_nonneg (F : C(S.Limit, ℝ)) (hF : 0 ≤ F) : 0 ≤ S.lamL hS hμ hp F := by
  set L := S.lamL hS hμ hp with hL
  have key : ∀ ε : ℝ, 0 < ε → -((1 + ‖L‖) * ε) ≤ L F := by
    intro ε hε
    obtain ⟨y, hy⟩ := (Metric.denseRange_iff.1 S.denseRange_cylSubalgebra_val) F ε hε
    obtain ⟨i, φ, hG⟩ := S.exists_cyl y
    have hy' : dist F (y : C(S.Limit, ℝ)) < ε := by simpa using hy
    have hpt : ∀ x, -ε ≤ S.cyl i φ x := by
      intro x
      rw [← hG]
      have h1 := ContinuousMap.dist_apply_le_dist (f := F) (g := (y : C(S.Limit, ℝ))) x
      have h2 : 0 ≤ F x := hF x
      rw [Real.dist_eq] at h1
      have := (abs_le.1 h1).2
      linarith [le_of_lt hy']
    have hge := S.lamL_cyl_ge hS hμ hp i φ hpt
    have hd : ‖F - S.cyl i φ‖ < ε := by
      rw [← hG, ← dist_eq_norm]; exact hy'
    have hb : |L (F - S.cyl i φ)| ≤ ‖L‖ * ε := by
      have := L.le_opNorm (F - S.cyl i φ)
      rw [Real.norm_eq_abs] at this
      calc |L (F - S.cyl i φ)| ≤ ‖L‖ * ‖F - S.cyl i φ‖ := this
        _ ≤ ‖L‖ * ε := by gcongr
    have hsub : L F = L (S.cyl i φ) + L (F - S.cyl i φ) := by
      rw [← map_add]; congr 1; abel
    have := (abs_le.1 hb).1
    nlinarith
  by_contra hneg
  rw [not_le] at hneg
  have hpos : 0 < 1 + ‖L‖ := by positivity
  have := key (-(L F) / (2 * (1 + ‖L‖))) (by apply div_pos <;> linarith)
  have e : (1 + ‖L‖) * (-(L F) / (2 * (1 + ‖L‖))) = -(L F) / 2 := by
    field_simp
  rw [e] at this
  linarith

end InvSystem

end Lightlike.Rows.G2_008
