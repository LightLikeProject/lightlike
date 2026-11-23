import Mathlib
import Lightlike.Spacetime.GreenOperators.MassiveSupport
import Lightlike.Spacetime.GreenOperators.MassiveAdvanced

/-!
# Green operator identities for Klein–Gordon on 1+1 Minkowski space

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
If `g` is `C⁴` with compact support, then `kgOp m g` is `C²` with compact support
(`kgOp_contDiff`, `kgOp_hasCompactSupport`), so the retarded and advanced solutions of
`kgOp m u = kgOp m g` are defined, and by uniqueness they equal `g` (`massiveSol_kgOp`,
`massiveAdvancedSol_kgOp`): the identities `G± P = id` on test functions.
-/

namespace Lightlike.GreenOperators

/-- A second derivative of a `C^{n+2}` function evaluated on fixed vectors is `C^n`. -/
lemma contDiff_fderiv_fderiv_apply {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 4 g) (v w : ℝ × ℝ) :
    ContDiff ℝ 2 (fun p => fderiv ℝ (fderiv ℝ g) p v w) := by
  have h1 : ContDiff ℝ 3 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ g)) := h1.fderiv_right (by norm_num)
  exact (h2.clm_apply contDiff_const).clm_apply contDiff_const

/-- `kgOp m g` is `C²` for `g` of class `C⁴`. -/
theorem kgOp_contDiff (m : ℝ) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 4 g) :
    ContDiff ℝ 2 (kgOp m g) := by
  unfold kgOp
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  exact ((contDiff_fderiv_fderiv_apply hg _ _).neg.add (contDiff_fderiv_fderiv_apply hg _ _)).sub
    (contDiff_const.mul hg2)

/-- `kgOp m g` has compact support if `g` does. -/
theorem kgOp_hasCompactSupport (m : ℝ) {g : ℝ × ℝ → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (kgOp m g) := by
  have h1 : HasCompactSupport (fderiv ℝ g) := hc.fderiv ℝ
  have h2 : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) := h1.fderiv ℝ
  have h3 : ∀ v w : ℝ × ℝ, HasCompactSupport (fun p => fderiv ℝ (fderiv ℝ g) p v w) := by
    intro v w
    exact h2.comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ => L v w) (by simp)
  unfold kgOp
  exact ((h3 _ _).neg.add (h3 _ _)).sub (hc.mul_left)

/-- `g` and `kgOp m g` both vanish for `|t| ≥ R`, for some `R`. -/
lemma exists_time_bound {g : ℝ × ℝ → ℝ} (m : ℝ) (hc : HasCompactSupport g) :
    ∃ R : ℝ, ∀ p : ℝ × ℝ, R ≤ |p.1| → g p = 0 ∧ kgOp m g p = 0 := by
  obtain ⟨R₁, h₁⟩ := exists_box hc
  obtain ⟨R₂, h₂⟩ := exists_box (kgOp_hasCompactSupport m hc)
  refine ⟨max R₁ R₂, fun p hp => ⟨?_, ?_⟩⟩
  · by_contra hne
    have := (h₁ p hne).1
    linarith [le_max_left R₁ R₂]
  · by_contra hne
    have := (h₂ p hne).1
    linarith [le_max_right R₁ R₂]

/-- **`G⁺ P = id` on test functions** (`1+1` Minkowski, any mass): the retarded solution of
`P g` is `g`, for `g` of class `C⁴` with compact support. -/
theorem massiveSol_kgOp (m : ℝ) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 4 g) (hc : HasCompactSupport g) :
    massiveSol m (kgOp m g) = g := by
  obtain ⟨R, hR⟩ := exists_time_bound m hc
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hf := kgOp_contDiff m hg
  have hfc := kgOp_hasCompactSupport m hc
  refine retarded_unique m (-R) (massiveSol_contDiff m hf hfc) hg2
    (fun p => by rw [kgOp_massiveSol m hf hfc]) ?_ ?_
  · refine massiveSol_eq_zero (fun p hp => (hR p ?_).2)
    linarith [neg_le_abs p.1]
  · intro p hp
    refine (hR p ?_).1
    linarith [neg_le_abs p.1]

/-- **`G⁻ P = id` on test functions** (`1+1` Minkowski, any mass). -/
theorem massiveAdvancedSol_kgOp (m : ℝ) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 4 g)
    (hc : HasCompactSupport g) : massiveAdvancedSol m (kgOp m g) = g := by
  obtain ⟨R, hR⟩ := exists_time_bound m hc
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  have hf := kgOp_contDiff m hg
  have hfc := kgOp_hasCompactSupport m hc
  refine advanced_unique m R (massiveAdvancedSol_contDiff m hf hfc) hg2
    (fun p => by rw [kgOp_massiveAdvancedSol m hf hfc]) ?_ ?_
  · refine massiveAdvancedSol_eq_zero (fun p hp => (hR p ?_).2)
    linarith [le_abs_self p.1]
  · intro p hp
    refine (hR p ?_).1
    linarith [le_abs_self p.1]

end Lightlike.GreenOperators
