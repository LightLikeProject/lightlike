import Lightlike.OperatorAlgebras.MomentumSmooth
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollification of the test functions of `momentumMin`

Helper lemmas for `T-OP1-P6` (`Tasks/OP/T_OP1_P6.lean`). For a normed smooth bump function `φ` and a `C²`
function `g` with compact support inside `(0, 1)`, the convolution `φ ⋆ g` is a `C^∞` function with compact
support, its derivative is `φ ⋆ g'`, and it is uniformly close to `g` when the support radius of `φ` is
small (Mathlib: `ContDiffBump.dist_normed_convolution_le`, `HasCompactSupport.hasDerivAt_convolution_right`).
-/

open MeasureTheory Set Metric
open scoped ContDiff Convolution

namespace Lightlike.OperatorAlgebras

/-- The mollification `φ ⋆ g` of `g : ℝ → ℂ` by the normed bump function `φ` (Lebesgue measure). -/
noncomputable def moll (φ : ContDiffBump (0 : ℝ)) (g : ℝ → ℂ) : ℝ → ℂ :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g

variable {φ : ContDiffBump (0 : ℝ)} {g : ℝ → ℂ}

lemma moll_contDiff (hg : Continuous g) : ContDiff ℝ ∞ (moll φ g) := by
  have hcf : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  exact hcf.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed
    (hg.locallyIntegrable)

lemma moll_hasCompactSupport (hcg : HasCompactSupport g) : HasCompactSupport (moll φ g) :=
  φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcg

lemma moll_hasDerivAt (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (x : ℝ) :
    HasDerivAt (moll φ g) (moll φ (deriv g) x) x :=
  hcg.hasDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.continuous_normed.locallyIntegrable) hg x

lemma moll_deriv (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g) :
    deriv (moll φ g) = moll φ (deriv g) :=
  funext fun x => (moll_hasDerivAt hcg hg x).deriv

lemma moll_tsupport_subset : tsupport (moll φ g) ⊆ cthickening φ.rOut (tsupport g) := by
  refine closure_minimal ?_ isClosed_cthickening
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1
    (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hx)
  have ha' : a ∈ ball (0 : ℝ) φ.rOut := by rwa [← φ.support_normed_eq (μ := volume)]
  have hb' : b ∈ tsupport g := subset_closure hb
  refine mem_cthickening_of_dist_le (a + b) b φ.rOut (tsupport g) hb' ?_
  rw [Real.dist_eq]; simp only [add_sub_cancel_right]
  exact (mem_ball_zero_iff.1 ha').le

lemma moll_dist_le (hg : Continuous g) (hcg : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ (φ : ContDiffBump (0 : ℝ)), φ.rOut ≤ r → ∀ x, dist (moll φ g x) (g x) ≤ ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1 (hcg.uniformContinuous_of_continuous hg) ε hε
  refine ⟨δ, hδ, fun φ hφ x => ?_⟩
  exact φ.dist_normed_convolution_le (μ := volume) hg.aestronglyMeasurable
    (fun y hy => (h (mem_ball.1 hy |>.trans_le hφ)).le)

/-- If two continuous functions supported inside `(0, 1)` differ by at most `ε` everywhere, their classes in
`L²(0, 1)` are at distance at most `ε` (the interval has length one). -/
lemma norm_classI_sub_le {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b)
    (hsa : tsupport a ⊆ Ioo (0 : ℝ) 1) (hsb : tsupport b ⊆ Ioo (0 : ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, ‖a x - b x‖ ≤ ε) : ‖classI a ha hsa - classI b hb hsb‖ ≤ ε := by
  have hae : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      ‖(classI a ha hsa - classI b hb hsb : L2I) x‖ ≤ ε := by
    have h1 := Lp.coeFn_sub (classI a ha hsa) (classI b hb hsb)
    have h2 : (classI a ha hsa : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] a :=
      MemLp.coeFn_toLp _
    have h3 : (classI b hb hsb : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] b :=
      MemLp.coeFn_toLp _
    filter_upwards [h1, h2, h3] with x h1 h2 h3
    rw [h1]; simp only [Pi.sub_apply, h2, h3]; exact h x
  have := Lp.norm_le_of_ae_bound hε hae
  refine this.trans (le_of_eq ?_)
  simp [measureUnivNNReal]

/-- A bump function with outer radius `r > 0`. -/
noncomputable def bumpOfRadius (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r / 2, r, half_pos hr, half_lt_self hr⟩

/-- Every point of `momentumGraph` is a limit of points of `momentumGraphSmooth`: mollify the test function
and its derivative. -/
theorem momentumGraph_le_closure : momentumGraph ≤ momentumGraphSmooth.topologicalClosure := by
  rintro x ⟨f, -, rfl⟩
  have hx : momentumPairLin f ∈ closure (momentumGraphSmooth : Set (L2I × L2I)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set g : ℝ → ℂ := f.1 with hg
    have hg2 : ContDiff ℝ 2 g := f.2.1
    have hsg : tsupport g ⊆ Ioo (0 : ℝ) 1 := f.2.2
    have hcg : HasCompactSupport g := hasCompactSupport_of_tsupport_subset hsg
    have hg' : Continuous (deriv g) := continuous_deriv_of_two hg2
    have hcg' : HasCompactSupport (deriv g) := hcg.deriv
    have hsg' : tsupport (deriv g) ⊆ Ioo (0 : ℝ) 1 := tsupport_deriv_subset.trans hsg
    have hε4 : 0 < ε / 4 := by positivity
    obtain ⟨r1, hr1, h1⟩ := moll_dist_le hg2.continuous hcg hε4
    obtain ⟨r2, hr2, h2⟩ := moll_dist_le hg' hcg' hε4
    obtain ⟨δ, hδ, hth⟩ := hcg.isCompact.exists_cthickening_subset_open isOpen_Ioo hsg
    set r := min (min r1 r2) δ with hr
    have hrpos : 0 < r := lt_min (lt_min hr1 hr2) hδ
    set φ := bumpOfRadius r hrpos with hφ
    have hrO : φ.rOut = r := rfl
    have hsupp : tsupport (moll φ g) ⊆ Ioo (0 : ℝ) 1 :=
      (moll_tsupport_subset (φ := φ) (g := g)).trans
        ((cthickening_mono (by rw [hrO]; exact min_le_right _ _) _).trans hth)
    have hcont : ContDiff ℝ ∞ (moll φ g) := moll_contDiff hg2.continuous
    have hmem : moll φ g ∈ testFunctions := ⟨hcont.of_le (by norm_num), hsupp⟩
    set h : testFunctions := ⟨moll φ g, hmem⟩
    have hsm : h ∈ smoothTestFunctions := hcont
    refine ⟨momentumPairLin h, Submodule.mem_map_of_mem hsm, ?_⟩
    have hd : deriv (moll φ g) = moll φ (deriv g) := moll_deriv hcg (hg2.of_le (by norm_num))
    have hsd : tsupport (deriv (moll φ g)) ⊆ Ioo (0 : ℝ) 1 := tsupport_deriv_subset.trans hsupp
    have e1 : ‖classI g hg2.continuous hsg - classI (moll φ g) hcont.continuous hsupp‖ ≤ ε / 4 := by
      refine norm_classI_sub_le _ _ _ _ hε4.le fun x => ?_
      rw [← dist_eq_norm, dist_comm]
      exact h1 φ (by rw [hrO]; exact (min_le_left _ _).trans (min_le_left _ _)) x
    have e2 : ‖classI (deriv g) hg' hsg' - classI (deriv (moll φ g))
        (continuous_deriv_of_two (hcont.of_le (by norm_num))) hsd‖ ≤ ε / 4 := by
      refine norm_classI_sub_le _ _ _ _ hε4.le fun x => ?_
      rw [← dist_eq_norm, dist_comm, hd]
      exact h2 φ (by rw [hrO]; exact (min_le_left _ _).trans (min_le_right _ _)) x
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · show dist (classI g hg2.continuous hsg) (classI (moll φ g) hcont.continuous hsupp) < ε
      rw [dist_eq_norm]; linarith
    · show dist ((-Complex.I) • classI (deriv g) hg' hsg')
        ((-Complex.I) • classI (deriv (moll φ g))
          (continuous_deriv_of_two (hcont.of_le (by norm_num))) hsd) < ε
      rw [dist_eq_norm, ← smul_sub, norm_smul]
      simp only [norm_neg, Complex.norm_I, one_mul]
      linarith
  exact hx

/-- **The closure of `-i d/dx` on `L²(0, 1)` does not depend on the class of test functions.** -/
theorem closure_momentumGraphSmooth_eq :
    momentumGraphSmooth.topologicalClosure = momentumGraph.topologicalClosure :=
  le_antisymm (Submodule.topologicalClosure_mono momentumGraphSmooth_le)
    (Submodule.topologicalClosure_minimal _ momentumGraph_le_closure
      (Submodule.isClosed_topologicalClosure _))

end Lightlike.OperatorAlgebras
