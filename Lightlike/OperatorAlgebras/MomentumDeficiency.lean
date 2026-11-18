import Lightlike.OperatorAlgebras.MomentumSmooth
import Lightlike.OperatorAlgebras.Deficiency
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The deficiency indices of `-i d/dx` on `L²(0, 1)`

Helper lemmas for `T-OP1-P5` (`Tasks/OP/T_OP1_P5.lean`).
-/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace Lightlike.OperatorAlgebras

/-- A vector is in the domain of `momentumMin` iff it is the class of a `C²` test function. -/
lemma mem_momentumMin_domain {x : L2I} :
    x ∈ momentumMin.domain ↔ ∃ f : testFunctions, classI f.1 f.2.1.continuous f.2.2 = x := by
  constructor
  · intro hx
    have hg : (x, momentumMin ⟨x, hx⟩) ∈ momentumMin.graph := by
      rw [LinearPMap.mem_graph_iff]; exact ⟨⟨x, hx⟩, rfl, rfl⟩
    rw [momentumMin_graph] at hg
    obtain ⟨f, -, hf⟩ := hg
    exact ⟨f, congrArg Prod.fst hf⟩
  · rintro ⟨f, rfl⟩
    have hg : momentumPair f ∈ momentumGraph := ⟨f, trivial, rfl⟩
    rw [← momentumMin_graph] at hg
    exact LinearPMap.mem_domain_of_mem_graph hg

/-- `momentumMin` maps the class of a test function `f` to `-i` times the class of `f'`. -/
lemma momentumMin_apply (f : testFunctions) (hx : (momentumPair f).1 ∈ momentumMin.domain) :
    momentumMin ⟨(momentumPair f).1, hx⟩ = (momentumPair f).2 := by
  have hg : momentumPair f ∈ momentumMin.graph := by
    rw [momentumMin_graph]; exact ⟨f, trivial, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 hg
  have : y = ⟨(momentumPair f).1, hx⟩ := Subtype.ext hy1
  rw [← this]; exact hy2

/-- A real smooth function with compact support inside `(0, 1)`, as a `C²` test function. -/
lemma realTest_mem {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo (0 : ℝ) 1) :
    (fun x => (g x : ℂ)) ∈ testFunctions := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp hg).of_le (by norm_num), ?_⟩
  refine (closure_mono ?_).trans hs
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  exact fun h => hx (by simp [h])

/-- A vector of `L²(0, 1)` orthogonal to all test functions is zero. -/
lemma eq_zero_of_orthogonal {y : L2I} (h : ∀ f : testFunctions, ⟪classI f.1 f.2.1.continuous f.2.2, y⟫_ℂ = 0) :
    y = 0 := by
  have hint : Integrable (fun x => (y : ℝ → ℂ) x) ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) :=
    (Lp.memLp y).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hloc : LocallyIntegrableOn (fun x => (y : ℝ → ℂ) x) (Ioo (0 : ℝ) 1)
      ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) :=
    hint.locallyIntegrable.locallyIntegrableOn _
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
    intro g hg hc hs
    have h0 := h ⟨fun x => (g x : ℂ), realTest_mem hg hc hs⟩
    rw [MeasureTheory.L2.inner_def] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    have h1 : (classI (fun x => (g x : ℂ)) (realTest_mem hg hc hs).1.continuous
        (realTest_mem hg hc hs).2 : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)]
        fun x => (g x : ℂ) := MemLp.coeFn_toLp _
    filter_upwards [h1] with x hx
    simp only [hx]
    simp [Complex.real_smul, mul_comm])
  have hy0 : (y : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxU
    exact hx hxU
  exact (Lp.eq_zero_iff_ae_eq_zero).2 hy0

/-- **The domain of `momentumMin` is dense in `L²(0, 1)`.** -/
theorem dense_momentumMin_domain : Dense (momentumMin.domain : Set L2I) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  exact eq_zero_of_orthogonal fun f => hy _ (mem_momentumMin_domain.2 ⟨f, rfl⟩)

end Lightlike.OperatorAlgebras
