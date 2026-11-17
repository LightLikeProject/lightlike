import Lightlike.OperatorAlgebras.GeneratorTranslation
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.LinearAlgebra.LinearPMap

/-!
# The momentum operator on `L²(0, 1)` without boundary conditions

`L2I` is `L²(0, 1)` (the endpoints are null sets, so it is `L²[0, 1]`). The operator `momentumMin` is
`-i d/dx` on the `C²` functions with compact support inside `(0, 1)`, which is the operator without any
boundary condition. It is built from its graph (`momentumGraph`), which is the graph of a function because a
continuous function that vanishes almost everywhere on `(0, 1)` and is supported inside it is zero.

Its deficiency indices are the dimensions of the kernels of `A† ∓ i`, `deficiencyDim`; the milestone check
`T-OP1-P5` says they are `(1, 1)`.
-/

open MeasureTheory Set

namespace Lightlike.OperatorAlgebras

/-- The Hilbert space `L²(0, 1)` of complex functions (the same space as `L²[0, 1]`). -/
abbrev L2I : Type := Lp ℂ 2 ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))

/-- A function `f` supported inside `(0, 1)` has compact support. -/
lemma hasCompactSupport_of_tsupport_subset {f : ℝ → ℂ} (hs : tsupport f ⊆ Ioo (0 : ℝ) 1) :
    HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) (hs.trans Ioo_subset_Icc_self)

/-- The class in `L²(0, 1)` of a continuous function supported inside `(0, 1)`. -/
noncomputable def classI (f : ℝ → ℂ) (hf : Continuous f) (hs : tsupport f ⊆ Ioo (0 : ℝ) 1) : L2I :=
  (hf.memLp_of_hasCompactSupport (p := 2)
    (μ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) (hasCompactSupport_of_tsupport_subset hs)).toLp f

/-- The class of the sum is the sum of the classes. -/
lemma classI_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hsf : tsupport f ⊆ Ioo (0 : ℝ) 1) (hsg : tsupport g ⊆ Ioo (0 : ℝ) 1)
    (h : Continuous (f + g)) (hs : tsupport (f + g) ⊆ Ioo (0 : ℝ) 1) :
    classI (f + g) h hs = classI f hf hsf + classI g hg hsg := by
  unfold classI
  exact MemLp.toLp_add _ _

/-- The class of a scalar multiple is the scalar multiple of the class. -/
lemma classI_smul {f : ℝ → ℂ} (c : ℂ) (hf : Continuous f) (hsf : tsupport f ⊆ Ioo (0 : ℝ) 1)
    (h : Continuous (c • f)) (hs : tsupport (c • f) ⊆ Ioo (0 : ℝ) 1) :
    classI (c • f) h hs = c • classI f hf hsf := by
  unfold classI
  exact MemLp.toLp_const_smul _ _

/-- A function that is zero has class zero. -/
lemma classI_zero {f : ℝ → ℂ} (hf : Continuous f) (hs : tsupport f ⊆ Ioo (0 : ℝ) 1) (h0 : f = 0) :
    classI f hf hs = 0 := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (hf.memLp_of_hasCompactSupport (p := 2)
    (μ := (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) (hasCompactSupport_of_tsupport_subset hs)),
    Lp.coeFn_zero ℂ 2 ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1))] with x h1 h2
  rw [h2]
  have h1' : (classI f hf hs : ℝ → ℂ) x = f x := h1
  rw [h1', h0]

/-- A continuous function supported inside `(0, 1)` whose class is zero is zero. -/
lemma eq_zero_of_classI_eq_zero {f : ℝ → ℂ} (hf : Continuous f) (hs : tsupport f ⊆ Ioo (0 : ℝ) 1)
    (h : classI f hf hs = 0) : f = 0 := by
  have hae : f =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] 0 := by
    have := (Lp.eq_zero_iff_ae_eq_zero (f := classI f hf hs)).mp h
    refine (MemLp.coeFn_toLp _).symm.trans (this.trans ?_)
    exact Filter.EventuallyEq.rfl
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo hf.continuousOn continuousOn_const
  funext x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · exact heq hx
  · exact image_eq_zero_of_notMem_tsupport fun hm => hx (hs hm)

/-- The `C²` functions supported inside `(0, 1)`, as a subspace of all functions. -/
def testFunctions : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ 2 f ∧ tsupport f ⊆ Ioo (0 : ℝ) 1}
  add_mem' := by
    rintro f g ⟨hf, hsf⟩ ⟨hg, hsg⟩
    refine ⟨hf.add hg, ?_⟩
    refine (closure_mono (Function.support_add f g)).trans ?_
    rw [closure_union]
    exact union_subset hsf hsg
  zero_mem' := ⟨contDiff_const, by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hsf⟩
    exact ⟨hf.const_smul c, (tsupport_smul_subset_right (fun _ => c) f).trans hsf⟩

/-- The pair `(ψ, -i ψ')` of classes of a test function `ψ`. -/
noncomputable def momentumPair (f : testFunctions) : L2I × L2I :=
  (classI f.1 f.2.1.continuous f.2.2,
    (-Complex.I) • classI (deriv f.1) (continuous_deriv_of_two f.2.1)
      ((tsupport_deriv_subset).trans f.2.2))

/-- Equal functions have equal classes, whatever the proofs. -/
lemma classI_congr {f g : ℝ → ℂ} (h : f = g) (hf : Continuous f) (hg : Continuous g)
    (hsf : tsupport f ⊆ Ioo (0 : ℝ) 1) (hsg : tsupport g ⊆ Ioo (0 : ℝ) 1) :
    classI f hf hsf = classI g hg hsg := by
  subst h; rfl

/-- The pair map `f ↦ (ψ, -i ψ')` is additive. -/
lemma momentumPair_add (f g : testFunctions) :
    momentumPair (f + g) = momentumPair f + momentumPair g := by
  have hd : deriv (f + g : testFunctions).1 = deriv f.1 + deriv g.1 := by
    funext x
    exact deriv_add (f.2.1.differentiable (by norm_num) x) (g.2.1.differentiable (by norm_num) x)
  have hc1 : Continuous (deriv f.1) := continuous_deriv_of_two f.2.1
  have hc2 : Continuous (deriv g.1) := continuous_deriv_of_two g.2.1
  have hs1 : tsupport (deriv f.1) ⊆ Ioo (0 : ℝ) 1 := (tsupport_deriv_subset).trans f.2.2
  have hs2 : tsupport (deriv g.1) ⊆ Ioo (0 : ℝ) 1 := (tsupport_deriv_subset).trans g.2.2
  have hs3 : tsupport (deriv f.1 + deriv g.1) ⊆ Ioo (0 : ℝ) 1 := by
    refine (closure_mono (Function.support_add _ _)).trans ?_
    rw [closure_union]
    exact union_subset hs1 hs2
  refine Prod.ext ?_ ?_
  · exact classI_add f.2.1.continuous g.2.1.continuous f.2.2 g.2.2 (f + g).2.1.continuous (f + g).2.2
  · show (-Complex.I) • classI (deriv (f + g : testFunctions).1) _ _ =
      (-Complex.I) • classI (deriv f.1) hc1 hs1 + (-Complex.I) • classI (deriv g.1) hc2 hs2
    rw [← smul_add, ← classI_add hc1 hc2 hs1 hs2 (hc1.add hc2) hs3]
    congr 1
    exact classI_congr hd _ _ _ _

/-- The pair map `f ↦ (ψ, -i ψ')` is homogeneous. -/
lemma momentumPair_smul (c : ℂ) (f : testFunctions) :
    momentumPair (c • f) = c • momentumPair f := by
  have hd : deriv (c • f : testFunctions).1 = c • deriv f.1 := by
    funext x
    exact deriv_const_smul c (f.2.1.differentiable (by norm_num) x)
  have hc1 : Continuous (deriv f.1) := continuous_deriv_of_two f.2.1
  have hs1 : tsupport (deriv f.1) ⊆ Ioo (0 : ℝ) 1 := (tsupport_deriv_subset).trans f.2.2
  have hs3 : tsupport (c • deriv f.1) ⊆ Ioo (0 : ℝ) 1 :=
    (tsupport_smul_subset_right (fun _ => c) _).trans hs1
  refine Prod.ext ?_ ?_
  · exact classI_smul c f.2.1.continuous f.2.2 (c • f).2.1.continuous (c • f).2.2
  · show (-Complex.I) • classI (deriv (c • f : testFunctions).1) _ _ =
      c • ((-Complex.I) • classI (deriv f.1) hc1 hs1)
    rw [smul_comm, ← classI_smul c hc1 hs1 (hc1.const_smul c) hs3]
    congr 1
    exact classI_congr hd _ _ _ _

/-- **The graph of `-i d/dx` on `C²` functions supported inside `(0, 1)`**, as a subspace of
`L²(0, 1) × L²(0, 1)`. -/
noncomputable def momentumGraph : Submodule ℂ (L2I × L2I) :=
  Submodule.map
    (({ toFun := momentumPair, map_add' := momentumPair_add,
        map_smul' := fun c f => by simpa using momentumPair_smul c f } :
      testFunctions →ₗ[ℂ] L2I × L2I)) ⊤

/-- The graph `momentumGraph` is the graph of a function: if the first component is `0`, so is the
second. -/
lemma momentumGraph_fun : ∀ (x : L2I × L2I), x ∈ momentumGraph → x.fst = 0 → x.snd = 0 := by
  rintro x ⟨f, -, rfl⟩ h0
  have h1 : f.1 = 0 := eq_zero_of_classI_eq_zero f.2.1.continuous f.2.2 h0
  have h2 : deriv f.1 = 0 := by
    rw [h1]
    funext x
    exact deriv_const x (0 : ℂ)
  show (-Complex.I) • classI (deriv f.1) _ _ = 0
  rw [classI_zero _ _ h2, smul_zero]

/-- **The momentum operator on `L²(0, 1)` without boundary conditions**: `-i d/dx` on the `C²` functions
supported inside `(0, 1)`. -/
noncomputable def momentumMin : L2I →ₗ.[ℂ] L2I := momentumGraph.toLinearPMap

/-- The graph of `momentumMin` is `momentumGraph`: `momentumMin` maps the class of `ψ` to `-i ψ'`. -/
theorem momentumMin_graph : momentumMin.graph = momentumGraph :=
  Submodule.toLinearPMap_graph_eq momentumGraph momentumGraph_fun

end Lightlike.OperatorAlgebras
