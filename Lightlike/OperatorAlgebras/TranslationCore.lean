import Lightlike.OperatorAlgebras.StoneCore
import Lightlike.OperatorAlgebras.GeneratorTranslation
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# The `C_c^∞` functions are a core of the momentum operator on `L²(ℝ)`

Helper lemmas for `T-OP1-P4` (`Tasks/OP/T_OP1_P4.lean`). The classes of `C_c^∞(ℝ)` functions form a subspace
`smoothCS` of `L²(ℝ)` that is dense (Mathlib: `MeasureTheory.Lp.dense_hasCompactSupport_contDiff`), lies in
the domain of the generator of the translation group with the generator `-i d/dx` on it
(`translationGroup_generator_ofCS`), and is invariant under translation. By `closure_domRestrict_generator`
(a dense invariant subspace of the domain of the generator of a unitary group is a core) the closure of
`-i d/dx` on it is the generator.
-/

open MeasureTheory Filter Topology
open scoped ContDiff LinearPMap

namespace Lightlike.OperatorAlgebras

/-- The classes in `L²(ℝ)` of `C_c^∞` functions, as a subspace. -/
def smoothCS : Submodule ℂ L2R where
  carrier := {f | ∃ g : ℝ → ℂ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, h₁, c₁, d₁⟩ ⟨g₂, h₂, c₂, d₂⟩
    refine ⟨g₁ + g₂, ?_, c₁.add c₂, d₁.add d₂⟩
    filter_upwards [Lp.coeFn_add f₁ f₂, h₁, h₂] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2]; rfl
  zero_mem' := ⟨0, Lp.coeFn_zero ℂ 2 volume, HasCompactSupport.zero, contDiff_const⟩
  smul_mem' := by
    rintro c f ⟨g, h, hc, hd⟩
    refine ⟨c • g, ?_, hc.smul_left, hd.const_smul c⟩
    filter_upwards [Lp.coeFn_smul c f, h] with x hx h1
    rw [hx, Pi.smul_apply, h1]; rfl

/-- The subspace of classes of `C_c^∞` functions is dense in `L²(ℝ)`. -/
lemma dense_smoothCS : Dense (smoothCS : Set L2R) :=
  MeasureTheory.Lp.dense_hasCompactSupport_contDiff (p := 2) (by norm_num)

/-- A class equal almost everywhere to a continuous compactly supported function is `ofCS` of it. -/
lemma eq_ofCS {f : L2R} {g : ℝ → ℂ} (h : f =ᵐ[volume] g) (hg : Continuous g) (hc : HasCompactSupport g) :
    f = ofCS hg hc := by
  refine Lp.ext (h.trans ?_)
  exact (MemLp.coeFn_toLp _).symm

lemma mem_smoothCS_iff {f : L2R} : f ∈ smoothCS ↔ ∃ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g), f = ofCS hg.continuous hc := by
  constructor
  · rintro ⟨g, h, hc, hg⟩
    exact ⟨g, hg, hc, eq_ofCS h hg.continuous hc⟩
  · rintro ⟨g, hg, hc, rfl⟩
    exact ⟨g, MemLp.coeFn_toLp _, hc, hg⟩

lemma smoothCS_le_domain : smoothCS ≤ translationGroup.generatorDomain := by
  intro f hf
  obtain ⟨g, hg, hc, rfl⟩ := mem_smoothCS_iff.1 hf
  exact (translationGroup_generator_ofCS (hg.of_le (by norm_num)) hc).1

lemma smoothCS_invariant : ∀ t : ℝ, ∀ x ∈ smoothCS, translationGroup t x ∈ smoothCS := by
  intro t x hx
  obtain ⟨g, hg, hc, rfl⟩ := mem_smoothCS_iff.1 hx
  refine mem_smoothCS_iff.2 ⟨fun x => g (x + t), hg.comp (contDiff_id.add contDiff_const),
    hc.comp_homeomorph (Homeomorph.addRight t), ?_⟩
  exact translate_ofCS hg.continuous hc t

/-- **The `C_c^∞` functions are a core of the momentum operator on `L²(ℝ)`**: every vector of the domain of
the generator of the translation group is the limit of classes `ψₙ` of `C_c^∞` functions whose derivatives
`ψₙ'` tend to `i` times the generator of the vector. -/
theorem translationGroup_core_smooth (ψ : L2R) (hψ : ψ ∈ translationGroup.generatorDomain) :
    ∃ (f : ℕ → ℝ → ℂ) (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n)),
      Tendsto (fun n => ofCS (hf n).continuous (hc n)) atTop (𝓝 ψ) ∧
      Tendsto (fun n => ofCS (continuous_deriv_of_two ((hf n).of_le (by norm_num))) (hc n).deriv)
        atTop (𝓝 (Complex.I • translationGroup.generator ⟨ψ, hψ⟩)) := by
  set A := translationGroup.generator with hA
  set AD := A.domRestrict smoothCS with hAD
  have hcl : AD.closure = A :=
    UnitaryGroup.closure_domRestrict_generator dense_smoothCS smoothCS_le_domain smoothCS_invariant
  have hle : AD ≤ A := by
    refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
    · have hiff : ∀ z : L2R, z ∈ AD.domain ↔ z ∈ smoothCS ⊓ A.domain := fun z => by
        rw [hAD, LinearPMap.domRestrict_domain]
      exact ((hiff x).1 hx).2
    · exact LinearPMap.domRestrict_apply hxy
  have hclosable : AD.IsClosable :=
    (translationGroup.generator_isSelfAdjoint.isClosed.isClosable).leIsClosable hle
  have hmem : (ψ, (A ⟨ψ, hψ⟩ : L2R)) ∈ AD.graph.topologicalClosure := by
    rw [hclosable.graph_closure_eq_closure_graph, hcl]
    exact LinearPMap.mem_graph A ⟨ψ, hψ⟩
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (by exact hmem)
  have hex : ∀ n, ∃ (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g),
      (u n).1 = ofCS hg.continuous hc ∧
        (u n).2 = (-Complex.I) • ofCS (continuous_deriv_of_two (hg.of_le (by norm_num))) hc.deriv := by
    intro n
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff AD).1 (hu n)
    have hiff : ∀ z : L2R, z ∈ AD.domain ↔ z ∈ smoothCS ⊓ A.domain := fun z => by
      rw [hAD, LinearPMap.domRestrict_domain]
    have hyD : (y : L2R) ∈ smoothCS := ((hiff y).1 y.2).1
    obtain ⟨g, hg, hc, hyg⟩ := mem_smoothCS_iff.1 hyD
    refine ⟨g, hg, hc, by rw [← hy1, hyg], ?_⟩
    have hyA : (y : L2R) ∈ A.domain := ((hiff y).1 y.2).2
    have h2 : AD y = A ⟨y, hyA⟩ := LinearPMap.domRestrict_apply (rfl : (y : L2R) = ((⟨y, hyA⟩ : A.domain) : L2R))
    rw [← hy2, h2]
    have := (translationGroup_generator_ofCS (hg.of_le (by norm_num)) hc).2
    simp only [hyg] at *
    exact this
  choose g hg hc hu1 hu2 using hex
  refine ⟨g, hg, hc, ?_, ?_⟩
  · have := (continuous_fst.tendsto _).comp hlim
    simpa [Function.comp_def, hu1] using this
  · have h1 := ((continuous_snd.tendsto _).comp hlim).const_smul Complex.I
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply, hu2, smul_smul]
    simp

end Lightlike.OperatorAlgebras
