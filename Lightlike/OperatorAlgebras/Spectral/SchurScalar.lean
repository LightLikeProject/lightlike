import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# A self-adjoint operator commuting with an irreducible set of operators is a scalar

Let `S` be a set of bounded operators on a Hilbert space `H` such that the only closed subspaces invariant under all
of `S` are `0` and `H`. A bounded self-adjoint operator `T` commuting with every element of `S` is a scalar multiple of
the identity (`exists_scalar_of_commute_irreducible`). Proof by the continuous functional calculus: if the spectrum of
`T` had two points `x < y`, two continuous functions `f, g` with `f g = 0`, `f(x) ≠ 0`, `g(y) ≠ 0` would give
nonzero commuting operators `f(T)`, `g(T)` with `f(T) g(T) = 0`; the closure of the range of `f(T)` is a nonzero
closed `S`-invariant subspace, hence everything, so `g(T) = 0`, a contradiction.

Supporting results for the converse of the Wigner classification; no catalogue entry.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closure of the range of an operator commuting with `S` is `S`-invariant. -/
lemma closure_range_invariant {S : Set (H →L[ℂ] H)} {F : H →L[ℂ] H} (hc : ∀ a ∈ S, Commute a F) :
    ∀ a ∈ S, ∀ x ∈ (LinearMap.range (F : H →ₗ[ℂ] H)).topologicalClosure,
      a x ∈ (LinearMap.range (F : H →ₗ[ℂ] H)).topologicalClosure := by
  intro a ha x hx
  have hmap : ∀ y ∈ (LinearMap.range (F : H →ₗ[ℂ] H) : Set H), a y ∈ (LinearMap.range (F : H →ₗ[ℂ] H) : Set H) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨a y, ?_⟩
    have := congrArg (fun G : H →L[ℂ] H => G y) (hc a ha).eq
    simpa using this.symm
  have hx' : x ∈ closure (LinearMap.range (F : H →ₗ[ℂ] H) : Set H) := by
    rw [← Submodule.topologicalClosure_coe]; exact hx
  have := map_mem_closure a.continuous hx' hmap
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact this

/-- **A closed invariant subspace containing the range of a nonzero commuting operator is everything.** -/
lemma range_dense_of_commute {S : Set (H →L[ℂ] H)}
    (hirr : ∀ M : Submodule ℂ H, IsClosed (M : Set H) → (∀ a ∈ S, ∀ x ∈ M, a x ∈ M) → M = ⊥ ∨ M = ⊤)
    {F : H →L[ℂ] H} (hc : ∀ a ∈ S, Commute a F) (hF : F ≠ 0) :
    (LinearMap.range (F : H →ₗ[ℂ] H)).topologicalClosure = ⊤ := by
  rcases hirr _ (Submodule.isClosed_topologicalClosure _) (closure_range_invariant hc) with h | h
  · exfalso
    apply hF
    ext x
    have : F x ∈ (LinearMap.range (F : H →ₗ[ℂ] H)).topologicalClosure :=
      Submodule.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h, Submodule.mem_bot] at this
    simpa using this
  · exact h

/-- The tent function of height `ε` at `x`. -/
def tent (x ε : ℝ) (t : ℝ) : ℝ := max 0 (ε - |t - x|)

lemma continuous_tent (x ε : ℝ) : Continuous (tent x ε) := by
  unfold tent; fun_prop

lemma tent_mul_tent_eq_zero {x y ε : ℝ} (hε : 3 * ε ≤ |y - x|) (t : ℝ) : tent x ε t * tent y ε t = 0 := by
  unfold tent
  by_contra h
  have h1 : 0 < max 0 (ε - |t - x|) := by
    by_contra h1
    exact h (by rw [le_antisymm (not_lt.1 h1) (le_max_left _ _), zero_mul])
  have h2 : 0 < max 0 (ε - |t - y|) := by
    by_contra h2
    exact h (by rw [le_antisymm (not_lt.1 h2) (le_max_left _ _), mul_zero])
  have h1' : 0 < ε - |t - x| := by
    rcases lt_max_iff.1 h1 with h | h
    · exact absurd h (lt_irrefl _)
    · exact h
  have h2' : 0 < ε - |t - y| := by
    rcases lt_max_iff.1 h2 with h | h
    · exact absurd h (lt_irrefl _)
    · exact h
  have : |y - x| ≤ |t - x| + |t - y| := by
    calc |y - x| = |(t - x) - (t - y)| := by ring_nf
      _ ≤ |t - x| + |t - y| := abs_sub _ _
  linarith [abs_nonneg (t - x), abs_nonneg (t - y)]

lemma tent_self {x ε : ℝ} (hε : 0 < ε) : tent x ε x = ε := by
  simp [tent, hε.le]

/-- **Schur's lemma for a self-adjoint operator.** -/
theorem exists_scalar_of_commute_irreducible {S : Set (H →L[ℂ] H)}
    (hirr : ∀ M : Submodule ℂ H, IsClosed (M : Set H) → (∀ a ∈ S, ∀ x ∈ M, a x ∈ M) → M = ⊥ ∨ M = ⊤)
    {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (hc : ∀ a ∈ S, Commute a T) [Nontrivial H] :
    ∃ c : ℝ, T = (c : ℂ) • 1 := by
  by_cases hone : ∃ c : ℝ, spectrum ℝ T ⊆ {c}
  · obtain ⟨c, hc'⟩ := hone
    refine ⟨c, ?_⟩
    have h1 : cfc (id : ℝ → ℝ) T = cfc (fun _ : ℝ => c) T :=
      (cfc_eq_cfc_iff_eqOn (a := T) (f := (id : ℝ → ℝ)) (g := fun _ => c)).2 fun t ht => by
        simpa using hc' ht
    rw [cfc_id ℝ T, cfc_const c T] at h1
    rw [h1]
    simp [Algebra.algebraMap_eq_smul_one]
  · exfalso
    push Not at hone
    obtain ⟨x, hx⟩ : (spectrum ℝ T).Nonempty := by
      exact ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (p := IsSelfAdjoint) T hT
    obtain ⟨y, hy, hyx⟩ := Set.not_subset.1 (hone x)
    have hyx' : y ≠ x := hyx
    set ε : ℝ := |y - x| / 3 with hε
    have hε0 : 0 < ε := by
      have : 0 < |y - x| := abs_pos.2 (sub_ne_zero.2 hyx')
      positivity
    have h3 : 3 * ε ≤ |y - x| := by rw [hε]; linarith
    set F : H →L[ℂ] H := cfc (tent x ε) T with hF
    set G : H →L[ℂ] H := cfc (tent y ε) T with hG
    have hFne : F ≠ 0 := by
      intro h0
      have : cfc (tent x ε) T = cfc (0 : ℝ → ℝ) T := by rw [← hF, h0, cfc_zero]
      have := (cfc_eq_cfc_iff_eqOn (a := T) (f := tent x ε) (g := 0) (hf := (continuous_tent x ε).continuousOn)
        (hg := continuous_zero.continuousOn)).1 this hx
      simp [tent_self hε0] at this
      linarith
    have hGne : G ≠ 0 := by
      intro h0
      have : cfc (tent y ε) T = cfc (0 : ℝ → ℝ) T := by rw [← hG, h0, cfc_zero]
      have := (cfc_eq_cfc_iff_eqOn (a := T) (f := tent y ε) (g := 0) (hf := (continuous_tent y ε).continuousOn)
        (hg := continuous_zero.continuousOn)).1 this hy
      simp [tent_self hε0] at this
      linarith
    have hFG : G * F = 0 := by
      rw [hG, hF, ← cfc_mul (tent y ε) (tent x ε) T (continuous_tent y ε).continuousOn
        (continuous_tent x ε).continuousOn]
      rw [← cfc_zero (R := ℝ) T]
      refine cfc_congr fun t _ => ?_
      simp only [Pi.zero_apply]
      rw [mul_comm]
      exact tent_mul_tent_eq_zero h3 t
    have hFc : ∀ a ∈ S, Commute a F := fun a ha => ((hc a ha).symm.cfc_real (tent x ε)).symm
    have hdense := range_dense_of_commute hirr hFc hFne
    apply hGne
    ext z
    have hz : z ∈ (LinearMap.range (F : H →ₗ[ℂ] H)).topologicalClosure := by rw [hdense]; trivial
    have hclosed : IsClosed {z : H | G z = 0} := isClosed_eq G.continuous continuous_const
    have hsub : ((LinearMap.range (F : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) ⊆ {z : H | G z = 0} := by
      rintro _ ⟨w, rfl⟩
      show G (F w) = 0
      have := congrArg (fun A : H →L[ℂ] H => A w) hFG
      simpa using this
    have := closure_minimal hsub hclosed
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hz
    simpa using this hz

end Lightlike.OperatorAlgebras.Spectral
