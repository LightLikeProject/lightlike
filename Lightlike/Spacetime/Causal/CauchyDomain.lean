import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.DomainOfDependence
import Lightlike.Spacetime.Causal.Ladder

/-!
# Cauchy surfaces and domains of dependence

An achronal set whose domain of dependence is the whole manifold is a Cauchy surface: an inextendible
future-directed timelike curve is an inextendible future-directed causal curve, so it meets the
set (through any of its points the domain-of-dependence condition gives a meeting point), and it
meets it at most once because the set is achronal.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Chapter 6.

The comparison of the statements with the book at its location is pending.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Restriction of a timelike curve to a compact subinterval** of its domain. -/
theorem IsFutureTimelikeCurve.restrict {γ : ℝ → M} {s : Set ℝ} {c d : ℝ}
    (h : IsFutureTimelikeCurve T γ s) (hsub : Icc c d ⊆ s) (hcd : c < d) :
    IsFutureTimelikeCurve T γ (Icc c d) :=
  ⟨IsCurveWith.restrict h.1 hsub hcd, fun a b hab hab' => h.2 a b hab (hab'.trans hsub)⟩

/-- A future timelike curve meets an achronal set at most once. -/
theorem IsAchronal.eq_of_isFutureTimelikeCurve {S : Set M} (hA : IsAchronal T S) {γ : ℝ → M}
    {s : Set ℝ} (h : IsFutureTimelikeCurve T γ s) {t₁ t₂ : ℝ} (h₁ : t₁ ∈ s) (h₂ : t₂ ∈ s)
    (hS₁ : γ t₁ ∈ S) (hS₂ : γ t₂ ∈ S) : t₁ = t₂ := by
  have key : ∀ {a b : ℝ}, a ∈ s → b ∈ s → γ a ∈ S → γ b ∈ S → a < b → False := by
    intro a b ha hb hSa hSb hab
    refine hA _ hSa _ hSb ⟨γ, a, b, hab, h.restrict T (fun r hr => h.1.ordConnected.out ha hb hr) hab,
      rfl, rfl⟩
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · exact (key h₁ h₂ hS₁ hS₂ hlt).elim
  · exact heq
  · exact (key h₂ h₁ hS₂ hS₁ hgt).elim

/-- **An achronal set whose domain of dependence is the whole manifold is a Cauchy surface.**
(Hawking–Ellis, Chapter 6; the comparison with the book at its location is pending.) -/
theorem isCauchySurface_of_domainDep_eq_univ {S : Set M} (hA : IsAchronal T S)
    (h : domainDep T S = Set.univ) : IsCauchySurface T S := by
  intro γ s hγ
  obtain ⟨hT, hne, hnf, hnp⟩ := hγ
  have hcau : IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) γ s :=
    ⟨isFutureCausalCurve_of_isFutureTimelikeCurve T hT, hne, hnf, hnp⟩
  obtain ⟨t₀, ht₀⟩ := hne
  have hp : γ t₀ ∈ domainDep T S := h ▸ mem_univ _
  have hex : ∃ t ∈ s, γ t ∈ S := by
    rcases hp with hp | hp
    · obtain ⟨t', ht', -, hS⟩ := hp γ s hcau t₀ ht₀ rfl
      exact ⟨t', ht', hS⟩
    · obtain ⟨t', ht', -, hS⟩ := hp γ s hcau t₀ ht₀ rfl
      exact ⟨t', ht', hS⟩
  obtain ⟨t, ht, hS⟩ := hex
  exact ⟨t, ⟨ht, hS⟩, fun t' ⟨ht', hS'⟩ => hA.eq_of_isFutureTimelikeCurve T hT ht' ht hS' hS⟩

end Causal

end Lightlike
