import Lightlike.Spacetime.Causal.CauchyCover
import Lightlike.Spacetime.Causal.DomainOfDependence

/-!
# A Cauchy surface has the whole manifold as domain of dependence, from the perturbation step

Let `S` be a Cauchy surface. Every point `p` lies in `S`, in the chronological future of a point of
`S`, or in the chronological past of one (`IsCauchySurface.cover`). Suppose that an inextendible
causal curve through a point of `S ∪ I⁺(S)` that misses `S` in the past of that point can be
perturbed into an inextendible timelike curve missing `S` (`PerturbFuture`), and the time dual
(`PerturbPast`). Then a point of `S ∪ I⁺(S)` is in `D⁺(S)` and a point of `I⁻(S)` is in `D⁻(S)`:
otherwise the perturbed timelike curve would miss the Cauchy surface. The perturbation step is the
hard part of the equivalence of the two Cauchy conditions and is not proved here.

## References

* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Section 6.6.

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

/-- **The perturbation step, forwards**: an inextendible future causal curve through a point of
`S` or of the chronological future of `S` that misses `S` at all parameters up to that point yields
an inextendible future timelike curve that misses `S` altogether. -/
def PerturbFuture (S : Set M) : Prop :=
  ∀ p : M, (p ∈ S ∨ p ∈ chronFutureSet T S) →
    ∀ (c : ℝ → M) (s : Set ℝ),
      IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) c s →
      ∀ t ∈ s, c t = p → (∀ t' ∈ s, t' ≤ t → c t' ∉ S) →
        ∃ (G : ℝ → M) (s' : Set ℝ), IsInextendibleFutureTimelike T G s' ∧ ∀ u ∈ s', G u ∉ S

/-- **The perturbation step, backwards**: the time dual of `PerturbFuture`. -/
def PerturbPast (S : Set M) : Prop :=
  ∀ p : M, (p ∈ S ∨ p ∈ ⋃ x ∈ S, chronPast T x) →
    ∀ (c : ℝ → M) (s : Set ℝ),
      IsInextendibleWith (I := I) (fun _ v ↦ T.IsFutureCausal v) c s →
      ∀ t ∈ s, c t = p → (∀ t' ∈ s, t ≤ t' → c t' ∉ S) →
        ∃ (G : ℝ → M) (s' : Set ℝ), IsInextendibleFutureTimelike T G s' ∧ ∀ u ∈ s', G u ∉ S

variable [T2Space M] [BoundarylessManifold I M] [SecondCountableTopology M]

/-- **A Cauchy surface has the whole manifold as domain of dependence**, given the perturbation
step in both time directions. -/
theorem IsCauchySurface.domainDep_eq_univ_of_perturb {S : Set M} (h : IsCauchySurface T S)
    (hF : PerturbFuture T S) (hP : PerturbPast T S) : domainDep T S = Set.univ := by
  refine eq_univ_of_forall fun p => ?_
  have hmiss : ∀ (G : ℝ → M) (s' : Set ℝ), IsInextendibleFutureTimelike T G s' →
      (∀ u ∈ s', G u ∉ S) → False := fun G s' hG hmiss => by
    obtain ⟨t, ⟨hts, htS⟩, -⟩ := h G s' hG
    exact hmiss t hts htS
  have hDF : p ∈ S ∨ p ∈ chronFutureSet T S → p ∈ domainDepFuture T S := by
    intro hp c s hc t ht hct
    by_contra hno
    push Not at hno
    obtain ⟨G, s', hG, hGS⟩ := hF p hp c s hc t ht hct (fun t' ht' htt' hS => hno t' ht' htt' hS)
    exact hmiss G s' hG hGS
  have hDP : p ∈ S ∨ p ∈ ⋃ x ∈ S, chronPast T x → p ∈ domainDepPast T S := by
    intro hp c s hc t ht hct
    by_contra hno
    push Not at hno
    obtain ⟨G, s', hG, hGS⟩ := hP p hp c s hc t ht hct (fun t' ht' htt' hS => hno t' ht' htt' hS)
    exact hmiss G s' hG hGS
  rcases h.cover T p with hS | ⟨x, hx, hpx⟩ | ⟨x, hx, hxp⟩
  · exact Or.inl (hDF (Or.inl hS))
  · exact Or.inl (hDF (Or.inr (mem_iUnion₂.2 ⟨x, hx, hpx⟩)))
  · exact Or.inr (hDP (Or.inr (mem_iUnion₂.2 ⟨x, hx, hxp⟩)))

end Causal

end Lightlike
