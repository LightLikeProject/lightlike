import Lightlike.Rows.G1_012.GeneratorChain
import Lightlike.Rows.G1_012.AchronalBoundary
import Lightlike.Rows.G1_012.Orthogonality

/-!
# Generators of the boundary of the causal future of a set (G1-012)

A point of `J⁺(S) \ I⁺(S)` is on a future null geodesic from a point of `S`
(`exists_generator`): a causal curve from `S` to the point has no timelike shortcut (by the push-up
lemmas), so it is a monotone reparametrisation of a null geodesic
(`exists_null_geodesic_of_no_shortcut`). If moreover the point is reached by the geodesic in the
boundary then the geodesic is orthogonal to `S` (`null_geodesic_orthogonal`).
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- **A point of the curve is in the causal future of an earlier point.** -/
theorem mem_causalFuture_of_le (T : Causal.TimeOrientation g) {β : ℝ → M} {a b t₁ t₂ : ℝ}
    (hβ : Causal.IsFutureCausalCurve T β (Icc a b)) (h₁ : a ≤ t₁) (h12 : t₁ ≤ t₂) (h₂ : t₂ ≤ b) :
    β t₂ ∈ Causal.causalFuture T (β t₁) := by
  rcases h12.eq_or_lt with rfl | hlt
  · exact Causal.self_mem_causalFuture T _
  · exact ⟨β, t₁, t₂, h12, Causal.IsCurveWith.mono hβ h₁ h₂ hlt, rfl, rfl⟩

/-- **A causal curve from `S` to a point outside `I⁺(S)` has no timelike shortcut.** -/
theorem no_shortcut_of_not_mem_chronFutureSet (T : Causal.TimeOrientation g) {S : Set M} {β : ℝ → M}
    {a b : ℝ} (hβ : Causal.IsFutureCausalCurve T β (Icc a b)) (haS : β a ∈ S)
    (hq : β b ∉ Causal.chronFutureSet T S) :
    ∀ t' ∈ Icc a b, ∀ t'' ∈ Icc a b, t' ≤ t'' → β t'' ∉ Causal.chronFuture T (β t') := by
  intro t' ht' t'' ht'' h'' hcon
  have h1 : β b ∈ Causal.chronFuture T (β t') :=
    Causal.chronFuture_causalFuture_trans_of_isOpen T (Causal.isOpen_chronFuture_of_reach T) hcon
      (mem_causalFuture_of_le T hβ ht''.1 ht''.2 le_rfl)
  have h0 : β t' ∈ Causal.causalFuture T (β a) := mem_causalFuture_of_le T hβ le_rfl ht'.1 ht'.2
  have h2 : β b ∈ Causal.chronFuture T (β a) :=
    Causal.causalFuture_chronFuture_trans_of_isOpen T (Causal.isOpen_chronFuture_of_reach T.neg) h0 h1
  exact hq (mem_iUnion₂.2 ⟨β a, haS, h2⟩)

/-- **Generators exist.** A point of `J⁺(S) \ I⁺(S)` is in `S` or is the end of a future null
geodesic starting in `S`. -/
theorem exists_generator (T : Causal.TimeOrientation g) {S : Set M} {q : M}
    (hqJ : q ∈ Causal.causalFutureSet T S) (hqI : q ∉ Causal.chronFutureSet T S) :
    q ∈ S ∨ ∃ s ∈ S, ∃ (γ : ℝ → M) (L : ℝ), 0 < L ∧ IsFutureNullGeodesicOn T γ (Icc 0 L) ∧
      γ 0 = s ∧ γ L = q := by
  obtain ⟨s, hsS, hq⟩ := (Causal.mem_causalFutureSet T).1 hqJ
  obtain ⟨β, a, b, hab, hβ, hβa, hβb⟩ := hq
  rcases hab.eq_or_lt with rfl | hlt
  · left
    rw [← hβb, hβa]; exact hsS
  · right
    have hno := no_shortcut_of_not_mem_chronFutureSet T hβ (hβa ▸ hsS) (hβb ▸ hqI)
    obtain ⟨γ, L, hL, hγ, hγ0, hγL⟩ := exists_null_geodesic_of_no_shortcut T hlt hβ hno
    exact ⟨s, hsS, γ, L, hL, hγ, by rw [hγ0, hβa], by rw [hγL, hβb]⟩

end Lightlike.Penrose
