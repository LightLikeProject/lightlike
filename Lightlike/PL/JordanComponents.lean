import Lightlike.PL.WeakJordanCircle

/-!
# The components of the complement of a Jordan curve

The complement of the image of a continuous injective map of the circle into the plane has
exactly one unbounded component and at least one bounded component, whose frontier lies in the curve.
That there is exactly one bounded component, and that the curve is the frontier of each, is the
rest of the Jordan curve theorem; it needs the Arc Theorem and is not proved here.
-/

open Set

namespace Lightlike.PL

/-- The squareOutside of a square: the union of four half-planes. -/
def squareOutside (R : ℝ) : Set (ℝ × ℝ) :=
  {x | R < x.1} ∪ {x | R < x.2} ∪ {x | x.1 < -R} ∪ {x | x.2 < -R}

/-- Outside a square the plane is connected. -/
lemma isPreconnected_outside (R : ℝ) : IsPreconnected (squareOutside R) := by
  have h1 : IsPreconnected {x : ℝ × ℝ | R < x.1} :=
    (convex_halfSpace_gt (f := fun x : ℝ × ℝ => x.1) (LinearMap.fst ℝ ℝ ℝ).isLinear R).isPreconnected
  have h2 : IsPreconnected {x : ℝ × ℝ | R < x.2} :=
    (convex_halfSpace_gt (f := fun x : ℝ × ℝ => x.2) (LinearMap.snd ℝ ℝ ℝ).isLinear R).isPreconnected
  have h3 : IsPreconnected {x : ℝ × ℝ | x.1 < -R} :=
    (convex_halfSpace_lt (f := fun x : ℝ × ℝ => x.1) (LinearMap.fst ℝ ℝ ℝ).isLinear (-R)).isPreconnected
  have h4 : IsPreconnected {x : ℝ × ℝ | x.2 < -R} :=
    (convex_halfSpace_lt (f := fun x : ℝ × ℝ => x.2) (LinearMap.snd ℝ ℝ ℝ).isLinear (-R)).isPreconnected
  unfold squareOutside
  refine IsPreconnected.union (R + 1, -R - 1) ?_ ?_ ?_ h4
  · exact Or.inl (Or.inl (by simp))
  · simp
  · refine IsPreconnected.union (-R - 1, R + 1) ?_ ?_ ?_ h3
    · exact Or.inr (by simp)
    · simp
    · exact IsPreconnected.union (R + 1, R + 1) (by simp) (by simp) h1 h2

/-- **The components of the complement of a Jordan curve.** The complement of the image of a continuous
injective map of the circle into the plane has exactly one unbounded component, and has a bounded
component, whose frontier lies in the curve. (That there is exactly one bounded component, and that
the curve is the frontier of each component, is the rest of the Jordan curve theorem and needs the
Arc Theorem; it is not proved here.) -/
theorem jordan_components {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) :
    (∃ x ∈ (range f)ᶜ, ¬ Bornology.IsBounded (connectedComponentIn (range f)ᶜ x) ∧
      ∀ y ∈ (range f)ᶜ, ¬ Bornology.IsBounded (connectedComponentIn (range f)ᶜ y) →
        connectedComponentIn (range f)ᶜ y = connectedComponentIn (range f)ᶜ x) ∧
    (∃ y ∈ (range f)ᶜ, Bornology.IsBounded (connectedComponentIn (range f)ᶜ y) ∧
      frontier (connectedComponentIn (range f)ᶜ y) ⊆ range f) := by
  set K : Set (ℝ × ℝ) := range f with hK
  have hKc : IsCompact K := isCompact_range hc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  have hKo : IsOpen Kᶜ := hKc.isClosed.isOpen_compl
  have hout : squareOutside R ⊆ Kᶜ := by
    intro x hx hxK
    have h := hR x hxK
    have h1 : |x.1| ≤ R := by simpa using (norm_fst_le x).trans h
    have h2 : |x.2| ≤ R := by simpa using (norm_snd_le x).trans h
    rcases hx with ((hx | hx) | hx) | hx
    · have := le_abs_self x.1; simp only [mem_ofPred_eq] at hx; linarith
    · have := le_abs_self x.2; simp only [mem_ofPred_eq] at hx; linarith
    · have := neg_abs_le x.1; simp only [mem_ofPred_eq] at hx; linarith
    · have := neg_abs_le x.2; simp only [mem_ofPred_eq] at hx; linarith
  have hx0 : ((R + 1, 0) : ℝ × ℝ) ∈ squareOutside R := Or.inl (Or.inl (Or.inl (by simp)))
  set Cinf := connectedComponentIn Kᶜ (R + 1, 0) with hCinf
  have hsubI : squareOutside R ⊆ Cinf :=
    (isPreconnected_outside R).subset_connectedComponentIn hx0 hout
  have hunb : ¬ Bornology.IsBounded Cinf := by
    intro hb
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    have hz : ((max R M + 1, 0) : ℝ × ℝ) ∈ squareOutside R :=
      Or.inl (Or.inl (Or.inl (by simp only [mem_ofPred_eq]; linarith [le_max_left R M])))
    have := hM _ (hsubI hz)
    have h2 := (norm_fst_le ((max R M + 1, 0) : ℝ × ℝ)).trans this
    simp only [Real.norm_eq_abs] at h2
    have := le_abs_self (max R M + 1)
    linarith [le_max_right R M]
  have hbox : ∀ z : ℝ × ℝ, z ∉ squareOutside R → ‖z‖ ≤ R := by
    intro z hz
    simp only [squareOutside, mem_union, mem_ofPred_eq, not_or, not_lt] at hz
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hz
    rw [Prod.norm_def, max_le_iff]
    constructor <;> rw [Real.norm_eq_abs, abs_le] <;> constructor <;> linarith
  refine ⟨⟨(R + 1, 0), hout hx0, hunb, fun y hy hyu => ?_⟩, ?_⟩
  · -- another unbounded component meets the squareOutside
    obtain ⟨z, hz, hzR⟩ : ∃ z ∈ connectedComponentIn Kᶜ y, R < ‖z‖ := by
      by_contra hcon
      push Not at hcon
      exact hyu ((Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := R)).subset (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hcon z hz))
    have hzo : z ∈ squareOutside R := by
      by_contra hn
      exact absurd (hbox z hn) (not_le.2 hzR)
    rw [connectedComponentIn_eq hz]
    exact (connectedComponentIn_eq (hsubI hzo)).symm
  · by_cases hall : Kᶜ ⊆ Cinf
    · exfalso
      have hpre : IsPreconnected Kᶜ := by
        have : Kᶜ = Cinf := Subset.antisymm hall (connectedComponentIn_subset _ _)
        rw [this]; exact isPreconnected_connectedComponentIn
      exact weak_jordan hc hi hpre
    · obtain ⟨y, hyK, hyC⟩ := not_subset.1 hall
      refine ⟨y, hyK, ?_, ?_⟩
      · refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := R)).subset (fun z hz => ?_)
        rw [Metric.mem_closedBall, dist_zero_right]
        apply hbox
        intro hzo
        apply hyC
        have h1 : z ∈ connectedComponentIn Kᶜ (R + 1, 0) := hsubI hzo
        have h2 := connectedComponentIn_eq hz
        have h3 := connectedComponentIn_eq h1
        rw [hCinf, h3, ← h2]
        exact mem_connectedComponentIn hyK
      · intro z hz
        by_contra hzK
        have hzKc : z ∈ Kᶜ := hzK
        have hCz : IsOpen (connectedComponentIn Kᶜ z) := hKo.connectedComponentIn
        obtain ⟨w, hwC, hwU⟩ := mem_closure_iff.1 (frontier_subset_closure hz) _ hCz
          (mem_connectedComponentIn hzKc)
        have hzU : connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ y := by
          rw [connectedComponentIn_eq hwC, connectedComponentIn_eq hwU]
        have hUo : IsOpen (connectedComponentIn Kᶜ y) := hKo.connectedComponentIn
        apply hz.2
        rw [hUo.interior_eq, ← hzU]
        exact mem_connectedComponentIn hzKc

end Lightlike.PL
