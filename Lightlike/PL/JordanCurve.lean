import Lightlike.PL.IndexCurve
import Lightlike.PL.JordanComponents
import Lightlike.PL.JordanFrontier

/-!
# The Jordan curve theorem

The complement of the image `J` of a continuous injective map `f` from the circle into the plane has exactly two
connected components, one bounded and one unbounded, both open and connected, and `J` is the frontier of each.

**Method.** (McCleary, Chapter 9: the chapter location is verified, the lemma-level numbering is not.) The index of a loop
about a point, defined through a lift of the logarithm (`Lightlike/PL/Index.lean`), and the θ configuration of a Jordan
curve (`Lightlike/PL/ThetaRay.lean`) show that the index about the curve vanishes on the component of a point above the
curve and is nonzero elsewhere; computing the same index with a θ configuration at a point of another component
(`Theta.iota_eq`: the index does not depend on the splitting) shows that there is at most one other component
(`jordan_at_most_two`). The existence of a bounded and an unbounded component is `jordan_components` and the
frontier statement is `jordan_frontier`. The statements and proofs are Lean's own.

## Main results

* `jordan_at_most_two`: among three points off a Jordan curve in the complex plane two lie in the same component.
* `jordan_curve_theorem`: the Jordan curve theorem for a continuous injective map from the circle to `ℝ × ℝ`.

## References

* McCleary, *A First Course in Topology: Continuity and Dimension* (2006), `mccleary-2006`, Chapter 9.
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

/-- **In an open subset of the plane a component is path connected**: a point of the connected component of `x` in an
open set `F` is joined to `x` by a path in `F`. -/
theorem joinedIn_of_mem_connectedComponentIn {F : Set ℂ} (hF : IsOpen F) {x y : ℂ}
    (hy : y ∈ connectedComponentIn F x) : JoinedIn F x y := by
  have hxF : x ∈ F := by
    by_contra h
    rw [connectedComponentIn_eq_empty h] at hy
    exact hy
  set C := connectedComponentIn F x with hC
  set P := pathComponentIn F x with hP
  have hPo : IsOpen P := hF.pathComponentIn x
  have hPC : P ⊆ C :=
    (isPathConnected_pathComponentIn hxF).isConnected.isPreconnected.subset_connectedComponentIn
      (mem_pathComponentIn_self hxF) pathComponentIn_subset
  have hCF : C ⊆ F := connectedComponentIn_subset F x
  set Q := ⋃ z ∈ C \ P, pathComponentIn F z with hQ
  have hQo : IsOpen Q := isOpen_biUnion fun z _ => hF.pathComponentIn z
  have hdisj : Disjoint P Q := by
    rw [Set.disjoint_left]
    intro w hwP hwQ
    simp only [hQ, Set.mem_iUnion] at hwQ
    obtain ⟨z, hz, hwz⟩ := hwQ
    apply hz.2
    have h1 : pathComponentIn F w = pathComponentIn F x := pathComponentIn_congr hwP
    have h2 : pathComponentIn F w = pathComponentIn F z := pathComponentIn_congr hwz
    have h3 : P = pathComponentIn F z := h1.symm.trans h2
    rw [h3]
    exact mem_pathComponentIn_self (hCF hz.1)
  have hsub : C ⊆ P ∪ Q := by
    intro w hw
    by_cases hwP : w ∈ P
    · exact Or.inl hwP
    · refine Or.inr ?_
      simp only [hQ, Set.mem_iUnion]
      exact ⟨w, ⟨hw, hwP⟩, mem_pathComponentIn_self (hCF hw)⟩
  have hCP : C ⊆ P :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hPo hQo hdisj hsub
      ⟨x, mem_connectedComponentIn hxF, mem_pathComponentIn_self hxF⟩
  exact hCP hy


/-- **The complement of a Jordan curve has at most two components**: among any three points off the curve, two lie in the
same component. The proof compares the index about the curve (well defined, by `Theta.iota_eq`) computed with two
different θ configurations: the index vanishes exactly on the component of the point above the curve, and for a
configuration at a point of another component it takes one constant value on all the remaining components. -/
theorem jordan_at_most_two {f : Circle → ℂ} (hc : Continuous f) (hi : Function.Injective f) {x y z : ℂ}
    (hx : x ∉ range f) (hy : y ∉ range f) (hz : z ∉ range f) :
    connectedComponentIn (range f)ᶜ x = connectedComponentIn (range f)ᶜ y ∨
      connectedComponentIn (range f)ᶜ y = connectedComponentIn (range f)ᶜ z ∨
      connectedComponentIn (range f)ᶜ x = connectedComponentIn (range f)ᶜ z := by
  have hJo : IsOpen (range f)ᶜ := (isCompact_range hc).isClosed.isOpen_compl
  obtain ⟨T, hS, hU, a, b, hab, hb2, hγ₁, hγ₂⟩ := exists_theta_top hc hi
  have hcurve : T.curve = range f := hU
  have hΩJ : T.Ω ∉ range f := hcurve ▸ fun h => T.hΩ h
  set C0 := connectedComponentIn (range f)ᶜ T.Ω with hC0
  -- the index vanishes on `C0`
  have A1 : ∀ R ∈ C0, loopIndex T.ω₀ R = 0 := fun R hR => by
    refine T.iota_of_joined hS ?_
    rw [hcurve]
    exact (joinedIn_of_mem_connectedComponentIn hJo hR).symm
  -- and is nonzero off `C0`
  have A2 : ∀ R, R ∉ range f → R ∉ C0 → loopIndex T.ω₀ R ≠ 0 := fun R hRJ hR0 => by
    refine T.iota_ne_zero hS ?_ ?_
    · rintro ((h | h) | h)
      · exact hRJ (hcurve ▸ h)
      · rcases T.segments_subset_component (Or.inl h) with h' | h'
        · exact hRJ (hcurve ▸ h')
        · rw [hcurve] at h'
          exact hR0 h'
      · rcases T.segments_subset_component (Or.inr h) with h' | h'
        · exact hRJ (hcurve ▸ h')
        · rw [hcurve] at h'
          exact hR0 h'
    · intro hj
      rw [hcurve] at hj
      exact hR0 (joinedIn_mem_connectedComponentIn (by exact hΩJ) hj.symm)
  have hin : ∀ u, u ∉ range f → u ∈ C0 → connectedComponentIn (range f)ᶜ u = C0 := fun u hu h =>
    (connectedComponentIn_eq h).symm
  -- two points off the curve and outside `C0` lie in the same component
  have L : ∀ R R', R ∉ range f → R' ∉ range f → R ∉ C0 → R' ∉ C0 →
      connectedComponentIn (range f)ᶜ R = connectedComponentIn (range f)ᶜ R' := by
    intro R R' hR hR' hR0 hR'0
    by_contra hne
    have hR'R : R' ∉ connectedComponentIn (range f)ᶜ R := fun h => hne (connectedComponentIn_eq h)
    obtain ⟨T', hΩ', hU', a', b', hab', hb2', hγ₁', hγ₂'⟩ := exists_theta_at hc hi hR
    have hcurve' : T'.curve = range f := hU'
    obtain ⟨K', hK'⟩ := T'.iota_const
    have key : ∀ w, w ∉ range f → w ∉ connectedComponentIn (range f)ᶜ R → loopIndex T'.ω₀ w = K' := by
      intro w hwJ hwR
      refine hK' w ?_ ?_
      · rintro ((h | h) | h)
        · exact hwJ (hcurve' ▸ h)
        · rcases T'.segments_subset_component (Or.inl h) with h' | h'
          · exact hwJ (hcurve' ▸ h')
          · rw [hcurve', hΩ'] at h'
            exact hwR h'
        · rcases T'.segments_subset_component (Or.inr h) with h' | h'
          · exact hwJ (hcurve' ▸ h')
          · rw [hcurve', hΩ'] at h'
            exact hwR h'
      · intro hj
        rw [hcurve', hΩ'] at hj
        exact hwR (joinedIn_mem_connectedComponentIn (by exact hR) hj.symm)
    have hΩR : T.Ω ∉ connectedComponentIn (range f)ᶜ R := by
      intro h
      apply hR0
      have := connectedComponentIn_eq h
      rw [hC0]
      rw [← this]
      exact mem_connectedComponentIn hR
    have e1 : loopIndex T'.ω₀ T.Ω = loopIndex T.ω₀ T.Ω :=
      (Theta.iota_eq hc T T' hΩJ hγ₁ hγ₂ hγ₁' hγ₂').symm
    have e2 : loopIndex T'.ω₀ R' = loopIndex T.ω₀ R' :=
      (Theta.iota_eq hc T T' hR' hγ₁ hγ₂ hγ₁' hγ₂').symm
    have k1 := key T.Ω hΩJ hΩR
    have k2 := key R' hR' hR'R
    have z1 : loopIndex T.ω₀ T.Ω = 0 := A1 T.Ω (mem_connectedComponentIn hΩJ)
    exact A2 R' hR' hR'0 (by rw [← e2, k2, ← k1, e1, z1])
  by_cases hx0 : x ∈ C0 <;> by_cases hy0 : y ∈ C0 <;> by_cases hz0 : z ∈ C0
  · exact Or.inl ((hin x hx hx0).trans (hin y hy hy0).symm)
  · exact Or.inl ((hin x hx hx0).trans (hin y hy hy0).symm)
  · exact Or.inr (Or.inr ((hin x hx hx0).trans (hin z hz hz0).symm))
  · exact Or.inr (Or.inl (L y z hy hz hy0 hz0))
  · exact Or.inr (Or.inl ((hin y hy hy0).trans (hin z hz hz0).symm))
  · exact Or.inr (Or.inr (L x z hx hz hx0 hz0))
  · exact Or.inl (L x y hx hy hx0 hy0)
  · exact Or.inl (L x y hx hy hx0 hy0)


/-- The image of a connected component under the homeomorphism between the complex numbers and the plane. -/
lemma image_component_prod {f : Circle → ℝ × ℝ} {x : ℝ × ℝ} (hx : x ∉ range f) :
    Complex.equivRealProdCLM.symm '' connectedComponentIn (range f)ᶜ x =
      connectedComponentIn (range (Complex.equivRealProdCLM.symm ∘ f))ᶜ (Complex.equivRealProdCLM.symm x) := by
  have h := Complex.equivRealProdCLM.toHomeomorph.symm.image_connectedComponentIn (s := (range f)ᶜ) hx
  have e : Complex.equivRealProdCLM.toHomeomorph.symm '' (range f)ᶜ =
      (range (Complex.equivRealProdCLM.symm ∘ f))ᶜ := by
    rw [Set.range_comp]
    exact (Complex.equivRealProdCLM.toHomeomorph.symm.toEquiv.image_compl _)
  refine h.trans ?_
  rw [e]
  rfl

/-- **The complement of a Jordan curve in the plane has at most two components**: the statement of
`jordan_at_most_two` for maps into `ℝ × ℝ`, transferred along `Complex.equivRealProdCLM`. -/
theorem jordan_at_most_two_prod {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {x y z : ℝ × ℝ} (hx : x ∉ range f) (hy : y ∉ range f) (hz : z ∉ range f) :
    connectedComponentIn (range f)ᶜ x = connectedComponentIn (range f)ᶜ y ∨
      connectedComponentIn (range f)ᶜ y = connectedComponentIn (range f)ᶜ z ∨
      connectedComponentIn (range f)ᶜ x = connectedComponentIn (range f)ᶜ z := by
  set e := Complex.equivRealProdCLM with he
  have hnot : ∀ {w : ℝ × ℝ}, w ∉ range f → e.symm w ∉ range (e.symm ∘ f) := fun {w} hw h => by
    rw [Set.range_comp] at h
    obtain ⟨v, hv, hvw⟩ := h
    exact hw (e.symm.injective hvw ▸ hv)
  have inj := (Set.image_injective.2 e.symm.injective : Function.Injective (fun s : Set (ℝ × ℝ) => e.symm '' s))
  have key := jordan_at_most_two (f := e.symm ∘ f) (e.symm.continuous.comp hc) (e.symm.injective.comp hi)
    (hnot hx) (hnot hy) (hnot hz)
  rw [← image_component_prod hx, ← image_component_prod hy, ← image_component_prod hz] at key
  rcases key with h | h | h
  · exact Or.inl (inj h)
  · exact Or.inr (Or.inl (inj h))
  · exact Or.inr (Or.inr (inj h))

/-- **The Jordan curve theorem.** The complement of the image of a continuous injective map from the circle into
`ℝ × ℝ` is the disjoint union of two open connected sets, one bounded and one unbounded, and the curve is the frontier
of each. (The chapter location in McCleary's book is verified, the lemma-level numbering is not; the proof is Lean's
own.) -/
theorem jordan_curve_theorem {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) :
    ∃ U V : Set (ℝ × ℝ), IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (range f)ᶜ ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      frontier U = range f ∧ frontier V = range f := by
  have hJo : IsOpen (range f)ᶜ := (isCompact_range hc).isClosed.isOpen_compl
  obtain ⟨⟨x₁, hx₁, hunb, -⟩, ⟨y₁, hy₁, hb, -⟩⟩ := jordan_components hc hi
  have hx₁J : x₁ ∉ range f := hx₁
  have hy₁J : y₁ ∉ range f := hy₁
  have hne : connectedComponentIn (range f)ᶜ x₁ ≠ connectedComponentIn (range f)ᶜ y₁ := fun h =>
    hunb (h ▸ hb)
  refine ⟨connectedComponentIn (range f)ᶜ y₁, connectedComponentIn (range f)ᶜ x₁, hJo.connectedComponentIn,
    hJo.connectedComponentIn, isConnected_connectedComponentIn_iff.2 hy₁, isConnected_connectedComponentIn_iff.2 hx₁,
    ?_, ?_, hb, hunb, jordan_frontier hc hi hy₁J, jordan_frontier hc hi hx₁J⟩
  · rw [Set.disjoint_left]
    intro w hwU hwV
    exact hne ((connectedComponentIn_eq hwV).trans (connectedComponentIn_eq hwU).symm)
  · refine Set.Subset.antisymm
      (Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)) fun w hw => ?_
    rcases jordan_at_most_two_prod hc hi hx₁J hy₁J hw with h | h | h
    · exact absurd h hne
    · exact Or.inl (h ▸ mem_connectedComponentIn hw)
    · exact Or.inr (h ▸ mem_connectedComponentIn hw)

end Lightlike.PL
