import Lightlike.PL.Schoenflies.RegionCompact

/-!
# A neighbourhood of a simple polygon, minus the polygon's region, is connected

Row G3-188, milestone PL5 (third pass), item 5c (annulus lemma, step 1: connectedness).  For a simple polygon
`p` and an open connected set `Ω ⊇ p.carrier`, the set `Ω ∩ p.outside` is connected.  The proof:
near each point of the carrier the outside is a connected half-disc (`local_outside`); each component of
`Ω ∩ p.outside` has closure meeting the carrier (otherwise it is clopen in `Ω`); and the set of carrier
points in the closure of a component is open and closed in the (connected) carrier.

* `local_outside`: arbitrarily small balls at a carrier point meet the outside in a connected set.
* `isPreconnected_inter_outside`: `Ω ∩ p.outside` is preconnected.
* `isPreconnected_inside_diff_region`: the annulus `q.inside \ region p` is preconnected when
  `p.carrier ⊆ q.inside`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL Metric

/-- **The outside is locally connected at the carrier.** At each point `w` of a simple polygon there are
arbitrarily small balls whose intersection with the outside is connected and accumulates at `w`. -/
theorem local_outside {n : ℕ} [NeZero n] {p : Polygon n} (hs : p.IsSimple) {w : ℝ × ℝ}
    (hw : w ∈ p.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧ IsPreconnected (p.outside ∩ ball w ρ) ∧
      w ∈ closure (p.outside ∩ ball w ρ) := by
  obtain ⟨a, b, ha, hb, hnp, ρ0, hρ0, hcar⟩ := Polygon.local_data hs hw
  have hρ : 0 < min ρ0 ε := lt_min hρ0 hε
  have hcar' : ∀ z ∈ ball w (min ρ0 ε), z ∈ p.carrier ↔ z - w ∈ ray0 a ∪ ray0 b :=
    fun z hz => hcar z (ball_subset_ball (min_le_left _ _) hz)
  obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, y₁, hy₁, y₂, hy₂, hne⟩ :=
    Polygon.exists_sectors hs ha hb hnp hρ hcar'
  obtain ⟨hc, hcl⟩ := local_classes (Polygon.isClosed_carrier p)
    (fun x hx => Polygon.eventually_parity_eq p hx) h1 h2 h3 h4 h5 hy₁ hy₂ hne 0
  refine ⟨min ρ0 ε, hρ, min_le_right _ _, hc, ?_⟩
  have := isOpen_ball.inter_closure (s := ball w (min ρ0 ε)) (t := p.outside)
    ⟨mem_ball_self hρ, hcl⟩
  rwa [inter_comm] at this

/-- **A connected open neighbourhood of a simple polygon, minus the polygon's region, is connected.**
For an open preconnected `Ω` containing the carrier of a simple polygon `p`, the set `Ω ∩ p.outside` is
preconnected. -/
theorem isPreconnected_inter_outside {n : ℕ} [NeZero n] {p : Polygon n} (hs : p.IsSimple)
    {Ω : Set (ℝ × ℝ)} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω) (hsub : p.carrier ⊆ Ω) :
    IsPreconnected (Ω ∩ p.outside) := by
  set X : Set (ℝ × ℝ) := Ω ∩ p.outside with hX
  have hXo : IsOpen X := hΩo.inter p.isOpen_outside
  have hball : ∀ w ∈ p.carrier, ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Ω ∧
      IsPreconnected (p.outside ∩ ball w ρ) ∧ w ∈ closure (p.outside ∩ ball w ρ) := by
    intro w hw
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩo w (hsub hw)
    obtain ⟨ρ, hρ, hρε, hc, hcl⟩ := local_outside hs hw hε
    exact ⟨ρ, hρ, (ball_subset_ball hρε).trans hεΩ, hc, hcl⟩
  choose! ρ hρ using hball
  -- every component of `X` has closure meeting the carrier
  have hmeet : ∀ x ∈ X, (p.carrier ∩ closure (connectedComponentIn X x)).Nonempty := by
    intro x hx
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    set C := connectedComponentIn X x with hC
    have hCo : IsOpen C := hXo.connectedComponentIn
    have hCX : C ⊆ X := connectedComponentIn_subset _ _
    have hxC : x ∈ C := mem_connectedComponentIn hx
    have hcl : Ω ∩ closure C ⊆ C := by
      rintro z ⟨hzΩ, hzcl⟩
      have h1 : z ∈ closure p.outside := closure_mono (hCX.trans inter_subset_right) hzcl
      have h2 : z ∉ p.inside := fun hzi => by
        obtain ⟨y, hyi, hyo⟩ := mem_closure_iff.1 h1 _ p.isOpen_inside hzi
        exact Set.disjoint_left.1 p.disjoint_outside_inside hyo hyi
      have h3 : z ∉ p.carrier := fun hzc => by
        have : z ∈ p.carrier ∩ closure C := ⟨hzc, hzcl⟩
        rw [hemp] at this
        exact this
      have h4 : z ∈ p.outside := by
        have : z ∈ p.carrierᶜ := h3
        rw [Polygon.compl_carrier_eq] at this
        exact this.resolve_right h2
      have hzX : z ∈ X := ⟨hzΩ, h4⟩
      obtain ⟨y, hyz, hyC⟩ := mem_closure_iff.1 hzcl _ (hXo.connectedComponentIn (x := z))
        (mem_connectedComponentIn hzX)
      have e1 : C = connectedComponentIn X y := connectedComponentIn_eq hyC
      have e2 : connectedComponentIn X z = connectedComponentIn X y := connectedComponentIn_eq hyz
      rw [e1, ← e2]
      exact mem_connectedComponentIn hzX
    have := isPreconnected_iff_subset_of_disjoint.1 hΩc C (closure C)ᶜ hCo
      isClosed_closure.isOpen_compl
      (fun y hy => by
        by_cases h : y ∈ closure C
        · exact Or.inl (hcl ⟨hy, h⟩)
        · exact Or.inr h)
      (eq_empty_of_forall_notMem fun y ⟨_, hyC, hyn⟩ => hyn (subset_closure hyC))
    obtain ⟨w, hw⟩ := Polygon.carrier_nonempty p
    rcases this with h | h
    · exact (hCX (h (hsub hw))).2.1 hw
    · exact h (hCX hxC).1 (subset_closure hxC)
  -- the local pieces lie in a single component
  have hB : ∀ x ∈ X, ∀ w ∈ p.carrier, w ∈ closure (connectedComponentIn X x) →
      p.outside ∩ ball w (ρ w) ⊆ connectedComponentIn X x := by
    intro x hx w hw hwcl
    obtain ⟨hρpos, hρΩ, hρc, -⟩ := hρ w hw
    obtain ⟨y, hyb, hyC⟩ := mem_closure_iff.1 hwcl _ isOpen_ball (mem_ball_self hρpos)
    have hyX : y ∈ X := connectedComponentIn_subset _ _ hyC
    have e1 : connectedComponentIn X x = connectedComponentIn X y := connectedComponentIn_eq hyC
    rw [e1]
    exact hρc.subset_connectedComponentIn ⟨hyX.2, hyb⟩ fun z hz => ⟨hρΩ hz.2, hz.1⟩
  -- the carrier lies in the closure of every component
  have hall : ∀ x ∈ X, p.carrier ⊆ closure (connectedComponentIn X x) := by
    intro x hx
    set C := connectedComponentIn X x with hC
    have hnb : ∀ w ∈ p.carrier, w ∈ closure C → ∀ z ∈ p.carrier, z ∈ ball w (ρ w) →
        z ∈ closure C := by
      intro w hw hwcl z hz hzb
      have h1 : z ∈ closure p.outside := Polygon.carrier_subset_closure_class hs 0 hz
      have h2 := isOpen_ball.inter_closure (s := ball w (ρ w)) (t := p.outside) ⟨hzb, h1⟩
      rw [inter_comm] at h2
      exact closure_mono (hB x hx w hw hwcl) h2
    have := (Polygon.isPreconnected_carrier p)
    have h5 := isPreconnected_iff_subset_of_disjoint.1 this
      (⋃ w ∈ p.carrier ∩ closure C, ball w (ρ w)) (closure C)ᶜ
      (isOpen_biUnion fun _ _ => isOpen_ball) isClosed_closure.isOpen_compl
      (fun z hz => by
        by_cases h : z ∈ closure C
        · exact Or.inl (mem_biUnion (x := z) ⟨hz, h⟩ (mem_ball_self (hρ z hz).1))
        · exact Or.inr h)
      (eq_empty_of_forall_notMem fun z ⟨hz, hzu, hzn⟩ => by
        obtain ⟨w, hw, hzb⟩ := mem_iUnion₂.1 hzu
        exact hzn (hnb w hw.1 hw.2 z hz hzb))
    rcases h5 with h | h
    · intro z hz
      obtain ⟨w, hw, hzb⟩ := mem_iUnion₂.1 (h hz)
      exact hnb w hw.1 hw.2 z hz hzb
    · obtain ⟨w, hw, hwcl⟩ := hmeet x hx
      exact (h hw hwcl).elim
  rcases X.eq_empty_or_nonempty with hXe | ⟨x0, hx0⟩
  · rw [hXe]; exact isPreconnected_empty
  · obtain ⟨w0, hw0⟩ := Polygon.carrier_nonempty p
    obtain ⟨-, -, -, hcl0⟩ := hρ w0 hw0
    obtain ⟨z, hz⟩ := closure_nonempty_iff.1 ⟨w0, hcl0⟩
    refine isPreconnected_of_forall x0 fun y hy => ?_
    have hz0 := hB x0 hx0 w0 hw0 (hall x0 hx0 hw0) hz
    have hzy := hB y hy w0 hw0 (hall y hy hw0) hz
    refine ⟨connectedComponentIn X x0 ∪ connectedComponentIn X y,
      union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _),
      Or.inl (mem_connectedComponentIn hx0), Or.inr (mem_connectedComponentIn hy), ?_⟩
    exact IsPreconnected.union z hz0 hzy isPreconnected_connectedComponentIn
      isPreconnected_connectedComponentIn

/-- **The annulus between two nested simple polygons is connected.** If the carrier of `p` lies in the
inside of `q` then `q.inside \ region p` is preconnected. -/
theorem isPreconnected_inside_diff_region {n m : ℕ} [NeZero n] [NeZero m] {p : Polygon n}
    {q : Polygon m} (hp : p.IsSimple) (hq : q.IsSimple) (hsub : p.carrier ⊆ q.inside) :
    IsPreconnected (q.inside \ region p) := by
  have h := isPreconnected_inter_outside hp (Polygon.isOpen_inside q) (Polygon.isPreconnected_inside hq) hsub
  have heq : q.inside \ region p = q.inside ∩ p.outside := by
    ext y
    simp only [mem_sdiff, mem_inter_iff, region, mem_union, not_or]
    constructor
    · rintro ⟨hy, hi, hc⟩
      refine ⟨hy, ?_⟩
      have : y ∈ p.carrierᶜ := hc
      rw [Polygon.compl_carrier_eq] at this
      exact this.resolve_right hi
    · rintro ⟨hy, ho⟩
      exact ⟨hy, fun hi => Set.disjoint_left.1 p.disjoint_outside_inside ho hi, ho.1⟩
  rw [heq]
  exact h

end Lightlike.PL.Schoenflies
