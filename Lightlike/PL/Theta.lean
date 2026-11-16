import Lightlike.PL.ChainCarrier

/-!
# Local jumps and the theta configuration

Near a point of the carrier of a simple polygon, points of either parity occur arbitrarily close,
off any given closed set that does not contain the point.
-/

open Set Metric

namespace Lightlike.PL

lemma isClosed_chainSet : ∀ l : List (ℝ × ℝ), IsClosed (chainSet l)
  | [] => by simp [chainSet]
  | [a] => by simp [chainSet]
  | a :: b :: l => by
    simp only [chainSet]
    exact (isCompact_segment' ..).isClosed.union (isClosed_chainSet (b :: l))

/-- **The carrier of a polygon made of two arcs is the union of the arcs.** -/
theorem carrier_two_arcs (a b : ℝ × ℝ) (m₁ m₂ : List (ℝ × ℝ)) :
    (Polygon.ofList (a :: m₁ ++ b :: m₂)).carrier =
      chainSet (a :: m₁ ++ [b]) ∪ chainSet (b :: m₂ ++ [a]) := by
  rcases List.eq_nil_or_concat m₂ with rfl | ⟨m₂', z, rfl⟩
  · have h := @carrier_ofList a b m₁
    simp only [List.nil_append, List.cons_append] at h ⊢
    rw [h, chainSet_pair b a, segment_symm ℝ b a]
  · simp only [List.concat_eq_append]
    have e : a :: m₁ ++ b :: (m₂' ++ [z]) = a :: (m₁ ++ b :: m₂') ++ [z] := by simp
    suffices H : ∀ L : List (ℝ × ℝ), L = a :: (m₁ ++ b :: m₂') ++ [z] →
        (Polygon.ofList L).carrier =
          chainSet (a :: m₁ ++ [b]) ∪ chainSet (b :: (m₂' ++ [z]) ++ [a]) from H _ (by simp)
    intro L hL
    subst hL
    rw [carrier_ofList]
    have hQ : chainSet (b :: (m₂' ++ [z]) ++ [a]) = chainSet (b :: m₂' ++ [z]) ∪ segment ℝ z a := by
      have := chainSet_append (b :: m₂') z [a]
      rw [show (b :: m₂') ++ z :: [a] = b :: (m₂' ++ [z]) ++ [a] from by simp,
        show (b :: m₂') ++ [z] = b :: m₂' ++ [z] from rfl, chainSet_pair] at this
      exact this
    have hW : chainSet (a :: (m₁ ++ b :: m₂') ++ [z]) =
        chainSet (a :: m₁ ++ [b]) ∪ chainSet (b :: m₂' ++ [z]) := by
      have := chainSet_append (a :: m₁) b (m₂' ++ [z])
      rw [show (a :: m₁) ++ b :: (m₂' ++ [z]) = a :: (m₁ ++ b :: m₂') ++ [z] from by simp] at this
      rw [this]
      simp
    rw [hW, hQ]
    ext y; simp only [mem_union]; tauto

/-- A simple chain from `x` to `y` minus its ends is preconnected (the chain given as
`x :: m ++ [y]`). -/
theorem isPreconnected_chainSet_diff_ends' {x y : ℝ × ℝ} {m : List (ℝ × ℝ)}
    (h : IsSimpleChain (x :: m ++ [y])) :
    IsPreconnected (chainSet (x :: m ++ [y]) \ {x, y}) := by
  rcases m with _ | ⟨c, m'⟩
  · have : chainSet [x, y] \ {x, y} = segment ℝ x y \ {x, y} := by rw [chainSet_pair]
    have h' : IsSimpleChain [x, y] := h
    show IsPreconnected (chainSet [x, y] \ {x, y})
    rw [this]
    exact isPreconnected_segment_diff_ends h'.1
  · have := isPreconnected_chainSet_diff_ends (a := x) (b := c) (l := m' ++ [y])
      (by simpa using h)
    simpa using this

/-- Points of the first segment of a chain, other than its start, come arbitrarily close to the
start. -/
lemma exists_near_start {x w : ℝ × ℝ} {r : List (ℝ × ℝ)} (hxw : x ≠ w) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ u ∈ segment ℝ x w, u ≠ x ∧ dist u x < ρ ∧ u ∈ chainSet (x :: w :: r) := by
  set d := dist w x with hd
  have hd0 : 0 < d := dist_pos.2 hxw.symm
  set t : ℝ := min 1 (ρ / (2 * d)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hρ (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ ρ / (2 * d) := min_le_right _ _
  refine ⟨AffineMap.lineMap x w t, ?_, ?_, ?_, ?_⟩
  · rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht0.le, ht1⟩, rfl⟩
  · intro h
    have := (AffineMap.lineMap_injective ℝ hxw) (h.trans (AffineMap.lineMap_apply_zero x w).symm)
    exact ht0.ne' this
  · rw [dist_lineMap_left, Real.norm_of_nonneg ht0.le, dist_comm x w]
    have : t * d ≤ ρ / 2 := by
      calc t * d ≤ ρ / (2 * d) * d := mul_le_mul_of_nonneg_right ht2 hd0.le
        _ = ρ / 2 := by field_simp
    linarith
  · simp only [chainSet]
    left
    rw [segment_eq_image_lineMap]; exact ⟨t, ⟨ht0.le, ht1⟩, rfl⟩

/-- Points of the last segment of a chain, other than its end, come arbitrarily close to the end. -/
lemma exists_near_end {c : List (ℝ × ℝ)} {z y : ℝ × ℝ} (hzy : z ≠ y) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ u ∈ segment ℝ z y, u ≠ y ∧ dist u y < ρ ∧ u ∈ chainSet (c ++ [z, y]) := by
  obtain ⟨u, hu1, hu2, hu3, -⟩ := exists_near_start (r := []) hzy.symm hρ
  refine ⟨u, by rw [segment_symm]; exact hu1, hu2, hu3, ?_⟩
  have := chainSet_append c z [y]
  rw [show c ++ z :: [y] = c ++ [z, y] from rfl] at this
  rw [this]
  right
  rw [chainSet_pair]
  rw [segment_symm]; exact hu1

namespace Polygon

variable {n : ℕ} [NeZero n]

/-- **Both parities occur near a point of the carrier**, off a closed set missing the point. -/
theorem exists_near_parity {Pg : Polygon n} (hs : Pg.IsSimple) {w : ℝ × ℝ}
    (hw : w ∈ Pg.carrier) {F : Set (ℝ × ℝ)} (hF : IsClosed F) (hwF : w ∉ F) (c : ZMod 2) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ z, z ∈ ball w ρ ∧ z ∉ Pg.carrier ∧ z ∉ F ∧ Pg.parity z = c := by
  have hcl := carrier_subset_closure_class hs c hw
  have hU : IsOpen (ball w ρ ∩ Fᶜ) := isOpen_ball.inter hF.isOpen_compl
  obtain ⟨z, ⟨hz1, hz2⟩, hz3, hz4⟩ := mem_closure_iff.1 hcl _ hU ⟨mem_ball_self hρ, hwF⟩
  exact ⟨z, hz1, hz3, hz2, hz4⟩

omit [NeZero n] in
/-- The parity is locally constant off the carrier. -/
lemma locally_const_parity {Pg : Polygon n} {w : ℝ × ℝ} (hw : w ∉ Pg.carrier) :
    ∃ ε > 0, ∀ u, dist u w < ε → u ∉ Pg.carrier ∧ Pg.parity u = Pg.parity w := by
  have h1 : ∀ᶠ u in nhds w, u ∉ Pg.carrier := (isClosed_carrier Pg).isOpen_compl.mem_nhds hw
  have h2 : ∀ᶠ u in nhds w, Pg.parity u = Pg.parity w := eventually_parity_eq Pg hw
  obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
  exact ⟨ε, hε, fun u hu => h hu⟩

/-- **Nearby points with a prescribed parity for one polygon and the parity of the other.** -/
theorem near_two {m k : ℕ} [NeZero m] [NeZero k] {P₁ : Polygon m} {P₂ : Polygon k}
    (hs₂ : P₂.IsSimple) {w : ℝ × ℝ} (hw₂ : w ∈ P₂.carrier) (hw₁ : w ∉ P₁.carrier)
    {F : Set (ℝ × ℝ)} (hF : IsClosed F) (hwF : w ∉ F) (c : ZMod 2) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z, dist z w < ρ ∧ z ∉ P₂.carrier ∧ z ∉ F ∧ P₂.parity z = c ∧ z ∉ P₁.carrier ∧
      P₁.parity z = P₁.parity w := by
  obtain ⟨ε, hε, h⟩ := locally_const_parity hw₁
  obtain ⟨z, hz1, hz2, hz3, hz4⟩ := exists_near_parity hs₂ hw₂ hF hwF c (lt_min hρ hε)
  have hd : dist z w < min ρ ε := by simpa using hz1
  exact ⟨z, lt_of_lt_of_le hd (min_le_left _ _), hz2, hz3, hz4,
    (h z (lt_of_lt_of_le hd (min_le_right _ _))).1, (h z (lt_of_lt_of_le hd (min_le_right _ _))).2⟩

omit [NeZero n] in
/-- A preconnected set off the carrier has constant parity. -/
lemma const_parity_of_preconnected {Pg : Polygon n} {S : Set (ℝ × ℝ)} (hS : IsPreconnected S)
    (hc : S ⊆ Pg.carrierᶜ) : ∃ s : ZMod 2, ∀ z ∈ S, Pg.parity z = s := by
  rcases subset_outside_or_inside hS hc with h | h
  · exact ⟨0, fun z hz => (h hz).2⟩
  · exact ⟨1, fun z hz => (h hz).2⟩

end Polygon

end Lightlike.PL
