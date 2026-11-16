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

end Polygon

end Lightlike.PL
