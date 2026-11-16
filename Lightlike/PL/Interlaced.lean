import Lightlike.PL.Theta

/-!
# Interlaced chords of a polygon cannot lie on the same side

Let `C` be a simple polygon made of two arcs `arc1` from `a` to `b` and `arc2` from `b` to `a`,
`e` a polygonal chord from `a` to `b`, and `f` a polygonal chord from a point `x` inside `arc1` to a
point `y` inside `arc2`, all meeting only where forced. Then `e` and `f` cannot lie on the same
side of `C`.

The proof splits `C` along `e` into `C₁ = arc1 ∪ e` and `C₂ = arc2 ∪ e`; the parities of the
crossings of the horizontal ray add up modulo 2 (`parity_theta`), the chord `f` is connected and
meets neither carrier, so it lies in one parity class, and near its ends both parities of the other
polygon occur (`near_two`). The proof splits the 6-cycle of `K₃,₃` along chords in this way instead
of using an orientation argument.
-/

open Set

namespace Lightlike.PL

lemma exists_near_first {x y : ℝ × ℝ} {m : List (ℝ × ℝ)} (hf : IsSimpleChain (x :: m ++ [y]))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ u ∈ chainSet (x :: m ++ [y]), u ≠ x ∧ dist u x < ρ := by
  rcases m with _ | ⟨w, r⟩
  · have hxy : x ≠ y := hf.1
    obtain ⟨u, -, hu2, hu3, hu4⟩ := exists_near_start (r := []) hxy hρ
    exact ⟨u, hu4, hu2, hu3⟩
  · have hxw : x ≠ w := hf.1
    obtain ⟨u, -, hu2, hu3, hu4⟩ := exists_near_start (r := r ++ [y]) hxw hρ
    exact ⟨u, by simpa using hu4, hu2, hu3⟩

lemma exists_near_last {x y : ℝ × ℝ} {m : List (ℝ × ℝ)} (hf : IsSimpleChain (x :: m ++ [y]))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ u ∈ chainSet (x :: m ++ [y]), u ≠ y ∧ dist u y < ρ := by
  rcases List.eq_nil_or_concat m with rfl | ⟨m', z, rfl⟩
  · have hxy : x ≠ y := hf.1
    obtain ⟨u, -, hu2, hu3, hu4⟩ := exists_near_end (c := []) hxy hρ
    exact ⟨u, hu4, hu2, hu3⟩
  · simp only [List.concat_eq_append] at hf ⊢
    have hzy : z ≠ y := by
      have h := isSimpleChain_reverse hf
      have e : (x :: (m' ++ [z]) ++ [y]).reverse = y :: z :: (x :: m').reverse := by simp
      rw [e] at h
      exact h.1.symm
    obtain ⟨u, -, hu2, hu3, hu4⟩ := exists_near_end (c := x :: m') hzy hρ
    exact ⟨u, by simpa using hu4, hu2, hu3⟩

/-- **Interlaced chords of a simple polygon cannot lie on the same side.** -/
theorem no_interlaced_chord {a b x y : ℝ × ℝ} {m₁ m₂ mₑ m_f : List (ℝ × ℝ)} (hab : a ≠ b)
    (h₁ : IsSimpleChain (a :: m₁ ++ [b])) (h₂ : IsSimpleChain (b :: m₂ ++ [a]))
    (hₑ : IsSimpleChain (a :: mₑ ++ [b])) (h_f : IsSimpleChain (x :: m_f ++ [y]))
    (h₁₂ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (b :: m₂ ++ [a]) = {a, b})
    (h₁ₑ : chainSet (a :: m₁ ++ [b]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (h₂ₑ : chainSet (b :: m₂ ++ [a]) ∩ chainSet (a :: mₑ ++ [b]) = {a, b})
    (hx₁ : x ∈ chainSet (a :: m₁ ++ [b])) (hxa : x ≠ a) (hxb : x ≠ b)
    (hy₂ : y ∈ chainSet (b :: m₂ ++ [a])) (hya : y ≠ a) (hyb : y ≠ b)
    (hf₁ : chainSet (x :: m_f ++ [y]) ∩ chainSet (a :: m₁ ++ [b]) = {x})
    (hf₂ : chainSet (x :: m_f ++ [y]) ∩ chainSet (b :: m₂ ++ [a]) = {y})
    (hfₑ : chainSet (x :: m_f ++ [y]) ∩ chainSet (a :: mₑ ++ [b]) = ∅)
    (hside : (chainSet (a :: mₑ ++ [b]) \ {a, b} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside ∧
        chainSet (x :: m_f ++ [y]) \ {x, y} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).inside) ∨
      (chainSet (a :: mₑ ++ [b]) \ {a, b} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).outside ∧
        chainSet (x :: m_f ++ [y]) \ {x, y} ⊆ (Polygon.ofList (a :: m₁ ++ b :: m₂)).outside)) :
    False := by
  classical
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  set A₁ := chainSet (a :: m₁ ++ [b]) with hA₁
  set A₂ := chainSet (b :: m₂ ++ [a]) with hA₂
  set E := chainSet (a :: mₑ ++ [b]) with hE
  set F := chainSet (x :: m_f ++ [y]) with hF
  set C := Polygon.ofList (a :: m₁ ++ b :: m₂) with hC
  set C₁ := Polygon.ofList (a :: m₁ ++ b :: mₑ.reverse) with hC₁
  set C₂ := Polygon.ofList (b :: m₂ ++ a :: mₑ) with hC₂
  have iC : NeZero (a :: m₁ ++ b :: m₂).length := ⟨by simp⟩
  have iC₁ : NeZero (a :: m₁ ++ b :: mₑ.reverse).length := ⟨by simp⟩
  have iC₂ : NeZero (b :: m₂ ++ a :: mₑ).length := ⟨by simp⟩
  -- the three polygons are simple
  have hrev : (a :: mₑ ++ [b]).reverse = b :: mₑ.reverse ++ [a] := by simp
  have hEr : IsSimpleChain (b :: mₑ.reverse ++ [a]) := hrev ▸ isSimpleChain_reverse hₑ
  have hEs : chainSet (b :: mₑ.reverse ++ [a]) = E := by
    rw [← hrev, chainSet_reverse]
  have sC : C.IsSimple := isSimple_two_arcs h₁ h₂ h₁₂ hab
  have sC₁ : C₁.IsSimple := isSimple_two_arcs h₁ hEr (by rw [hEs]; exact h₁ₑ) hab
  have sC₂ : C₂.IsSimple := isSimple_two_arcs (a := b) (b := a) h₂ hₑ
    (by rw [Set.pair_comm]; exact h₂ₑ) hab.symm
  have cC : C.carrier = A₁ ∪ A₂ := carrier_two_arcs a b m₁ m₂
  have cC₁ : C₁.carrier = A₁ ∪ E := by
    have := carrier_two_arcs a b m₁ mₑ.reverse
    rw [hEs] at this; exact this
  have cC₂ : C₂.carrier = A₂ ∪ E := carrier_two_arcs b a m₂ mₑ
  have hpar : ∀ z, C₁.parity z + C₂.parity z = C.parity z := fun z => parity_theta a b z m₁ m₂ mₑ
  -- the points `a`, `b`, `x`, `y`
  have haA₁ : a ∈ A₁ := mem_chainSet_head a _
  have haA₂ : a ∈ A₂ := mem_chainSet_last (b :: m₂) a
  have hbA₁ : b ∈ A₁ := mem_chainSet_last (a :: m₁) b
  have hbA₂ : b ∈ A₂ := mem_chainSet_head b _
  have hxA₂ : x ∉ A₂ := fun h => by
    have : x ∈ A₁ ∩ A₂ := ⟨hx₁, h⟩
    rw [h₁₂] at this
    rcases this with rfl | rfl
    · exact hxa rfl
    · exact hxb rfl
  have hxE : x ∉ E := fun h => by
    have : x ∈ A₁ ∩ E := ⟨hx₁, h⟩
    rw [h₁ₑ] at this
    rcases this with rfl | rfl
    · exact hxa rfl
    · exact hxb rfl
  have hyA₁ : y ∉ A₁ := fun h => by
    have : y ∈ A₁ ∩ A₂ := ⟨h, hy₂⟩
    rw [h₁₂] at this
    rcases this with rfl | rfl
    · exact hya rfl
    · exact hyb rfl
  have hyE : y ∉ E := fun h => by
    have : y ∈ A₂ ∩ E := ⟨hy₂, h⟩
    rw [h₂ₑ] at this
    rcases this with rfl | rfl
    · exact hya rfl
    · exact hyb rfl
  have hxy : x ≠ y := fun h => hxA₂ (h ▸ hy₂)
  have hxF : x ∈ F := mem_chainSet_head x _
  have hyF : y ∈ F := mem_chainSet_last (x :: m_f) y
  -- the open chord
  set F₀ := F \ {x, y} with hF₀
  have hF₀pre : IsPreconnected F₀ := isPreconnected_chainSet_diff_ends' h_f
  have hF₀N : ∀ z ∈ F₀, z ∉ A₁ ∧ z ∉ A₂ ∧ z ∉ E := by
    intro z ⟨hzF, hzxy⟩
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have : z ∈ F ∩ A₁ := ⟨hzF, h⟩
      rw [hf₁] at this
      exact hzxy (Or.inl (by simpa using this))
    · have : z ∈ F ∩ A₂ := ⟨hzF, h⟩
      rw [hf₂] at this
      exact hzxy (Or.inr (by simpa using this))
    · have : z ∈ F ∩ E := ⟨hzF, h⟩
      rw [hfₑ] at this
      exact this
  have hclA₁ : IsClosed A₁ := isClosed_chainSet _
  have hclA₂ : IsClosed A₂ := isClosed_chainSet _
  have hclE : IsClosed E := isClosed_chainSet _
  -- points of the chord near its ends
  have hnear_x : ∀ ρ > 0, ∃ u ∈ F₀, dist u x < ρ := by
    intro ρ hρ
    have hd : 0 < dist x y := dist_pos.2 hxy
    obtain ⟨u, hu1, hu2, hu3⟩ := exists_near_first h_f (lt_min hρ hd)
    refine ⟨u, ⟨hu1, ?_⟩, lt_of_lt_of_le hu3 (min_le_left _ _)⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨hu2, fun h => ?_⟩
    have := lt_of_lt_of_le hu3 (min_le_right _ _)
    rw [h, dist_comm] at this
    exact lt_irrefl _ this
  have hnear_y : ∀ ρ > 0, ∃ u ∈ F₀, dist u y < ρ := by
    intro ρ hρ
    have hd : 0 < dist x y := dist_pos.2 hxy
    obtain ⟨u, hu1, hu2, hu3⟩ := exists_near_last h_f (lt_min hρ hd)
    refine ⟨u, ⟨hu1, ?_⟩, lt_of_lt_of_le hu3 (min_le_left _ _)⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨fun h => ?_, hu2⟩
    have := lt_of_lt_of_le hu3 (min_le_right _ _)
    rw [h] at this
    exact lt_irrefl _ this
  sorry

end Lightlike.PL