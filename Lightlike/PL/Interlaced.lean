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

end Lightlike.PL
