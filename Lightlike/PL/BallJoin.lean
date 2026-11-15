import Lightlike.PL.Slicing
import Lightlike.PL.JoinTame

/-!
# Replacing a ball inside a join

Two PL balls with the same boundary can be exchanged inside a complex `R` that meets each of them
only in that boundary (`stellarEquivIn_replace_ball`). Here the balls are replaced inside a join
`B * Z`: the exchange is carried out by moves in `B` alone, joined with `Z`, and glued to `R`. This
is what lets a ball in the link of a cell be replaced while the rest of the complex, which need
not be a manifold, stays untouched.
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V] [Infinite V]

omit [Infinite V] in
/-- A face `{x}` of `B` is a face of `B * Z`. -/
lemma singleton_mem_join_left {B Z : SComplex V} (hZ : ∅ ∈ Z) {x : V} (hx : x ∈ B.verts) :
    ({x} : Finset V) ∈ B.join Z :=
  mem_join.2 ⟨{x}, mem_verts.1 hx, ∅, hZ, union_empty _⟩

/-- **A ball is stellar equivalent to the cone on its boundary, inside a join and a complex `R`.**
`R` meets `B * Z` only in `∂B * Z`. -/
theorem stellarEquivIn_ball_cone_join {m : ℕ} {B Z R : SComplex V} (hB : IsSB true m B)
    (hbb : IsBallIn B) (hZ : ∅ ∈ Z) (hBZ : Disjoint B.verts Z.verts)
    (hv : ∀ x ∈ R.verts, x ∈ (B.join Z).verts → x ∈ (B.bd.join Z).verts)
    (hf : ∀ s ∈ B.join Z, s ∈ R → s ∈ B.bd.join Z) {w : V} (hwB : w ∉ B.verts)
    (hwZ : w ∉ Z.verts) (hwR : w ∉ R.verts) :
    StellarEquivIn ((B.join Z).union R) (((cone w B.bd).join Z).union R) := by
  have hE : B.bd.verts ⊆ B.verts := fun x hx =>
    subset_verts (bd_subset (mem_verts.1 hx)) (mem_singleton_self x)
  have hvB : ∀ x ∈ R.verts, x ∈ B.verts → x ∈ B.bd.verts := by
    intro x hxR hxB
    have := hv x hxR (mem_verts.2 (singleton_mem_join_left hZ hxB))
    rcases mem_union.1 (verts_join_subset _ _ this) with h | h
    · exact h
    · exact absurd h (disjoint_left.1 hBZ hxB)
  have hSv : ∀ x ∈ Z.verts ∪ R.verts, x ∈ B.verts → x ∈ B.bd.verts := by
    intro x hx hxB
    rcases mem_union.1 hx with h | h
    · exact absurd h (disjoint_left.1 hBZ hxB)
    · exact hvB x h hxB
  have hch := starrable_ball m B hB hbb (Z.verts ∪ R.verts) hSv w
    (by simp [hwZ, hwR]) hwB (fun h => hwB (hE h))
  have hch' := TChain.join_right hch hZ subset_union_left hBZ
  exact (hch'.glue (R := R) subset_union_right hv hf subset_union_left
    (fun s hs => .inl hs) subset_rfl).stellarEquivIn

/-- **Replacing a ball inside a join.** Two PL balls of the same dimension with the same boundary
can be exchanged inside `B * Z ∪ R`, where `R` meets each join only in `∂B * Z`. -/
theorem stellarEquivIn_replace_ball_join {m : ℕ} {B B' Z R : SComplex V}
    (hB : IsSB true m B) (hbb : IsBallIn B) (hB' : IsSB true m B') (hbb' : IsBallIn B')
    (hbd : B.bd = B'.bd) (hZ : ∅ ∈ Z) (hBZ : Disjoint B.verts Z.verts)
    (hBZ' : Disjoint B'.verts Z.verts)
    (hv : ∀ x ∈ R.verts, x ∈ (B.join Z).verts → x ∈ (B.bd.join Z).verts)
    (hf : ∀ s ∈ B.join Z, s ∈ R → s ∈ B.bd.join Z)
    (hv' : ∀ x ∈ R.verts, x ∈ (B'.join Z).verts → x ∈ (B.bd.join Z).verts)
    (hf' : ∀ s ∈ B'.join Z, s ∈ R → s ∈ B.bd.join Z) :
    StellarEquivIn ((B.join Z).union R) ((B'.join Z).union R) := by
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (B.verts ∪ B'.verts ∪ Z.verts ∪ R.verts)
  simp only [mem_union, not_or] at hw
  obtain ⟨⟨⟨hwB, hwB'⟩, hwZ⟩, hwR⟩ := hw
  have h1 := stellarEquivIn_ball_cone_join hB hbb hZ hBZ hv hf hwB hwZ hwR
  have h2 := stellarEquivIn_ball_cone_join hB' hbb' hZ hBZ' (by rwa [← hbd]) (by rwa [← hbd])
    hwB' hwZ hwR
  rw [← hbd] at h2
  exact h1.trans h2.symm

end SComplex
end Lightlike.PL
