import Lightlike.PL.OrderComplex

/-!
# Replacing a ball by another ball with the same boundary

Two PL balls with the same boundary sphere are interchangeable inside a bigger complex that meets
them only along that boundary: both are stellar equivalent, relative to the boundary, to the cone
on it (Lickorish's Theorem 3.6), and such equivalences extend to the surrounding complex. This is
the local replacement step of the slicing induction in Newman's theorem.
-/

open Finset

namespace Lightlike.PL
namespace SComplex
variable {V : Type*} [DecidableEq V]

/-- A ball `B` is stellar equivalent to the cone on its boundary, inside any complex `R` that
meets `B` only in `B.bd`. -/
theorem stellarEquivIn_ball_cone [Infinite V] {m : ℕ} {B R : SComplex V} (hB : IsSB true m B)
    (hbb : IsBallIn B) (hv : ∀ x ∈ R.verts, x ∈ B.verts → x ∈ B.bd.verts)
    (hf : ∀ s ∈ B, s ∈ R → s ∈ B.bd) {w : V} (hwB : w ∉ B.verts) (hwR : w ∉ R.verts) :
    StellarEquivIn (B.union R) ((cone w B.bd).union R) := by
  have hE : B.bd.verts ⊆ B.verts := fun x hx => subset_verts (bd_subset (mem_verts.1 hx)) (mem_singleton_self x)
  have hch := starrable_ball m B hB hbb R.verts hv w hwR hwB (fun h => hwB (hE h))
  exact (hch.glue (R := R) subset_rfl hv hf (subset_union_left) (fun s hs => .inl hs)
    subset_rfl).stellarEquivIn

/-- **Replacing a ball.** Two PL balls of the same dimension with the same boundary can be
exchanged inside a complex `R` meeting each of them only in that boundary. -/
theorem stellarEquivIn_replace_ball [Infinite V] {m : ℕ} {B B' R : SComplex V}
    (hB : IsSB true m B) (hbb : IsBallIn B) (hB' : IsSB true m B') (hbb' : IsBallIn B')
    (hbd : B.bd = B'.bd) (hv : ∀ x ∈ R.verts, x ∈ B.verts → x ∈ B.bd.verts)
    (hf : ∀ s ∈ B, s ∈ R → s ∈ B.bd) (hv' : ∀ x ∈ R.verts, x ∈ B'.verts → x ∈ B.bd.verts)
    (hf' : ∀ s ∈ B', s ∈ R → s ∈ B.bd) :
    StellarEquivIn (B.union R) (B'.union R) := by
  obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (B.verts ∪ B'.verts ∪ R.verts)
  simp only [mem_union, not_or] at hw
  obtain ⟨⟨hwB, hwB'⟩, hwR⟩ := hw
  have h1 := stellarEquivIn_ball_cone hB hbb hv hf hwB hwR
  have h2 := stellarEquivIn_ball_cone hB' hbb' (by rwa [← hbd]) (by rwa [← hbd]) hwB' hwR
  rw [← hbd] at h2
  exact h1.trans h2.symm

end SComplex
end Lightlike.PL
