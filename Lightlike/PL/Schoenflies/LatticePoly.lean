import Lightlike.PL.Schoenflies.LatticeSeg
import Lightlike.PL.Polygon

/-!
# Boundary cycles are simple polygons

Row G3-188, milestone PL5 (third pass), item 5b, route A.  A cyclic sequence of distinct lattice points
with consecutive points at unit distance is a simple polygon (`latticePoly_isSimple`), and so is its
rescaling by a positive factor (`smul_isSimple`).  With `exists_boundary_cycle` this turns the boundary of a
finite pinch-free union of lattice squares into a simple polygon.
-/

namespace Lightlike.PL.Schoenflies

open Set

lemma rot_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro h
  have h' := congrArg Fin.val h
  have := i.isLt
  simp only [coe_finRotate, Fin.ext_iff, Fin.val_last] at h'
  split_ifs at h' <;> omega

lemma rot2_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : finRotate n (finRotate n i) ≠ i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro h
  have h' := congrArg Fin.val h
  have := i.isLt
  simp only [coe_finRotate, Fin.ext_iff, Fin.val_last] at h'
  split_ifs at h' <;> omega

/-- The polygon through the lattice points `v i`. -/
def latticePoly {n : ℕ} (v : Fin n → ℤ × ℤ) : Polygon n := fun i => pt (v i)

lemma pt_injective : Function.Injective pt := by
  intro a b h
  simp only [pt, Prod.mk.injEq] at h
  exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)

lemma mem_pair_inj {n : ℕ} {v : Fin n → ℤ × ℤ} (hv : Function.Injective v) {a b c : Fin n}
    (h : v a ∈ ({v b, v c} : Set (ℤ × ℤ))) : a = b ∨ a = c := by
  rcases h with h | h
  · exact Or.inl (hv h)
  · exact Or.inr (hv (Set.mem_singleton_iff.1 h))

/-- **A cycle of distinct lattice points with unit steps is a simple polygon.** -/
theorem latticePoly_isSimple {n : ℕ} (hn : 3 ≤ n) {v : Fin n → ℤ × ℤ} (hv : Function.Injective v)
    (hs : ∀ i, UnitStep (v i) (v (finRotate n i))) : (latticePoly v).IsSimple := by
  have hrot : Function.Injective (finRotate n) := (finRotate n).injective
  have edge_eq : ∀ i, (latticePoly v).edge i = segment ℝ (pt (v i)) (pt (v (finRotate n i))) :=
    fun i => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i h
    exact (hs i).ne (pt_injective h)
  · intro i j hij hi hj
    rw [Set.disjoint_left]
    intro z hz hz'
    rw [edge_eq] at hz hz'
    rcases seg_inter (hs i) (hs j) hz hz' with h | ⟨w, hw1, hw2, -⟩
    · have h1 : v i ∈ ({v j, v (finRotate n j)} : Set (ℤ × ℤ)) := by rw [← h]; simp
      have h2 : v (finRotate n i) ∈ ({v j, v (finRotate n j)} : Set (ℤ × ℤ)) := by rw [← h]; simp
      rcases mem_pair_inj hv h1 with e | e
      · exact hij e
      · exact hj e.symm
    · rcases hw1 with rfl | hw1
      · rcases mem_pair_inj hv (a := i) (b := j) (c := finRotate n j) hw2 with e | e
        · exact hij e
        · exact hj e.symm
      · have hw1 : w = v (finRotate n i) := hw1
        subst hw1
        rcases mem_pair_inj hv (a := finRotate n i) (b := j) (c := finRotate n j) hw2 with e | e
        · exact hi e
        · exact hij (hrot e)
  · intro i
    apply Set.Subset.antisymm
    · intro z ⟨hz, hz'⟩
      rw [edge_eq] at hz hz'
      rcases seg_inter (hs i) (hs (finRotate n i)) hz hz' with h | ⟨w, hw1, hw2, hzw⟩
      · exfalso
        have h1 : v i ∈ ({v (finRotate n i), v (finRotate n (finRotate n i))} : Set (ℤ × ℤ)) := by
          rw [← h]; simp
        rcases mem_pair_inj hv h1 with e | e
        · exact rot_ne (by omega) i e.symm
        · exact rot2_ne hn i e.symm
      · have hw : w = v (finRotate n i) := by
          rcases hw1 with rfl | hw1
          · exfalso
            rcases mem_pair_inj hv (a := i) (b := finRotate n i) (c := finRotate n (finRotate n i))
              hw2 with e | e
            · exact rot_ne (by omega) i e.symm
            · exact rot2_ne hn i e.symm
          · exact hw1
        rw [hzw, hw]
        rfl
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨by rw [edge_eq]; exact right_mem_segment ℝ _ _,
        by rw [edge_eq]; exact left_mem_segment ℝ _ _⟩

/-- Rescaling a simple polygon by a positive factor keeps it simple. -/
theorem smul_isSimple {n : ℕ} {p : Polygon n} (hp : p.IsSimple) {h : ℝ} (hh : h ≠ 0) :
    Polygon.IsSimple (n := n) (fun i => h • p i) := by
  set f : ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ := (LinearMap.lsmul ℝ (ℝ × ℝ) h).toAffineMap with hf
  have finj : Function.Injective f := by
    intro a b hab
    simpa [hf, hh] using hab
  have fapp : ∀ a, f a = h • a := fun a => rfl
  have edge_eq : ∀ i, Polygon.edge (n := n) (fun i => h • p i) i = f '' p.edge i := by
    intro i
    simp only [Polygon.edge]
    rw [image_segment, fapp, fapp]
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact h1 i (finj (by rw [fapp, fapp]; exact hi))
  · intro i j hij hi hj
    rw [edge_eq, edge_eq]
    exact Set.disjoint_image_of_injective finj (h2 i j hij hi hj)
  · intro i
    rw [edge_eq, edge_eq, ← Set.image_inter finj, h3 i, Set.image_singleton, fapp]

end Lightlike.PL.Schoenflies
