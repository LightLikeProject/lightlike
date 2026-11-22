import Lightlike.PL.Schoenflies.LatticeGraph

/-!
# Unit lattice segments

Row G3-188, milestone PL5 (third pass), item 5b, route A.  Two unit segments between lattice points of
the plane meet only in a common endpoint, unless they are the same segment (`seg_inter`).  This is the
geometric input for turning a cycle of the boundary graph (`LatticeCycle`) into a simple polygon.

* `pt a`: the lattice point `a` as a point of `ℝ × ℝ`.
* `UnitStep a b`: `b` is a neighbour of `a` in the lattice.
* `seg_inter`: two unit segments are equal or meet in a common endpoint.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- A lattice point as a point of the plane. -/
def pt (a : ℤ × ℤ) : ℝ × ℝ := ((a.1 : ℝ), (a.2 : ℝ))

/-- `b` is a lattice neighbour of `a`. -/
def UnitStep (a b : ℤ × ℤ) : Prop :=
  (b.1 = a.1 + 1 ∧ b.2 = a.2) ∨ (a.1 = b.1 + 1 ∧ b.2 = a.2) ∨
  (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (b.1 = a.1 ∧ a.2 = b.2 + 1)

lemma UnitStep.symm {a b : ℤ × ℤ} (h : UnitStep a b) : UnitStep b a := by
  unfold UnitStep at h ⊢
  omega

lemma UnitStep.ne {a b : ℤ × ℤ} (h : UnitStep a b) : a ≠ b := by
  intro e
  subst e
  unfold UnitStep at h
  omega

/-- Boundary graph edges are unit steps. -/
lemma BdAdj.unitStep {S : Set (ℤ × ℤ)} {a b : ℤ × ℤ} (h : BdAdj S a b) : UnitStep a b := by
  unfold BdAdj at h
  unfold UnitStep
  omega

/-- A point of a unit segment, in normal form: a horizontal or a vertical unit lattice edge. -/
lemma seg_unit {a b : ℤ × ℤ} (hu : UnitStep a b) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ (pt a) (pt b)) :
    ∃ x y : ℤ, (({a, b} : Set (ℤ × ℤ)) = {(x, y), (x + 1, y)} ∧ z.2 = y ∧ (x : ℝ) ≤ z.1 ∧
        z.1 ≤ x + 1) ∨
      (({a, b} : Set (ℤ × ℤ)) = {(x, y), (x, y + 1)} ∧ z.1 = x ∧ (y : ℝ) ≤ z.2 ∧ z.2 ≤ y + 1) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  have hs' : s = 1 - t := by linarith
  subst hs'
  simp only [UnitStep] at hu
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hb : b = (a.1 + 1, a.2) := Prod.ext h1 h2
    subst hb
    refine ⟨a.1, a.2, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
    · simp [pt]; ring
    · simp [pt]; linarith
    · simp [pt]; linarith
  · have ha : a = (b.1 + 1, b.2) := Prod.ext h1 h2.symm
    subst ha
    refine ⟨b.1, b.2, Or.inl ⟨Set.pair_comm _ _, ?_, ?_, ?_⟩⟩
    · simp [pt]; ring
    · simp [pt]; linarith
    · simp [pt]; linarith
  · have hb : b = (a.1, a.2 + 1) := Prod.ext h1 h2
    subst hb
    refine ⟨a.1, a.2, Or.inr ⟨rfl, ?_, ?_, ?_⟩⟩
    · simp [pt]; ring
    · simp [pt]; linarith
    · simp [pt]; linarith
  · have ha : a = (b.1, b.2 + 1) := Prod.ext h1.symm h2
    subst ha
    refine ⟨b.1, b.2, Or.inr ⟨Set.pair_comm _ _, ?_, ?_, ?_⟩⟩
    · simp [pt]; ring
    · simp [pt]; linarith
    · simp [pt]; linarith

/-- Two unit lattice segments are equal or meet in a common endpoint (the common point is that
endpoint). -/
lemma seg_inter {a b c d : ℤ × ℤ} (hu : UnitStep a b) (hv : UnitStep c d) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ (pt a) (pt b)) (hz' : z ∈ segment ℝ (pt c) (pt d)) :
    ({a, b} : Set (ℤ × ℤ)) = {c, d} ∨
      ∃ w : ℤ × ℤ, w ∈ ({a, b} : Set (ℤ × ℤ)) ∧ w ∈ ({c, d} : Set (ℤ × ℤ)) ∧ z = pt w := by
  obtain ⟨x, y, h1 | h1⟩ := seg_unit hu hz <;> obtain ⟨x', y', h2 | h2⟩ := seg_unit hv hz'
  · obtain ⟨e1, e2, e3, e4⟩ := h1
    obtain ⟨f1, f2, f3, f4⟩ := h2
    have hy : y = y' := by
      have : (y : ℝ) = y' := by rw [← e2, ← f2]
      exact_mod_cast this
    have i1 : x ≤ x' + 1 := by
      have : (x : ℝ) ≤ x' + 1 := by linarith
      exact_mod_cast this
    have i2 : x' ≤ x + 1 := by
      have : (x' : ℝ) ≤ x + 1 := by linarith
      exact_mod_cast this
    subst hy
    have hc : x' = x ∨ x' = x + 1 ∨ x = x' + 1 := by omega
    rcases hc with rfl | rfl | rfl
    · left; rw [e1, f1]
    · right
      refine ⟨(x + 1, y), by rw [e1]; simp, by rw [f1]; simp, ?_⟩
      have : z.1 = (x : ℝ) + 1 := by push_cast at f3 e4; linarith
      ext <;> simp [pt, this, e2]
    · right
      refine ⟨(x' + 1, y), by rw [e1]; simp, by rw [f1]; simp, ?_⟩
      have : z.1 = (x' : ℝ) + 1 := by push_cast at e3 f4; linarith
      ext <;> simp [pt, this, e2]
  · obtain ⟨e1, e2, e3, e4⟩ := h1
    obtain ⟨f1, f2, f3, f4⟩ := h2
    have i1 : x ≤ x' := by
      have : (x : ℝ) ≤ x' := by rw [← f2]; exact e3
      exact_mod_cast this
    have i2 : x' ≤ x + 1 := by
      have : (x' : ℝ) ≤ x + 1 := by rw [← f2]; exact e4
      exact_mod_cast this
    have j1 : y' ≤ y := by
      have : (y' : ℝ) ≤ y := by rw [← e2]; exact f3
      exact_mod_cast this
    have j2 : y ≤ y' + 1 := by
      have : (y : ℝ) ≤ y' + 1 := by rw [← e2]; exact f4
      exact_mod_cast this
    right
    refine ⟨(x', y), ?_, ?_, ?_⟩
    · rw [e1]
      have : x' = x ∨ x' = x + 1 := by omega
      rcases this with h | h <;> simp [h]
    · rw [f1]
      have : y = y' ∨ y = y' + 1 := by omega
      rcases this with h | h <;> simp [h]
    · ext <;> simp [pt, e2, f2]
  · obtain ⟨e1, e2, e3, e4⟩ := h1
    obtain ⟨f1, f2, f3, f4⟩ := h2
    have i1 : x' ≤ x := by
      have : (x' : ℝ) ≤ x := by rw [← e2]; exact f3
      exact_mod_cast this
    have i2 : x ≤ x' + 1 := by
      have : (x : ℝ) ≤ x' + 1 := by rw [← e2]; exact f4
      exact_mod_cast this
    have j1 : y ≤ y' := by
      have : (y : ℝ) ≤ y' := by rw [← f2]; exact e3
      exact_mod_cast this
    have j2 : y' ≤ y + 1 := by
      have : (y' : ℝ) ≤ y + 1 := by rw [← f2]; exact e4
      exact_mod_cast this
    right
    refine ⟨(x, y'), ?_, ?_, ?_⟩
    · rw [e1]
      have : y' = y ∨ y' = y + 1 := by omega
      rcases this with h | h <;> simp [h]
    · rw [f1]
      have : x = x' ∨ x = x' + 1 := by omega
      rcases this with h | h <;> simp [h]
    · ext <;> simp [pt, e2, f2]
  · obtain ⟨e1, e2, e3, e4⟩ := h1
    obtain ⟨f1, f2, f3, f4⟩ := h2
    have hx : x = x' := by
      have : (x : ℝ) = x' := by rw [← e2, ← f2]
      exact_mod_cast this
    have i1 : y ≤ y' + 1 := by
      have : (y : ℝ) ≤ y' + 1 := by linarith
      exact_mod_cast this
    have i2 : y' ≤ y + 1 := by
      have : (y' : ℝ) ≤ y + 1 := by linarith
      exact_mod_cast this
    subst hx
    have hc : y' = y ∨ y' = y + 1 ∨ y = y' + 1 := by omega
    rcases hc with rfl | rfl | rfl
    · left; rw [e1, f1]
    · right
      refine ⟨(x, y + 1), by rw [e1]; simp, by rw [f1]; simp, ?_⟩
      have : z.2 = (y : ℝ) + 1 := by push_cast at f3 e4; linarith
      ext <;> simp [pt, this, e2]
    · right
      refine ⟨(x, y' + 1), by rw [e1]; simp, by rw [f1]; simp, ?_⟩
      have : z.2 = (y' : ℝ) + 1 := by push_cast at e3 f4; linarith
      ext <;> simp [pt, this, e2]

end Lightlike.PL.Schoenflies
