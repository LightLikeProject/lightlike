import Lightlike.PL.Polygon

/-!
# The parity jumps across an edge

For a simple polygon, the crossing parity of the horizontal ray takes different values on the two
sides of an edge, near any point of the edge that is not a vertex.
-/

open Set Filter Topology Metric

namespace Lightlike.PL

/-- The cross product of two plane vectors. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-! ## A topological assembly lemma -/

open Metric in
/-- **Gluing local connectedness along a connected set.** Let `X` be a closed connected nonempty
set in the plane and `P` a function that is locally constant off `X`. If, around each point `w` of
`X`, the set `C` of points off `X` where `P = c` is preconnected in a small ball and accumulates
at `w`, then `C` is preconnected. -/
theorem isPreconnected_class {X : Set (ℝ × ℝ)} (hXc : IsClosed X) (hXconn : IsPreconnected X)
    (hXne : X.Nonempty) (P : ℝ × ℝ → ZMod 2) (hP : ∀ x ∉ X, ∀ᶠ y in 𝓝 x, P y = P x)
    (c : ZMod 2)
    (hloc : ∀ w ∈ X, ∃ ρ > 0, IsPreconnected ({y | y ∉ X ∧ P y = c} ∩ ball w ρ) ∧
      w ∈ closure {y | y ∉ X ∧ P y = c}) :
    IsPreconnected {y | y ∉ X ∧ P y = c} := by
  set C : Set (ℝ × ℝ) := {y | y ∉ X ∧ P y = c} with hC
  have hCopen : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hXc.isOpen_compl.mem_nhds hy.1, hP y hy.1] with z hz1 hz2
    exact ⟨hz1, hz2.trans hy.2⟩
  have hCcl : ∀ z, z ∉ X → z ∈ closure C → z ∈ C := by
    intro z hz hzc
    refine ⟨hz, ?_⟩
    obtain ⟨y, hyP, hyC⟩ := mem_closure_iff_nhds.1 hzc _ (hP z hz)
    exact hyP.symm.trans hyC.2
  have key : ∀ u v : Set (ℝ × ℝ), IsOpen u → IsOpen v → C ⊆ u ∪ v → C ∩ (u ∩ v) = ∅ →
      (∀ z ∈ X, ∃ r > 0, C ∩ ball z r ⊆ u) → C ⊆ u := by
    intro u v hu hv hsub hdisj hX
    by_contra hCu
    obtain ⟨y, hyC, hyu⟩ := Set.not_subset.1 hCu
    have hyv : y ∈ v := (hsub hyC).resolve_left hyu
    have hTo : IsOpen (C ∩ v) := hCopen.inter hv
    have hTc : ¬ IsClosed (C ∩ v) := by
      intro hcl
      rcases isClopen_iff.1 ⟨hcl, hTo⟩ with h | h
      · have : y ∈ C ∩ v := ⟨hyC, hyv⟩
        rw [h] at this
        exact this
      · obtain ⟨x0, hx0⟩ := hXne
        have : x0 ∈ C ∩ v := h ▸ Set.mem_univ x0
        exact this.1.1 hx0
    obtain ⟨z, hzcl, hzT⟩ := Set.not_subset.1 (mt closure_subset_iff_isClosed.1 hTc)
    by_cases hzX : z ∈ X
    · obtain ⟨r, hr, hsubr⟩ := hX z hzX
      obtain ⟨t, ht1, ht2⟩ := mem_closure_iff.1 hzcl (ball z r) isOpen_ball (mem_ball_self hr)
      exact (Set.eq_empty_iff_forall_notMem.1 hdisj) t
        ⟨ht2.1, hsubr ⟨ht2.1, ht1⟩, ht2.2⟩
    · have hzC : z ∈ C := hCcl z hzX (closure_mono Set.inter_subset_left hzcl)
      rcases hsub hzC with hzu | hzv
      · obtain ⟨t, ht1, ht2⟩ := mem_closure_iff.1 hzcl u hu hzu
        exact (Set.eq_empty_iff_forall_notMem.1 hdisj) t ⟨ht2.1, ht1, ht2.2⟩
      · exact hzT ⟨hzC, hzv⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hsub hdisj
  have hlab : ∀ w ∈ X, (∃ ρ > 0, C ∩ ball w ρ ⊆ u) ∨ (∃ ρ > 0, C ∩ ball w ρ ⊆ v) := by
    intro w hw
    obtain ⟨ρ, hρ, hpre, -⟩ := hloc w hw
    rcases isPreconnected_iff_subset_of_disjoint.1 hpre u v hu hv
      (fun y hy => hsub hy.1)
      (Set.eq_empty_iff_forall_notMem.2 fun y hy =>
        (Set.eq_empty_iff_forall_notMem.1 hdisj) y ⟨hy.1.1, hy.2⟩) with h | h
    · exact Or.inl ⟨ρ, hρ, h⟩
    · exact Or.inr ⟨ρ, hρ, h⟩
  set Ou : Set (ℝ × ℝ) := {z | ∃ w ∈ X, ∃ ρ > 0, z ∈ ball w ρ ∧ C ∩ ball w ρ ⊆ u} with hOu
  set Ov : Set (ℝ × ℝ) := {z | ∃ w ∈ X, ∃ ρ > 0, z ∈ ball w ρ ∧ C ∩ ball w ρ ⊆ v} with hOv
  have hOuo : IsOpen Ou := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨w, hw, ρ, hρ, hz, hs⟩
    exact Filter.mem_of_superset (isOpen_ball.mem_nhds hz)
      fun z' hz' => ⟨w, hw, ρ, hρ, hz', hs⟩
  have hOvo : IsOpen Ov := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨w, hw, ρ, hρ, hz, hs⟩
    exact Filter.mem_of_superset (isOpen_ball.mem_nhds hz)
      fun z' hz' => ⟨w, hw, ρ, hρ, hz', hs⟩
  have hzu : ∀ z ∈ X, z ∈ Ou → ∃ r > 0, C ∩ ball z r ⊆ u := by
    rintro z hz ⟨w, hw, ρ, hρ, hzb, hs⟩
    obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.1 isOpen_ball z hzb
    exact ⟨r, hr, fun y hy => hs ⟨hy.1, hrs hy.2⟩⟩
  have hzv : ∀ z ∈ X, z ∈ Ov → ∃ r > 0, C ∩ ball z r ⊆ v := by
    rintro z hz ⟨w, hw, ρ, hρ, hzb, hs⟩
    obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.1 isOpen_ball z hzb
    exact ⟨r, hr, fun y hy => hs ⟨hy.1, hrs hy.2⟩⟩
  have hcov : X ⊆ Ou ∪ Ov := by
    intro w hw
    rcases hlab w hw with ⟨ρ, hρ, hs⟩ | ⟨ρ, hρ, hs⟩
    · exact Or.inl ⟨w, hw, ρ, hρ, mem_ball_self hρ, hs⟩
    · exact Or.inr ⟨w, hw, ρ, hρ, mem_ball_self hρ, hs⟩
  have hdX : X ∩ (Ou ∩ Ov) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun z ⟨hzX, hzOu, hzOv⟩ => ?_
    obtain ⟨r1, hr1, hs1⟩ := hzu z hzX hzOu
    obtain ⟨r2, hr2, hs2⟩ := hzv z hzX hzOv
    obtain ⟨-, -, -, hcl⟩ := hloc z hzX
    obtain ⟨t, ht1, ht2⟩ := mem_closure_iff.1 hcl (ball z (min r1 r2)) isOpen_ball
      (mem_ball_self (lt_min hr1 hr2))
    exact (Set.eq_empty_iff_forall_notMem.1 hdisj) t
      ⟨ht2, hs1 ⟨ht2, Metric.ball_subset_ball (min_le_left _ _) ht1⟩,
        hs2 ⟨ht2, Metric.ball_subset_ball (min_le_right _ _) ht1⟩⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 hXconn Ou Ov hOuo hOvo hcov hdX with h | h
  · exact Or.inl (key u v hu hv hsub hdisj fun z hz => hzu z hz (h hz))
  · refine Or.inr (key v u hv hu (by rwa [Set.union_comm]) ?_ fun z hz => hzv z hz (h hz))
    rwa [Set.inter_comm v u]

namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- Two different edges of a simple polygon meet only at the vertex they share. -/
lemma eq_vertex_of_mem_edge_inter (hs : p.IsSimple) {e f : Fin n} (hef : e ≠ f) {w : ℝ × ℝ}
    (hwe : w ∈ p.edge e) (hwf : w ∈ p.edge f) :
    (finRotate n e = f ∧ w = p (finRotate n e)) ∨ (finRotate n f = e ∧ w = p e) := by
  obtain ⟨-, h2, h3⟩ := hs
  by_cases hA : finRotate n e = f
  · left
    refine ⟨hA, ?_⟩
    rw [← hA] at hwf
    have hm : w ∈ p.edge e ∩ p.edge (finRotate n e) := ⟨hwe, hwf⟩
    rw [h3 e] at hm
    exact hm
  · by_cases hB : finRotate n f = e
    · right
      refine ⟨hB, ?_⟩
      have hm : w ∈ p.edge f ∩ p.edge (finRotate n f) := ⟨hwf, by rw [hB]; exact hwe⟩
      rw [h3 f, hB] at hm
      exact hm
    · exact absurd hwf (Set.disjoint_left.1 (h2 e f hef hA hB) hwe)

/-- A point of an edge that is not an endpoint is on no other edge. -/
lemma not_mem_edge_of_ne (hs : p.IsSimple) {e f : Fin n} (hef : e ≠ f) {w : ℝ × ℝ}
    (hwe : w ∈ p.edge e) (h1 : w ≠ p e) (h2 : w ≠ p (finRotate n e)) : w ∉ p.edge f := by
  intro hwf
  rcases eq_vertex_of_mem_edge_inter hs hef hwe hwf with ⟨-, h⟩ | ⟨-, h⟩
  · exact h2 h
  · exact h1 h

/-- A vertex lies on exactly the two edges at it. -/
lemma eq_of_vertex_mem_edge (hs : p.IsSimple) {i f : Fin n} (hf : p (finRotate n i) ∈ p.edge f) :
    f = i ∨ f = finRotate n i := by
  by_contra hcon
  rw [not_or] at hcon
  rcases eq_vertex_of_mem_edge_inter hs (Ne.symm hcon.1) (right_mem_segment ℝ _ _) hf with
    ⟨hA, -⟩ | ⟨-, h⟩
  · exact hcon.2 hA.symm
  · exact hs.1 i h.symm

/-- The crossings of all edges but `e`. -/
noncomputable def restSum (p : Polygon n) (e : Fin n) (x : ℝ × ℝ) : ZMod 2 :=
  ∑ i ∈ Finset.univ.erase e, ind (CrossesRay (p i) (p (finRotate n i)) x)

/-- The crossings of all edges but `e`, with the opposite half-open rule. -/
noncomputable def restSum' (p : Polygon n) (e : Fin n) (x : ℝ × ℝ) : ZMod 2 :=
  ∑ i ∈ Finset.univ.erase e, ind (CrossesRay' (p i) (p (finRotate n i)) x)

lemma parity_eq_add_restSum (p : Polygon n) (e : Fin n) (y : ℝ × ℝ) :
    p.parity y = ind (CrossesRay (p e) (p (finRotate n e)) y) + p.restSum e y :=
  (Finset.add_sum_erase Finset.univ
    (fun i => ind (CrossesRay (p i) (p (finRotate n i)) y)) (Finset.mem_univ e)).symm

/-- Near a point on no edge but `e`, the crossings of the other edges are given by one of two
constants, according to whether the point is below or not. -/
lemma eventually_restSum {e : Fin n} {w : ℝ × ℝ} (hw : ∀ f, f ≠ e → w ∉ p.edge f) :
    ∀ᶠ y in 𝓝 w, p.restSum e y = if w.2 ≤ y.2 then p.restSum e w else p.restSum' e w := by
  have hall : ∀ᶠ y in 𝓝 w, ∀ i ∈ Finset.univ.erase e,
      (CrossesRay (p i) (p (finRotate n i)) y ↔
        if w.2 ≤ y.2 then CrossesRay (p i) (p (finRotate n i)) w
        else CrossesRay' (p i) (p (finRotate n i)) w) :=
    (Filter.eventually_all_finset _).2 fun i hi =>
      eventually_crossesRay_side (hw i (Finset.ne_of_mem_erase hi))
  filter_upwards [hall] with y hy
  unfold restSum restSum'
  split_ifs with hc
  · exact Finset.sum_congr rfl fun i hi => ind_congr ((hy i hi).trans (by simp [hc]))
  · exact Finset.sum_congr rfl fun i hi => ind_congr ((hy i hi).trans (by simp [hc]))

/-- The two sums of the other edges differ by the endpoints of `e` on the line of `w`, to its
right. -/
lemma restSum_add_restSum' {e : Fin n} {w : ℝ × ℝ} (hw : ∀ f, f ≠ e → w ∉ p.edge f) :
    p.restSum e w + p.restSum' e w =
      ind (OnRight (p e) w) + ind (OnRight (p (finRotate n e)) w) := by
  unfold restSum restSum'
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl fun i hi => ind_crossesRay_add (hw i (Finset.ne_of_mem_erase hi))]
  rw [Finset.sum_add_distrib]
  have hS : ∑ i, ind (OnRight (p (finRotate n i)) w) = ∑ i, ind (OnRight (p i) w) :=
    Equiv.sum_comp (finRotate n) fun i => ind (OnRight (p i) w)
  have h1 := Finset.add_sum_erase Finset.univ (fun i => ind (OnRight (p i) w))
    (Finset.mem_univ e)
  have h2 := Finset.add_sum_erase Finset.univ (fun i => ind (OnRight (p (finRotate n i)) w))
    (Finset.mem_univ e)
  have h2' : (2 : ZMod 2) = 0 := by decide
  rw [hS] at h2
  linear_combination h1 + h2 +
    (∑ i, ind (OnRight (p i) w) - ind (OnRight (p e) w) - ind (OnRight (p (finRotate n e)) w)) * h2'

end Polygon

lemma ind_of {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]

lemma ind_of_not {P : Prop} (h : ¬P) : ind P = 0 := by simp [ind, h]

/-- A point of an open segment is a strict convex combination of its endpoints. -/
lemma strict_of_mem_segment {u v w : ℝ × ℝ} (hw : w ∈ segment ℝ u v) (h1 : w ≠ u) (h2 : w ≠ v) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ w.1 = a * u.1 + b * v.1 ∧
      w.2 = a * u.2 + b * v.2 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  refine ⟨a, b, ?_, ?_, hab, by simp, by simp⟩
  · rcases ha.eq_or_lt with h | h
    · have h0 : a = 0 := h.symm
      subst h0
      have h1' : b = 1 := by linarith
      subst h1'
      exact absurd (by simp) h2
    · exact h
  · rcases hb.eq_or_lt with h | h
    · have h0 : b = 0 := h.symm
      subst h0
      have h1' : a = 1 := by linarith
      subst h1'
      exact absurd (by simp) h1
    · exact h

lemma xAt_sub (u v y : ℝ × ℝ) (h : u.2 ≠ v.2) :
    xAt u v y.2 - y.1 = cross (v - u) (y - u) / (v.2 - u.2) := by
  have : v.2 - u.2 ≠ 0 := sub_ne_zero.2 h.symm
  unfold xAt cross
  simp only [Prod.fst_sub, Prod.snd_sub]
  field_simp
  ring

/-- For an edge going up, the point is left of the edge exactly when the cross product is
positive. -/
lemma lt_xAt_iff_pos {u v : ℝ × ℝ} (y : ℝ × ℝ) (h : u.2 < v.2) :
    y.1 < xAt u v y.2 ↔ 0 < cross (v - u) (y - u) := by
  rw [← sub_pos, xAt_sub u v y h.ne]
  exact div_pos_iff_of_pos_right (sub_pos.2 h)

/-- For an edge going down, the point is left of the edge exactly when the cross product is
negative. -/
lemma lt_xAt_iff_neg {u v : ℝ × ℝ} (y : ℝ × ℝ) (h : v.2 < u.2) :
    y.1 < xAt u v y.2 ↔ cross (v - u) (y - u) < 0 := by
  rw [← sub_pos, xAt_sub u v y h.ne']
  have hn : v.2 - u.2 < 0 := sub_neg.2 h
  rw [← neg_div_neg_eq, div_pos_iff_of_pos_right (neg_pos.2 hn), neg_pos]

namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- **The parity takes different values on the two sides of an edge**, near any point of the edge
that is not an endpoint. -/
theorem exists_parity_sides (hs : p.IsSimple) {e : Fin n} {w : ℝ × ℝ} (hw : w ∈ p.edge e)
    (h1 : w ≠ p e) (h2 : w ≠ p (finRotate n e)) :
    ∃ c : ZMod 2, ∀ᶠ y in 𝓝 w,
      (0 < cross (p (finRotate n e) - p e) (y - w) → p.parity y = c) ∧
      (cross (p (finRotate n e) - p e) (y - w) < 0 → p.parity y = c + 1) := by
  have hother : ∀ f, f ≠ e → w ∉ p.edge f := fun f hf => not_mem_edge_of_ne hs hf.symm hw h1 h2
  have hrest := eventually_restSum (p := p) hother
  have hKK := restSum_add_restSum' (p := p) hother
  have hne : p e ≠ p (finRotate n e) := hs.1 e
  obtain ⟨a, b, ha, hb, hab, hw1, hw2⟩ := strict_of_mem_segment hw h1 h2
  have hcw : ∀ y : ℝ × ℝ, cross (p (finRotate n e) - p e) (y - w) =
      cross (p (finRotate n e) - p e) (y - p e) := by
    intro y
    have : a = 1 - b := by linarith
    unfold cross
    simp only [Prod.fst_sub, Prod.snd_sub, hw1, hw2, this]
    ring
  obtain rfl : a = 1 - b := by linarith
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  set K := p.restSum e w
  set K' := p.restSum' e w
  rcases lt_trichotomy (p e).2 (p (finRotate n e)).2 with huv | huv | huv
  · have hlo : (p e).2 < w.2 := by rw [hw2]; nlinarith [mul_pos hb (sub_pos.2 huv)]
    have hhi : w.2 < (p (finRotate n e)).2 := by rw [hw2]; nlinarith [mul_pos hb (sub_pos.2 huv)]
    have hK : K' = K := by
      have h0 : ind (OnRight (p e) w) + ind (OnRight (p (finRotate n e)) w) = 0 := by
        rw [ind_of_not (fun h => hlo.ne h.1), ind_of_not (fun h => hhi.ne' h.1), add_zero]
      rw [h0] at hKK
      exact (CharTwo.add_eq_zero.1 hKK).symm
    refine ⟨K + 1, ?_⟩
    have e1 : ∀ᶠ y in 𝓝 w, (p e).2 < y.2 :=
      continuous_snd.continuousAt.eventually (lt_mem_nhds hlo)
    have e2 : ∀ᶠ y in 𝓝 w, y.2 < (p (finRotate n e)).2 :=
      continuous_snd.continuousAt.eventually (gt_mem_nhds hhi)
    filter_upwards [hrest, e1, e2] with y hy h1y h2y
    have hcr : CrossesRay (p e) (p (finRotate n e)) y ↔
        0 < cross (p (finRotate n e) - p e) (y - w) := by
      rw [hcw, ← lt_xAt_iff_pos y huv]
      exact ⟨fun h => h.2, fun h => ⟨Or.inl ⟨h1y.le, h2y⟩, h⟩⟩
    have hrs : p.restSum e y = K := by
      rw [hy]; split_ifs with hc
      · rfl
      · exact hK
    rw [parity_eq_add_restSum p e y, hrs]
    refine ⟨fun hpos => ?_, fun hneg => ?_⟩
    · rw [ind_of (hcr.2 hpos), add_comm]
    · rw [ind_of_not (fun h => absurd (hcr.1 h) (not_lt.2 hneg.le)), zero_add, add_assoc, h11,
        add_zero]
  · -- horizontal edge
    have hwu : w.2 = (p e).2 := by rw [hw2, ← huv]; linear_combination (p e).2 * hab
    have hwv : w.2 = (p (finRotate n e)).2 := hwu.trans huv
    have hx : (p e).1 ≠ (p (finRotate n e)).1 := fun h => hne (Prod.ext h huv)
    have hcr : ∀ y : ℝ × ℝ, ¬ CrossesRay (p e) (p (finRotate n e)) y := by
      rintro y ⟨⟨h3, h4⟩ | ⟨h3, h4⟩, -⟩ <;> linarith
    have hdz : ∀ y : ℝ × ℝ, cross (p (finRotate n e) - p e) (y - w) =
        ((p (finRotate n e)).1 - (p e).1) * (y.2 - w.2) := by
      intro y
      simp [cross, huv]
    have h2' : (2 : ZMod 2) = 0 := by decide
    have hK : K' = K + 1 := by
      have h0 : ind (OnRight (p e) w) + ind (OnRight (p (finRotate n e)) w) = 1 := by
        rcases lt_or_gt_of_ne hx with hlt | hgt
        · have a1 : ¬ OnRight (p e) w := fun h => by
            have := h.2; rw [hw1] at this; nlinarith [mul_pos hb (sub_pos.2 hlt)]
          have a2 : OnRight (p (finRotate n e)) w :=
            ⟨hwv.symm, by rw [hw1]; nlinarith [mul_pos hb (sub_pos.2 hlt)]⟩
          rw [ind_of_not a1, ind_of a2, zero_add]
        · have a1 : OnRight (p e) w :=
            ⟨hwu.symm, by rw [hw1]; nlinarith [mul_pos hb (sub_pos.2 hgt)]⟩
          have a2 : ¬ OnRight (p (finRotate n e)) w := fun h => by
            have := h.2; rw [hw1] at this; nlinarith [mul_pos hb (sub_pos.2 hgt)]
          rw [ind_of a1, ind_of_not a2, add_zero]
      rw [h0] at hKK
      linear_combination hKK - K * h2'
    have hup : ∀ y : ℝ × ℝ, p.parity y = p.restSum e y := fun y => by
      rw [parity_eq_add_restSum p e y, ind_of_not (hcr y), zero_add]
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · have hdpos : 0 < (p (finRotate n e)).1 - (p e).1 := sub_pos.2 hlt
      refine ⟨K, ?_⟩
      filter_upwards [hrest] with y hy
      rw [hup y, hy]
      refine ⟨fun hpos => ?_, fun hneg => ?_⟩
      · rw [hdz] at hpos
        have : w.2 ≤ y.2 := by
          by_contra h
          rw [not_le] at h
          nlinarith [mul_pos hdpos (sub_pos.2 h)]
        rw [ite_eq_left this]
      · rw [hdz] at hneg
        have : ¬ w.2 ≤ y.2 := by
          intro h
          nlinarith [mul_nonneg hdpos.le (sub_nonneg.2 h)]
        rw [ite_eq_right this, hK]
    · have hdneg : (p (finRotate n e)).1 - (p e).1 < 0 := sub_neg.2 hgt
      refine ⟨K + 1, ?_⟩
      filter_upwards [hrest] with y hy
      rw [hup y, hy]
      refine ⟨fun hpos => ?_, fun hneg => ?_⟩
      · rw [hdz] at hpos
        have : ¬ w.2 ≤ y.2 := by
          intro h
          nlinarith [mul_nonneg (neg_nonneg.2 hdneg.le) (sub_nonneg.2 h)]
        rw [ite_eq_right this, hK]
      · rw [hdz] at hneg
        have : w.2 ≤ y.2 := by
          by_contra h
          rw [not_le] at h
          nlinarith [mul_pos (neg_pos.2 hdneg) (sub_pos.2 h)]
        rw [ite_eq_left this, add_assoc, h11, add_zero]
  · have hhi : (p (finRotate n e)).2 < w.2 := by rw [hw2]; nlinarith [mul_pos hb (sub_pos.2 huv)]
    have hlo : w.2 < (p e).2 := by rw [hw2]; nlinarith [mul_pos hb (sub_pos.2 huv)]
    have hK : K' = K := by
      have h0 : ind (OnRight (p e) w) + ind (OnRight (p (finRotate n e)) w) = 0 := by
        rw [ind_of_not (fun h => hlo.ne' h.1), ind_of_not (fun h => hhi.ne h.1), add_zero]
      rw [h0] at hKK
      exact (CharTwo.add_eq_zero.1 hKK).symm
    refine ⟨K, ?_⟩
    have e1 : ∀ᶠ y in 𝓝 w, (p (finRotate n e)).2 < y.2 :=
      continuous_snd.continuousAt.eventually (lt_mem_nhds hhi)
    have e2 : ∀ᶠ y in 𝓝 w, y.2 < (p e).2 :=
      continuous_snd.continuousAt.eventually (gt_mem_nhds hlo)
    filter_upwards [hrest, e1, e2] with y hy h1y h2y
    have hcr : CrossesRay (p e) (p (finRotate n e)) y ↔
        cross (p (finRotate n e) - p e) (y - w) < 0 := by
      rw [hcw, ← lt_xAt_iff_neg y huv]
      exact ⟨fun h => h.2, fun h => ⟨Or.inr ⟨h1y.le, h2y⟩, h⟩⟩
    have hrs : p.restSum e y = K := by
      rw [hy]; split_ifs with hc
      · rfl
      · exact hK
    rw [parity_eq_add_restSum p e y, hrs]
    refine ⟨fun hpos => ?_, fun hneg => ?_⟩
    · rw [ind_of_not (fun h => absurd (hcr.1 h) (not_lt.2 hpos.le)), zero_add]
    · rw [ind_of (hcr.2 hneg), add_comm]

end Polygon
/-! ## Classes near a point of the set -/

open Metric in
/-- The set of points off `X` where a locally constant `P` takes the value `c` is open. -/
lemma isOpen_class {X : Set (ℝ × ℝ)} (hXc : IsClosed X) {P : ℝ × ℝ → ZMod 2}
    (hP : ∀ x ∉ X, ∀ᶠ y in 𝓝 x, P y = P x) (c : ZMod 2) :
    IsOpen {y | y ∉ X ∧ P y = c} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hy, hc⟩
  filter_upwards [hXc.isOpen_compl.mem_nhds hy, hP y hy] with z hz hz'
  exact ⟨hz, hz'.trans hc⟩

/-- A locally constant function is constant on a preconnected set off `X`. -/
lemma constOn_of_isPreconnected {X : Set (ℝ × ℝ)} (hXc : IsClosed X) {P : ℝ × ℝ → ZMod 2}
    (hP : ∀ x ∉ X, ∀ᶠ y in 𝓝 x, P y = P x) {S : Set (ℝ × ℝ)} (hS : IsPreconnected S)
    (hSX : S ⊆ Xᶜ) {a b : ℝ × ℝ} (ha : a ∈ S) (hb : b ∈ S) : P a = P b := by
  have h2 : ∀ x : ZMod 2, x = P a ∨ x = P a + 1 := by
    intro x; revert x; generalize P a = k; revert k; decide
  rcases isPreconnected_iff_subset_of_disjoint.1 hS _ _ (isOpen_class hXc hP (P a))
    (isOpen_class hXc hP (P a + 1)) (fun y hy => by
      rcases h2 (P y) with h | h
      · exact Or.inl ⟨hSX hy, h⟩
      · exact Or.inr ⟨hSX hy, h⟩)
    (by
      refine eq_empty_of_forall_notMem fun y ⟨_, h1, h2⟩ => ?_
      have := h1.2.symm.trans h2.2
      revert this; generalize P a = k; revert k; decide) with h | h
  · exact (h hb).2.symm
  · exact absurd (h ha).2 (by generalize P a = k; revert k; decide)

open Metric in
/-- **Local structure of the classes at a point of `X`.** Suppose that near `w` the complement of
`X` is the union of two preconnected pieces `Q₁`, `Q₂`, both accumulating at `w`, on which a
locally constant `P` takes different values. Then for each value `c`, the class of `c` is
preconnected in the ball and accumulates at `w`. -/
theorem local_classes {X : Set (ℝ × ℝ)} (hXc : IsClosed X) {P : ℝ × ℝ → ZMod 2}
    (hP : ∀ x ∉ X, ∀ᶠ y in 𝓝 x, P y = P x) {w : ℝ × ℝ} {ρ : ℝ} {Q₁ Q₂ : Set (ℝ × ℝ)}
    (hQ₁ : IsPreconnected Q₁) (hQ₂ : IsPreconnected Q₂) (hU : ball w ρ \ X = Q₁ ∪ Q₂)
    (hw₁ : w ∈ closure Q₁) (hw₂ : w ∈ closure Q₂) {y₁ y₂ : ℝ × ℝ} (h₁ : y₁ ∈ Q₁) (h₂ : y₂ ∈ Q₂)
    (hne : P y₁ ≠ P y₂) (c : ZMod 2) :
    IsPreconnected ({y | y ∉ X ∧ P y = c} ∩ ball w ρ) ∧ w ∈ closure {y | y ∉ X ∧ P y = c} := by
  have hQX : ∀ y ∈ Q₁ ∪ Q₂, y ∉ X ∧ y ∈ ball w ρ := fun y hy => by
    rw [← hU] at hy; exact ⟨hy.2, hy.1⟩
  have hc1 : ∀ y ∈ Q₁, P y = P y₁ := fun y hy =>
    constOn_of_isPreconnected hXc hP hQ₁ (fun z hz => (hQX z (Or.inl hz)).1) hy h₁
  have hc2 : ∀ y ∈ Q₂, P y = P y₂ := fun y hy =>
    constOn_of_isPreconnected hXc hP hQ₂ (fun z hz => (hQX z (Or.inr hz)).1) hy h₂
  have hcases : c = P y₁ ∨ c = P y₂ := by
    revert hne; generalize P y₁ = a; generalize P y₂ = b; revert a b c; decide
  rcases hcases with rfl | rfl
  · have : {y | y ∉ X ∧ P y = P y₁} ∩ ball w ρ = Q₁ := by
      ext y
      constructor
      · rintro ⟨⟨hyX, hyc⟩, hyb⟩
        have hy : y ∈ ball w ρ \ X := ⟨hyb, hyX⟩
        rw [hU] at hy
        rcases hy with hy | hy
        · exact hy
        · exact absurd (hyc.symm.trans (hc2 y hy)) hne
      · intro hy
        exact ⟨⟨(hQX y (Or.inl hy)).1, hc1 y hy⟩, (hQX y (Or.inl hy)).2⟩
    refine ⟨this ▸ hQ₁, closure_mono (fun y hy => ?_) hw₁⟩
    exact ⟨(hQX y (Or.inl hy)).1, hc1 y hy⟩
  · have : {y | y ∉ X ∧ P y = P y₂} ∩ ball w ρ = Q₂ := by
      ext y
      constructor
      · rintro ⟨⟨hyX, hyc⟩, hyb⟩
        have hy : y ∈ ball w ρ \ X := ⟨hyb, hyX⟩
        rw [hU] at hy
        rcases hy with hy | hy
        · exact absurd ((hc1 y hy).symm.trans hyc) hne
        · exact hy
      · intro hy
        exact ⟨⟨(hQX y (Or.inr hy)).1, hc2 y hy⟩, (hQX y (Or.inr hy)).2⟩
    refine ⟨this ▸ hQ₂, closure_mono (fun y hy => ?_) hw₂⟩
    exact ⟨(hQX y (Or.inr hy)).1, hc2 y hy⟩

/-! ## The two sectors at the meeting point of two rays -/

/-- The ray from the origin in the direction `a`. -/
def ray0 (a : ℝ × ℝ) : Set (ℝ × ℝ) := {x | ∃ s : ℝ, 0 ≤ s ∧ x = s • a}

/-- The complement of two rays from the origin, with independent directions, is described by
signs: with `α x = cross x b` and `β x = cross a x`, a point lies on a ray exactly when it is not
in the open sector `α > 0, β > 0` and not in `α < 0` or `β < 0`. -/
lemma classify_pos {a b : ℝ × ℝ} (hD : 0 < cross a b) (x : ℝ × ℝ) :
    x ∈ ray0 a ∪ ray0 b ↔
      ¬ ((0 < cross x b ∧ 0 < cross a x) ∨ cross x b < 0 ∨ cross a x < 0) := by
  have key1 : x.1 * cross a b = cross x b * a.1 + cross a x * b.1 := by unfold cross; ring
  have key2 : x.2 * cross a b = cross x b * a.2 + cross a x * b.2 := by unfold cross; ring
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · have h1 : cross (s • a) b = s * cross a b := by simp [cross]; ring
      have h2 : cross a (s • a) = 0 := by simp [cross]; ring
      rw [h1, h2]
      rintro (⟨-, h⟩ | h | h) <;> nlinarith [mul_nonneg hs hD.le]
    · have h1 : cross (s • b) b = 0 := by simp [cross]; ring
      have h2 : cross a (s • b) = s * cross a b := by simp [cross]; ring
      rw [h1, h2]
      rintro (⟨h, -⟩ | h | h) <;> nlinarith [mul_nonneg hs hD.le]
  · intro h
    have hα : 0 ≤ cross x b := le_of_not_gt fun h' => h (Or.inr (Or.inl h'))
    have hβ : 0 ≤ cross a x := le_of_not_gt fun h' => h (Or.inr (Or.inr h'))
    by_cases h0 : cross a x = 0
    · left
      refine ⟨cross x b / cross a b, div_nonneg hα hD.le, Prod.ext ?_ ?_⟩
      · show x.1 = cross x b / cross a b * a.1
        rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
        linear_combination key1 + b.1 * h0
      · show x.2 = cross x b / cross a b * a.2
        rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
        linear_combination key2 + b.2 * h0
    · right
      have h0' : 0 < cross a x := lt_of_le_of_ne hβ (Ne.symm h0)
      have h1 : cross x b = 0 := by
        by_contra h1
        exact h (Or.inl ⟨lt_of_le_of_ne hα (Ne.symm h1), h0'⟩)
      refine ⟨cross a x / cross a b, div_nonneg hβ hD.le, Prod.ext ?_ ?_⟩
      · show x.1 = cross a x / cross a b * b.1
        rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
        linear_combination key1 + a.1 * h1
      · show x.2 = cross a x / cross a b * b.2
        rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
        linear_combination key2 + a.2 * h1

/-- The same description when the two rays are opposite, so that they form a line. -/
lemma classify_anti {a : ℝ × ℝ} (ha : a ≠ 0) {l : ℝ} (hl : 0 < l) (x : ℝ × ℝ) :
    x ∈ ray0 a ∪ ray0 ((-l) • a) ↔
      ¬ ((0 < cross x ((-l) • a) ∧ 0 < cross a x) ∨ cross x ((-l) • a) < 0 ∨ cross a x < 0) := by
  have hα : cross x ((-l) • a) = l * cross a x := by simp [cross]; ring
  rw [hα]
  have hN : 0 < a.1 ^ 2 + a.2 ^ 2 := by
    rcases ne_or_eq a.1 0 with h | h
    · positivity
    · have : a.2 ≠ 0 := fun h2 => ha (Prod.ext h h2)
      positivity
  constructor
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · have h2 : cross a (s • a) = 0 := by simp [cross]; ring
      rw [h2]; simp
    · have h2 : cross a (s • (-l) • a) = 0 := by simp [cross]; ring
      rw [h2]; simp
  · intro h
    have h0 : cross a x = 0 := by
      by_contra h0
      rcases lt_or_gt_of_ne h0 with h1 | h1
      · exact h (Or.inr (Or.inr h1))
      · exact h (Or.inl ⟨mul_pos hl h1, h1⟩)
    set μ := (x.1 * a.1 + x.2 * a.2) / (a.1 ^ 2 + a.2 ^ 2) with hμ
    have hx : x = μ • a := by
      refine Prod.ext ?_ ?_
      · show x.1 = μ * a.1
        rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
        unfold cross at h0
        linear_combination (-a.2) * h0
      · show x.2 = μ * a.2
        rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
        unfold cross at h0
        linear_combination a.1 * h0
    rcases le_or_gt 0 μ with hμ0 | hμ0
    · exact Or.inl ⟨μ, hμ0, hx⟩
    · refine Or.inr ⟨-μ / l, div_nonneg (by linarith) hl.le, ?_⟩
      rw [hx, smul_smul]
      congr 1
      field_simp

/-- **Two rays from a point that do not point the same way** can be ordered so that the sign
description of their complement holds, with a point in the first sector, and either the two are
independent or they are opposite. -/
lemma planar_two_rays {a b : ℝ × ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hnp : ∀ l : ℝ, 0 < l → b ≠ l • a) :
    ∃ a' b' : ℝ × ℝ, ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧
      (∀ x, x ∈ ray0 a' ∪ ray0 b' ↔
        ¬ ((0 < cross x b' ∧ 0 < cross a' x) ∨ cross x b' < 0 ∨ cross a' x < 0)) ∧
      (∃ v, 0 < cross v b' ∧ 0 < cross a' v) ∧
      (0 < cross a' b' ∨ ∃ l : ℝ, 0 < l ∧ b' = (-l) • a') := by
  rcases lt_trichotomy 0 (cross a b) with hD | hD | hD
  · refine ⟨a, b, Or.inl ⟨rfl, rfl⟩, classify_pos hD, ⟨a + b, ?_, ?_⟩, Or.inl hD⟩
    · have : cross (a + b) b = cross a b := by simp [cross]; ring
      rw [this]; exact hD
    · have : cross a (a + b) = cross a b := by simp [cross]; ring
      rw [this]; exact hD
  · have hN : 0 < a.1 ^ 2 + a.2 ^ 2 := by
      rcases ne_or_eq a.1 0 with h | h
      · positivity
      · have : a.2 ≠ 0 := fun h2 => ha (Prod.ext h h2)
        positivity
    set μ := (b.1 * a.1 + b.2 * a.2) / (a.1 ^ 2 + a.2 ^ 2) with hμ
    have hbμ : b = μ • a := by
      refine Prod.ext ?_ ?_
      · show b.1 = μ * a.1
        rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
        unfold cross at hD
        linear_combination a.2 * hD
      · show b.2 = μ * a.2
        rw [hμ, div_mul_eq_mul_div, eq_div_iff hN.ne']
        unfold cross at hD
        linear_combination (-a.1) * hD
    rcases lt_trichotomy μ 0 with hμ0 | hμ0 | hμ0
    · have hl : 0 < -μ := by linarith
      have hba : b = (-(-μ)) • a := by rw [hbμ]; simp
      refine ⟨a, b, Or.inl ⟨rfl, rfl⟩, ?_, ⟨(-a.2, a.1), ?_, ?_⟩, Or.inr ⟨-μ, hl, hba⟩⟩
      · rw [hba]; exact classify_anti ha hl
      · rw [hba]
        have : cross ((-a.2, a.1)) ((-(-μ)) • a) = (-μ) * (a.1 ^ 2 + a.2 ^ 2) := by
          simp [cross]; ring
        rw [this]; positivity
      · have : cross a ((-a.2, a.1)) = a.1 ^ 2 + a.2 ^ 2 := by simp [cross]; ring
        rw [this]; exact hN
    · exact absurd (by rw [hbμ, hμ0, zero_smul]) hb
    · exact absurd hbμ (hnp μ hμ0)
  · have hD' : 0 < cross b a := by
      have : cross b a = -cross a b := by simp [cross]; ring
      rw [this]; linarith
    refine ⟨b, a, Or.inr ⟨rfl, rfl⟩, ?_, ⟨b + a, ?_, ?_⟩, Or.inl hD'⟩
    · intro x; exact classify_pos hD' x
    · have : cross (b + a) a = cross b a := by simp [cross]; ring
      rw [this]; exact hD'
    · have : cross b (b + a) = cross b a := by simp [cross]; ring
      rw [this]; exact hD'

open Metric in
/-- The open sector at `w` between the two directions `a`, `b`, within a ball. -/
def sec1 (w a b : ℝ × ℝ) (ρ : ℝ) : Set (ℝ × ℝ) :=
  ball w ρ ∩ {z | 0 < cross (z - w) b ∧ 0 < cross a (z - w)}

open Metric in
/-- The other open region at `w` cut out by two rays, within a ball. -/
def sec2 (w a b : ℝ × ℝ) (ρ : ℝ) : Set (ℝ × ℝ) :=
  ball w ρ ∩ ({z | cross (z - w) b < 0} ∪ {z | cross a (z - w) < 0})

/-- An affine function has convex positive set. -/
lemma convex_gt_of_aff {f : ℝ × ℝ → ℝ}
    (hf : ∀ x y (s t : ℝ), s + t = 1 → f (s • x + t • y) = s * f x + t * f y) :
    Convex ℝ {z | 0 < f z} := by
  intro x hx y hy s t hs ht hst
  show 0 < f (s • x + t • y)
  rw [hf x y s t hst]
  have hx' : 0 < f x := hx
  have hy' : 0 < f y := hy
  rcases hs.eq_or_lt with h | h
  · have : t = 1 := by linarith
    subst this; rw [← h]; nlinarith
  · nlinarith [mul_pos h hx', mul_nonneg ht hy'.le]

/-- An affine function has convex negative set. -/
lemma convex_lt_of_aff {f : ℝ × ℝ → ℝ}
    (hf : ∀ x y (s t : ℝ), s + t = 1 → f (s • x + t • y) = s * f x + t * f y) :
    Convex ℝ {z | f z < 0} := by
  have := convex_gt_of_aff (f := fun z => -f z) (fun x y s t h => by
    simp only [hf x y s t h]; ring)
  simpa using this

lemma aff_cross_left (w b : ℝ × ℝ) (x y : ℝ × ℝ) (s t : ℝ) (h : s + t = 1) :
    cross (s • x + t • y - w) b = s * cross (x - w) b + t * cross (y - w) b := by
  obtain rfl : t = 1 - s := by linarith
  simp [cross]; ring

lemma aff_cross_right (w a : ℝ × ℝ) (x y : ℝ × ℝ) (s t : ℝ) (h : s + t = 1) :
    cross a (s • x + t • y - w) = s * cross a (x - w) + t * cross a (y - w) := by
  obtain rfl : t = 1 - s := by linarith
  simp [cross]; ring

open Metric in
/-- **The two sectors cut out by two rays.** If the complement of the two rays from `w` is
described by the signs `α`, `β`, and the first sector is nonempty, then within a ball the
complement of the rays is the union of two preconnected sets, each accumulating at `w`. -/
lemma sectors {w a b : ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcl : ∀ x, x ∈ ray0 a ∪ ray0 b ↔
      ¬ ((0 < cross x b ∧ 0 < cross a x) ∨ cross x b < 0 ∨ cross a x < 0))
    (hv : ∃ v, 0 < cross v b ∧ 0 < cross a v) :
    IsPreconnected (sec1 w a b ρ) ∧ IsPreconnected (sec2 w a b ρ) ∧
      ball w ρ \ {z | z - w ∈ ray0 a ∪ ray0 b} = sec1 w a b ρ ∪ sec2 w a b ρ ∧
      w ∈ closure (sec1 w a b ρ) ∧ w ∈ closure (sec2 w a b ρ) := by
  obtain ⟨v, hv1, hv2⟩ := hv
  have hα : Convex ℝ {z : ℝ × ℝ | 0 < cross (z - w) b} :=
    convex_gt_of_aff fun x y s t h => aff_cross_left w b x y s t h
  have hβ : Convex ℝ {z : ℝ × ℝ | 0 < cross a (z - w)} :=
    convex_gt_of_aff fun x y s t h => aff_cross_right w a x y s t h
  have hα' : Convex ℝ {z : ℝ × ℝ | cross (z - w) b < 0} :=
    convex_lt_of_aff fun x y s t h => aff_cross_left w b x y s t h
  have hβ' : Convex ℝ {z : ℝ × ℝ | cross a (z - w) < 0} :=
    convex_lt_of_aff fun x y s t h => aff_cross_right w a x y s t h
  have tend : ∀ u : ℝ × ℝ, Filter.Tendsto (fun ε : ℝ => w + ε • u) (𝓝[>] 0) (𝓝 w) := by
    intro u
    have : Continuous fun ε : ℝ => w + ε • u := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hball : ∀ u : ℝ × ℝ, ∀ᶠ ε : ℝ in 𝓝[>] 0, w + ε • u ∈ ball w ρ := fun u =>
    (tend u).eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hc1 : ∀ ε : ℝ, cross (w + ε • v - w) b = ε * cross v b := fun ε => by
    simp [cross]; ring
  have hc2 : ∀ ε : ℝ, cross a (w + ε • v - w) = ε * cross a v := fun ε => by
    simp [cross]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ((convex_ball w ρ).inter (hα.inter hβ)).isPreconnected
  · have hmem : w - (1 / 2 : ℝ) • (0 : ℝ × ℝ) = w := by simp
    -- the two pieces share a point near `w`
    obtain ⟨ε, hε, hεb⟩ := ((hball (-v)).and hpos).exists
    have hpt1 : w + ε • -v ∈ ball w ρ ∩ {z | cross (z - w) b < 0} := by
      refine ⟨hε, ?_⟩
      show cross (w + ε • -v - w) b < 0
      have : cross (w + ε • -v - w) b = -(ε * cross v b) := by simp [cross]; ring
      rw [this]; nlinarith [mul_pos hεb hv1]
    have hpt2 : w + ε • -v ∈ ball w ρ ∩ {z | cross a (z - w) < 0} := by
      refine ⟨hε, ?_⟩
      show cross a (w + ε • -v - w) < 0
      have : cross a (w + ε • -v - w) = -(ε * cross a v) := by simp [cross]; ring
      rw [this]; nlinarith [mul_pos hεb hv2]
    have := IsPreconnected.union (w + ε • -v) hpt1 hpt2
      ((convex_ball w ρ).inter hα').isPreconnected ((convex_ball w ρ).inter hβ').isPreconnected
    simpa [sec2, Set.inter_union_distrib_left] using this
  · ext z
    constructor
    · rintro ⟨hb, hn⟩
      have hn' : ¬ (z - w ∈ ray0 a ∪ ray0 b) := hn
      rw [hcl] at hn'
      rcases not_not.1 hn' with h | h | h
      · exact Or.inl ⟨hb, h⟩
      · exact Or.inr ⟨hb, Or.inl h⟩
      · exact Or.inr ⟨hb, Or.inr h⟩
    · rintro (⟨hb, h⟩ | ⟨hb, h⟩)
      · refine ⟨hb, fun hm => ?_⟩
        have hm' : z - w ∈ ray0 a ∪ ray0 b := hm
        rw [hcl] at hm'
        exact hm' (Or.inl h)
      · refine ⟨hb, fun hm => ?_⟩
        have hm' : z - w ∈ ray0 a ∪ ray0 b := hm
        rw [hcl] at hm'
        rcases h with h | h
        · exact hm' (Or.inr (Or.inl h))
        · exact hm' (Or.inr (Or.inr h))
  · refine mem_closure_of_tendsto (tend v) ?_
    filter_upwards [hball v, hpos] with ε hb hp
    refine ⟨hb, ?_, ?_⟩
    · show 0 < cross (w + ε • v - w) b
      rw [hc1]; exact mul_pos hp hv1
    · show 0 < cross a (w + ε • v - w)
      rw [hc2]; exact mul_pos hp hv2
  · refine mem_closure_of_tendsto (tend (-v)) ?_
    filter_upwards [hball (-v), hpos] with ε hb hp
    refine ⟨hb, Or.inl ?_⟩
    show cross (w + ε • -v - w) b < 0
    have : cross (w + ε • -v - w) b = -(ε * cross v b) := by simp [cross]; ring
    rw [this]; nlinarith [mul_pos hp hv1]

/-- A segment in the plane is compact. -/
lemma isCompact_segment' (u v : ℝ × ℝ) : IsCompact (segment ℝ u v) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-! ## Rays that lie along edges -/

namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- The ray from `w` in the direction `a` runs along an edge: some edge has direction a nonzero
multiple of `a`, and the points `w + t a`, `0 < t < 1`, lie on the edge, not at its endpoints. -/
def RayEdge (p : Polygon n) (w a : ℝ × ℝ) : Prop :=
  a ≠ 0 ∧ ∃ (e : Fin n) (κ : ℝ), κ ≠ 0 ∧ p (finRotate n e) - p e = κ • a ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      (w + t • a ∈ p.edge e ∧ w + t • a ≠ p e ∧ w + t • a ≠ p (finRotate n e))

open Metric in
/-- **The parity jumps across a ray that runs along an edge**, at points of the ray close to
its start. -/
lemma parity_jump_at (hs : p.IsSimple) {w a : ℝ × ℝ} (hre : RayEdge p w a) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ c : ZMod 2, ∃ t0 : ℝ, 0 < t0 ∧ t0 < 1 ∧ w + t0 • a ∈ ball w ρ ∧
      ∀ᶠ y in 𝓝 (w + t0 • a),
        (0 < cross a (y - w) → p.parity y = c) ∧ (cross a (y - w) < 0 → p.parity y = c + 1) := by
  obtain ⟨ha, e, κ, hκ, hd, hon⟩ := hre
  have hcont : Continuous fun t : ℝ => w + t • a := by fun_prop
  have hmem0 : w + (0 : ℝ) • a ∈ ball w ρ := by
    rw [zero_smul, add_zero]; exact mem_ball_self hρ
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, w + t • a ∈ ball w ρ :=
    (hcont.tendsto 0 |>.mono_left nhdsWithin_le_nhds).eventually
      (isOpen_ball.mem_nhds hmem0)
  obtain ⟨t0, hb, h01⟩ := (ht.and
    (Ioo_mem_nhdsGT zero_lt_one : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1)).exists
  obtain ⟨hw, h1, h2⟩ := hon t0 h01.1 h01.2
  obtain ⟨c', hc'⟩ := exists_parity_sides hs hw h1 h2
  have hcr : ∀ y : ℝ × ℝ, cross (p (finRotate n e) - p e) (y - (w + t0 • a)) =
      κ * cross a (y - w) := by
    intro y
    rw [hd]
    simp [cross]; ring
  have h22 : ∀ x : ZMod 2, x + 1 + 1 = x := by decide
  refine ⟨if 0 < κ then c' else c' + 1, t0, h01.1, h01.2, hb, ?_⟩
  filter_upwards [hc'] with y hy
  rw [hcr] at hy
  rcases lt_or_gt_of_ne hκ with hk | hk
  · rw [ite_eq_right (not_lt.2 hk.le)]
    constructor
    · intro h; exact hy.2 (by nlinarith)
    · intro h; rw [h22]; exact hy.1 (by nlinarith)
  · rw [ite_eq_left hk]
    constructor
    · intro h; exact hy.1 (by nlinarith)
    · intro h; exact hy.2 (by nlinarith)

open Metric in
open Metric in
/-- **The parity differs between the two sectors at a point of an edge ray.** For rays `a'`, `b'`
from `w`, with `a'` along an edge and `b'` either on the positive side of `a'` or opposite to it,
the open sectors `sec1` and `sec2` of a small ball contain points of different parity. -/
lemma parity_ne_sectors (hs : p.IsSimple) {w a' b' : ℝ × ℝ} (ha' : RayEdge p w a')
    (hcase : 0 < cross a' b' ∨ ∃ l : ℝ, 0 < l ∧ b' = (-l) • a') {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ y₁ ∈ sec1 w a' b' ρ, ∃ y₂ ∈ sec2 w a' b' ρ, p.parity y₁ ≠ p.parity y₂ := by
  obtain ⟨c, t0, ht0, ht1, hball, hev⟩ := parity_jump_at hs ha' hρ
  -- a vector perpendicular to `a'`
  set u : ℝ × ℝ := (-a'.2, a'.1) with hu
  have hN : 0 < a'.1 ^ 2 + a'.2 ^ 2 := by
    have := ha'.1
    rcases ne_or_eq a'.1 0 with h | h
    · positivity
    · have : a'.2 ≠ 0 := fun h2 => ha'.1 (Prod.ext h h2)
      positivity
  have hβu : ∀ (σ δ : ℝ), cross a' (w + t0 • a' + (σ * δ) • u - w) = σ * δ * (a'.1 ^ 2 + a'.2 ^ 2) := by
    intro σ δ; simp [cross, hu]; ring
  -- sign of `α` near the base point
  have hα : ∀ᶠ y in 𝓝 (w + t0 • a'), 0 < cross a' (y - w) → 0 < cross (y - w) b' := by
    rcases hcase with hD | ⟨l, hl, hlb⟩
    · have hcont : Continuous fun y : ℝ × ℝ => cross (y - w) b' := by
        unfold cross; fun_prop
      have hpos : 0 < cross (w + t0 • a' - w) b' := by
        have : cross (w + t0 • a' - w) b' = t0 * cross a' b' := by simp [cross]; ring
        rw [this]; exact mul_pos ht0 hD
      filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hpos)] with y hy _ using hy
    · refine Filter.Eventually.of_forall fun y hy => ?_
      have : cross (y - w) b' = l * cross a' (y - w) := by
        rw [hlb]; simp [cross]; ring
      rw [this]; exact mul_pos hl hy
  have hball' : ∀ᶠ y in 𝓝 (w + t0 • a'), y ∈ ball w ρ := isOpen_ball.mem_nhds hball
  have hG := hev.and (hα.and hball')
  have tend : ∀ σ : ℝ, Filter.Tendsto (fun δ : ℝ => w + t0 • a' + (σ * δ) • u) (𝓝[>] 0)
      (𝓝 (w + t0 • a')) := by
    intro σ
    have : Continuous fun δ : ℝ => w + t0 • a' + (σ * δ) • u := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨δ1, hG1, hδ1⟩ := (((tend 1).eventually hG).and
    (self_mem_nhdsWithin : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ)).exists
  obtain ⟨δ2, hG2, hδ2⟩ := (((tend (-1)).eventually hG).and
    (self_mem_nhdsWithin : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ)).exists
  refine ⟨w + t0 • a' + (1 * δ1) • u, ?_, w + t0 • a' + (-1 * δ2) • u, ?_, ?_⟩
  · obtain ⟨⟨hp1, hp2⟩, hα1, hb1⟩ := hG1
    have hβ1 : 0 < cross a' (w + t0 • a' + (1 * δ1) • u - w) := by
      rw [hβu]; nlinarith [mul_pos hδ1 hN]
    exact ⟨hb1, hα1 hβ1, hβ1⟩
  · obtain ⟨⟨hp1, hp2⟩, hα1, hb1⟩ := hG2
    have hβ1 : cross a' (w + t0 • a' + (-1 * δ2) • u - w) < 0 := by
      rw [hβu]; nlinarith [mul_pos hδ2 hN]
    exact ⟨hb1, Or.inr hβ1⟩
  · obtain ⟨⟨hp1, hp2⟩, hα1, hb1⟩ := hG1
    obtain ⟨⟨hq1, hq2⟩, hα2, hb2⟩ := hG2
    have hβ1 : 0 < cross a' (w + t0 • a' + (1 * δ1) • u - w) := by
      rw [hβu]; nlinarith [mul_pos hδ1 hN]
    have hβ2 : cross a' (w + t0 • a' + (-1 * δ2) • u - w) < 0 := by
      rw [hβu]; nlinarith [mul_pos hδ2 hN]
    rw [hp1 hβ1, hq2 hβ2]
    intro h
    exact absurd (by linear_combination h : (0 : ZMod 2) = 1) (by decide)

open Metric in
/-- **The two sides of the carrier at a point where it is two rays along edges.** Near `w` the
complement of the carrier is the union of two preconnected sets, both accumulating at `w`, on
which the parity takes different values. -/
theorem exists_sectors (hs : p.IsSimple) {w a b : ℝ × ℝ} (ha : RayEdge p w a) (hb : RayEdge p w b)
    (hnp : ∀ l : ℝ, 0 < l → b ≠ l • a) {ρ : ℝ} (hρ : 0 < ρ)
    (hcar : ∀ z ∈ ball w ρ, z ∈ p.carrier ↔ z - w ∈ ray0 a ∪ ray0 b) :
    ∃ Q₁ Q₂ : Set (ℝ × ℝ), IsPreconnected Q₁ ∧ IsPreconnected Q₂ ∧
      ball w ρ \ p.carrier = Q₁ ∪ Q₂ ∧ w ∈ closure Q₁ ∧ w ∈ closure Q₂ ∧
      ∃ y₁ ∈ Q₁, ∃ y₂ ∈ Q₂, p.parity y₁ ≠ p.parity y₂ := by
  obtain ⟨a', b', hab, hcl, hv, hcase⟩ := planar_two_rays ha.1 hb.1 hnp
  have ha' : RayEdge p w a' := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hU : ray0 a' ∪ ray0 b' = ray0 a ∪ ray0 b := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact union_comm _ _
  obtain ⟨h1, h2, h3, h4, h5⟩ := sectors (w := w) hρ hcl hv
  have hEq : ball w ρ \ p.carrier = sec1 w a' b' ρ ∪ sec2 w a' b' ρ := by
    rw [← h3]
    ext z
    constructor
    · rintro ⟨hz, hn⟩
      refine ⟨hz, fun hm => hn ?_⟩
      rw [hcar z hz, ← hU]; exact hm
    · rintro ⟨hz, hn⟩
      refine ⟨hz, fun hm => hn ?_⟩
      rw [hcar z hz, ← hU] at hm; exact hm
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := parity_ne_sectors hs ha' hcase hρ
  exact ⟨sec1 w a' b' ρ, sec2 w a' b' ρ, h1, h2, hEq, h4, h5, y₁, hy₁, y₂, hy₂, hne⟩

/-! ## The carrier near a point -/

open Metric in
/-- A point off finitely many closed sets has a ball that misses all of them. -/
lemma exists_ball_avoid_edges (p : Polygon n) (S : Set (Fin n)) {w : ℝ × ℝ}
    (h : ∀ f ∈ S, w ∉ p.edge f) : ∃ ρ > 0, ∀ f ∈ S, ∀ z ∈ ball w ρ, z ∉ p.edge f := by
  have hcl : IsClosed (⋃ f ∈ S, p.edge f) :=
    (Set.toFinite S).isClosed_biUnion fun f _ => (isCompact_segment' _ _).isClosed
  have hw : w ∈ (⋃ f ∈ S, p.edge f)ᶜ := fun hm => by
    obtain ⟨f, hf, hwf⟩ := mem_iUnion₂.1 hm
    exact h f hf hwf
  obtain ⟨ρ, hρ, hsub⟩ := isOpen_iff.1 hcl.isOpen_compl w hw
  refine ⟨ρ, hρ, fun f hf z hz hzf => hsub hz (mem_iUnion₂.2 ⟨f, hf, hzf⟩)⟩

/-- A point `w + s (v - w)` with `0 ≤ s ≤ 1` lies on the segment from `w` to `v`. -/
lemma mem_segment_of_ray {w v : ℝ × ℝ} {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    w + s • (v - w) ∈ segment ℝ w v :=
  ⟨1 - s, s, by linarith, h0, by ring, by ext <;> simp <;> ring⟩

/-- A point of the open ray from `w` towards `v`, short of `v`, is on the segment but is neither
end. -/
lemma ray_point_ne {w v : ℝ × ℝ} (hwv : w ≠ v) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    w + t • (v - w) ≠ w ∧ w + t • (v - w) ≠ v := by
  constructor
  · intro h
    have : t • (v - w) = 0 := by simpa using h
    rcases smul_eq_zero.1 this with h' | h'
    · exact h0.ne' h'
    · exact hwv (sub_eq_zero.1 h').symm
  · intro h
    have : (1 - t) • (v - w) = 0 := by
      have : w + t • (v - w) - v = -((1 - t) • (v - w)) := by
        ext <;> simp <;> ring
      rw [h, sub_self] at this
      exact (neg_eq_zero.1 this.symm)
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact hwv (sub_eq_zero.1 h').symm

/-- A point `w + s a` of a ray, in a ball of radius at most `‖a‖` about `w`, has `s < 1`. -/
lemma ray_param_lt_one {w a : ℝ × ℝ} {ρ s : ℝ} (hρ : ρ ≤ ‖a‖) (hs : 0 ≤ s)
    (hz : w + s • a ∈ ball w ρ) : s < 1 := by
  by_contra h
  push Not at h
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs] at hz
  nlinarith [norm_nonneg a]

/-- Points of a segment from `u` to `v` through `w` lie on a ray from `w` towards `v` or towards
`u`. -/
lemma sub_mem_rays {u v w z : ℝ × ℝ} (hw : w ∈ segment ℝ u v) (h1 : w ≠ u) (h2 : w ≠ v)
    (hz : z ∈ segment ℝ u v) : z - w ∈ ray0 (v - w) ∪ ray0 (u - w) := by
  obtain ⟨a, b, ha, hb, hab, hw1, hw2⟩ := strict_of_mem_segment hw h1 h2
  obtain ⟨r1, r2, hr1, hr2, hr, hzz⟩ := hz
  have hz1 : z.1 = r1 * u.1 + r2 * v.1 := by rw [← hzz]; simp
  have hz2 : z.2 = r1 * u.2 + r2 * v.2 := by rw [← hzz]; simp
  obtain rfl : a = 1 - b := by linarith
  obtain rfl : r1 = 1 - r2 := by linarith
  have ha' : (1 - b) ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  rcases le_total b r2 with h | h
  · left
    refine ⟨(r2 - b) / (1 - b), div_nonneg (by linarith) ha.le, Prod.ext ?_ ?_⟩
    · show z.1 - w.1 = (r2 - b) / (1 - b) * (v.1 - w.1)
      rw [hw1, hz1]; field_simp; ring
    · show z.2 - w.2 = (r2 - b) / (1 - b) * (v.2 - w.2)
      rw [hw2, hz2]; field_simp; ring
  · right
    refine ⟨(b - r2) / b, div_nonneg (by linarith) hb.le, Prod.ext ?_ ?_⟩
    · show z.1 - w.1 = (b - r2) / b * (u.1 - w.1)
      rw [hw1, hz1]; field_simp; ring
    · show z.2 - w.2 = (b - r2) / b * (u.2 - w.2)
      rw [hw2, hz2]; field_simp; ring

/-- A point of the segment from `w` to `v` lies on the ray from `w` towards `v`. -/
lemma sub_mem_ray_of_mem_segment {w v z : ℝ × ℝ} (hz : z ∈ segment ℝ w v) :
    z - w ∈ ray0 (v - w) := by
  obtain ⟨r1, r2, hr1, hr2, hr, hzz⟩ := hz
  refine ⟨r2, hr2, Prod.ext ?_ ?_⟩
  · show z.1 - w.1 = r2 * (v.1 - w.1)
    have : z.1 = r1 * w.1 + r2 * v.1 := by rw [← hzz]; simp
    rw [this]; obtain rfl : r1 = 1 - r2 := by linarith
    ring
  · show z.2 - w.2 = r2 * (v.2 - w.2)
    have : z.2 = r1 * w.2 + r2 * v.2 := by rw [← hzz]; simp
    rw [this]; obtain rfl : r1 = 1 - r2 := by linarith
    ring

/-- **A vertex of a simple polygon.** Near a vertex, the carrier is two rays, along the two edges
at the vertex, pointing in different directions. -/
theorem local_data_vertex (hs : p.IsSimple) {j : Fin n} {w : ℝ × ℝ}
    (hw : w = p (finRotate n j)) :
    ∃ a b : ℝ × ℝ, RayEdge p w a ∧ RayEdge p w b ∧ (∀ l : ℝ, 0 < l → b ≠ l • a) ∧
      ∃ ρ > 0, ∀ z ∈ Metric.ball w ρ, z ∈ p.carrier ↔ z - w ∈ ray0 a ∪ ray0 b := by
  set k := finRotate n j with hk
  set u := p j with hu
  set v := p (finRotate n k) with hv
  have hjk : p k = w := hw.symm
  have huw : u ≠ w := by rw [hw]; exact hs.1 j
  have hwv : w ≠ v := by rw [← hjk]; exact hs.1 k
  have hedgek : p.edge k = segment ℝ w v := by
    show segment ℝ (p k) (p (finRotate n k)) = _
    rw [hjk]
  have hedgej : p.edge j = segment ℝ w u := by
    show segment ℝ (p j) (p (finRotate n j)) = _
    rw [← hw, segment_symm]
  have hrA : RayEdge p w (v - w) := by
    refine ⟨sub_ne_zero.2 hwv.symm, k, 1, one_ne_zero, by rw [hjk, one_smul], fun t h0 h1 => ?_⟩
    obtain ⟨n1, n2⟩ := ray_point_ne hwv h0 h1
    refine ⟨?_, by rw [hjk]; exact n1, n2⟩
    rw [hedgek]; exact mem_segment_of_ray h0.le h1.le
  have hrB : RayEdge p w (u - w) := by
    refine ⟨sub_ne_zero.2 huw, j, -1, by norm_num, ?_, fun t h0 h1 => ?_⟩
    · rw [← hw]; ext <;> simp [hu]
    · obtain ⟨n1, n2⟩ := ray_point_ne huw.symm h0 h1
      refine ⟨?_, n2, by rw [← hw]; exact n1⟩
      rw [hedgej]; exact mem_segment_of_ray h0.le h1.le
  have hnp : ∀ l : ℝ, 0 < l → u - w ≠ l • (v - w) := by
    intro l hl heq
    set s := min 1 l / 2 with hs'
    have hs0 : 0 < s := by have : 0 < min 1 l := lt_min one_pos hl; linarith
    have hs1 : s ≤ 1 / 2 := by have := min_le_left 1 l; linarith
    have hsl : s ≤ l / 2 := by have := min_le_right 1 l; linarith
    have hzk : w + s • (v - w) ∈ p.edge k := by
      rw [hedgek]; exact mem_segment_of_ray hs0.le (by linarith)
    have hzj : w + s • (v - w) ∈ p.edge j := by
      rw [hedgej]
      have : w + s • (v - w) = w + (s / l) • (u - w) := by
        rw [heq, smul_smul]; congr 2; field_simp
      rw [this]; exact mem_segment_of_ray (by positivity) (by rw [div_le_one hl]; linarith)
    have hmem : w + s • (v - w) ∈ p.edge j ∩ p.edge (finRotate n j) := ⟨hzj, hzk⟩
    rw [hs.2.2 j] at hmem
    have : s • (v - w) = 0 := by
      have h' : w + s • (v - w) = w := (Set.mem_singleton_iff.1 hmem).trans hjk
      simpa using h'
    rcases smul_eq_zero.1 this with h' | h'
    · exact hs0.ne' h'
    · exact hwv (sub_eq_zero.1 h').symm
  obtain ⟨ρ1, hρ1, havoid⟩ := exists_ball_avoid_edges p {f | f ≠ j ∧ f ≠ k} (w := w) (by
    intro f hf hwf
    rcases eq_of_vertex_mem_edge hs (i := j) (by rw [← hw]; exact hwf) with h | h
    · exact hf.1 h
    · exact hf.2 h)
  have hna : 0 < ‖v - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hwv.symm)
  have hnb : 0 < ‖u - w‖ := norm_pos_iff.2 (sub_ne_zero.2 huw)
  refine ⟨v - w, u - w, hrA, hrB, fun l hl => hnp l hl, min ρ1 (min ‖v - w‖ ‖u - w‖),
    lt_min hρ1 (lt_min hna hnb), fun z hz => ?_⟩
  have hz1 : z ∈ Metric.ball w ρ1 := Metric.mem_ball.2
    (lt_of_lt_of_le (Metric.mem_ball.1 hz) (min_le_left _ _))
  constructor
  · intro hc
    obtain ⟨f, hf⟩ := mem_iUnion.1 hc
    by_cases hfj : f = j
    · subst hfj
      rw [hedgej] at hf
      exact Or.inr (sub_mem_ray_of_mem_segment hf)
    · by_cases hfk : f = k
      · subst hfk
        rw [hedgek] at hf
        exact Or.inl (sub_mem_ray_of_mem_segment hf)
      · exact absurd hf (havoid f ⟨hfj, hfk⟩ z hz1)
  · rintro (⟨s, hs0, hsz⟩ | ⟨s, hs0, hsz⟩)
    · have hzeq : z = w + s • (v - w) := by rw [← hsz]; simp
      have hzb : w + s • (v - w) ∈ Metric.ball w (min ρ1 (min ‖v - w‖ ‖u - w‖)) := hzeq ▸ hz
      have hlt := ray_param_lt_one ((min_le_right _ _).trans (min_le_left _ _)) hs0 hzb
      refine mem_iUnion.2 ⟨k, ?_⟩
      rw [hedgek, hzeq]; exact mem_segment_of_ray hs0 hlt.le
    · have hzeq : z = w + s • (u - w) := by rw [← hsz]; simp
      have hzb : w + s • (u - w) ∈ Metric.ball w (min ρ1 (min ‖v - w‖ ‖u - w‖)) := hzeq ▸ hz
      have hlt := ray_param_lt_one ((min_le_right _ _).trans (min_le_right _ _)) hs0 hzb
      refine mem_iUnion.2 ⟨j, ?_⟩
      rw [hedgej, hzeq]; exact mem_segment_of_ray hs0 hlt.le

/-- **A point inside an edge of a simple polygon.** Near such a point, the carrier is a straight
line through it, two opposite rays along the edge. -/
theorem local_data_interior (hs : p.IsSimple) {e : Fin n} {w : ℝ × ℝ} (hwe : w ∈ p.edge e)
    (h1 : w ≠ p e) (h2 : w ≠ p (finRotate n e)) :
    ∃ a b : ℝ × ℝ, RayEdge p w a ∧ RayEdge p w b ∧ (∀ l : ℝ, 0 < l → b ≠ l • a) ∧
      ∃ ρ > 0, ∀ z ∈ Metric.ball w ρ, z ∈ p.carrier ↔ z - w ∈ ray0 a ∪ ray0 b := by
  set u := p e with hu
  set v := p (finRotate n e) with hv
  have huv : u ≠ v := hs.1 e
  obtain ⟨α, β, hα, hβ, hαβ, hw1, hw2⟩ := strict_of_mem_segment hwe h1 h2
  obtain rfl : α = 1 - β := by linarith
  have hwuv : w = u + β • (v - u) := by
    ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]; rw [hw1]; ring
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]; rw [hw2]; ring
  have hβ1 : β < 1 := by linarith
  have ha : v - w = (1 - β) • (v - u) := by rw [hwuv]; ext <;> simp <;> ring
  have hb : u - w = (-β) • (v - u) := by rw [hwuv]; ext <;> simp <;> ring
  have hvu : v - u ≠ 0 := sub_ne_zero.2 huv.symm
  have hrA : RayEdge p w (v - w) := by
    refine ⟨by rw [ha]; exact smul_ne_zero (by linarith) hvu, e, 1 / (1 - β), by
      have : (1 - β) ≠ 0 := by linarith
      positivity, ?_, fun t h0 h1' => ?_⟩
    · rw [ha, smul_smul, div_mul_cancel₀ _ (by linarith : (1 - β) ≠ 0), one_smul]
    · have hl : w + t • (v - w) = u + (β + t * (1 - β)) • (v - u) := by
        rw [ha, hwuv]; ext <;> simp <;> ring
      rw [hl]
      have hp0 : 0 < β + t * (1 - β) := by nlinarith
      have hp1 : β + t * (1 - β) < 1 := by nlinarith
      obtain ⟨n1, n2⟩ := ray_point_ne huv hp0 hp1
      exact ⟨mem_segment_of_ray hp0.le hp1.le, n1, n2⟩
  have hrB : RayEdge p w (u - w) := by
    refine ⟨by rw [hb]; exact smul_ne_zero (by linarith) hvu, e, -1 / β, by
      have : β ≠ 0 := hβ.ne'
      positivity, ?_, fun t h0 h1' => ?_⟩
    · have h1' : (-1 / β * -β) = 1 := by field_simp
      rw [hb, smul_smul, h1', one_smul]
    · have hl : w + t • (u - w) = u + (β * (1 - t)) • (v - u) := by
        rw [hb, hwuv]; ext <;> simp <;> ring
      rw [hl]
      have hp0 : 0 < β * (1 - t) := by nlinarith
      have hp1 : β * (1 - t) < 1 := by nlinarith
      obtain ⟨n1, n2⟩ := ray_point_ne huv hp0 hp1
      exact ⟨mem_segment_of_ray hp0.le hp1.le, n1, n2⟩
  have hnp : ∀ l : ℝ, 0 < l → u - w ≠ l • (v - w) := by
    intro l hl heq
    rw [hb, ha, smul_smul] at heq
    have : (-β - l * (1 - β)) • (v - u) = 0 := by
      rw [sub_smul, ← heq]; simp
    rcases smul_eq_zero.1 this with h' | h'
    · nlinarith [mul_pos hl (by linarith : (0 : ℝ) < 1 - β)]
    · exact hvu h'
  obtain ⟨ρ1, hρ1, havoid⟩ := exists_ball_avoid_edges p {f | f ≠ e} (w := w) (fun f hf hwf =>
    not_mem_edge_of_ne hs (Ne.symm hf) hwe h1 h2 hwf)
  have hna : 0 < ‖v - w‖ := norm_pos_iff.2 (by rw [ha]; exact smul_ne_zero (by linarith) hvu)
  have hnb : 0 < ‖u - w‖ := norm_pos_iff.2 (by rw [hb]; exact smul_ne_zero (by linarith) hvu)
  refine ⟨v - w, u - w, hrA, hrB, fun l hl => hnp l hl, min ρ1 (min ‖v - w‖ ‖u - w‖),
    lt_min hρ1 (lt_min hna hnb), fun z hz => ?_⟩
  have hz1 : z ∈ Metric.ball w ρ1 := Metric.mem_ball.2
    (lt_of_lt_of_le (Metric.mem_ball.1 hz) (min_le_left _ _))
  have hwv : w ∈ segment ℝ u v := hwe
  constructor
  · intro hc
    obtain ⟨f, hf⟩ := mem_iUnion.1 hc
    by_cases hfe : f = e
    · subst hfe
      exact sub_mem_rays hwe h1 h2 hf
    · exact absurd hf (havoid f hfe z hz1)
  · rintro (⟨s, hs0, hsz⟩ | ⟨s, hs0, hsz⟩)
    · have hzeq : z = w + s • (v - w) := by rw [← hsz]; simp
      have hzb : w + s • (v - w) ∈ Metric.ball w (min ρ1 (min ‖v - w‖ ‖u - w‖)) := hzeq ▸ hz
      have hlt := ray_param_lt_one ((min_le_right _ _).trans (min_le_left _ _)) hs0 hzb
      refine mem_iUnion.2 ⟨e, ?_⟩
      rw [hzeq]
      exact (convex_segment u v).segment_subset hwv (right_mem_segment ℝ u v)
        (mem_segment_of_ray hs0 hlt.le)
    · have hzeq : z = w + s • (u - w) := by rw [← hsz]; simp
      have hzb : w + s • (u - w) ∈ Metric.ball w (min ρ1 (min ‖v - w‖ ‖u - w‖)) := hzeq ▸ hz
      have hlt := ray_param_lt_one ((min_le_right _ _).trans (min_le_right _ _)) hs0 hzb
      refine mem_iUnion.2 ⟨e, ?_⟩
      rw [hzeq]
      exact (convex_segment u v).segment_subset hwv (left_mem_segment ℝ u v)
        (mem_segment_of_ray hs0 hlt.le)

/-- **Local structure of the carrier at every point.** -/
theorem local_data (hs : p.IsSimple) {w : ℝ × ℝ} (hw : w ∈ p.carrier) :
    ∃ a b : ℝ × ℝ, RayEdge p w a ∧ RayEdge p w b ∧ (∀ l : ℝ, 0 < l → b ≠ l • a) ∧
      ∃ ρ > 0, ∀ z ∈ Metric.ball w ρ, z ∈ p.carrier ↔ z - w ∈ ray0 a ∪ ray0 b := by
  obtain ⟨e, hwe⟩ := mem_iUnion.1 hw
  by_cases hv : ∃ j, w = p (finRotate n j)
  · obtain ⟨j, hj⟩ := hv
    exact local_data_vertex hs hj
  · push Not at hv
    refine local_data_interior hs hwe ?_ (hv e)
    intro h
    exact hv ((finRotate n).symm e) (by rw [Equiv.apply_symm_apply]; exact h)

end Polygon

/-! ## The carrier -/

namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- The carrier of a polygon is closed, being a finite union of closed segments. -/
theorem isClosed_carrier (p : Polygon n) : IsClosed p.carrier :=
  isClosed_iUnion_of_finite fun _ => (isCompact_segment' _ _).isClosed

/-- The carrier of a polygon is nonempty when there is a vertex. -/
theorem carrier_nonempty [NeZero n] (p : Polygon n) : p.carrier.Nonempty :=
  ⟨p 0, mem_iUnion.2 ⟨0, left_mem_segment ℝ _ _⟩⟩

/-- The carrier of a polygon is connected: consecutive edges share a vertex. -/
theorem isPreconnected_carrier [NeZero n] (p : Polygon n) : IsPreconnected p.carrier := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  have : Std.Symm (fun i j : Fin (m + 1) => (p.edge i ∩ p.edge j).Nonempty) :=
    ⟨fun i j ⟨x, hx⟩ => ⟨x, hx.2, hx.1⟩⟩
  have hstep : ∀ k (hk : k < m + 1), Relation.ReflTransGen
      (fun i j : Fin (m + 1) => (p.edge i ∩ p.edge j).Nonempty) 0 ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      refine (ih (by omega)).tail ?_
      have hr : finRotate (m + 1) ⟨k, by omega⟩ = ⟨k + 1, hk⟩ :=
        finRotate_of_lt (by omega)
      refine ⟨p ⟨k + 1, hk⟩, ?_, ?_⟩
      · rw [← hr]; exact right_mem_segment ℝ _ _
      · exact left_mem_segment ℝ _ _
  have hall : ∀ i : Fin (m + 1), Relation.ReflTransGen
      (fun i j : Fin (m + 1) => (p.edge i ∩ p.edge j).Nonempty) 0 i := fun i => hstep i.1 i.2
  exact IsPreconnected.iUnion_of_reflTransGen (fun i => (convex_segment _ _).isPreconnected)
    fun i j => ((Relation.ReflTransGen.stdSymm (r := fun i j : Fin (m + 1) => (p.edge i ∩ p.edge j).Nonempty)).symm _ _ (hall i)).trans (hall j)

/-- **Each parity class is preconnected.** -/
theorem isPreconnected_parity_class [NeZero n] (hs : p.IsSimple) (c : ZMod 2) :
    IsPreconnected {y | y ∉ p.carrier ∧ p.parity y = c} := by
  refine isPreconnected_class (isClosed_carrier p) (isPreconnected_carrier p) (carrier_nonempty p)
    p.parity (fun x hx => eventually_parity_eq p hx) c fun w hw => ?_
  obtain ⟨a, b, ha, hb, hnp, ρ, hρ, hcar⟩ := local_data hs hw
  obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, y₁, hy₁, y₂, hy₂, hne⟩ := exists_sectors hs ha hb hnp hρ hcar
  obtain ⟨hpre, hcl⟩ := local_classes (isClosed_carrier p) (fun x hx => eventually_parity_eq p hx)
    h1 h2 h3 h4 h5 hy₁ hy₂ hne c
  exact ⟨ρ, hρ, hpre, hcl⟩

/-- **Both parities occur off the polygon.** -/
theorem exists_parity_pair [NeZero n] (hs : p.IsSimple) :
    ∃ y₁ y₂ : ℝ × ℝ, y₁ ∉ p.carrier ∧ y₂ ∉ p.carrier ∧ p.parity y₁ ≠ p.parity y₂ := by
  obtain ⟨w, hw⟩ := carrier_nonempty p
  obtain ⟨a, b, ha, hb, hnp, ρ, hρ, hcar⟩ := local_data hs hw
  obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, y₁, hy₁, y₂, hy₂, hne⟩ := exists_sectors hs ha hb hnp hρ hcar
  have hQ : ∀ y ∈ Q₁ ∪ Q₂, y ∉ p.carrier := fun y hy => by
    rw [← h3] at hy; exact hy.2
  exact ⟨y₁, y₂, hQ y₁ (Or.inl hy₁), hQ y₂ (Or.inr hy₂), hne⟩

end Polygon

/-! ## Far from the polygon -/

namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- A bound on the norms of the vertices. -/
lemma exists_bound (p : Polygon n) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ‖p i‖ ≤ M :=
  ⟨∑ i, ‖p i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun i =>
    Finset.single_le_sum (f := fun i => ‖p i‖) (fun i _ => norm_nonneg _) (Finset.mem_univ i)⟩

/-- The carrier lies in the ball bounding the vertices. -/
lemma carrier_subset_closedBall {M : ℝ} (hM : ∀ i, ‖p i‖ ≤ M) :
    p.carrier ⊆ Metric.closedBall 0 M := by
  refine iUnion_subset fun i => ?_
  exact (convex_closedBall (0 : ℝ × ℝ) M).segment_subset (by simpa using hM i)
    (by simpa using hM (finRotate n i))

/-- Above all vertices the parity is zero: no edge is crossed. -/
lemma parity_eq_zero_of_above {x : ℝ × ℝ} (h : ∀ i, (p i).2 < x.2) : p.parity x = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  apply ind_of_not
  rintro ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, -⟩
  · exact absurd h2 (not_lt.2 (h _).le)
  · exact absurd h2 (not_lt.2 (h _).le)

/-- **The parity is zero outside a ball about the origin.** -/
theorem parity_eq_zero_far {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, ‖p i‖ ≤ M) {y : ℝ × ℝ}
    (hy : M < ‖y‖) : p.parity y = 0 := by
  have hcar := carrier_subset_closedBall hM
  have hnot : ∀ z : ℝ × ℝ, M < ‖z‖ → z ∉ p.carrier := fun z hz hz' => by
    have := hcar hz'; rw [mem_closedBall, dist_zero_right] at this; linarith
  have hcomp : ∀ z : ℝ × ℝ, ‖z‖ = max |z.1| |z.2| := fun z => by
    simp [Prod.norm_def]
  -- the four half-planes
  have hpc : ∀ (f : ℝ × ℝ → ℝ), (∀ x y (s t : ℝ), s + t = 1 → f (s • x + t • y) = s * f x + t * f y) →
      (∀ z, 0 < f z → M < ‖z‖) → ∀ z₀, 0 < f z₀ → ∀ z, 0 < f z → p.parity z = p.parity z₀ := by
    intro f hf hfM z₀ h0 z hz
    exact constOn_of_isPreconnected (isClosed_carrier p) (fun x hx => eventually_parity_eq p hx)
      (convex_gt_of_aff hf).isPreconnected (fun z hz => hnot z (hfM z hz)) hz h0
  have hcont : ∀ (c1 c2 c3 : ℝ), ∀ x y (s t : ℝ), s + t = 1 →
      (fun z : ℝ × ℝ => c1 * z.1 + c2 * z.2 + c3) (s • x + t • y) =
      s * (fun z : ℝ × ℝ => c1 * z.1 + c2 * z.2 + c3) x +
        t * (fun z : ℝ × ℝ => c1 * z.1 + c2 * z.2 + c3) y := by
    intro c1 c2 c3 x y s t h
    obtain rfl : t = 1 - s := by linarith
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hM1 : ∀ z : ℝ × ℝ, M < z.2 → M < ‖z‖ := fun z hz => by
    rw [hcomp]; exact lt_max_of_lt_right (lt_of_lt_of_le hz (le_abs_self _))
  have hM2 : ∀ z : ℝ × ℝ, M < -z.2 → M < ‖z‖ := fun z hz => by
    rw [hcomp]; exact lt_max_of_lt_right (lt_of_lt_of_le hz (neg_le_abs _))
  have hM3 : ∀ z : ℝ × ℝ, M < z.1 → M < ‖z‖ := fun z hz => by
    rw [hcomp]; exact lt_max_of_lt_left (lt_of_lt_of_le hz (le_abs_self _))
  have hM4 : ∀ z : ℝ × ℝ, M < -z.1 → M < ‖z‖ := fun z hz => by
    rw [hcomp]; exact lt_max_of_lt_left (lt_of_lt_of_le hz (neg_le_abs _))
  have htop0 : p.parity (0, M + 1) = 0 := parity_eq_zero_of_above fun i => by
    have := hM i
    have h2 : |(p i).2| ≤ ‖p i‖ := by
      rw [Prod.norm_def]; exact le_max_right _ _
    have := (abs_le.1 (h2.trans this)).2
    show (p i).2 < M + 1
    linarith
  -- top
  have top : ∀ z : ℝ × ℝ, M < z.2 → p.parity z = 0 := fun z hz => by
    have := hpc (fun z => 0 * z.1 + 1 * z.2 + (-M)) (hcont 0 1 (-M))
      (fun z hz => hM1 z (by simpa using hz)) (0, M + 1) (by simp) z (by simpa using hz)
    rw [this, htop0]
  have right : ∀ z : ℝ × ℝ, M < z.1 → p.parity z = 0 := fun z hz => by
    have := hpc (fun z => 1 * z.1 + 0 * z.2 + (-M)) (hcont 1 0 (-M))
      (fun z hz => hM3 z (by simpa using hz)) (M + 1, M + 1) (by simp) z (by simpa using hz)
    rw [this, top _ (by simp)]
  have left : ∀ z : ℝ × ℝ, M < -z.1 → p.parity z = 0 := fun z hz => by
    have := hpc (fun z => (-1) * z.1 + 0 * z.2 + (-M)) (hcont (-1) 0 (-M))
      (fun z hz => hM4 z (by simpa using hz)) (-(M + 1), M + 1) (by simp) z (by simpa using hz)
    rw [this, top _ (by simp)]
  have bot : ∀ z : ℝ × ℝ, M < -z.2 → p.parity z = 0 := fun z hz => by
    have := hpc (fun z => 0 * z.1 + (-1) * z.2 + (-M)) (hcont 0 (-1) (-M))
      (fun z hz => hM2 z (by simpa using hz)) (-(M + 1), -(M + 1)) (by simp) z (by simpa using hz)
    rw [this, left _ (by simp)]
  rw [hcomp] at hy
  rcases lt_max_iff.1 hy with h | h
  · rcases lt_abs.1 h with h | h
    · exact right y h
    · exact left y (by linarith)
  · rcases lt_abs.1 h with h | h
    · exact top y h
    · exact bot y (by linarith)

end Polygon

namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- **The polygonal Jordan curve theorem.** The complement of a simple closed polygon is the
disjoint union of two nonempty, open, connected sets, one bounded (the inside) and one unbounded
(the outside). -/
theorem polygon_jordan [NeZero n] (hs : p.IsSimple) :
    ∃ A B : Set (ℝ × ℝ), p.carrierᶜ = A ∪ B ∧ Disjoint A B ∧ IsOpen A ∧ IsOpen B ∧
      IsPreconnected A ∧ IsPreconnected B ∧ A.Nonempty ∧ B.Nonempty ∧
      Bornology.IsBounded B ∧ ¬ Bornology.IsBounded A := by
  obtain ⟨M, hM0, hM⟩ := exists_bound p
  refine ⟨{y | y ∉ p.carrier ∧ p.parity y = 0}, {y | y ∉ p.carrier ∧ p.parity y = 1},
    ?_, ?_, isOpen_class (isClosed_carrier p) (fun x hx => eventually_parity_eq p hx) 0,
    isOpen_class (isClosed_carrier p) (fun x hx => eventually_parity_eq p hx) 1,
    isPreconnected_parity_class hs 0, isPreconnected_parity_class hs 1, ?_, ?_, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      have : p.parity y = 0 ∨ p.parity y = 1 := by
        generalize p.parity y = k; revert k; decide
      rcases this with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  · refine Set.disjoint_left.2 fun y h1 h2 => ?_
    have := h1.2.symm.trans h2.2
    revert this; decide
  · obtain ⟨y₁, y₂, h1, h2, hne⟩ := exists_parity_pair hs
    have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases h01 (p.parity y₁) with h | h
    · exact ⟨y₁, h1, h⟩
    · refine ⟨y₂, h2, ?_⟩
      rcases h01 (p.parity y₂) with h' | h'
      · exact h'
      · exact absurd (h.trans h'.symm) hne
  · obtain ⟨y₁, y₂, h1, h2, hne⟩ := exists_parity_pair hs
    have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases h01 (p.parity y₁) with h | h
    · refine ⟨y₂, h2, ?_⟩
      rcases h01 (p.parity y₂) with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · exact h'
    · exact ⟨y₁, h1, h⟩
  · refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := M)).subset fun y hy => ?_
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    have := parity_eq_zero_far hM0 hM (not_le.1 h)
    exact absurd (hy.2.symm.trans this) (by decide)
  · intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℝ × ℝ)
    have hH : 0 < max M R + 1 := by have := le_max_left M R; linarith
    have hn : ‖((0 : ℝ), max M R + 1)‖ = max M R + 1 := by
      rw [Prod.norm_def, norm_zero, Real.norm_of_nonneg hH.le]; exact max_eq_right hH.le
    have hy : p.parity (0, max M R + 1) = 0 :=
      parity_eq_zero_far hM0 hM (by rw [hn]; linarith [le_max_left M R])
    have hnot : ((0 : ℝ), max M R + 1) ∉ p.carrier := fun hc => by
      have := carrier_subset_closedBall hM hc
      rw [mem_closedBall, dist_zero_right, hn] at this
      linarith [le_max_left M R]
    have := hR ⟨hnot, hy⟩
    rw [mem_closedBall, dist_zero_right, hn] at this
    linarith [le_max_right M R]

/-- **Every point of the polygon is a limit of each parity class.** -/
theorem carrier_subset_closure_class [NeZero n] (hs : p.IsSimple) (c : ZMod 2) :
    p.carrier ⊆ closure {y | y ∉ p.carrier ∧ p.parity y = c} := by
  intro w hw
  obtain ⟨a, b, ha, hb, hnp, ρ, hρ, hcar⟩ := local_data hs hw
  obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, y₁, hy₁, y₂, hy₂, hne⟩ := exists_sectors hs ha hb hnp hρ hcar
  exact (local_classes (isClosed_carrier p) (fun x hx => eventually_parity_eq p hx)
    h1 h2 h3 h4 h5 hy₁ hy₂ hne c).2

/-- **The polygon is the frontier of each of the two regions.** The frontier of the set of points
off the polygon with parity `c` is exactly the polygon. -/
theorem frontier_class [NeZero n] (hs : p.IsSimple) (c : ZMod 2) :
    frontier {y | y ∉ p.carrier ∧ p.parity y = c} = p.carrier := by
  have hopen := isOpen_class (isClosed_carrier p) (fun x hx => eventually_parity_eq p hx) c
  rw [frontier, hopen.interior_eq]
  ext z
  constructor
  · rintro ⟨hcl, hz⟩
    by_contra hzc
    apply hz
    refine ⟨hzc, ?_⟩
    by_contra hne
    have hev := eventually_parity_eq p hzc
    have hnc : ∀ᶠ y in nhds z, y ∉ {y | y ∉ p.carrier ∧ p.parity y = c} := by
      filter_upwards [hev] with y hy hy'
      exact hne (hy.symm.trans hy'.2)
    exact (mem_closure_iff_frequently.1 hcl) hnc
  · intro hz
    exact ⟨carrier_subset_closure_class hs c hz, fun h => h.1 hz⟩

end Polygon


end Lightlike.PL
