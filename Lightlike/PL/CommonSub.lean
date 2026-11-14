import Lightlike.PL.Carrier
import Mathlib.Tactic.Module

/-!
# Common subdivisions

Two geometric complexes `K` and `L` with the same underlying set have a common subdivision
(Rourke–Sanderson, *Introduction to piecewise-linear topology*, Addendum 2.12). The usual proof
intersects the simplices of `K` and `L` into convex cells and takes a derived subdivision of the
resulting cell complex. The construction here does the same without introducing cells:

* a **stratum** is a pair `(σ, τ)` of faces of `K` and `L` whose open simplices meet; the strata
  are ordered by inclusion in both coordinates (they are the open cells `σ° ∩ τ°`);
* a point `pt (σ, τ)` is chosen in each stratum;
* the faces of `commonSub K L` are the sets of chosen points of the chains of strata.

A chain with top stratum `(σ, τ)` spans a simplex inside `σ ∩ τ`, so `commonSub K L` refines both
complexes. It is geometric because the top chosen point of a chain lies off the affine span of the
others (it is in an open simplex whose proper faces contain them), and because a point determines
its chain: the top stratum is its pair of carriers, and the rest of the chain is found from the
point where the ray from the top chosen point through it leaves that stratum. The same rays show
that every point of `|K|` is covered.

## Main results

* `SComplex.isGeom_commonSub`: the chain complex is geometric.
* `SComplex.isSubdivision_commonSub_left`, `isSubdivision_commonSub_right`: it subdivides both.
* `SComplex.IsGeom.exists_common_subdivision`: geometric complexes with the same underlying set
  have a common subdivision.
-/

open Finset

namespace Lightlike.PL

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Two general facts -/

/-- A nonempty finite chain has a greatest element. -/
lemma exists_greatest_of_isChain {α : Type*} [PartialOrder α] {C : Finset α}
    (hC : IsChain (· ≤ ·) (C : Set α)) (hne : C.Nonempty) : ∃ m ∈ C, ∀ p ∈ C, p ≤ m := by
  obtain ⟨m, hm⟩ := exists_maximal hne
  refine ⟨m, hm.1, fun p hp => ?_⟩
  by_cases hpm : p = m
  · exact hpm.le
  · rcases hC hp hm.1 hpm with h | h
    · exact h
    · exact hm.2 hp h

/-- If every point of `S` lies in the closed simplex of `T` and one of them lies in its open
simplex, then the open simplex of `S` lies in the open simplex of `T`. -/
lemma mem_openHull_of_subset_convexHull {S T : Finset E}
    (hST : ∀ y ∈ S, y ∈ convexHull ℝ (T : Set E)) {a : E} (ha : a ∈ S) (haT : a ∈ openHull T)
    {x : E} (hx : x ∈ openHull S) : x ∈ openHull T := by
  classical
  obtain ⟨w, hw, hw1, rfl⟩ := hx
  have hv : ∀ y, ∃ v : E → ℝ, y ∈ S → (∀ z ∈ T, 0 ≤ v z) ∧ (y = a → ∀ z ∈ T, 0 < v z) ∧
      ∑ z ∈ T, v z = 1 ∧ ∑ z ∈ T, v z • z = y := by
    intro y
    by_cases hya : y = a
    · subst hya
      obtain ⟨v, hv, hv1, hvx⟩ := haT
      exact ⟨v, fun _ => ⟨fun z hz => (hv z hz).le, fun _ => hv, hv1, hvx⟩⟩
    · by_cases hyS : y ∈ S
      · obtain ⟨v, hv0, hv1, hvx⟩ := Finset.mem_convexHull'.1 (hST y hyS)
        exact ⟨v, fun _ => ⟨hv0, fun h => absurd h hya, hv1, hvx⟩⟩
      · exact ⟨0, fun h => absurd h hyS⟩
  choose v hv using hv
  refine ⟨fun z => ∑ y ∈ S, w y * v y z, fun z hz => ?_, ?_, ?_⟩
  · show 0 < ∑ y ∈ S, w y * v y z
    rw [← add_sum_erase S _ ha]
    exact add_pos_of_pos_of_nonneg (mul_pos (hw a ha) ((hv a ha).2.1 rfl z hz))
      (sum_nonneg fun y hy => mul_nonneg (hw y (mem_of_mem_erase hy)).le
        ((hv y (mem_of_mem_erase hy)).1 z hz))
  · rw [sum_comm]
    simp_rw [← mul_sum]
    rw [sum_congr rfl fun y hy => by rw [(hv y hy).2.2.1, mul_one]]
    exact hw1
  · simp_rw [sum_smul, mul_smul]
    rw [sum_comm]
    simp_rw [← smul_sum]
    exact sum_congr rfl fun y hy => by rw [(hv y hy).2.2.2]

/-- A point of the open simplex of `insert b S` is `b` itself (when `S` is empty) or lies strictly
between `b` and a point of the open simplex of `S`. -/
lemma openHull_insert_cases [DecidableEq E] {b : E} {S : Finset E} (hb : b ∉ S) {x : E}
    (hx : x ∈ openHull (insert b S)) :
    (S = ∅ ∧ x = b) ∨ ∃ l : ℝ, 0 < l ∧ l < 1 ∧ ∃ y ∈ openHull S, x = l • b + (1 - l) • y := by
  obtain ⟨w, hw, hw1, rfl⟩ := hx
  rw [sum_insert hb] at hw1 ⊢
  rcases S.eq_empty_or_nonempty with rfl | hne
  · left
    simp only [sum_empty, add_zero] at hw1 ⊢
    simp [hw1]
  · right
    have hpos : 0 < ∑ y ∈ S, w y := sum_pos (fun y hy => hw y (mem_insert_of_mem hy)) hne
    have hl : 1 - w b = ∑ y ∈ S, w y := by linarith
    have hl1 : 0 < 1 - w b := hl ▸ hpos
    refine ⟨w b, hw b (mem_insert_self b S), by linarith, ∑ y ∈ S, (w y / (1 - w b)) • y,
      ⟨fun y => w y / (1 - w b), fun y hy => div_pos (hw y (mem_insert_of_mem hy)) hl1, ?_, rfl⟩,
      ?_⟩
    · simp_rw [div_eq_mul_inv]
      rw [← sum_mul, ← hl, mul_inv_cancel₀ hl1.ne']
    · rw [smul_sum]
      congr 1
      refine sum_congr rfl fun y _ => ?_
      rw [smul_smul, mul_div_cancel₀ _ hl1.ne']

namespace SComplex

variable {K L : SComplex E}

/-! ## Strata and their chosen points -/

open Classical in
/-- The **strata** of a pair of complexes: the pairs of faces `(σ, τ)` whose open simplices
meet. -/
noncomputable def strata (K L : SComplex E) : Finset (Finset E × Finset E) :=
  (K.faces ×ˢ L.faces).filter fun p => (openHull p.1 ∩ openHull p.2).Nonempty

lemma mem_strata {p : Finset E × Finset E} :
    p ∈ strata K L ↔ p.1 ∈ K ∧ p.2 ∈ L ∧ (openHull p.1 ∩ openHull p.2).Nonempty := by
  classical
  simp only [strata, mem_filter, mem_product, mem_faces, and_assoc]

/-- The **chosen point** of a stratum, a point of `σ° ∩ τ°` (junk value when they are
disjoint). -/
noncomputable def pt (p : Finset E × Finset E) : E :=
  Classical.epsilon fun x => x ∈ openHull p.1 ∧ x ∈ openHull p.2

lemma pt_mem {p : Finset E × Finset E} (h : (openHull p.1 ∩ openHull p.2).Nonempty) :
    pt p ∈ openHull p.1 ∧ pt p ∈ openHull p.2 :=
  Classical.epsilon_spec (p := fun x => x ∈ openHull p.1 ∧ x ∈ openHull p.2) h

lemma pt_mem_of_mem_strata {p : Finset E × Finset E} (hp : p ∈ strata K L) :
    pt p ∈ openHull p.1 ∧ pt p ∈ openHull p.2 :=
  pt_mem (mem_strata.1 hp).2.2

/-- Distinct strata have distinct chosen points: carriers are unique. -/
lemma pt_injOn (hK : IsGeom K) (hL : IsGeom L) : Set.InjOn pt (↑(strata K L) : Set (Finset E × Finset E)) := by
  intro p hp q hq hpq
  have hp' := mem_strata.1 hp
  have hq' := mem_strata.1 hq
  have h₁ : pt q ∈ openHull p.1 := by rw [← hpq]; exact (pt_mem_of_mem_strata hp).1
  have h₂ : pt q ∈ openHull p.2 := by rw [← hpq]; exact (pt_mem_of_mem_strata hp).2
  exact Prod.ext (hK.eq_of_mem_openHull hp'.1 hq'.1 h₁ (pt_mem_of_mem_strata hq).1)
    (hL.eq_of_mem_openHull hp'.2.1 hq'.2.1 h₂ (pt_mem_of_mem_strata hq).2)

/-! ## The chain complex -/

/-- A **chain of strata**: strata totally ordered by inclusion in both coordinates. -/
def IsStrataChain (K L : SComplex E) (C : Finset (Finset E × Finset E)) : Prop :=
  C ⊆ strata K L ∧ IsChain (· ≤ ·) (C : Set (Finset E × Finset E))

lemma IsStrataChain.mono {C D : Finset (Finset E × Finset E)} (hD : IsStrataChain K L D)
    (h : C ⊆ D) : IsStrataChain K L C :=
  ⟨h.trans hD.1, hD.2.mono (coe_subset.2 h)⟩

variable [DecidableEq E]

open Classical in
/-- The **common subdivision** of `K` and `L`: its faces are the sets of chosen points of the
chains of strata. -/
noncomputable def commonSub (K L : SComplex E) : SComplex E where
  faces := ((strata K L).powerset.filter fun C : Finset (Finset E × Finset E) =>
    IsChain (· ≤ ·) (↑C : Set (Finset E × Finset E))).image (Finset.image pt)
  down s hs t ht := by
    simp only [Finset.mem_image, mem_filter, mem_powerset] at hs ⊢
    obtain ⟨C, ⟨hCs, hC⟩, rfl⟩ := hs
    obtain ⟨C', hC'C, rfl⟩ := subset_image_iff.1 ht
    exact ⟨C', ⟨hC'C.trans hCs, hC.mono (coe_subset.2 hC'C)⟩, rfl⟩

lemma mem_commonSub {s : Finset E} :
    s ∈ commonSub K L ↔ ∃ C, IsStrataChain K L C ∧ C.image pt = s := by
  classical
  rw [← mem_faces]
  simp only [commonSub, Finset.mem_image, mem_filter, mem_powerset, IsStrataChain]

/-- A chain whose strata lie below `m` spans a simplex inside `σ ∩ τ`, for `m = (σ, τ)`. -/
lemma convexHull_image_pt_subset {C : Finset (Finset E × Finset E)} (hC : C ⊆ strata K L)
    {m : Finset E × Finset E} (hm : ∀ p ∈ C, p ≤ m) :
    convexHull ℝ (↑(C.image pt) : Set E) ⊆
      convexHull ℝ (m.1 : Set E) ∩ convexHull ℝ (m.2 : Set E) := by
  refine convexHull_min ?_ ((convex_convexHull ℝ _).inter (convex_convexHull ℝ _))
  intro y hy
  rw [coe_image] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  have hpt := pt_mem_of_mem_strata (hC hp)
  have hle := hm p hp
  exact ⟨convexHull_mono (coe_subset.2 hle.1) (openHull_subset_convexHull _ hpt.1),
    convexHull_mono (coe_subset.2 hle.2) (openHull_subset_convexHull _ hpt.2)⟩

/-- A point of the open simplex of a chain lies in the top stratum of the chain. -/
lemma mem_openHull_top {C : Finset (Finset E × Finset E)} (hC : C ⊆ strata K L)
    {m : Finset E × Finset E} (hmC : m ∈ C) (hm : ∀ p ∈ C, p ≤ m) {x : E}
    (hx : x ∈ openHull (C.image pt)) : x ∈ openHull m.1 ∧ x ∈ openHull m.2 := by
  have hpt := pt_mem_of_mem_strata (hC hmC)
  have hsub := convexHull_image_pt_subset hC hm
  have hS : ∀ y ∈ C.image pt, y ∈ convexHull ℝ (↑(C.image pt) : Set E) := fun y hy =>
    subset_convexHull ℝ _ (mem_coe.2 hy)
  exact ⟨mem_openHull_of_subset_convexHull (fun y hy => (hsub (hS y hy)).1)
      (mem_image_of_mem pt hmC) hpt.1 hx,
    mem_openHull_of_subset_convexHull (fun y hy => (hsub (hS y hy)).2)
      (mem_image_of_mem pt hmC) hpt.2 hx⟩

/-- Points spanned by strata strictly below a stratum `m` are not in the open stratum `m`. -/
lemma not_mem_openHull_of_lt (hK : IsGeom K) (hL : IsGeom L) {C : Finset (Finset E × Finset E)}
    (hC : IsStrataChain K L C) {m : Finset E × Finset E} (hm : m ∈ strata K L)
    (hlt : ∀ p ∈ C, p < m) {y : E} (hy : y ∈ convexHull ℝ (↑(C.image pt) : Set E)) :
    ¬ (y ∈ openHull m.1 ∧ y ∈ openHull m.2) := by
  rintro ⟨h₁, h₂⟩
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp at hy
  obtain ⟨m', hm'C, hm'⟩ := exists_greatest_of_isChain hC.2 hne
  obtain ⟨hy₁, hy₂⟩ := convexHull_image_pt_subset hC.1 hm' hy
  obtain ⟨hm₁, hm₂, -⟩ := mem_strata.1 hm
  have hlt' := hlt m' hm'C
  by_cases he : m'.1 = m.1
  · have hne₂ : m'.2 ≠ m.2 := fun h => hlt'.ne (Prod.ext he h)
    exact notMem_convexHull_of_mem_openHull (hL.indep _ hm₂) hlt'.le.2 hne₂ h₂ hy₂
  · exact notMem_convexHull_of_mem_openHull (hK.indep _ hm₁) hlt'.le.1 he h₁ hy₁

omit [AddCommGroup E] [Module ℝ E] in
/-- The greatest element of a chain, and the rest of the chain below it. -/
lemma lt_of_mem_erase_greatest {C : Finset (Finset E × Finset E)} {m : Finset E × Finset E}
    (hm : ∀ p ∈ C, p ≤ m) {p : Finset E × Finset E} (hp : p ∈ C.erase m) : p < m :=
  lt_of_le_of_ne (hm p (mem_of_mem_erase hp)) (ne_of_mem_erase hp)

/-- **The chosen points of a chain are affinely independent.** -/
theorem affineIndepOn_image_pt (hK : IsGeom K) (hL : IsGeom L) :
    ∀ C : Finset (Finset E × Finset E), IsStrataChain K L C →
      AffineIndepOn ℝ id (↑(C.image pt) : Set E) := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro hC
    rcases C.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨m, hmC, hm⟩ := exists_greatest_of_isChain hC.2 hne
    have hC'C : C.erase m ⊂ C := erase_ssubset hmC
    have ih' := ih _ hC'C (hC.mono hC'C.subset)
    rw [← insert_erase hmC, image_insert, coe_insert]
    refine ih'.id_insert fun hmem => ?_
    have hmn := mem_strata.1 (hC.1 hmC)
    have hpt := pt_mem_of_mem_strata (hC.1 hmC)
    rcases (C.erase m).eq_empty_or_nonempty with he | hne'
    · rw [he] at hmem
      simp only [Finset.image_empty, coe_empty, AffineSubspace.span_empty] at hmem
      exact AffineSubspace.notMem_bot ℝ E _ hmem
    obtain ⟨m', hm'C, hm'⟩ := exists_greatest_of_isChain (hC.mono hC'C.subset).2 hne'
    have hlt : m' < m := lt_of_mem_erase_greatest hm hm'C
    have hsub := convexHull_image_pt_subset (hC.mono hC'C.subset).1 hm'
    have hA₁ : affineSpan ℝ (↑((C.erase m).image pt) : Set E) ≤ affineSpan ℝ (m'.1 : Set E) := by
      rw [← affineSpan_convexHull (m'.1 : Set E)]
      exact affineSpan_mono ℝ fun y hy => (hsub (subset_convexHull ℝ _ hy)).1
    have hA₂ : affineSpan ℝ (↑((C.erase m).image pt) : Set E) ≤ affineSpan ℝ (m'.2 : Set E) := by
      rw [← affineSpan_convexHull (m'.2 : Set E)]
      exact affineSpan_mono ℝ fun y hy => (hsub (subset_convexHull ℝ _ hy)).2
    by_cases he : m'.1 = m.1
    · have hne₂ : m'.2 ≠ m.2 := fun h => hlt.ne (Prod.ext he h)
      exact notMem_affineSpan_of_mem_openHull (hL.indep _ hmn.2.1) hlt.le.2 hne₂ hpt.2
        (hA₂ hmem)
    · exact notMem_affineSpan_of_mem_openHull (hK.indep _ hmn.1) hlt.le.1 he hpt.1 (hA₁ hmem)

/-- The key step of chain uniqueness: a point strictly between the top chosen point `b` and a
point below `m` cannot also be written with a smaller weight on `b` and a point spanned by a chain
strictly below `m`. -/
lemma not_combo_eq (hK : IsGeom K) (hL : IsGeom L) {C : Finset (Finset E × Finset E)}
    (hC : IsStrataChain K L C) {m : Finset E × Finset E} (hm : m ∈ strata K L)
    (hlt : ∀ p ∈ C, p < m) {y z : E} (hy : y ∈ convexHull ℝ (↑(C.image pt) : Set E))
    (hz₁ : z ∈ convexHull ℝ (m.1 : Set E)) (hz₂ : z ∈ convexHull ℝ (m.2 : Set E)) {l l' : ℝ}
    (hll' : l < l') (hl' : l' ≤ 1) (heq : l • pt m + (1 - l) • y = l' • pt m + (1 - l') • z) :
    False := by
  have hpos : 0 < 1 - l := by linarith
  set μ := (l' - l) / (1 - l) with hμ
  have hμ0 : 0 < μ := div_pos (by linarith) hpos
  have hμ1 : μ ≤ 1 := (div_le_one hpos).2 (by linarith)
  have h1 : (1 - l) * μ = l' - l := by rw [hμ]; field_simp
  have h2 : (1 - l) * (1 - μ) = 1 - l' := by rw [mul_sub, h1]; ring
  have key : (1 - l) • y = (1 - l) • (μ • pt m + (1 - μ) • z) := by
    rw [smul_add, smul_smul, smul_smul, h1, h2]
    linear_combination (norm := module) heq
  have hyz : y = μ • pt m + (1 - μ) • z := smul_right_injective E hpos.ne' key
  have hpt := pt_mem_of_mem_strata hm
  refine not_mem_openHull_of_lt hK hL hC hm hlt hy ⟨?_, ?_⟩ <;> rw [hyz]
  · exact combo_mem_openHull hpt.1 hz₁ hμ0 hμ1
  · exact combo_mem_openHull hpt.2 hz₂ hμ0 hμ1

/-- **A point determines its chain**: if a point lies in the open simplices spanned by two chains
of strata, the chains are equal. -/
theorem eq_of_mem_openHull_image_pt (hK : IsGeom K) (hL : IsGeom L) :
    ∀ C D : Finset (Finset E × Finset E), ∀ x : E, IsStrataChain K L C → IsStrataChain K L D →
      x ∈ openHull (C.image pt) → x ∈ openHull (D.image pt) → C = D := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
    intro D x hC hD hxC hxD
    have hCne : C.Nonempty := by
      rcases C.eq_empty_or_nonempty with rfl | h
      · simp at hxC
      · exact h
    have hDne : D.Nonempty := by
      rcases D.eq_empty_or_nonempty with rfl | h
      · simp at hxD
      · exact h
    obtain ⟨m, hmC, hm⟩ := exists_greatest_of_isChain hC.2 hCne
    obtain ⟨n, hnD, hn⟩ := exists_greatest_of_isChain hD.2 hDne
    have hxm := mem_openHull_top hC.1 hmC hm hxC
    have hxn := mem_openHull_top hD.1 hnD hn hxD
    have hm' := mem_strata.1 (hC.1 hmC)
    have hn' := mem_strata.1 (hD.1 hnD)
    have hmn : m = n := Prod.ext (hK.eq_of_mem_openHull hm'.1 hn'.1 hxm.1 hxn.1)
      (hL.eq_of_mem_openHull hm'.2.1 hn'.2.1 hxm.2 hxn.2)
    subst hmn
    have hC' : IsStrataChain K L (C.erase m) := hC.mono (erase_subset _ _)
    have hD' : IsStrataChain K L (D.erase m) := hD.mono (erase_subset _ _)
    have hltC : ∀ p ∈ C.erase m, p < m := fun p hp => lt_of_mem_erase_greatest hm hp
    have hltD : ∀ p ∈ D.erase m, p < m := fun p hp => lt_of_mem_erase_greatest hn hp
    have hbC : pt m ∉ (C.erase m).image pt := by
      intro h
      obtain ⟨p, hp, hpm⟩ := Finset.mem_image.1 h
      exact (hltC p hp).ne (pt_injOn hK hL (hC.1 (mem_of_mem_erase hp)) (hC.1 hmC) hpm)
    have hbD : pt m ∉ (D.erase m).image pt := by
      intro h
      obtain ⟨p, hp, hpm⟩ := Finset.mem_image.1 h
      exact (hltD p hp).ne (pt_injOn hK hL (hD.1 (mem_of_mem_erase hp)) (hD.1 hnD) hpm)
    rw [← insert_erase hmC, image_insert] at hxC
    rw [← insert_erase hnD, image_insert] at hxD
    have hpt := pt_mem_of_mem_strata (hC.1 hmC)
    have hb₁ := openHull_subset_convexHull _ hpt.1
    have hb₂ := openHull_subset_convexHull _ hpt.2
    suffices h : C.erase m = D.erase m by rw [← insert_erase hmC, ← insert_erase hnD, h]
    rcases openHull_insert_cases hbC hxC with ⟨hCe, rfl⟩ | ⟨l, hl0, hl1, y, hy, rfl⟩ <;>
      rcases openHull_insert_cases hbD hxD with ⟨hDe, hxe⟩ | ⟨l', hl0', hl1', y', hy', hxe⟩
    · rw [image_eq_empty.1 hCe, image_eq_empty.1 hDe]
    · exact (not_combo_eq hK hL hD' (hC.1 hmC) hltD (openHull_subset_convexHull _ hy') hb₁ hb₂
        hl1' le_rfl (by rw [← hxe]; module)).elim
    · exact (not_combo_eq hK hL hC' (hC.1 hmC) hltC (openHull_subset_convexHull _ hy) hb₁ hb₂
        hl1 le_rfl (by rw [hxe]; module)).elim
    · have hsub := convexHull_image_pt_subset hC'.1 fun p hp => (hltC p hp).le
      have hsub' := convexHull_image_pt_subset hD'.1 fun p hp => (hltD p hp).le
      have hyc := hsub (openHull_subset_convexHull _ hy)
      have hyc' := hsub' (openHull_subset_convexHull _ hy')
      rcases lt_trichotomy l l' with h | rfl | h
      · exact (not_combo_eq hK hL hC' (hC.1 hmC) hltC (openHull_subset_convexHull _ hy) hyc'.1
          hyc'.2 h hl1'.le hxe).elim
      · have hpos : (1 - l) ≠ 0 := by linarith
        have hyy : y = y' := smul_right_injective E hpos (add_left_cancel hxe)
        subst hyy
        exact ih _ (erase_ssubset hmC) _ y hC' hD' hy hy'
      · exact (not_combo_eq hK hL hD' (hC.1 hmC) hltD (openHull_subset_convexHull _ hy') hyc.1
          hyc.2 h hl1.le hxe.symm).elim

/-- **The chain complex is geometric.** -/
theorem isGeom_commonSub (hK : IsGeom K) (hL : IsGeom L) : IsGeom (commonSub K L) where
  indep s hs := by
    obtain ⟨C, hC, rfl⟩ := mem_commonSub.1 hs
    exact affineIndepOn_image_pt hK hL C hC
  inter s hs t ht := by
    obtain ⟨C, hC, rfl⟩ := mem_commonSub.1 hs
    obtain ⟨D, hD, rfl⟩ := mem_commonSub.1 ht
    rintro x ⟨hxC, hxD⟩
    obtain ⟨s', hs'C, hxs'⟩ := exists_openHull_of_mem_convexHull hxC
    obtain ⟨t', ht'D, hxt'⟩ := exists_openHull_of_mem_convexHull hxD
    obtain ⟨C', hC'C, rfl⟩ := subset_image_iff.1 hs'C
    obtain ⟨D', hD'D, rfl⟩ := subset_image_iff.1 ht'D
    have hCD := eq_of_mem_openHull_image_pt hK hL C' D' x (hC.mono hC'C) (hD.mono hD'D) hxs' hxt'
    subst hCD
    refine convexHull_mono ?_ (openHull_subset_convexHull _ hxs')
    rw [← coe_inter]
    exact coe_subset.2 (subset_inter hs'C ht'D)

/-! ## The chain complex covers both complexes -/

/-- Every point of a stratum `(σ, τ)` lies in the simplex of a chain of strata below `(σ, τ)`.
The induction follows the ray from the chosen point through `x` until it leaves the stratum. -/
theorem exists_chain_of_mem_openHull (hK : IsGeom K) (hL : IsGeom L) :
    ∀ n : ℕ, ∀ σ τ : Finset E, σ.card + τ.card = n → σ ∈ K → τ ∈ L → ∀ x : E,
      x ∈ openHull σ → x ∈ openHull τ → ∃ C, IsStrataChain K L C ∧ (∀ p ∈ C, p ≤ (σ, τ)) ∧
        x ∈ convexHull ℝ (↑(C.image pt) : Set E) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ τ hn hσ hτ x hxσ hxτ
    have hst : (σ, τ) ∈ strata K L := mem_strata.2 ⟨hσ, hτ, ⟨x, hxσ, hxτ⟩⟩
    have hb := pt_mem_of_mem_strata hst
    by_cases hxb : x = pt (σ, τ)
    · refine ⟨{(σ, τ)}, ⟨singleton_subset_iff.2 hst, ?_⟩, by simp, ?_⟩
      · rw [coe_singleton]; exact IsChain.singleton
      · rw [image_singleton, coe_singleton, convexHull_singleton, hxb]; rfl
    obtain ⟨t₁, ht₁, hy₁, hn₁⟩ :=
      exists_exit (hK.indep σ hσ) hb.1 (openHull_subset_convexHull _ hxσ) hxb
    obtain ⟨t₂, ht₂, hy₂, hn₂⟩ :=
      exists_exit (hL.indep τ hτ) hb.2 (openHull_subset_convexHull _ hxτ) hxb
    have ht1 : 1 ≤ min t₁ t₂ := le_min ht₁ ht₂
    have htpos : 0 < min t₁ t₂ := by linarith
    have seg : ∀ {s : Finset E} {t' : ℝ}, min t₁ t₂ ≤ t' → 1 ≤ t' →
        pt (σ, τ) ∈ convexHull ℝ (s : Set E) →
        pt (σ, τ) + t' • (x - pt (σ, τ)) ∈ convexHull ℝ (s : Set E) →
        pt (σ, τ) + min t₁ t₂ • (x - pt (σ, τ)) ∈ convexHull ℝ (s : Set E) := by
      intro s t' hle h1 hbs hys
      have hmem := (convex_convexHull ℝ (s : Set E)).add_smul_sub_mem hbs hys
        (t := min t₁ t₂ / t') ⟨div_nonneg htpos.le (by linarith), (div_le_one (by linarith)).2 hle⟩
      convert hmem using 2
      rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ (by linarith : t' ≠ 0)]
    have hyσ := seg (min_le_left _ _) ht₁ (openHull_subset_convexHull _ hb.1) hy₁
    have hyτ := seg (min_le_right _ _) ht₂ (openHull_subset_convexHull _ hb.2) hy₂
    have hnot : pt (σ, τ) + min t₁ t₂ • (x - pt (σ, τ)) ∉ openHull σ ∨
        pt (σ, τ) + min t₁ t₂ • (x - pt (σ, τ)) ∉ openHull τ := by
      rcases min_choice t₁ t₂ with h | h <;> rw [h]
      · exact Or.inl hn₁
      · exact Or.inr hn₂
    obtain ⟨σ', hσ'K, hσ'σ, hyσ'⟩ := exists_face_openHull hσ hyσ
    obtain ⟨τ', hτ'L, hτ'τ, hyτ'⟩ := exists_face_openHull hτ hyτ
    have hlt : σ'.card + τ'.card < n := by
      rw [← hn]
      rcases hnot with h | h
      · have hne : σ' ≠ σ := fun he => h (he ▸ hyσ')
        have h₁ := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hσ'σ, hne⟩)
        have h₂ := card_le_card hτ'τ
        omega
      · have hne : τ' ≠ τ := fun he => h (he ▸ hyτ')
        have h₁ := card_le_card hσ'σ
        have h₂ := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hτ'τ, hne⟩)
        omega
    obtain ⟨C', hC', hC'le, hyC'⟩ := ih _ hlt σ' τ' rfl hσ'K hτ'L _ hyσ' hyτ'
    have hle : (σ', τ') ≤ (σ, τ) := Prod.mk_le_mk.2 ⟨hσ'σ, hτ'τ⟩
    refine ⟨insert (σ, τ) C', ⟨insert_subset hst hC'.1, ?_⟩, ?_, ?_⟩
    · rw [coe_insert]
      exact hC'.2.insert fun p hp _ => Or.inr ((hC'le p hp).trans hle)
    · intro p hp
      rcases mem_insert.1 hp with rfl | hp
      · exact le_rfl
      · exact (hC'le p hp).trans hle
    · rw [image_insert]
      have hbh : pt (σ, τ) ∈ convexHull ℝ (↑(insert (pt (σ, τ)) (C'.image pt)) : Set E) :=
        subset_convexHull ℝ _ (by simp)
      have hyh : pt (σ, τ) + min t₁ t₂ • (x - pt (σ, τ)) ∈
          convexHull ℝ (↑(insert (pt (σ, τ)) (C'.image pt)) : Set E) :=
        convexHull_mono (by rw [coe_insert]; exact Set.subset_insert _ _) hyC'
      have hmem := (convex_convexHull ℝ _).add_smul_sub_mem hbh hyh
        ⟨inv_nonneg.2 htpos.le, inv_le_one_of_one_le₀ ht1⟩
      convert hmem using 1
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htpos.ne', one_smul, add_sub_cancel]

/-- Every point of `|K|` lies in a simplex of the chain complex, when `|K| = |L|`. -/
lemma space_subset_commonSub (hK : IsGeom K) (hL : IsGeom L) (h : K.space = L.space) :
    K.space ⊆ (commonSub K L).space := by
  intro x hx
  obtain ⟨σ, hσ, hxσ⟩ := exists_carrier hx
  obtain ⟨τ, hτ, hxτ⟩ := exists_carrier (h ▸ hx : x ∈ L.space)
  obtain ⟨C, hC, -, hxC⟩ := exists_chain_of_mem_openHull hK hL _ σ τ rfl hσ hτ x hxσ hxτ
  exact mem_space.2 ⟨_, mem_commonSub.2 ⟨C, hC, rfl⟩, hxC⟩

/-- A simplex of the chain complex lies in both simplices of its top stratum. -/
lemma exists_top_of_mem_commonSub {s : Finset E} (hs : s ∈ commonSub K L) (hne : s.Nonempty) :
    ∃ m ∈ strata K L, convexHull ℝ (s : Set E) ⊆
      convexHull ℝ (m.1 : Set E) ∩ convexHull ℝ (m.2 : Set E) := by
  obtain ⟨C, hC, rfl⟩ := mem_commonSub.1 hs
  obtain ⟨m, hmC, hm⟩ := exists_greatest_of_isChain hC.2 (image_nonempty.1 hne)
  exact ⟨m, hC.1 hmC, convexHull_image_pt_subset hC.1 hm⟩

/-- **The chain complex subdivides the first complex.** -/
theorem isSubdivision_commonSub_left (hK : IsGeom K) (hL : IsGeom L) (h : K.space = L.space)
    (h₀ : ∅ ∈ K) : IsSubdivision (commonSub K L) K where
  geom' := isGeom_commonSub hK hL
  geom := hK
  space_eq := by
    refine Set.Subset.antisymm ?_ (space_subset_commonSub hK hL h)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space.1 hx
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp at hxs
    obtain ⟨m, hm, hsub⟩ := exists_top_of_mem_commonSub hs hne
    exact mem_space.2 ⟨m.1, (mem_strata.1 hm).1, (hsub hxs).1⟩
  le s hs := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, h₀, le_rfl⟩
    obtain ⟨m, hm, hsub⟩ := exists_top_of_mem_commonSub hs hne
    exact ⟨m.1, (mem_strata.1 hm).1, fun x hx => (hsub hx).1⟩

/-- **The chain complex subdivides the second complex.** -/
theorem isSubdivision_commonSub_right (hK : IsGeom K) (hL : IsGeom L) (h : K.space = L.space)
    (h₀ : ∅ ∈ L) : IsSubdivision (commonSub K L) L where
  geom' := isGeom_commonSub hK hL
  geom := hL
  space_eq := by
    refine Set.Subset.antisymm ?_ (h ▸ space_subset_commonSub hK hL h)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space.1 hx
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp at hxs
    obtain ⟨m, hm, hsub⟩ := exists_top_of_mem_commonSub hs hne
    exact mem_space.2 ⟨m.2, (mem_strata.1 hm).2.1, (hsub hxs).2⟩
  le s hs := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, h₀, le_rfl⟩
    obtain ⟨m, hm, hsub⟩ := exists_top_of_mem_commonSub hs hne
    exact ⟨m.2, (mem_strata.1 hm).2.1, fun x hx => (hsub hx).2⟩

omit [DecidableEq E] in
/-- A void complex is subdivided by anything with the same (empty) underlying set, and in
particular two void-or-empty-space complexes subdivide each other. -/
lemma isSubdivision_of_void {K' K : SComplex E} (hK' : IsGeom K') (hK : IsGeom K)
    (h : K'.space = K.space) (hv : ∀ s, s ∉ K') : IsSubdivision K' K :=
  ⟨hK', hK, h, fun s hs => (hv s hs).elim⟩

omit [DecidableEq E] in
/-- **Common subdivisions.** Two geometric complexes with the same underlying set have a common
subdivision. -/
theorem IsGeom.exists_common_subdivision (hK : IsGeom K) (hL : IsGeom L)
    (h : K.space = L.space) : ∃ M, IsSubdivision M K ∧ IsSubdivision M L := by
  classical
  by_cases hKv : ∀ s, s ∉ K
  · exact ⟨K, IsSubdivision.refl hK, isSubdivision_of_void hK hL h hKv⟩
  by_cases hLv : ∀ s, s ∉ L
  · exact ⟨L, isSubdivision_of_void hL hK h.symm hLv, IsSubdivision.refl hL⟩
  obtain ⟨s, hs⟩ := not_forall.1 hKv
  obtain ⟨t, ht⟩ := not_forall.1 hLv
  exact ⟨commonSub K L, isSubdivision_commonSub_left hK hL h (empty_mem (not_not.1 hs)),
    isSubdivision_commonSub_right hK hL h (empty_mem (not_not.1 ht))⟩

end SComplex

end Lightlike.PL
