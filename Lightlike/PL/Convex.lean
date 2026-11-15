import Mathlib.Topology.Instances.Real.Lemmas
import Lightlike.PL.Cells

/-!
# Convexity of open simplices and signs of affine functionals

The open simplex of a finite set is convex. An affine functional that takes both signs on an open
simplex vanishes somewhere on it, so the signs a functional takes on an open simplex are either one
of `{0}`, `{+}`, `{-}` or all three of `{-, 0, +}` (when the simplex is cut). This dichotomy is what
makes the slicing induction work cell by cell.
-/

open Finset Filter Topology

namespace Lightlike.PL

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The open simplex of a finite set is convex. -/
theorem convex_openHull (s : Finset E) : Convex ℝ (openHull s) := by
  intro x hx y hy a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_smul, zero_add]
    have : b = 1 := by linarith
    rw [this, one_smul]; exact hy
  · have := combo_mem_openHull hx (openHull_subset_convexHull s hy) ha' (by linarith)
    rwa [show 1 - a = b by linarith] at this

/-- An affine functional taking opposite signs at two points of an open simplex vanishes at a point
of that open simplex. -/
theorem exists_zero_openHull {s : Finset E} (h : E →ᵃ[ℝ] ℝ) {x y : E} (hx : x ∈ openHull s)
    (hy : y ∈ openHull s) (hxp : 0 < h x) (hyn : h y < 0) : ∃ z ∈ openHull s, h z = 0 := by
  have hd : 0 < h x - h y := by linarith
  set t : ℝ := -h y / (h x - h y) with ht
  have ht0 : 0 < t := div_pos (by linarith) hd
  have ht1 : 0 < 1 - t := by
    rw [ht, sub_pos, div_lt_one hd]; linarith
  refine ⟨t • x + (1 - t) • y, convex_openHull s hx hy ht0.le ht1.le (by ring), ?_⟩
  have := AffineMap.lineMap_apply_module y x t
  have e : t • x + (1 - t) • y = AffineMap.lineMap y x t := by
    rw [AffineMap.lineMap_apply_module]; simp [add_comm]
  rw [e, AffineMap.apply_lineMap]
  simp only [AffineMap.lineMap_apply_module', smul_eq_mul, vsub_eq_sub, vadd_eq_add]
  rw [ht]; field_simp; ring

/-- A functional **cuts** the open simplex of `s` when it takes both signs on it. -/
def Cuts (h : E →ᵃ[ℝ] ℝ) (s : Finset E) : Prop :=
  (∃ x ∈ openHull s, 0 < h x) ∧ ∃ y ∈ openHull s, h y < 0

/-- **The sign dichotomy.** A functional that cuts an open simplex also vanishes at a point of it;
otherwise it has one strict sign (or vanishes) on the whole simplex. -/
theorem Cuts.exists_zero {s : Finset E} {h : E →ᵃ[ℝ] ℝ} (hc : Cuts h s) :
    ∃ z ∈ openHull s, h z = 0 := by
  obtain ⟨⟨x, hx, hxp⟩, ⟨y, hy, hyn⟩⟩ := hc
  exact exists_zero_openHull h hx hy hxp hyn

/-- A functional that does not cut an open simplex has a constant sign condition on it: it is
nonnegative everywhere or nonpositive everywhere there. -/
theorem not_cuts_iff {s : Finset E} {h : E →ᵃ[ℝ] ℝ} :
    ¬ Cuts h s ↔ (∀ x ∈ openHull s, 0 ≤ h x) ∨ ∀ x ∈ openHull s, h x ≤ 0 := by
  unfold Cuts
  push Not
  constructor
  · intro H
    by_cases hp : ∃ x ∈ openHull s, 0 < h x
    · left; exact H hp
    · right; push Not at hp; exact hp
  · rintro (H | H) hp
    · exact H
    · obtain ⟨x, hx, hxp⟩ := hp
      exact absurd (H x hx) (by linarith)

/-! ## Segments into a cell -/

/-- An affine functional on a convex combination. -/
lemma aff_combo (h : E →ᵃ[ℝ] ℝ) (p x : E) (t : ℝ) :
    h (t • p + (1 - t) • x) = t * h p + (1 - t) * h x := by
  have e : t • p + (1 - t) • x = AffineMap.lineMap x p t := by
    rw [AffineMap.lineMap_apply_module]; simp [add_comm]
  rw [e, AffineMap.apply_lineMap]
  simp only [AffineMap.lineMap_apply_module', smul_eq_mul, vsub_eq_sub, vadd_eq_add]
  ring

/-- Going through a zero of an affine functional in the direction away from a point where it is
positive reaches a point of the same open simplex where it is negative. -/
theorem exists_neg_of_zero_pos {s : Finset E} (h : E →ᵃ[ℝ] ℝ) {z y : E} (hz : z ∈ openHull s)
    (hy : y ∈ openHull s) (hz0 : h z = 0) (hy0 : 0 < h y) : ∃ u ∈ openHull s, h u < 0 := by
  obtain ⟨wz, hwz, hz1, rfl⟩ := hz
  obtain ⟨wy, hwy, hy1, rfl⟩ := hy
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, ∀ v ∈ s, ε * wy v < wz v := by
    refine (Filter.eventually_all_finset s).2 fun v hv => ?_
    have hc : ContinuousAt (fun ε : ℝ => ε * wy v) 0 := (continuous_id.mul continuous_const).continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa using hwz v hv)
  obtain ⟨ε, hε, hεpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  have hεpos : 0 < ε := hεpos
  refine ⟨(1 + ε) • ∑ v ∈ s, wz v • v + (1 - (1 + ε)) • ∑ v ∈ s, wy v • v, ?_, ?_⟩
  · refine ⟨fun v => (1 + ε) * wz v - ε * wy v, fun v hv => ?_, ?_, ?_⟩
    · have := hε v hv; nlinarith [hwz v hv]
    · rw [Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum, hz1, hy1]
      ring
    · rw [show (∑ v ∈ s, ((1 + ε) * wz v - ε * wy v) • v) =
          ∑ v ∈ s, ((1 + ε) • (wz v • v) + (1 - (1 + ε)) • (wy v • v)) from
          Finset.sum_congr rfl fun v _ => by module,
        Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  · rw [aff_combo, hz0]; nlinarith

/-- **Constant sign.** If a functional does not cut an open simplex, its sign is constant on it. -/
theorem sign_const_of_not_cuts {s : Finset E} {h : E →ᵃ[ℝ] ℝ} (hc : ¬ Cuts h s) :
    ∃ e : SignType, ∀ x ∈ openHull s, SignType.sign (h x) = e := by
  have key : ∀ g : E →ᵃ[ℝ] ℝ, (∀ x ∈ openHull s, 0 ≤ g x) →
      ∃ e : SignType, ∀ x ∈ openHull s, SignType.sign (g x) = e := by
    intro g hg
    by_cases hall : ∀ x ∈ openHull s, g x = 0
    · exact ⟨0, fun x hx => by simp [hall x hx]⟩
    · push Not at hall
      obtain ⟨y, hy, hy0⟩ := hall
      have hypos : 0 < g y := lt_of_le_of_ne (hg y hy) (Ne.symm hy0)
      refine ⟨1, fun x hx => ?_⟩
      rcases (hg x hx).eq_or_lt with h0 | hpos
      · obtain ⟨u, hu, hun⟩ := exists_neg_of_zero_pos g hx hy h0.symm hypos
        exact absurd (hg u hu) (not_le.2 hun)
      · simp [sign_pos hpos]
  rcases not_cuts_iff.1 hc with hnn | hnp
  · exact key h hnn
  · obtain ⟨e, he⟩ := key (-h) fun x hx => by
      change 0 ≤ -(h x)
      linarith [hnp x hx]
    refine ⟨-e, fun x hx => ?_⟩
    have := he x hx
    change SignType.sign (-(h x)) = e at this
    rw [Left.sign_neg] at this
    rw [← neg_neg (SignType.sign (h x)), this]

/-! ## Relatively open convex sets -/

/-- A set is **spread** when from any two of its points one can move a little further away from the
second through the first and stay in the set: it is open in its own affine span. -/
def Spread (C : Set E) : Prop :=
  ∀ z ∈ C, ∀ y ∈ C, ∀ᶠ ε : ℝ in 𝓝[>] 0, (1 + ε) • z - ε • y ∈ C

/-- Open simplices are spread. -/
theorem spread_openHull (s : Finset E) : Spread (openHull s) := by
  rintro z ⟨wz, hwz, hz1, rfl⟩ y ⟨wy, hwy, hy1, rfl⟩
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, ∀ v ∈ s, ε * wy v < wz v := by
    refine (Filter.eventually_all_finset s).2 fun v hv => ?_
    have hc : ContinuousAt (fun ε : ℝ => ε * wy v) 0 :=
      (continuous_id.mul continuous_const).continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa using hwz v hv)
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)] with ε hε hεpos
  have hεpos : 0 < ε := hεpos
  refine ⟨fun v => (1 + ε) * wz v - ε * wy v, fun v hv => ?_, ?_, ?_⟩
  · have := hε v hv; nlinarith [hwz v hv]
  · rw [Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum, hz1, hy1]
    ring
  · rw [show (∑ v ∈ s, ((1 + ε) * wz v - ε * wy v) • v) =
        ∑ v ∈ s, ((1 + ε) • (wz v • v) - ε • (wy v • v)) from
        Finset.sum_congr rfl fun v _ => by module,
      Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum]

/-- The intersection of two spread sets is spread. -/
theorem Spread.inter {C D : Set E} (hC : Spread C) (hD : Spread D) : Spread (C ∩ D) :=
  fun z hz y hy => (hC z hz.1 y hy.1).and (hD z hz.2 y hy.2)

/-- Pushing the real number `a` further away from `b` along the line through them keeps its sign
for small steps, when `a` and `b` have the same sign. -/
theorem eventually_sign_combo {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, SignType.sign ((1 + ε) * a - ε * b) = SignType.sign a := by
  have hc : ContinuousAt (fun ε : ℝ => (1 + ε) * a - ε * b) 0 :=
    ((continuous_const.add continuous_id).mul continuous_const |>.sub
      (continuous_id.mul continuous_const)).continuousAt
  rcases lt_trichotomy a 0 with hn | hz | hp
  · have hbn : b < 0 := sign_eq_neg_one_iff.1 (h.symm.trans (sign_neg hn))
    filter_upwards [(hc.eventually_lt continuousAt_const (by simpa using hn)).filter_mono
      nhdsWithin_le_nhds] with ε hε
    rw [sign_neg hε, sign_neg hn]
  · have hb : b = 0 := sign_eq_zero_iff.1 (h.symm.trans (by rw [hz]; simp))
    exact Filter.Eventually.of_forall fun ε => by simp [hz, hb]
  · have hbp : 0 < b := sign_eq_one_iff.1 (h.symm.trans (sign_pos hp))
    filter_upwards [(continuousAt_const.eventually_lt hc (by simpa using hp)).filter_mono
      nhdsWithin_le_nhds] with ε hε
    rw [sign_pos hε, sign_pos hp]

/-- A set of points where every functional of a finite family has a prescribed sign is spread. -/
theorem spread_signs {ι : Type*} [Finite ι] (H : ι → E →ᵃ[ℝ] ℝ) (s : ι → SignType) :
    Spread {x : E | ∀ i, SignType.sign (H i x) = s i} := by
  intro z hz y hy
  refine (Filter.eventually_all.2 fun i => ?_).mono fun ε h => h
  have key : ∀ ε : ℝ, H i ((1 + ε) • z - ε • y) = (1 + ε) * H i z - ε * H i y := fun ε => by
    have := aff_combo (H i) z y (1 + ε)
    rw [show (1 + ε) • z - ε • y = (1 + ε) • z + (1 - (1 + ε)) • y by module, this]
    ring
  simp only [key]
  filter_upwards [eventually_sign_combo ((hz i).trans (hy i).symm)] with ε hε
  rw [hε, hz i]

/-- Convex combinations of two reals of the same sign have that sign. -/
theorem sign_combo {a b t : ℝ} (hab : SignType.sign a = SignType.sign b) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : SignType.sign (t * a + (1 - t) * b) = SignType.sign a := by
  have h1t : 0 ≤ 1 - t := by linarith
  rcases lt_trichotomy a 0 with hn | hz | hp
  · have hbn : b < 0 := sign_eq_neg_one_iff.1 (hab.symm.trans (sign_neg hn))
    rw [sign_neg hn, sign_eq_neg_one_iff]
    rcases ht0.eq_or_lt with h0 | htp
    · subst h0; simpa using hbn
    · nlinarith [mul_neg_of_pos_of_neg htp hn, mul_nonpos_of_nonneg_of_nonpos h1t hbn.le]
  · have hb : b = 0 := sign_eq_zero_iff.1 (hab.symm.trans (by rw [hz]; simp))
    simp [hz, hb]
  · have hbp : 0 < b := sign_eq_one_iff.1 (hab.symm.trans (sign_pos hp))
    rw [sign_pos hp, sign_eq_one_iff]
    rcases ht0.eq_or_lt with h0 | htp
    · subst h0; simpa using hbp
    · nlinarith [mul_pos htp hp, mul_nonneg h1t hbp.le]

/-- A set of points where every functional of a family has a prescribed sign is convex. -/
theorem convex_signs {ι : Type*} (H : ι → E →ᵃ[ℝ] ℝ) (s : ι → SignType) :
    Convex ℝ {x : E | ∀ i, SignType.sign (H i x) = s i} := by
  intro x hx y hy a b ha hb hab
  intro i
  have hb' : b = 1 - a := by linarith
  subst hb'
  show SignType.sign (H i (a • x + (1 - a) • y)) = s i
  rw [aff_combo, sign_combo ((hx i).trans (hy i).symm) ha (by linarith), hx i]

/-- A convex set on which an affine functional takes both signs contains a zero of it. -/
theorem exists_zero_of_convex {C : Set E} (hC : Convex ℝ C) (h : E →ᵃ[ℝ] ℝ) {x y : E} (hx : x ∈ C)
    (hy : y ∈ C) (hxp : 0 < h x) (hyn : h y < 0) : ∃ z ∈ C, h z = 0 := by
  have hd : 0 < h x - h y := by linarith
  set t : ℝ := -h y / (h x - h y) with ht
  have ht0 : 0 < t := div_pos (by linarith) hd
  have ht1 : 0 < 1 - t := by
    rw [ht, sub_pos, div_lt_one hd]; linarith
  refine ⟨t • x + (1 - t) • y, hC hx hy ht0.le ht1.le (by ring), ?_⟩
  rw [aff_combo, ht]; field_simp; ring

/-- **Sign dichotomy on a convex spread set.** An affine functional has either a constant sign on
it, or takes the values `> 0`, `= 0` and `< 0` somewhere on it. -/
theorem sign_dichotomy {C : Set E} (hC : Convex ℝ C) (hS : Spread C) (h : E →ᵃ[ℝ] ℝ) :
    (∃ e : SignType, ∀ x ∈ C, SignType.sign (h x) = e) ∨
      ((∃ x ∈ C, 0 < h x) ∧ (∃ z ∈ C, h z = 0) ∧ ∃ y ∈ C, h y < 0) := by
  have key : ∀ g : E →ᵃ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ g x) → ∃ e : SignType, ∀ x ∈ C, SignType.sign (g x) = e := by
    intro g hg
    by_cases hall : ∀ x ∈ C, g x = 0
    · exact ⟨0, fun x hx => by simp [hall x hx]⟩
    · push Not at hall
      obtain ⟨y, hy, hy0⟩ := hall
      have hypos : 0 < g y := lt_of_le_of_ne (hg y hy) (Ne.symm hy0)
      refine ⟨1, fun x hx => ?_⟩
      rcases (hg x hx).eq_or_lt with h0 | hpos
      · obtain ⟨ε, hε, hεpos⟩ := ((hS x hx y hy).and
          (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
        have hεpos : 0 < ε := hεpos
        have := aff_combo g x y (1 + ε)
        rw [show 1 - (1 + ε) = -ε by ring, ← h0, show (1 + ε) • x + (-ε) • y = (1 + ε) • x - ε • y
          by module] at this
        have := hg _ hε
        nlinarith [aff_combo g x y (1 + ε), show (1 + ε) • x + (1 - (1 + ε)) • y
          = (1 + ε) • x - ε • y by module]
      · simp [sign_pos hpos]
  by_cases hp : ∃ x ∈ C, 0 < h x <;> by_cases hn : ∃ y ∈ C, h y < 0
  · obtain ⟨x, hx, hxp⟩ := hp
    obtain ⟨y, hy, hyn⟩ := hn
    exact .inr ⟨⟨x, hx, hxp⟩, exists_zero_of_convex hC h hx hy hxp hyn, y, hy, hyn⟩
  · push Not at hn
    exact .inl (key h hn)
  · push Not at hp
    obtain ⟨e, he⟩ := key (-h) fun x hx => by
      change 0 ≤ -(h x)
      linarith [hp x hx]
    refine .inl ⟨-e, fun x hx => ?_⟩
    have := he x hx
    change SignType.sign (-(h x)) = e at this
    rw [Left.sign_neg] at this
    rw [← neg_neg (SignType.sign (h x)), this]
  · push Not at hp hn
    exact .inl ⟨0, fun x hx => by simp [le_antisymm (hp x hx) (hn x hx)]⟩

/-- If the points `t a + (1 - t) b`, `0 < t ≤ 1`, all have the sign of `a`, then `b` is zero or has
the sign of `a`. -/
theorem sign_eq_of_segment {a b : ℝ}
    (H : ∀ t : ℝ, 0 < t → t ≤ 1 → SignType.sign (t * a + (1 - t) * b) = SignType.sign a) :
    SignType.sign b = 0 ∨ SignType.sign b = SignType.sign a := by
  rcases lt_trichotomy b 0 with hb | hb | hb
  · rcases lt_trichotomy a 0 with ha | ha | ha
    · exact .inr (by rw [sign_neg hb, sign_neg ha])
    · have := H (1 / 2) (by norm_num) (by norm_num)
      rw [ha] at this
      have h2 : (1 / 2 : ℝ) * 0 + (1 - 1 / 2) * b < 0 := by nlinarith
      rw [sign_neg h2] at this; simp at this
    · have hd : 0 < a - b := by linarith
      have := H (-b / (a - b)) (div_pos (by linarith) hd)
        (by rw [div_le_one hd]; linarith)
      have h0 : -b / (a - b) * a + (1 - -b / (a - b)) * b = 0 := by field_simp; ring
      rw [h0, sign_pos ha] at this; simp at this
  · exact .inl (by rw [hb]; simp)
  · rcases lt_trichotomy a 0 with ha | ha | ha
    · have hd : 0 < b - a := by linarith
      have := H (b / (b - a)) (div_pos hb hd) (by rw [div_le_one hd]; linarith)
      have h0 : b / (b - a) * a + (1 - b / (b - a)) * b = 0 := by field_simp; ring
      rw [h0, sign_neg ha] at this; simp at this
    · have := H (1 / 2) (by norm_num) (by norm_num)
      rw [ha] at this
      have h2 : 0 < (1 / 2 : ℝ) * 0 + (1 - 1 / 2) * b := by nlinarith
      rw [sign_pos h2] at this; simp at this
    · exact .inr (by rw [sign_pos hb, sign_pos ha])

/-- The order complex of the image of a set under a map that is an order embedding on the set. -/
lemma SComplex.orderComplex_map_on {P Q : Type*} [PartialOrder P] [DecidableEq P] [PartialOrder Q]
    [DecidableEq Q] (f : P ↪ Q) {S : Finset P} (hf : ∀ a ∈ S, ∀ b ∈ S, f a ≤ f b ↔ a ≤ b) :
    SComplex.orderComplex (S.map f) = (SComplex.orderComplex S).map f := by
  refine SComplex.ext_mem fun C => ?_
  rw [SComplex.mem_orderComplex, SComplex.mem_map]
  constructor
  · rintro ⟨hC, hch⟩
    obtain ⟨u, hu, rfl⟩ := Finset.subset_map_iff.1 hC
    refine ⟨u, SComplex.mem_orderComplex.2 ⟨hu, fun a ha b hb => ?_⟩, rfl⟩
    have := hch (f a) (Finset.mem_map_of_mem f ha) (f b) (Finset.mem_map_of_mem f hb)
    simpa only [hf a (hu ha) b (hu hb), hf b (hu hb) a (hu ha)] using this
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu1, hu2⟩ := SComplex.mem_orderComplex.1 hu
    refine ⟨Finset.map_subset_map.2 hu1, fun a ha b hb => ?_⟩
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
    simpa only [hf a' (hu1 ha') b' (hu1 hb'), hf b' (hu1 hb') a' (hu1 ha')] using
      hu2 a' ha' b' hb'

namespace SComplex

variable {ι : Type*} [DecidableEq E]

omit [DecidableEq E] in
/-- **Closure facts by segments.** If `c' ≤ c` in the cell order, `x` lies in the cell `c'` and `p`
in the cell `c`, then the half-open segment from `x` to `p` lies in the cell `c` (all but the
endpoint `x`). -/
theorem segment_mem_cell {H : ι → E →ᵃ[ℝ] ℝ} {c' c : CellIdx E ι} (hle : c' ≤ c) {x p : E}
    (hx : x ∈ cellSet (fun i => ⇑(H i)) c') (hp : p ∈ cellSet (fun i => ⇑(H i)) c) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) : t • p + (1 - t) • x ∈ cellSet (fun i => ⇑(H i)) c := by
  refine ⟨?_, fun i => ?_⟩
  · refine combo_mem_openHull hp.1 ?_ ht0 ht1
    exact convexHull_mono (by exact_mod_cast hle.1) (openHull_subset_convexHull _ hx.1)
  · have hpi : SignType.sign (H i p) = (show Finset E × (ι → SignType) from c).2 i := hp.2 i
    have hxi : SignType.sign (H i x) = (show Finset E × (ι → SignType) from c').2 i := hx.2 i
    have hli := hle.2 i
    change SignType.sign (H i (t • p + (1 - t) • x)) = (show Finset E × (ι → SignType) from c).2 i
    rw [aff_combo]
    have h1t : 0 ≤ 1 - t := by linarith
    rcases hli with h0 | heq
    · rw [h0] at hxi
      have hx0 : H i x = 0 := by simpa using hxi
      rw [hx0, mul_zero, add_zero, ← hpi]
      rcases lt_trichotomy (H i p) 0 with hn | hz | hpos
      · rw [sign_neg hn, sign_neg (by nlinarith)]
      · rw [hz]; simp
      · rw [sign_pos hpos, sign_pos (by nlinarith)]
    · rw [heq] at hxi
      rw [← hpi]
      rw [← hpi] at hxi
      rcases lt_trichotomy (H i p) 0 with hn | hz | hpos
      · have : H i x < 0 := by
          by_contra hh; push Not at hh
          rcases hh.eq_or_lt with h | h
          · rw [← h] at hxi; simp [sign_neg hn] at hxi
          · rw [sign_pos h, sign_neg hn] at hxi; exact absurd hxi (by decide)
        rw [sign_neg hn, sign_neg (by nlinarith)]
      · rw [hz] at hxi ⊢
        have : H i x = 0 := by simpa using hxi
        simp [this]
      · have : 0 < H i x := by
          by_contra hh; push Not at hh
          rcases hh.eq_or_lt with h | h
          · simp [h, sign_pos hpos] at hxi
          · rw [sign_neg h, sign_pos hpos] at hxi; exact absurd hxi (by decide)
        rw [sign_pos hpos, sign_pos (by nlinarith)]

/-! ## Adding one functional -/

/-- The family `H` with one more functional `h` adjoined (indexed by `ι ⊕ Unit`). -/
def extH (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) : ι ⊕ Unit → E → ℝ :=
  Sum.elim (fun i => ⇑(H i)) (fun _ => ⇑h)

/-- The sign pattern `s` extended by the sign `e` for the new functional. -/
def extSign (s : ι → SignType) (e : SignType) : ι ⊕ Unit → SignType :=
  Sum.elim s (fun _ => e)

omit [DecidableEq E] in
/-- A cell of the extended family lies in the cell of the old family with the new sign dropped. -/
lemma cellSet_ext_subset (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) (σ : Finset E) (s : ι → SignType)
    (e : SignType) :
    cellSet (extH H h) (σ, extSign s e) ⊆ cellSet (fun i => ⇑(H i)) (σ, s) := fun x hx =>
  ⟨hx.1, fun i => hx.2 (Sum.inl i)⟩

omit [DecidableEq E] in
/-- **Uncut cells keep their cell.** If `h` does not cut the open simplex of `σ`, it has a constant
sign `e` there, and the cell of the extended family with sign `e` is exactly the old cell. -/
lemma exists_cellSet_ext_eq {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {σ : Finset E}
    (hc : ¬ Cuts h σ) (s : ι → SignType) :
    ∃ e : SignType, cellSet (extH H h) (σ, extSign s e) = cellSet (fun i => ⇑(H i)) (σ, s) := by
  obtain ⟨e, he⟩ := sign_const_of_not_cuts hc
  refine ⟨e, Set.Subset.antisymm (cellSet_ext_subset H h σ s e) fun x hx => ⟨hx.1, ?_⟩⟩
  rintro (i | _)
  · exact hx.2 i
  · exact he x hx.1

omit [DecidableEq E] in
/-- A cell is convex. -/
theorem convex_cellSet (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) :
    Convex ℝ (cellSet (fun i => ⇑(H i)) c) :=
  (convex_openHull c.1).inter (convex_signs H c.2)

omit [DecidableEq E] in
/-- A cell is spread (open in its affine span). -/
theorem spread_cellSet [Finite ι] (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) :
    Spread (cellSet (fun i => ⇑(H i)) c) :=
  (spread_openHull c.1).inter (spread_signs H c.2)

omit [DecidableEq E] in
/-- **Sign dichotomy on a cell.** A new functional has constant sign on a cell, or takes all three
signs on it. -/
theorem cell_sign_dichotomy [Finite ι] (H : ι → E →ᵃ[ℝ] ℝ) (c : CellIdx E ι) (h : E →ᵃ[ℝ] ℝ) :
    (∃ e : SignType, ∀ x ∈ cellSet (fun i => ⇑(H i)) c, SignType.sign (h x) = e) ∨
      ((∃ x ∈ cellSet (fun i => ⇑(H i)) c, 0 < h x) ∧ (∃ z ∈ cellSet (fun i => ⇑(H i)) c, h z = 0) ∧
        ∃ y ∈ cellSet (fun i => ⇑(H i)) c, h y < 0) :=
  sign_dichotomy (convex_cellSet H c) (spread_cellSet H c) h

omit [DecidableEq E] in
/-- The sign pattern of the extended family is the old one together with the new sign. -/
lemma extSign_eq (s' : ι ⊕ Unit → SignType) :
    s' = extSign (s' ∘ Sum.inl) (s' (Sum.inr ())) := by
  funext i
  rcases i with i | ⟨⟩ <;> rfl

omit [DecidableEq E] in
/-- A point lies in the cell of the extended family exactly when it lies in the old cell and `h`
has the new sign there. -/
lemma mem_cellSet_ext {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {σ : Finset E} {s : ι → SignType}
    {e : SignType} {x : E} :
    x ∈ cellSet (extH H h) (σ, extSign s e) ↔
      x ∈ cellSet (fun i => ⇑(H i)) (σ, s) ∧ SignType.sign (h x) = e := by
  constructor
  · intro hx
    exact ⟨cellSet_ext_subset H h σ s e hx, hx.2 (Sum.inr ())⟩
  · rintro ⟨hx, he⟩
    refine ⟨hx.1, ?_⟩
    rintro (i | ⟨⟩)
    · exact hx.2 i
    · exact he

/-- The cell index with face `σ` and sign pattern `s`. -/
abbrev mkCell (σ : Finset E) (s : ι → SignType) : CellIdx E ι := (σ, s)

/-- **Cells after adding a functional, constant case.** If `h` has constant sign `e` on the nonempty
cell `(σ, s)`, exactly the extension by `e` is a cell of the extended family. -/
lemma ext_cell_mem_iff_const [Fintype ι] [DecidableEq ι] {K : SComplex E}
    {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {σ : Finset E} {s : ι → SignType} {e : SignType}
    (hσ : σ ∈ K) (hne : (cellSet (fun i => ⇑(H i)) (σ, s)).Nonempty)
    (hconst : ∀ x ∈ cellSet (fun i => ⇑(H i)) (σ, s), SignType.sign (h x) = e) (e' : SignType) :
    mkCell σ (extSign s e') ∈ cells K (extH H h) ↔ e' = e := by
  rw [mem_cells]
  constructor
  · rintro ⟨-, x, hx⟩
    rw [mem_cellSet_ext] at hx
    exact hx.2.symm.trans (hconst x hx.1)
  · rintro rfl
    obtain ⟨x, hx⟩ := hne
    exact ⟨hσ, x, mem_cellSet_ext.2 ⟨hx, hconst x hx⟩⟩

/-- **Cells after adding a functional, cut case.** If `h` takes all three signs on the cell
`(σ, s)`, each of the three extensions is a cell of the extended family. -/
lemma ext_cell_mem_of_cut [Fintype ι] [DecidableEq ι] {K : SComplex E}
    {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {σ : Finset E} {s : ι → SignType} (hσ : σ ∈ K)
    (hp : ∃ x ∈ cellSet (fun i => ⇑(H i)) (σ, s), 0 < h x)
    (hz : ∃ x ∈ cellSet (fun i => ⇑(H i)) (σ, s), h x = 0)
    (hn : ∃ x ∈ cellSet (fun i => ⇑(H i)) (σ, s), h x < 0) (e : SignType) :
    mkCell σ (extSign s e) ∈ cells K (extH H h) := by
  rw [mem_cells]
  refine ⟨hσ, ?_⟩
  rcases SignType.trichotomy e with rfl | rfl | rfl
  · obtain ⟨x, hx, h0⟩ := hn
    exact ⟨x, mem_cellSet_ext.2 ⟨hx, sign_neg h0⟩⟩
  · obtain ⟨x, hx, h0⟩ := hz
    exact ⟨x, mem_cellSet_ext.2 ⟨hx, by simp [h0]⟩⟩
  · obtain ⟨x, hx, h0⟩ := hp
    exact ⟨x, mem_cellSet_ext.2 ⟨hx, sign_pos h0⟩⟩

/-- **Every cell of the extended family comes from an old cell.** -/
lemma restrict_mem_cells [Fintype ι] [DecidableEq ι] {K : SComplex E}
    {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {σ : Finset E} {s : ι → SignType} {e : SignType}
    (hc : mkCell σ (extSign s e) ∈ cells K (extH H h)) : mkCell σ s ∈ cells K (fun i => ⇑(H i)) := by
  rw [mem_cells] at hc ⊢
  obtain ⟨hσ, x, hx⟩ := hc
  exact ⟨hσ, x, cellSet_ext_subset H h σ s e hx⟩

omit [DecidableEq E] in
/-- **Signs on a face of a cell with constant sign.** If `h` has constant sign on the cell `c`, a
point of a cell `c'` below `c` has `h`-sign zero or equal to that sign. -/
theorem sign_face_of_const {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ} {c' c : CellIdx E ι} (hle : c' ≤ c)
    {x p : E} (hx : x ∈ cellSet (fun i => ⇑(H i)) c') (hp : p ∈ cellSet (fun i => ⇑(H i)) c)
    {e : SignType} (hconst : ∀ q ∈ cellSet (fun i => ⇑(H i)) c, SignType.sign (h q) = e) :
    SignType.sign (h x) = 0 ∨ SignType.sign (h x) = e := by
  have := sign_eq_of_segment (a := h p) (b := h x) fun t ht0 ht1 => by
    have hq := segment_mem_cell hle hx hp ht0 ht1
    rw [← aff_combo, hconst _ hq, hconst p hp]
  rwa [hconst p hp] at this

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
/-- **Closure order of the extended cells.** One extended cell lies below another exactly when the
old cells are ordered and the new sign is zero or agrees. -/
lemma mkCell_ext_le {σ' σ : Finset E} {s' s : ι → SignType} {e' e : SignType} :
    mkCell σ' (extSign s' e') ≤ mkCell σ (extSign s e) ↔
      mkCell σ' s' ≤ mkCell σ s ∧ (e' = 0 ∨ e' = e) := by
  rw [cellIdx_le, cellIdx_le]
  refine ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, fun i => h2 (Sum.inl i)⟩, h2 (Sum.inr ())⟩, fun ⟨⟨h1, h2⟩, h3⟩ =>
    ⟨h1, ?_⟩⟩
  rintro (i | ⟨⟩)
  · exact h2 i
  · exact h3

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
/-- Dropping the new sign is monotone. -/
lemma mkCell_le_of_ext_le {σ' σ : Finset E} {s' s : ι → SignType} {e' e : SignType}
    (h : mkCell σ' (extSign s' e') ≤ mkCell σ (extSign s e)) : mkCell σ' s' ≤ mkCell σ s :=
  (mkCell_ext_le.1 h).1

omit [AddCommGroup E] [Module ℝ E] [DecidableEq E] in
/-- Extending the sign pattern by a function of the cell is injective. -/
def extEmb (e : CellIdx E ι → SignType) : CellIdx E ι ↪ CellIdx E (ι ⊕ Unit) where
  toFun c := mkCell c.1 (extSign c.2 (e c))
  inj' a b h := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (funext fun i => congr_fun h2 (Sum.inl i))

/-- **Slicing by a functional that cuts no cell.** If the new functional `h` has constant sign on
every cell of `K` and `H`, the slicing of `K` by `H` and `h` is the slicing by `H`, with the cells
renamed by adjoining that sign. -/
theorem sliceComplex_ext_of_const [Fintype ι] [DecidableEq ι] {K : SComplex E}
    {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ}
    (hreg : ∀ c ∈ cells K (fun i => ⇑(H i)), ∃ e : SignType,
      ∀ x ∈ cellSet (fun i => ⇑(H i)) c, SignType.sign (h x) = e) :
    ∃ φ : CellIdx E ι ↪ CellIdx E (ι ⊕ Unit),
      sliceComplex K (extH H h) = (sliceComplex K (fun i => ⇑(H i))).map φ := by
  choose! e he using hreg
  refine ⟨extEmb e, ?_⟩
  have hcells : cells K (extH H h) = (cells K (fun i => ⇑(H i))).map (extEmb e) := by
    have key : ∀ (σ : Finset E) (s' : ι ⊕ Unit → SignType), mkCell σ s' ∈ cells K (extH H h) ↔
        mkCell σ s' ∈ (cells K (fun i => ⇑(H i))).map (extEmb e) := by
      intro σ s'
      rw [Finset.mem_map]
      constructor
      · intro hc
        have hs : s' = extSign (s' ∘ Sum.inl) (s' (Sum.inr ())) := extSign_eq s'
        have hc' : mkCell σ (extSign (s' ∘ Sum.inl) (s' (Sum.inr ()))) ∈ cells K (extH H h) := by
          rw [← hs]; exact hc
        have h0 := restrict_mem_cells hc'
        obtain ⟨hσ, hne⟩ := mem_cells.1 h0
        have := (ext_cell_mem_iff_const hσ hne (he _ h0) (s' (Sum.inr ()))).1 hc'
        refine ⟨mkCell σ (s' ∘ Sum.inl), h0, ?_⟩
        show mkCell σ (extSign (s' ∘ Sum.inl) (e (mkCell σ (s' ∘ Sum.inl)))) = (σ, s')
        rw [← this]; exact Prod.ext rfl hs.symm
      · rintro ⟨c, hc, hφ⟩
        obtain ⟨hσ, hne⟩ := mem_cells.1 hc
        have : mkCell c.1 (extSign c.2 (e c)) = mkCell σ s' := hφ
        rw [← this]
        exact (ext_cell_mem_iff_const hσ hne (he c hc) (e c)).2 rfl
    ext c'
    exact key c'.1 c'.2
  rw [sliceComplex, sliceComplex, hcells]
  refine orderComplex_map_on _ fun a ha b hb => ?_
  show mkCell a.1 (extSign a.2 (e a)) ≤ mkCell b.1 (extSign b.2 (e b)) ↔ a ≤ b
  rw [mkCell_ext_le]
  refine ⟨fun h => h.1, fun hab => ⟨hab, ?_⟩⟩
  obtain ⟨-, x, hx⟩ := mem_cells.1 ha
  obtain ⟨-, p, hp⟩ := mem_cells.1 hb
  have := sign_face_of_const hab hx hp (he b hb)
  rwa [he a ha x hx] at this

end SComplex
end Lightlike.PL
