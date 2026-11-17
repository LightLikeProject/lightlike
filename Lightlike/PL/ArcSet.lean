
import Lightlike.PL.LoopErase

/-!
# Arcs as sets

An arc from `p` to `q` is a subset of the plane that is the image of an injective continuous map
`γ : [0, 1] → ℝ²` with `γ 0 = p` and `γ 1 = q`. Arcs reverse, split at a point, and glue.

## Main results

* `IsArc`, `IsArc.symm`, `IsArc.split`, `IsArc.glue`, `IsArc.of_segment`, `IsArc.chain`.
* `exists_chain_in_open`: two points of a connected open set of the plane are joined by a polygonal
  chain in the set (Klazar, arXiv:2604.04296, Proposition 1.18).
-/

open Set

namespace Lightlike.PL

/-- `A` is an **arc from `p` to `q`**. -/
def IsArc (A : Set (ℝ × ℝ)) (p q : ℝ × ℝ) : Prop :=
  ∃ γ : ℝ → ℝ × ℝ, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ γ 0 = p ∧ γ 1 = q ∧
    γ '' Icc 0 1 = A

namespace IsArc

/-- An arc reversed is an arc. -/
lemma symm {A : Set (ℝ × ℝ)} {p q : ℝ × ℝ} (h : IsArc A p q) : IsArc A q p := by
  obtain ⟨γ, hc, hi, h0, h1, rfl⟩ := h
  have hm : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨fun t => γ (1 - t), hc.comp (by fun_prop) hm, ?_, by simpa using h1, by simpa using h0, ?_⟩
  · intro s hs t ht hst
    have := hi (hm hs) (hm ht) hst
    linarith
  · ext y
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, hm ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, hm ht, by simp⟩

/-- An arc splits at each of its points other than the ends into two arcs that meet only there. -/
lemma split {A : Set (ℝ × ℝ)} {p q x : ℝ × ℝ} (h : IsArc A p q) (hx : x ∈ A) (hxp : x ≠ p)
    (hxq : x ≠ q) :
    ∃ A₁ A₂ : Set (ℝ × ℝ), IsArc A₁ p x ∧ IsArc A₂ x q ∧ A₁ ∪ A₂ = A ∧ A₁ ∩ A₂ = {x} := by
  obtain ⟨γ, hc, hi, h0, h1, rfl⟩ := h
  obtain ⟨τ, hτ, rfl⟩ := hx
  have hτ0 : 0 < τ := lt_of_le_of_ne hτ.1 (fun h => hxp (by rw [← h, h0]))
  have hτ1 : τ < 1 := lt_of_le_of_ne hτ.2 (fun h => hxq (by rw [h, h1]))
  have m1 : MapsTo (fun l : ℝ => l * τ) (Icc 0 1) (Icc 0 1) := fun l hl =>
    ⟨by nlinarith [hl.1], by nlinarith [hl.2]⟩
  have m2 : MapsTo (fun l : ℝ => τ + l * (1 - τ)) (Icc 0 1) (Icc 0 1) := fun l hl =>
    ⟨by nlinarith [hl.1], by nlinarith [hl.2]⟩
  refine ⟨γ '' Icc 0 τ, γ '' Icc τ 1, ⟨fun l => γ (l * τ), hc.comp (by fun_prop) m1, ?_, by simpa using h0,
    by simp, ?_⟩, ⟨fun l => γ (τ + l * (1 - τ)), hc.comp (by fun_prop) m2, ?_, by simp, by simpa using h1, ?_⟩,
    ?_, ?_⟩
  · intro a ha b hb hab
    have := hi (m1 ha) (m1 hb) hab
    exact mul_right_cancel₀ hτ0.ne' this
  · ext y; constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l * τ, ⟨by nlinarith [hl.1], by nlinarith [hl.2]⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u / τ, ⟨by positivity [hu.1], by rw [div_le_one hτ0]; exact hu.2⟩, by simp [div_mul_cancel₀ _ hτ0.ne']⟩
  · intro a ha b hb hab
    have := hi (m2 ha) (m2 hb) hab
    have h' : a * (1 - τ) = b * (1 - τ) := by linarith
    exact mul_right_cancel₀ (by linarith) h'
  · ext y; constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨τ + l * (1 - τ), ⟨by nlinarith [hl.1], by nlinarith [hl.2]⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(u - τ) / (1 - τ), ⟨div_nonneg (by linarith [hu.1]) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]; linarith [hu.2]
      · show γ (τ + (u - τ) / (1 - τ) * (1 - τ)) = γ u
        rw [div_mul_cancel₀ _ (by linarith : (1 - τ) ≠ 0)]; simp
  · ext y; constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · exact ⟨u, ⟨hu.1, le_trans hu.2 hτ.2⟩, rfl⟩
      · exact ⟨u, ⟨le_trans hτ.1 hu.1, hu.2⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rcases le_total u τ with h | h
      · exact Or.inl ⟨u, ⟨hu.1, h⟩, rfl⟩
      · exact Or.inr ⟨u, ⟨h, hu.2⟩, rfl⟩
  · apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨⟨τ, ⟨hτ0.le, le_rfl⟩, rfl⟩, ⟨τ, ⟨le_rfl, hτ1.le⟩, rfl⟩⟩, ?_⟩
    rintro y ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
    have hvu' := hi ⟨le_trans hτ.1 hv.1, hv.2⟩ ⟨hu.1, le_trans hu.2 hτ.2⟩ hvu
    have e : u = τ := by linarith [hu.2, hv.1]
    rw [e]

/-- Two arcs that meet only at the end of the first and the start of the second glue. -/
lemma glue {A₁ A₂ : Set (ℝ × ℝ)} {p x q : ℝ × ℝ} (h₁ : IsArc A₁ p x) (h₂ : IsArc A₂ x q)
    (h : A₁ ∩ A₂ = {x}) : IsArc (A₁ ∪ A₂) p q := by
  obtain ⟨γ₁, hc₁, hi₁, h10, h11, rfl⟩ := h₁
  obtain ⟨γ₂, hc₂, hi₂, h20, h21, rfl⟩ := h₂
  set γ : ℝ → ℝ × ℝ := fun l => if l ≤ 1 / 2 then γ₁ (2 * l) else γ₂ (2 * l - 1) with hγ
  have m1 : MapsTo (fun l : ℝ => 2 * l) (Icc 0 (1 / 2)) (Icc 0 1) := fun l hl =>
    ⟨by linarith [hl.1], by linarith [hl.2]⟩
  have m2 : MapsTo (fun l : ℝ => 2 * l - 1) (Icc (1 / 2) 1) (Icc 0 1) := fun l hl =>
    ⟨by linarith [hl.1], by linarith [hl.2]⟩
  have hA : ContinuousOn γ (Icc 0 (1 / 2)) := by
    have : ContinuousOn (fun l => γ₁ (2 * l)) (Icc 0 (1 / 2)) := hc₁.comp (by fun_prop) m1
    refine this.congr fun l hl => ?_
    simp only [hγ, hl.2, ↓reduceIte]
  have hB : ContinuousOn γ (Icc (1 / 2) 1) := by
    have : ContinuousOn (fun l => γ₂ (2 * l - 1)) (Icc (1 / 2) 1) := hc₂.comp (by fun_prop) m2
    refine this.congr fun l hl => ?_
    rcases eq_or_lt_of_le hl.1 with rfl | hlt
    · simp only [hγ, le_refl, ↓reduceIte]
      norm_num [h11, h20]
    · simp only [hγ, not_le.2 hlt, ↓reduceIte]
  have hIcc : Icc (0 : ℝ) 1 = Icc 0 (1 / 2) ∪ Icc (1 / 2) 1 :=
    (Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)).symm
  have hlo : ∀ l, l ≤ 1 / 2 → γ l = γ₁ (2 * l) := fun l hl => by simp only [hγ, hl, ↓reduceIte]
  have hhi : ∀ l, 1 / 2 < l → γ l = γ₂ (2 * l - 1) := fun l hl => by
    simp only [hγ, not_le.2 hl, ↓reduceIte]
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hIcc]
    exact hA.union_of_isClosed hB isClosed_Icc isClosed_Icc
  · intro a ha b hb hab
    rcases le_or_gt a (1 / 2) with ha' | ha' <;> rcases le_or_gt b (1 / 2) with hb' | hb'
    · rw [hlo a ha', hlo b hb'] at hab
      have := hi₁ (m1 ⟨ha.1, ha'⟩) (m1 ⟨hb.1, hb'⟩) hab
      linarith
    · rw [hlo a ha', hhi b hb'] at hab
      have hmem : γ₁ (2 * a) ∈ γ₁ '' Icc 0 1 ∩ γ₂ '' Icc 0 1 :=
        ⟨⟨2 * a, m1 ⟨ha.1, ha'⟩, rfl⟩, ⟨2 * b - 1, m2 ⟨hb'.le, hb.2⟩, hab.symm⟩⟩
      rw [h] at hmem
      have e1 : γ₁ (2 * a) = γ₁ 1 := by rw [h11]; exact hmem
      have e2 : γ₂ (2 * b - 1) = γ₂ 0 := by rw [h20, ← hab]; exact hmem
      have := hi₁ (m1 ⟨ha.1, ha'⟩) ⟨zero_le_one, le_rfl⟩ e1
      have := hi₂ (m2 ⟨hb'.le, hb.2⟩) ⟨le_rfl, zero_le_one⟩ e2
      linarith
    · rw [hhi a ha', hlo b hb'] at hab
      have hmem : γ₂ (2 * a - 1) ∈ γ₁ '' Icc 0 1 ∩ γ₂ '' Icc 0 1 :=
        ⟨⟨2 * b, m1 ⟨hb.1, hb'⟩, hab.symm⟩, ⟨2 * a - 1, m2 ⟨ha'.le, ha.2⟩, rfl⟩⟩
      rw [h] at hmem
      have e1 : γ₁ (2 * b) = γ₁ 1 := by rw [h11, ← hab]; exact hmem
      have e2 : γ₂ (2 * a - 1) = γ₂ 0 := by rw [h20]; exact hmem
      have := hi₁ (m1 ⟨hb.1, hb'⟩) ⟨zero_le_one, le_rfl⟩ e1
      have := hi₂ (m2 ⟨ha'.le, ha.2⟩) ⟨le_rfl, zero_le_one⟩ e2
      linarith
    · rw [hhi a ha', hhi b hb'] at hab
      have := hi₂ (m2 ⟨ha'.le, ha.2⟩) (m2 ⟨hb'.le, hb.2⟩) hab
      linarith
  · rw [hlo 0 (by norm_num)]; simpa using h10
  · rw [hhi 1 (by norm_num)]; norm_num [h21]
  · ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      rcases le_or_gt l (1 / 2) with h' | h'
      · rw [hlo l h']; exact Or.inl ⟨2 * l, m1 ⟨hl.1, h'⟩, rfl⟩
      · rw [hhi l h']; exact Or.inr ⟨2 * l - 1, m2 ⟨h'.le, hl.2⟩, rfl⟩
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
      · refine ⟨u / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
        rw [hlo _ (by linarith [hu.2])]; congr 1; ring
      · by_cases hu0 : u = 0
        · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
          rw [hlo _ le_rfl]; simp [hu0, h11, h20]
        · refine ⟨(u + 1) / 2, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
          rw [hhi _ (by have := lt_of_le_of_ne hu.1 (Ne.symm hu0); linarith)]
          congr 1; ring

/-- A segment between two different points is an arc. -/
lemma of_segment {p q : ℝ × ℝ} (h : p ≠ q) : IsArc (segment ℝ p q) p q := by
  refine ⟨fun l => p + l • (q - p), by fun_prop, ?_, by simp, by simp, ?_⟩
  · intro a _ b _ hab
    have : a • (q - p) = b • (q - p) := by simpa using hab
    exact smul_left_injective ℝ (sub_ne_zero.2 h.symm) this
  · rw [segment_eq_image']

/-- A simple chain with at least two points is an arc. -/
lemma chain : ∀ {l : List (ℝ × ℝ)} {p q : ℝ × ℝ}, IsSimpleChain l → l.head? = some p →
    l.getLast? = some q → 2 ≤ l.length → IsArc (chainSet l) p q
  | [], _, _, _, _, _, h => by simp at h
  | [_], _, _, _, _, _, h => by simp at h
  | [a, b], p, q, hs, h1, h2, _ => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at h2
    subst h1; subst h2
    rw [chainSet_pair]
    exact IsArc.of_segment hs.1
  | a :: b :: c :: r, p, q, hs, h1, h2, _ => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have h2' : (b :: c :: r).getLast? = some q := by simpa [List.getLast?_cons_cons] using h2
    have ih := IsArc.chain hs.2.2 rfl h2' (by simp)
    have hseg := IsArc.of_segment hs.1
    have : chainSet (a :: b :: c :: r) = segment ℝ a b ∪ chainSet (b :: c :: r) := rfl
    rw [this]
    exact IsArc.glue hseg ih hs.2.1

end IsArc


/-- A chain ending at `y` can be extended by a segment to `z`. -/
lemma exists_extend {l : List (ℝ × ℝ)} {x y : ℝ × ℝ} (h1 : l.head? = some x)
    (h2 : l.getLast? = some y) (z : ℝ × ℝ) :
    ∃ l', l'.head? = some x ∧ l'.getLast? = some z ∧ chainSet l' = chainSet l ∪ segment ℝ y z := by
  obtain ⟨m, hm⟩ : ∃ m, l = m ++ [y] := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, hL⟩
    · simp at h1
    · rw [hL, List.concat_eq_append, List.getLast?_concat, Option.some.injEq] at h2
      subst h2
      exact ⟨L, by rw [hL, List.concat_eq_append]⟩
  subst hm
  refine ⟨m ++ [y, z], ?_, by simp, ?_⟩
  · rcases m with _ | ⟨a, m'⟩
    · simpa using h1
    · simpa using h1
  · have := chainSet_append m y [z]
    rw [chainSet_pair] at this
    simpa using this

/-- **Polygonal connectedness.** Two points of a connected open set of the plane are joined by a
chain in the set (Klazar, Proposition 1.18). -/
theorem exists_chain_in_open {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hc : IsPreconnected U) {x y : ℝ × ℝ}
    (hx : x ∈ U) (hy : y ∈ U) :
    ∃ l : List (ℝ × ℝ), l.head? = some x ∧ l.getLast? = some y ∧ chainSet l ⊆ U := by
  set R : Set (ℝ × ℝ) := {y | ∃ l : List (ℝ × ℝ), l.head? = some x ∧ l.getLast? = some y ∧
    chainSet l ⊆ U} with hR
  have hRU : R ⊆ U := fun y ⟨l, h1, h2, h3⟩ => by
    obtain ⟨m, hm⟩ : ∃ m, l = m ++ [y] := by
      rcases List.eq_nil_or_concat l with rfl | ⟨L, b, hL⟩
      · simp at h1
      · rw [hL, List.concat_eq_append, List.getLast?_concat, Option.some.injEq] at h2
        subst h2
        exact ⟨L, by rw [hL, List.concat_eq_append]⟩
    subst hm
    exact h3 (mem_chainSet_last m y)
  have hxR : x ∈ R := ⟨[x], rfl, rfl, by simpa [chainSet] using hx⟩
  have hRo : IsOpen R := by
    rw [Metric.isOpen_iff]
    intro y hyR
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU y (hRU hyR)
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    obtain ⟨l, h1, h2, h3⟩ := hyR
    obtain ⟨l', e1, e2, e3⟩ := exists_extend h1 h2 z
    refine ⟨l', e1, e2, ?_⟩
    rw [e3]
    refine union_subset h3 ?_
    exact ((convex_ball y ρ).segment_subset (Metric.mem_ball_self hρ) hz).trans hball
  have hVo : IsOpen (U \ R) := by
    rw [Metric.isOpen_iff]
    intro y hyV
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU y hyV.1
    refine ⟨ρ, hρ, fun z hz => ⟨hball hz, fun hzR => hyV.2 ?_⟩⟩
    obtain ⟨l, h1, h2, h3⟩ := hzR
    obtain ⟨l', e1, e2, e3⟩ := exists_extend h1 h2 y
    refine ⟨l', e1, e2, ?_⟩
    rw [e3]
    refine union_subset h3 ?_
    have hzb : z ∈ Metric.ball y ρ := hz
    rw [segment_symm]
    exact ((convex_ball y ρ).segment_subset (Metric.mem_ball_self hρ) hzb).trans hball
  have hUR : U ⊆ R := by
    refine hc.subset_left_of_subset_union hRo hVo ?_ ?_ ⟨x, hx, hxR⟩
    · exact disjoint_sdiff_right
    · intro z hz
      by_cases hzR : z ∈ R
      · exact Or.inl hzR
      · exact Or.inr ⟨hz, hzR⟩
  exact hUR hy

end Lightlike.PL