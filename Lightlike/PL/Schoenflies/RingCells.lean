import Mathlib
import Lightlike.PL.Schoenflies.QuadBoundary
import Lightlike.PL.Schoenflies.SegmentAffine

/-!
# Extending a boundary map over a ring cell cut into cells by spokes

Row G3-188 (PL5), ring cells.  `quad_region_rot`: the polygon of the cell `α ++ β.reverse` split at the vertices `x` of `α`, `y` of `β`
has the same region as the rotated list used by `quad_split_region`.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

lemma quad_region_rot (pa qa pb qb : List (ℝ × ℝ)) (x y : ℝ × ℝ) :
    region (Polygon.ofList (quadList (pa ++ x :: qa) (pb ++ y :: qb))) =
      region (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa))) := by
  have e1 : quadList (pa ++ x :: qa) (pb ++ y :: qb) = pa ++ (x :: (qa ++ qb.reverse) ++ y :: pb.reverse) := by
    simp [quadList]
  have e2 : x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa) = (x :: (qa ++ qb.reverse) ++ y :: pb.reverse) ++ pa := by
    simp
  have i1 : NeZero (quadList (pa ++ x :: qa) (pb ++ y :: qb)).length := ⟨by simp [quadList]⟩
  have i2 : NeZero (pa ++ (x :: (qa ++ qb.reverse) ++ y :: pb.reverse)).length := ⟨by simp⟩
  have i3 : NeZero ((x :: (qa ++ qb.reverse) ++ y :: pb.reverse) ++ pa).length := ⟨by simp⟩
  have i4 : NeZero (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa)).length := ⟨by simp⟩
  rw [region_ofList_congr e1, ← region_ofList_rotate pa (x :: (qa ++ qb.reverse) ++ y :: pb.reverse)]
  exact region_ofList_congr (by simp)

/-- **A source cell and a target cell cut by `n` spokes, with matching cut data.** Each cut removes the first cell
`(pa ++ [x], pb ++ [y])`; the maps `fa`, `fb` of the arcs match the pieces and the cut points. -/
def PairCut : ℕ → (w w' v v' w₂ w₂' v₂ v₂' : ℝ × ℝ) → (α β α₂ β₂ : List (ℝ × ℝ)) →
    (ℝ × ℝ → ℝ × ℝ) → (ℝ × ℝ → ℝ × ℝ) → Prop
  | 0, w, w', v, v', w₂, w₂', v₂, v₂', α, β, α₂, β₂, _, _ =>
      GoodQuad w w' v v' α β ∧ GoodQuad w₂ w₂' v₂ v₂' α₂ β₂
  | n + 1, w, w', v, v', w₂, w₂', v₂, v₂', α, β, α₂, β₂, fa, fb =>
      ∃ (pa qa pb qb pa₂ qa₂ pb₂ qb₂ : List (ℝ × ℝ)) (x y x₂ y₂ : ℝ × ℝ),
        α = pa ++ x :: qa ∧ β = pb ++ y :: qb ∧ α₂ = pa₂ ++ x₂ :: qa₂ ∧ β₂ = pb₂ ++ y₂ :: qb₂ ∧
        GoodQuad w w' v v' α β ∧ GoodQuad w₂ w₂' v₂ v₂' α₂ β₂ ∧ x ≠ y ∧ x₂ ≠ y₂ ∧
        segment ℝ x y ∩ chainSet α = {x} ∧ segment ℝ x y ∩ chainSet β = {y} ∧
        Disjoint (segment ℝ x y) (segment ℝ w v) ∧ Disjoint (segment ℝ x y) (segment ℝ w' v') ∧
        segment ℝ x y \ {x, y} ⊆ (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa))).inside ∧
        segment ℝ x₂ y₂ ∩ chainSet α₂ = {x₂} ∧ segment ℝ x₂ y₂ ∩ chainSet β₂ = {y₂} ∧
        Disjoint (segment ℝ x₂ y₂) (segment ℝ w₂ v₂) ∧ Disjoint (segment ℝ x₂ y₂) (segment ℝ w₂' v₂') ∧
        segment ℝ x₂ y₂ \ {x₂, y₂} ⊆
          (Polygon.ofList (x₂ :: (qa₂ ++ qb₂.reverse) ++ y₂ :: (pb₂.reverse ++ pa₂))).inside ∧
        BijOn fa (chainSet (pa ++ [x])) (chainSet (pa₂ ++ [x₂])) ∧
        BijOn fa (chainSet (x :: qa)) (chainSet (x₂ :: qa₂)) ∧
        BijOn fb (chainSet (pb ++ [y])) (chainSet (pb₂ ++ [y₂])) ∧
        BijOn fb (chainSet (y :: qb)) (chainSet (y₂ :: qb₂)) ∧
        fa x = x₂ ∧ fb y = y₂ ∧
        PairCut n x w' y v' x₂ w₂' y₂ v₂' (x :: qa) (y :: qb) (x₂ :: qa₂) (y₂ :: qb₂) fa fb

lemma GoodQuad.neZero_quadList {w w' v v' : ℝ × ℝ} {α β : List (ℝ × ℝ)} (h : GoodQuad w w' v v' α β) :
    NeZero (quadList α β).length := by
  refine ⟨?_⟩
  have hα : α ≠ [] := by intro e; have := h.headα; rw [e] at this; simp at this
  have : 0 < α.length := List.length_pos_iff.2 hα
  simp only [quadList, List.length_append]
  omega

lemma GoodQuad.sides_subset_region {w w' v v' : ℝ × ℝ} {α β : List (ℝ × ℝ)} (h : GoodQuad w w' v v' α β)
    [NeZero (quadList α β).length] :
    chainSet α ⊆ region (Polygon.ofList (quadList α β)) ∧ chainSet β ⊆ region (Polygon.ofList (quadList α β)) ∧
    segment ℝ w v ⊆ region (Polygon.ofList (quadList α β)) ∧
    segment ℝ w' v' ⊆ region (Polygon.ofList (quadList α β)) := by
  have hc := h.polygon.2.2
  refine ⟨fun z hz => carrier_subset_region _ (hc ▸ Or.inl (Or.inl (Or.inl hz))),
    fun z hz => carrier_subset_region _ (hc ▸ Or.inl (Or.inr hz)),
    fun z hz => carrier_subset_region _ (hc ▸ Or.inr hz),
    fun z hz => carrier_subset_region _ (hc ▸ Or.inl (Or.inl (Or.inr hz)))⟩

theorem ring_extend : ∀ (n : ℕ) {w w' v v' w₂ w₂' v₂ v₂' : ℝ × ℝ} {α β α₂ β₂ : List (ℝ × ℝ)}
    {fa fb fs fs' : ℝ × ℝ → ℝ × ℝ},
    PairCut n w w' v v' w₂ w₂' v₂ v₂' α β α₂ β₂ fa fb →
    BijOn fa (chainSet α) (chainSet α₂) → BijOn fb (chainSet β) (chainSet β₂) →
    BijOn fs (segment ℝ w v) (segment ℝ w₂ v₂) → BijOn fs' (segment ℝ w' v') (segment ℝ w₂' v₂') →
    ContinuousOn fa (chainSet α) → ContinuousOn fb (chainSet β) →
    ContinuousOn fs (segment ℝ w v) → ContinuousOn fs' (segment ℝ w' v') →
    fa w = w₂ → fa w' = w₂' → fb v = v₂ → fb v' = v₂' →
    fs w = w₂ → fs v = v₂ → fs' w' = w₂' → fs' v' = v₂' →
    ∃ E : region (Polygon.ofList (quadList α β)) ≃ₜ region (Polygon.ofList (quadList α₂ β₂)),
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ chainSet α → (E ⟨x, hx⟩ : ℝ × ℝ) = fa x) ∧
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ chainSet β → (E ⟨x, hx⟩ : ℝ × ℝ) = fb x) ∧
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ segment ℝ w v → (E ⟨x, hx⟩ : ℝ × ℝ) = fs x) ∧
      (∀ x (hx : x ∈ region (Polygon.ofList (quadList α β))), x ∈ segment ℝ w' v' →
        (E ⟨x, hx⟩ : ℝ × ℝ) = fs' x)
  | 0, w, w', v, v', w₂, w₂', v₂, v₂', α, β, α₂, β₂, fa, fb, fs, fs', h, ha, hb, hs, hs', hca, hcb, hcs, hcs',
      haw, haw', hbv, hbv', hsw, hsv, hsw', hsv' => by
    obtain ⟨hQ, hQ₂⟩ := h
    haveI := hQ.neZero_quadList
    haveI := hQ₂.neZero_quadList
    exact GoodQuad.extend' hQ hQ₂ ha hb hs hs' hca hcb hcs hcs' haw haw' hbv hbv' hsw hsv hsw' hsv'
  | n + 1, w, w', v, v', w₂, w₂', v₂, v₂', α, β, α₂, β₂, fa, fb, fs, fs', h, ha, hb, hs, hs', hca, hcb, hcs, hcs',
      haw, haw', hbv, hbv', hsw, hsv, hsw', hsv' => by
    obtain ⟨pa, qa, pb, qb, pa₂, qa₂, pb₂, qb₂, x, y, x₂, y₂, rfl, rfl, rfl, rfl, hQ, hQ₂, hxy, hxy₂,
      hs1, hs2, hs3, hs4, hD, hs1₂, hs2₂, hs3₂, hs4₂, hD₂, hbaL, hbaR, hbbL, hbbR, hfax, hfby, hrest⟩ := h
    obtain ⟨L, R⟩ := hQ.split hs1 hs2 hs3 hs4
    obtain ⟨L₂, R₂⟩ := hQ₂.split hs1₂ hs2₂ hs3₂ hs4₂
    obtain ⟨h₁, h₂, h₁₂, h₁ₑ, h₂ₑ⟩ := hQ.split_hyps hs1 hs2 hs3 hs4 hxy
    obtain ⟨h₁', h₂', h₁₂', h₁ₑ', h₂ₑ'⟩ := hQ₂.split_hyps hs1₂ hs2₂ hs3₂ hs4₂ hxy₂
    obtain ⟨hsplit, hint⟩ := quad_split_region hxy h₁ h₂ h₁₂ h₁ₑ h₂ₑ hD
    obtain ⟨hsplit₂, hint₂⟩ := quad_split_region hxy₂ h₁' h₂' h₁₂' h₁ₑ' h₂ₑ' hD₂
    obtain ⟨A, hAc, hAb, hAx, hAy⟩ := exists_segment_affine hxy hxy₂
    have hsubα : chainSet (pa ++ [x]) ⊆ chainSet (pa ++ x :: qa) := by
      intro z hz; rw [chainSet_append pa x qa]; exact Or.inl hz
    have hsubα' : chainSet (x :: qa) ⊆ chainSet (pa ++ x :: qa) := by
      intro z hz; rw [chainSet_append pa x qa]; exact Or.inr hz
    have hsubβ : chainSet (pb ++ [y]) ⊆ chainSet (pb ++ y :: qb) := by
      intro z hz; rw [chainSet_append pb y qb]; exact Or.inl hz
    have hsubβ' : chainSet (y :: qb) ⊆ chainSet (pb ++ y :: qb) := by
      intro z hz; rw [chainSet_append pb y qb]; exact Or.inr hz
    have iR := R.neZero_quadList
    have iR₂ := R₂.neZero_quadList
    have iL := L.neZero_quadList
    have iL₂ := L₂.neZero_quadList
    -- the first cell
    obtain ⟨E₁, hE₁a, hE₁b, hE₁s, hE₁t⟩ := GoodQuad.extend' R R₂ hbaL hbbL hs hAb
      (hca.mono hsubα) (hcb.mono hsubβ) hcs hAc haw hfax hbv hfby hsw hsv hAx hAy
    -- the rest
    obtain ⟨E₂, hE₂a, hE₂b, hE₂s, hE₂t⟩ := ring_extend n hrest hbaR hbbR hAb hs' (hca.mono hsubα') (hcb.mono hsubβ')
      hAc hcs' hfax haw' hfby hbv' hAx hAy hsw' hsv'
    have hseg1 : ∀ z, z ∈ segment ℝ x y → z ∈ region (Polygon.ofList (quadList (x :: qa) (y :: qb))) ∧
        z ∈ region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) := by
      intro z hz
      have : z ∈ region (Polygon.ofList (quadList (x :: qa) (y :: qb))) ∩
          region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) := by rw [hint]; exact hz
      exact this
    obtain ⟨E, hEL, hER⟩ := quad_split_homeo hxy h₁ h₂ h₁₂ h₁ₑ h₂ₑ hD E₂ E₁
      (by
        intro z hz1 hz2
        have hz : z ∈ segment ℝ x y := by
          have : z ∈ region (Polygon.ofList (quadList (x :: qa) (y :: qb))) ∩
              region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y]))) := ⟨hz1, hz2⟩
          rw [hint] at this; exact this
        rw [hE₂s z hz1 hz, hE₁t z hz2 hz])
      (by
        intro u hu1 hu2
        have hu : u ∈ segment ℝ x₂ y₂ := by
          have : u ∈ region (Polygon.ofList (quadList (x₂ :: qa₂) (y₂ :: qb₂))) ∩
              region (Polygon.ofList (quadList (pa₂ ++ [x₂]) (pb₂ ++ [y₂]))) := ⟨hu1, hu2⟩
          rw [hint₂] at this; exact this
        obtain ⟨z, hz, rfl⟩ := hAb.surjOn hu
        exact ⟨z, (hseg1 z hz).1, (hseg1 z hz).2, hE₁t z _ hz⟩)
    obtain ⟨Rα, Rβ, Rσ, Rσ'⟩ := R.sides_subset_region
    obtain ⟨Lα, Lβ, Lσ, Lσ'⟩ := L.sides_subset_region
    let E' : region (Polygon.ofList (quadList (pa ++ x :: qa) (pb ++ y :: qb))) ≃ₜ
        region (Polygon.ofList (quadList (pa₂ ++ x₂ :: qa₂) (pb₂ ++ y₂ :: qb₂))) :=
      (Homeomorph.setCongr (quad_region_rot pa qa pb qb x y)).trans
        (E.trans (Homeomorph.setCongr (hsplit₂.symm.trans (quad_region_rot pa₂ qa₂ pb₂ qb₂ x₂ y₂).symm)))
    have hval : ∀ z (hz : z ∈ region (Polygon.ofList (quadList (pa ++ x :: qa) (pb ++ y :: qb))))
        (hz' : z ∈ region (Polygon.ofList (x :: (qa ++ qb.reverse) ++ y :: (pb.reverse ++ pa)))),
        (E' ⟨z, hz⟩ : ℝ × ℝ) = (E ⟨z, hz'⟩ : ℝ × ℝ) := fun z hz hz' => rfl
    have hL : ∀ z (hz : z ∈ region (Polygon.ofList (quadList (pa ++ x :: qa) (pb ++ y :: qb))))
        (hzL : z ∈ region (Polygon.ofList (quadList (x :: qa) (y :: qb)))),
        (E' ⟨z, hz⟩ : ℝ × ℝ) = (E₂ ⟨z, hzL⟩ : ℝ × ℝ) := fun z hz hzL =>
      (hval z hz ((quad_region_rot pa qa pb qb x y) ▸ hz)).trans (hEL z hzL)
    have hR : ∀ z (hz : z ∈ region (Polygon.ofList (quadList (pa ++ x :: qa) (pb ++ y :: qb))))
        (hzR : z ∈ region (Polygon.ofList (quadList (pa ++ [x]) (pb ++ [y])))),
        (E' ⟨z, hz⟩ : ℝ × ℝ) = (E₁ ⟨z, hzR⟩ : ℝ × ℝ) := fun z hz hzR =>
      (hval z hz ((quad_region_rot pa qa pb qb x y) ▸ hz)).trans (hER z hzR)
    refine ⟨E', ?_, ?_, ?_, ?_⟩
    · intro z hz hza
      rw [chainSet_append pa x qa] at hza
      rcases hza with hza | hza
      · rw [hR z hz (Rα hza), hE₁a z _ hza]
      · rw [hL z hz (Lα hza), hE₂a z _ hza]
    · intro z hz hzb
      rw [chainSet_append pb y qb] at hzb
      rcases hzb with hzb | hzb
      · rw [hR z hz (Rβ hzb), hE₁b z _ hzb]
      · rw [hL z hz (Lβ hzb), hE₂b z _ hzb]
    · intro z hz hzs
      rw [hR z hz (Rσ hzs), hE₁s z _ hzs]
    · intro z hz hzs
      rw [hL z hz (Lσ' hzs), hE₂t z _ hzs]

end Lightlike.PL.Schoenflies
