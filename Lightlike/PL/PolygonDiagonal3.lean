import Lightlike.PL.PolygonDiagonal2

/-!
# Points of the line through the two neighbours of the corner

Two points `x`, `y` on the line `λ + μ = 1` through `u` and `w`, with `λ` taking the value `0`
and `1` between them, have the points `w` and `u` on the segment between them.
-/

open Set

namespace Lightlike.PL

variable {v u w x y : ℝ × ℝ}

/-- On the line `λ + μ = 1`, the point of the segment `[x, y]` with prescribed `λ` between those
of `x` and `y`. -/
lemma exists_point_on_line (hx : wl v u w x + wm v u w x = 1) (hy : wl v u w y + wm v u w y = 1)
    {τ : ℝ} (hxy : wl v u w x < wl v u w y) (h1 : wl v u w x ≤ τ) (h2 : τ ≤ wl v u w y) :
    ∃ P ∈ segment ℝ x y, wl v u w P = τ ∧ wm v u w P = 1 - τ := by
  set r := (τ - wl v u w x) / (wl v u w y - wl v u w x) with hr
  have hd : 0 < wl v u w y - wl v u w x := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hd.le
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hd]; linarith
  refine ⟨(1 - r) • x + r • y, ⟨1 - r, r, by linarith, hr0, by ring, rfl⟩, ?_, ?_⟩
  · rw [Polygon.wl_aff (by ring)]
    rw [hr]; field_simp; ring
  · rw [Polygon.wm_aff (by ring)]
    have e1 : wm v u w x = 1 - wl v u w x := by linarith
    have e2 : wm v u w y = 1 - wl v u w y := by linarith
    rw [e1, e2, hr]; field_simp; ring

/-- **The corners lie on a segment through the diagonal.** If `[x, y]` lies on the line through
`u` and `w`, contains a point strictly between them, and neither end is strictly between them,
then `u` and `w` are on `[x, y]`. -/
lemma corners_mem_segment (hcr : cross (u - v) (w - v) ≠ 0)
    (hx : wl v u w x + wm v u w x = 1) (hy : wl v u w y + wm v u w y = 1)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1)
    (hq0 : 0 < wl v u w (s • x + t • y)) (hq1 : wl v u w (s • x + t • y) < 1)
    (hxl : wl v u w x ≤ 0 ∨ 1 ≤ wl v u w x) (hyl : wl v u w y ≤ 0 ∨ 1 ≤ wl v u w y) :
    u ∈ segment ℝ x y ∧ w ∈ segment ℝ x y := by
  have hq : wl v u w (s • x + t • y) = s * wl v u w x + t * wl v u w y := Polygon.wl_aff hst
  have hPw : ∀ P : ℝ × ℝ, wl v u w P = 0 → wm v u w P = 1 → P = w := by
    intro P h0 h1
    have h' : P - v = w - v := by rw [sub_eq_wl_wm hcr P, h0, h1]; simp
    exact sub_left_injective h'
  have hPu : ∀ P : ℝ × ℝ, wl v u w P = 1 → wm v u w P = 0 → P = u := by
    intro P h0 h1
    have h' : P - v = u - v := by rw [sub_eq_wl_wm hcr P, h0, h1]; simp
    exact sub_left_injective h'
  have key : ∀ x y : ℝ × ℝ, wl v u w x + wm v u w x = 1 → wl v u w y + wm v u w y = 1 →
      wl v u w x ≤ 0 → 1 ≤ wl v u w y → u ∈ segment ℝ x y ∧ w ∈ segment ℝ x y := by
    intro x y hx hy h1 h2
    have hxy : wl v u w x < wl v u w y := by linarith
    obtain ⟨P, hP, hP0, hP1⟩ := exists_point_on_line hx hy hxy h1 (by linarith : (0 : ℝ) ≤ wl v u w y)
    obtain ⟨Q, hQ, hQ0, hQ1⟩ := exists_point_on_line hx hy hxy (by linarith : wl v u w x ≤ 1) h2
    refine ⟨?_, ?_⟩
    · have : Q = u := hPu Q hQ0 (by rw [hQ1]; ring)
      rw [← this]; exact hQ
    · have : P = w := hPw P hP0 (by rw [hP1]; ring)
      rw [← this]; exact hP
  rcases hxl with h1 | h1 <;> rcases hyl with h2 | h2
  · exfalso; nlinarith
  · exact key x y hx hy h1 h2
  · have := key y x hy hx h2 h1
    rw [segment_symm]; exact this
  · exfalso; nlinarith


/-- The coordinates of `v + α (u - v) + β (w - v)` are `α` and `β`. -/
lemma wl_wm_comb (hcr : cross (u - v) (w - v) ≠ 0) (α β : ℝ) :
    wl v u w (v + (α • (u - v) + β • (w - v))) = α ∧
      wm v u w (v + (α • (u - v) + β • (w - v))) = β := by
  constructor
  · unfold wl
    rw [div_eq_iff hcr]
    unfold cross
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  · unfold wm
    rw [div_eq_iff hcr]
    unfold cross
    simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring

namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- **The diagonal from the two neighbours of the extreme vertex.** If no vertex other than `u`,
`v`, `w` lies in the closed triangle `u v w`, then the open segment from `u` to `w` lies in the
inside of the polygon. -/
theorem exists_uw_diagonal [NeZero n] (hs : p.IsSimple) (hn : 4 ≤ n) {j : Fin n}
    (hext : ∀ i, LexLE (p j) (p i))
    (hno : ∀ i, i ≠ (finRotate n).symm j → i ≠ j → i ≠ finRotate n j →
      ¬ (0 ≤ wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ∧
        0 ≤ wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ∧
        wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) +
          wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ≤ 1)) :
    openSegment ℝ (p ((finRotate n).symm j)) (p (finRotate n j)) ⊆ p.inside := by
  set k := (finRotate n).symm j with hk
  have hkj : finRotate n k = j := by rw [hk]; exact Equiv.apply_symm_apply _ _
  set v := p j with hv
  set u := p k with hu
  set w := p (finRotate n j) with hw
  have hcr : cross (u - v) (w - v) ≠ 0 := corner_cross_ne hs hext
  have hvw : v ≠ w := hs.1 j
  have hedgek : p.edge k = segment ℝ v u := by
    simp only [edge, hkj, hu, hv]; exact segment_symm ℝ _ _
  have hvert : ∀ i, ¬ (0 < wl v u w (p i) ∧ 0 < wm v u w (p i) ∧
      wl v u w (p i) + wm v u w (p i) < 1) := by
    rintro i ⟨ha, hb, hd⟩
    have hik : i ≠ k := by rintro rfl; rw [← hu, wm_u] at hb; exact lt_irrefl _ hb
    have hij : i ≠ j := by rintro rfl; rw [← hv, wl_self] at ha; exact lt_irrefl _ ha
    have him : i ≠ finRotate n j := by rintro rfl; rw [← hw, wl_w] at ha; exact lt_irrefl _ ha
    exact hno i hik hij him ⟨ha.le, hb.le, hd.le⟩
  -- no vertex lies on the open diagonal
  have hnov : ∀ i, p i ∈ openSegment ℝ u w → False := by
    rintro i ⟨a, b, ha, hb, hab, hi⟩
    have e1 : wl v u w (p i) = a := by
      rw [← hi, Polygon.wl_aff hab, wl_u hcr, wl_w]; ring
    have e2 : wm v u w (p i) = b := by
      rw [← hi, Polygon.wm_aff hab, wm_u, wm_w hcr]; ring
    have hik : i ≠ k := by rintro rfl; rw [← hu, wm_u] at e2; linarith
    have hij : i ≠ j := by rintro rfl; rw [← hv, wl_self] at e1; linarith
    have him : i ≠ finRotate n j := by rintro rfl; rw [← hw, wl_w] at e1; linarith
    exact hno i hik hij him ⟨by linarith, by linarith, by linarith⟩
  set f := wf v u w 1 with hf
  have hfa := wf_affine v u w 1
  have hlam : ∀ i, 1 - wl v u w (p i) - wm v u w (p i) = 0 →
      wl v u w (p i) ≤ 0 ∨ 1 ≤ wl v u w (p i) := by
    intro i hi
    by_cases hik : i = k
    · subst hik; rw [← hu, wl_u hcr]; right; exact le_rfl
    by_cases hij : i = j
    · subst hij; rw [← hv, wl_self, wm_self] at hi; norm_num at hi
    by_cases him : i = finRotate n j
    · subst him; rw [← hw, wl_w]; left; exact le_rfl
    have := hno i hik hij him
    by_contra hcon
    apply this
    push Not at hcon
    refine ⟨hcon.1.le, ?_, by linarith⟩
    linarith [hcon.2]
  have hD : ∀ q : ℝ × ℝ, 0 < wl v u w q → 0 < wm v u w q → wl v u w q + wm v u w q = 1 →
      q ∉ p.carrier := by
    intro q hq1 hq2 hq3 hqc
    obtain ⟨e, he⟩ := Set.mem_iUnion.1 hqc
    set x := p e with hx
    set y := p (finRotate n e) with hy
    have heS : q ∈ segment ℝ x y := he
    obtain ⟨s, t, hs0, ht0, hst, hqst⟩ := heS
    have heS' : q ∈ segment ℝ x y := ⟨s, t, hs0, ht0, hst, hqst⟩
    have hqv : ∀ i, p i = q → False := by
      intro i hi
      exact hnov i (by
        have hq' : q ∈ openSegment ℝ u w := by
          refine ⟨wl v u w q, wm v u w q, hq1, hq2, hq3, ?_⟩
          have := sub_eq_wl_wm hcr q
          have hm : wm v u w q = 1 - wl v u w q := by linarith
          have c1 := congrArg Prod.fst this
          have c2 := congrArg Prod.snd this
          simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
            Prod.smul_snd, smul_eq_mul] at c1 c2
          rw [hm] at c1 c2 ⊢
          ext
          · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
            linear_combination (-1) * c1
          · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
            linear_combination (-1) * c2
        rw [hi]; exact hq')
    have hs1 : 0 < s := by
      rcases hs0.eq_or_lt with h | h
      · exfalso
        have ht1 : t = 1 := by linarith
        rw [← h, ht1] at hqst
        exact hqv _ (by simpa using hqst)
      · exact h
    have ht1 : 0 < t := by
      rcases ht0.eq_or_lt with h | h
      · exfalso
        have hs1' : s = 1 := by linarith
        rw [← h, hs1'] at hqst
        exact hqv _ (by simpa using hqst)
      · exact h
    -- values of the three functions at `q` and at the ends of the edge
    have hqf : ∀ i, 0 ≤ f i q := by
      intro i
      rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
      · exact hq1.le
      · exact hq2.le
      · rw [hf, wf_two]; linarith
    have hqa : ∀ i, f i q = s * f i x + t * f i y := by
      intro i; rw [← hqst]; exact hfa i x y s t hst
    have hseg1 : ∀ z ∈ segment ℝ q x, z ∈ p.edge e := fun z hz =>
      (convex_segment x y).segment_subset heS' (left_mem_segment ℝ x y) hz
    have hseg2 : ∀ z ∈ segment ℝ q y, z ∈ p.edge e := fun z hz =>
      (convex_segment x y).segment_subset heS' (right_mem_segment ℝ x y) hz
    have hwed : ∀ z, (∀ i, 0 < f i z) → z ∈ p.edge e → False := by
      intro z hz hze
      have h0 : 0 < wl v u w z := by simpa [hf, wf_zero] using hz 0
      have h1 : 0 < wm v u w z := by simpa [hf, wf_one] using hz 1
      have h2 : 0 < 1 - wl v u w z - wm v u w z := by simpa [hf, wf_two] using hz 2
      exact wedge_disjoint_carrier hs hn hcr le_rfl hvert h0 h1 (by linarith)
        (Set.mem_iUnion.2 ⟨e, hze⟩)
    have hf2 : ∀ z, f 2 z = 1 - wl v u w z - wm v u w z := fun z => by rw [hf, wf_two]
    by_cases hg : 0 < f 2 x
    · obtain ⟨z, hz, hzp⟩ := exists_interior_point hfa hqf (x := x) (q := q) (fun i hi => by
        rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
        · exfalso; have : f 0 q = wl v u w q := by rw [hf, wf_zero]
          linarith
        · exfalso; have : f 1 q = wm v u w q := by rw [hf, wf_one]
          linarith
        · exact hg)
      exact hwed z hzp (hseg1 z hz)
    by_cases hg' : 0 < f 2 y
    · obtain ⟨z, hz, hzp⟩ := exists_interior_point hfa hqf (x := y) (q := q) (fun i hi => by
        rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
        · exfalso; have : f 0 q = wl v u w q := by rw [hf, wf_zero]
          linarith
        · exfalso; have : f 1 q = wm v u w q := by rw [hf, wf_one]
          linarith
        · exact hg')
      exact hwed z hzp (hseg2 z hz)
    -- the edge lies on the line through `u` and `w`
    have hq2z : f 2 q = 0 := by rw [hf2]; linarith
    have hx2 : f 2 x = 0 := by
      have := hqa 2
      nlinarith [not_lt.1 hg, not_lt.1 hg']
    have hy2 : f 2 y = 0 := by
      have := hqa 2
      nlinarith [not_lt.1 hg, not_lt.1 hg']
    rw [hf2] at hx2 hy2
    have hxl := hlam e (by simpa [hx] using hx2)
    have hyl := hlam (finRotate n e) (by simpa [hy] using hy2)
    have hlq : wl v u w q = wl v u w (s • x + t • y) := by rw [hqst]
    obtain ⟨hue, hwe⟩ := corners_mem_segment hcr (x := x) (y := y)
      (by linarith) (by linarith) hs1 ht1 hst (by rw [← hlq]; exact hq1)
      (by rw [← hlq]; linarith) hxl hyl
    have hej : e ≠ j := by
      intro h
      rw [h] at he
      have : q ∈ segment ℝ v w := he
      have := wl_of_mem_segment (u := u) this
      linarith
    have hek : e ≠ k := by
      intro h
      rw [h, hedgek] at he
      have := wm_of_mem_segment (w := w) he
      linarith
    have hwj : w ∈ p.edge j := right_mem_segment ℝ _ _
    have huk : u ∈ p.edge k := by rw [hedgek]; exact right_mem_segment ℝ _ _
    have hwe' : w ∈ p.edge e := hwe
    have hue' : u ∈ p.edge e := hue
    have hem : finRotate n j = e := by
      rcases edge_meet_cases hs hej hwe' hwj with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact absurd h2.symm hvw
      · exact h1
    rcases edge_meet_cases hs hek hue' huk with ⟨h1, -⟩ | ⟨h1, -⟩
    · have : finRotate n (finRotate n (finRotate n j)) = j := by rw [hem, h1, hkj]
      exact finRotate_three_ne hn j this
    · exact hej (by rw [← h1, hkj])
  -- the open triangle together with the open diagonal
  set S : Set (ℝ × ℝ) := {z | 0 < wl v u w z ∧ 0 < wm v u w z ∧ wl v u w z + wm v u w z ≤ 1}
    with hS
  have hSc : S ⊆ p.carrierᶜ := by
    rintro z ⟨h0, h1, h2⟩
    rcases h2.lt_or_eq with h2 | h2
    · exact wedge_disjoint_carrier hs hn hcr le_rfl hvert h0 h1 h2
    · exact hD z h0 h1 h2
  have hSconv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx0, hx1, hx2⟩ := hx
    obtain ⟨hy0, hy1, hy2⟩ := hy
    have e1 := Polygon.wl_aff (v := v) (u := u) (w := w) (x := x) (y := y) hab
    have e2 := Polygon.wm_aff (v := v) (u := u) (w := w) (x := x) (y := y) hab
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]
      rcases ha.eq_or_lt with h | h
      · rw [← h] at hab ⊢; have : b = 1 := by linarith
        subst this; simpa using hy0
      · nlinarith [mul_pos h hx0, mul_nonneg hb hy0.le]
    · rw [e2]
      rcases ha.eq_or_lt with h | h
      · rw [← h] at hab ⊢; have : b = 1 := by linarith
        subst this; simpa using hy1
      · nlinarith [mul_pos h hx1, mul_nonneg hb hy1.le]
    · rw [e1, e2]
      nlinarith [mul_nonneg ha (sub_nonneg.2 hx2), mul_nonneg hb (sub_nonneg.2 hy2)]
  have hdiag : openSegment ℝ u w ⊆ S := by
    rintro q ⟨a, b, ha, hb, hab, rfl⟩
    have e1 : wl v u w (a • u + b • w) = a := by
      rw [Polygon.wl_aff hab, wl_u hcr, wl_w]; ring
    have e2 : wm v u w (a • u + b • w) = b := by
      rw [Polygon.wm_aff hab, wm_u, wm_w hcr]; ring
    exact ⟨by rw [e1]; exact ha, by rw [e2]; exact hb, by rw [e1, e2]; linarith⟩
  obtain ⟨ρ, hρ, hcone⟩ := inside_near_corner hs hext
  have hpre : IsPreconnected S := hSconv.isPreconnected
  rcases subset_outside_or_inside hpre hSc with h | h
  · exfalso
    set N := ‖(u - v) + (w - v)‖ with hN
    have hN0 : 0 ≤ N := norm_nonneg _
    have hden : 0 < 2 * (N + 1) := by positivity
    set t := min (1 / 4 : ℝ) (ρ / (2 * (N + 1))) with ht
    have ht0 : 0 < t := lt_min (by norm_num) (div_pos hρ hden)
    have ht1 : t ≤ 1 / 4 := min_le_left _ _
    have ht2 : t ≤ ρ / (2 * (N + 1)) := min_le_right _ _
    set z0 := v + (t • (u - v) + t • (w - v)) with hz0
    have hz0S : z0 ∈ S := by
      obtain ⟨c1, c2⟩ := wl_wm_comb hcr t t
      exact ⟨by rw [hz0, c1]; exact ht0, by rw [hz0, c2]; exact ht0, by rw [hz0, c1, c2]; linarith⟩
    have hball : z0 ∈ Metric.ball v ρ := by
      rw [Metric.mem_ball, dist_eq_norm, hz0, add_sub_cancel_left, ← smul_add, norm_smul,
        Real.norm_of_nonneg ht0.le]
      have h1 : t * (2 * (N + 1)) ≤ ρ := by
        have := mul_le_mul_of_nonneg_right ht2 hden.le
        rwa [div_mul_cancel₀ _ hden.ne'] at this
      nlinarith
    have hin : z0 ∈ p.inside := hcone z0 hball ⟨t, t, ht0, ht0, by rw [hz0, add_sub_cancel_left]⟩
    exact (Set.disjoint_left.1 (disjoint_outside_inside p)) (h hz0S) hin
  · exact fun q hq => h (hdiag hq)

/-- **A simple polygon with at least four vertices has an interior diagonal.** Two vertices that
are not neighbours, whose open segment lies in the inside. -/
theorem exists_diagonal [NeZero n] (hs : p.IsSimple) (hn : 4 ≤ n) :
    ∃ a b : Fin n, a ≠ b ∧ finRotate n a ≠ b ∧ finRotate n b ≠ a ∧
      openSegment ℝ (p a) (p b) ⊆ p.inside := by
  obtain ⟨j, hext⟩ := exists_extreme p
  set k := (finRotate n).symm j with hk
  have hkj : finRotate n k = j := by rw [hk]; exact Equiv.apply_symm_apply _ _
  by_cases hz : ∃ i, i ≠ k ∧ i ≠ j ∧ i ≠ finRotate n j ∧
      0 ≤ wl (p j) (p k) (p (finRotate n j)) (p i) ∧ 0 ≤ wm (p j) (p k) (p (finRotate n j)) (p i) ∧
      wl (p j) (p k) (p (finRotate n j)) (p i) + wm (p j) (p k) (p (finRotate n j)) (p i) ≤ 1
  · obtain ⟨i, hij, hik, him, hsub⟩ := exists_vz_diagonal hs hn hext hz
    refine ⟨j, i, hij.symm, fun h => him h.symm, fun h => ?_, hsub⟩
    exact hik ((finRotate n).injective (h.trans hkj.symm))
  · have hno : ∀ i, i ≠ k → i ≠ j → i ≠ finRotate n j →
        ¬ (0 ≤ wl (p j) (p k) (p (finRotate n j)) (p i) ∧
          0 ≤ wm (p j) (p k) (p (finRotate n j)) (p i) ∧
          wl (p j) (p k) (p (finRotate n j)) (p i) + wm (p j) (p k) (p (finRotate n j)) (p i) ≤ 1) :=
      fun i h1 h2 h3 h => hz ⟨i, h1, h2, h3, h.1, h.2.1, h.2.2⟩
    have hsub := exists_uw_diagonal hs hn hext hno
    refine ⟨k, finRotate n j, ?_, ?_, ?_, hsub⟩
    · intro h
      have := congrArg (finRotate n) h
      rw [hkj] at this
      exact finRotate_two_ne (by omega) j this.symm
    · rw [hkj]; exact (finRotate_one_ne (by omega) j).symm
    · intro h
      have : finRotate n (finRotate n (finRotate n j)) = j := by rw [h, hkj]
      exact finRotate_three_ne hn j this

end Polygon

end Lightlike.PL
