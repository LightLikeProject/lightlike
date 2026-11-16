import Lightlike.PL.IndexOmega
import Lightlike.PL.ThetaExists

/-!
# The index about a Jordan curve split by a θ configuration

With the point `Ω` above the curve, the vertical ray argument shows the indices of the two arcs about points of the other arc add to a nonzero number, hence every point not joined to `Ω` in the complement has nonzero index about the curve, while the points joined to `Ω` have index zero.

## Main results

* `Theta.sum_ne_zero`: the ray argument
* `Theta.iota_ne_zero`: nonzero index off the component of `Ω`
* `Theta.iota_of_joined`: zero index in the component of `Ω`
* `exists_theta_top`: a θ configuration above any Jordan curve
* `exists_theta_at`: a θ configuration at any point off the curve

## References

* McCleary, *A First Course in Topology: Continuity and Dimension* (2006), `mccleary-2006`, Chapter 9: the chapter location is verified, the lemma-level numbering is not.
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

/-- **The index about a loop is constant on the open arc `γB`**: in the θ configuration, two points of `γB` that are not on
`γA` have the same index about the loop `ω` (the open arc is connected and avoids the loop). -/
theorem index_const_arc {a b P Q Ω z y : ℂ} (γA : Path a b) (γB : Path b a)
    (hB_inj : Function.Injective γB)
    (hends : ({a, b} : Set ℂ) = {P, Q}) (disj : range γA ∩ range γB = {a, b})
    (ω : Path P P)
    (hrange : range ω = range γA ∪ (segment ℝ P Ω ∪ segment ℝ Q Ω))
    (hsegP : segment ℝ P Ω ∩ (range γA ∪ range γB) ⊆ {P})
    (hsegQ : segment ℝ Q Ω ∩ (range γA ∪ range γB) ⊆ {Q})
    (hz : z ∈ range γB) (hzA : z ∉ range γA) (hy : y ∈ range γB) (hyA : y ∉ range γA) :
    loopIndex ω z = loopIndex ω y := by
  have haA : a ∈ range γA := ⟨0, γA.source⟩
  have hbA : b ∈ range γA := ⟨1, γA.target⟩
  have hPab : P ∈ ({a, b} : Set ℂ) := by rw [hends]; simp
  have hQab : Q ∈ ({a, b} : Set ℂ) := by rw [hends]; simp
  have hPA : P ∈ range γA := by rcases hPab with h | h <;> [exact h ▸ haA; exact h ▸ hbA]
  have hQA : Q ∈ range γA := by rcases hQab with h | h <;> [exact h ▸ haA; exact h ▸ hbA]
  -- the points of the open arc `γB` avoid the loop
  let g : ℝ → ℂ := fun r => γB (Set.projIcc (0 : ℝ) 1 zero_le_one r)
  have hgc : Continuous g := γB.continuous.comp (continuous_projIcc (h := zero_le_one))
  have hends_ne : ∀ r ∈ Ioo (0 : ℝ) 1, g r ≠ a ∧ g r ≠ b := by
    intro r hr
    have hmem : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    have hproj : (Set.projIcc (0 : ℝ) 1 zero_le_one r : ℝ) = r := Set.projIcc_of_mem _ hmem ▸ rfl
    constructor
    · intro h
      have h1 : γB (Set.projIcc (0 : ℝ) 1 zero_le_one r) = γB 1 := by rw [γB.target]; exact h
      have := congrArg Subtype.val (hB_inj h1)
      simp [hproj] at this
      linarith [hr.2]
    · intro h
      have h1 : γB (Set.projIcc (0 : ℝ) 1 zero_le_one r) = γB 0 := by rw [γB.source]; exact h
      have := congrArg Subtype.val (hB_inj h1)
      simp [hproj] at this
      linarith [hr.1]
  have havoid : ∀ r ∈ Ioo (0 : ℝ) 1, g r ∉ range ω := by
    intro r hr hmem
    rw [hrange] at hmem
    obtain ⟨h1, h2⟩ := hends_ne r hr
    have hgB : g r ∈ range γB := ⟨_, rfl⟩
    rcases hmem with h | h | h
    · have : g r ∈ ({a, b} : Set ℂ) := disj ▸ ⟨h, hgB⟩
      rcases this with h' | h' <;> [exact h1 h'; exact h2 h']
    · have := hsegP ⟨h, Or.inr hgB⟩
      have hP' : g r ∈ ({a, b} : Set ℂ) := by rw [hends]; left; exact this
      rcases hP' with h' | h' <;> [exact h1 h'; exact h2 h']
    · have := hsegQ ⟨h, Or.inr hgB⟩
      have hQ' : g r ∈ ({a, b} : Set ℂ) := by rw [hends]; right; exact this
      rcases hQ' with h' | h' <;> [exact h1 h'; exact h2 h']
  have hinner : ∀ w ∈ range γB, w ∉ range γA → ∃ r ∈ Ioo (0 : ℝ) 1, g r = w := by
    rintro w ⟨u, rfl⟩ hw
    have hu0 : u ≠ 0 := fun h => hw (by rw [h, γB.source]; exact hbA)
    have hu1 : u ≠ 1 := fun h => hw (by rw [h, γB.target]; exact haA)
    have hlt : (0 : ℝ) < u := lt_of_le_of_ne u.2.1 (fun h => hu0 (Subtype.ext h.symm))
    have hlt' : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 (fun h => hu1 (Subtype.ext h))
    exact ⟨u, ⟨hlt, hlt'⟩, by simp [g, Set.projIcc_val]⟩
  have hconst : loopIndex ω z = loopIndex ω y := by
    obtain ⟨r, hr, rfl⟩ := hinner z hz hzA
    obtain ⟨s, hs, rfl⟩ := hinner y hy hyA
    have hpc : IsPathConnected (g '' Ioo (0 : ℝ) 1) :=
      ((convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num, by norm_num⟩).image hgc
    have hj : JoinedIn (g '' Ioo (0 : ℝ) 1) (g r) (g s) := hpc.joinedIn _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    exact loopIndex_eq_of_joinedIn ω (hj.mono (by
      rintro _ ⟨t, ht, rfl⟩; exact havoid t ht))
  exact hconst

/-- The vertical ray below a point: `ρ t = q - t i`. -/
def ray (q : ℂ) (t : ℝ) : ℂ := q - (t : ℂ) * Complex.I

lemma ray_im (q : ℂ) (t : ℝ) : (ray q t).im = q.im - t := by simp [ray]
lemma ray_re (q : ℂ) (t : ℝ) : (ray q t).re = q.re := by simp [ray]

lemma segment_ray {q : ℂ} {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    segment ℝ (ray q t₁) (ray q t₂) = (ray q) '' Icc t₁ t₂ := by
  rw [segment_eq_image']
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨t₁ + s * (t₂ - t₁), ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩, ?_⟩
    simp only [ray, Complex.real_smul]
    push_cast
    ring
  · rintro ⟨t, ht, rfl⟩
    rcases h.eq_or_lt with h' | h'
    · subst h'
      have : t = t₁ := le_antisymm ht.2 ht.1
      subst this
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp⟩
    · refine ⟨(t - t₁) / (t₂ - t₁), ⟨div_nonneg (by linarith [ht.1]) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]; linarith [ht.2]
      · have hne : ((t₂ : ℂ) - t₁) ≠ 0 := by exact_mod_cast (sub_ne_zero.2 h'.ne')
        simp only [ray, Complex.real_smul]
        push_cast
        field_simp
        ring

/-- **The index is constant along a piece of the ray that avoids the loop.** -/
lemma loopIndex_ray_eq {a : ℂ} (ω : Path a a) (q : ℂ) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂)
    (hav : ∀ t ∈ Icc t₁ t₂, ray q t ∉ range ω) : loopIndex ω (ray q t₁) = loopIndex ω (ray q t₂) := by
  refine loopIndex_eq_of_joinedIn ω (JoinedIn.of_segment_subset ?_)
  rw [segment_ray h]
  rintro _ ⟨t, ht, rfl⟩
  exact hav t ht

/-- **A ray that ends far below the loop and starts at a point of nonzero index meets the loop.** -/
lemma ray_hit {a : ℂ} (ω : Path a a) (q : ℂ) {T₀ : ℝ} (hT₀ : 0 ≤ T₀)
    (hfar : ∀ z ∈ range ω, (ray q T₀).im < z.im) (hne : loopIndex ω q ≠ 0) :
    ∃ t ∈ Icc 0 T₀, ray q t ∈ range ω := by
  by_contra hcon
  push Not at hcon
  have h1 := loopIndex_ray_eq ω q hT₀ hcon
  have h0 : ray q 0 = q := by simp [ray]
  rw [h0] at h1
  apply hne
  rw [h1]
  refine loopIndex_eq_zero_of_above ω (fun t => hfar _ ⟨t, rfl⟩)

lemma im_segment_ge {a b z : ℂ} (hz : z ∈ segment ℝ a b) : min a.im b.im ≤ z.im := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  have h1 := min_le_left a.im b.im
  have h2 := min_le_right a.im b.im
  have h3 : s * min a.im b.im + t * min a.im b.im = min a.im b.im := by rw [← add_mul, hst, one_mul]
  nlinarith [mul_nonneg hs (sub_nonneg.2 h1), mul_nonneg ht (sub_nonneg.2 h2)]

namespace Theta

variable (T : Theta)

/-- **The setting of the last argument**: the point `Ω` is one above the topmost point `P` of the curve and `Q` is off the
vertical line through `P`. -/
structure Setting (T : Theta) : Prop where
  hΩ : T.Ω = T.P + Complex.I
  htop : ∀ z ∈ T.curve, z.im ≤ T.P.im
  hre : T.Q.re ≠ T.P.re

/-- **The point `q` and the vertical ray below it** (the notes' ray `Ωq`, made vertical): the barycentric point
`q = Ω + c (P - Ω) + c (Q - Ω)` with `c = 1/(2(1 + d))`, `d = Im Ω - Im Q ≥ 1`, lies at height `Im P + 1/2`, strictly
between `P` and `Ω` in height, off the lines `x = P.re`, `x = Q.re`; the ray below it avoids both segments. -/
theorem exists_q (hT : Setting T) : ∃ (c : ℝ) (q : ℂ), 0 < c ∧ 2 * c ≤ 1 / 2 ∧
    q = T.Ω + (c : ℂ) * (T.P - T.Ω) + (c : ℂ) * (T.Q - T.Ω) ∧ q.im = T.P.im + 1 / 2 ∧
    q.re = T.P.re + c * (T.Q.re - T.P.re) ∧
    (∀ t : ℝ, 0 ≤ t → ray q t ∉ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω) := by
  have hQ : T.Q.im ≤ T.P.im := hT.htop T.Q (Or.inl T.Q_mem)
  set d : ℝ := T.Ω.im - T.Q.im with hd
  have hd1 : 1 ≤ d := by
    have : T.Ω.im = T.P.im + 1 := by rw [hT.hΩ]; simp
    rw [hd, this]; linarith
  set c : ℝ := 1 / (2 * (1 + d)) with hc
  have hcpos : 0 < c := by positivity
  have hcd : c * (1 + d) = 1 / 2 := by rw [hc]; field_simp
  have hc2 : 2 * c ≤ 1 / 2 := by
    rw [hc]
    rw [show 2 * (1 / (2 * (1 + d))) = 1 / (1 + d) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    linarith
  set q : ℂ := T.Ω + (c : ℂ) * (T.P - T.Ω) + (c : ℂ) * (T.Q - T.Ω) with hq
  have hΩre : T.Ω.re = T.P.re := by rw [hT.hΩ]; simp
  have hΩim : T.Ω.im = T.P.im + 1 := by rw [hT.hΩ]; simp
  have hqim : q.im = T.P.im + 1 / 2 := by
    simp only [hq, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.sub_im]
    have hcd' : c * (1 + (T.Ω.im - T.Q.im)) = 1 / 2 := by rw [← hd]; exact hcd
    linear_combination (1 - c) * hΩim - hcd'
  have hqre : q.re = T.P.re + c * (T.Q.re - T.P.re) := by
    simp only [hq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_re]
    rw [hΩre]; ring
  refine ⟨c, q, hcpos, hc2, rfl, hqim, hqre, ?_⟩
  intro t ht hmem
  rcases hmem with ⟨a, b, ha, hb, hab, hz⟩ | ⟨a, b, ha, hb, hab, hz⟩
  · -- on the vertical segment `PΩ`
    have h1 := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, ray_re, hΩre] at h1
    have h3 : a * T.P.re + b * T.P.re = T.P.re := by rw [← add_mul, hab, one_mul]
    have : q.re = T.P.re := by rw [← h1, h3]
    rw [hqre] at this
    have : c * (T.Q.re - T.P.re) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact hcpos.ne' h
    · exact hT.hre (by linarith)
  · -- on the slanted segment `QΩ`
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero, ray_re, ray_im, hΩre, hΩim] at h1 h2
    rw [hqre] at h1
    rw [hqim] at h2
    have hb' : b = 1 - a := by linarith
    have ha' : a = c := by
      have : (a - c) * (T.Q.re - T.P.re) = 0 := by rw [hb'] at h1; nlinarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd (by linarith) hT.hre
    rw [hb', ha'] at h2
    have hcd' : c * d = 1 / 2 - c := by linarith
    have hdd : d = T.P.im + 1 - T.Q.im := by rw [hd, hΩim]
    rw [hdd] at hcd'
    nlinarith

end Theta

/-- **From the point `q` to the first hit**: the index about `ω` does not change from `q` to the first point of the ray
that meets the part `A` of the loop, provided that point is not on the loop's other part `S`. -/
lemma ray_index_first {P : ℂ} (ω : Path P P) (q : ℂ) {A S : Set ℂ} (hrange : range ω = A ∪ S)
    (hS : ∀ t : ℝ, 0 ≤ t → ray q t ∉ S) {tf : ℝ} (htf : 0 ≤ tf)
    (hbefore : ∀ t : ℝ, 0 ≤ t → t < tf → ray q t ∉ A) (hat : ray q tf ∉ A) :
    loopIndex ω (ray q tf) = loopIndex ω q := by
  have h := loopIndex_ray_eq ω q htf (fun t ht hmem => by
    rw [hrange] at hmem
    rcases hmem with h | h
    · rcases ht.2.eq_or_lt with h' | h'
      · rw [h'] at h; exact hat h
      · exact hbefore t ht.1 h' h
    · exact hS t ht.1 h)
  have h0 : ray q 0 = q := by simp [ray]
  rw [h0] at h
  exact h.symm

/-- **From the last hit to far below**: the index about `ω` at the last point of the ray that meets `A` is `0`, if the
ray avoids `A` after it and the loop lies far above the end of the ray. -/
lemma ray_index_last {P : ℂ} (ω : Path P P) (q : ℂ) {A S : Set ℂ} (hrange : range ω = A ∪ S)
    (hS : ∀ t : ℝ, 0 ≤ t → ray q t ∉ S) {tl T₀ : ℝ} (htl : 0 ≤ tl) (hle : tl ≤ T₀)
    (hafter : ∀ t : ℝ, tl < t → t ≤ T₀ → ray q t ∉ A) (hat : ray q tl ∉ A)
    (hfar : ∀ z ∈ range ω, (ray q T₀).im < z.im) : loopIndex ω (ray q tl) = 0 := by
  have h := loopIndex_ray_eq ω q hle (fun t ht hmem => by
    rw [hrange] at hmem
    rcases hmem with h | h
    · rcases ht.1.eq_or_lt with h' | h'
      · rw [← h'] at h; exact hat h
      · exact hafter t h' ht.2 h
    · exact hS t (htl.trans ht.1) h)
  rw [h]
  exact loopIndex_eq_zero_of_above ω (fun t => hfar _ ⟨t, rfl⟩)

namespace Theta

variable (T : Theta)

lemma isCompact_curve : IsCompact T.curve :=
  (isCompact_range T.γ₁.continuous).union (isCompact_range T.γ₂.continuous)

lemma P_mem_curve : T.P ∈ T.curve := Or.inl T.P_mem
lemma Q_mem_curve : T.Q ∈ T.curve := Or.inl T.Q_mem

/-- **The index about `ω₁` and `ω₂` of points of the two arcs do not cancel** (the heart of the notes' last argument):
with `x` a point of `γ₁` and `y` a point of `γ₂`, not ends, `ind_y(ω₁) + ind_x(ω₂) ≠ 0`. -/
theorem sum_ne_zero (hT : Setting T) {x y : ℂ} (hx : x ∈ range T.γ₁) (hxP : x ≠ T.P) (hxQ : x ≠ T.Q)
    (hy : y ∈ range T.γ₂) (hyP : y ≠ T.P) (hyQ : y ≠ T.Q) :
    loopIndex T.ω₁ y + loopIndex T.ω₂ x ≠ 0 := by
  classical
  obtain ⟨c, q, hcpos, hc2, hq, hqim, hqre, hrayseg⟩ := exists_q T hT
  have hCtop := hT.htop
  have hqabove : ∀ z ∈ T.curve, z.im < q.im := fun z hz => by rw [hqim]; linarith [hCtop z hz]
  have hΩre : T.Ω.re = T.P.re := by rw [hT.hΩ]; simp
  have hseg : ∀ t : ℝ, 0 ≤ t → ray q t ∉ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω := hrayseg
  have hq0 : ray q 0 = q := by simp [ray]
  have hq_through : q ∉ range T.through := by
    rw [T.range_through]
    have := hseg 0 le_rfl
    rwa [hq0] at this
  have hγq : ∀ t, T.γ₁ t ≠ q := fun t h => by
    have := hqabove _ (Or.inl ⟨t, rfl⟩); rw [h] at this; exact lt_irrefl _ this
  have hγq₂ : ∀ t, T.γ₂ t ≠ q := fun t h => by
    have := hqabove _ (Or.inr ⟨t, rfl⟩); rw [h] at this; exact lt_irrefl _ this
  have hthq : ∀ t, T.through t ≠ q := fun t h => hq_through ⟨t, h⟩
  -- `ε = ind_q(ω₁) = ±1`
  have hA : ((T.Q - T.Ω) * (starRingEnd ℂ) (T.P - T.Ω)).im ≠ 0 := by
    have : T.P - T.Ω = -Complex.I := by rw [hT.hΩ]; ring
    rw [this]
    simp only [map_neg, Complex.conj_I, neg_neg, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      Complex.sub_re]
    rw [hΩre]; simpa using sub_ne_zero.2 hT.hre
  have hε : loopIndex T.ω₁ q = 1 ∨ loopIndex T.ω₁ q = -1 :=
    loopIndex_omega1 T.γ₁ c c hcpos hcpos (by linarith) hq hA
      (fun t => hqabove _ (Or.inl ⟨t, rfl⟩)) (hqabove _ T.P_mem_curve) (hqabove _ T.Q_mem_curve)
  have hε0 : loopIndex T.ω₁ q ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hω0 : loopIndex (T.γ₁.trans T.γ₂) q = 0 :=
    loopIndex_eq_zero_of_below _ fun t => by
      rw [Path.trans_apply]
      split_ifs
      · exact hqabove _ (Or.inl ⟨_, rfl⟩)
      · exact hqabove _ (Or.inr ⟨_, rfl⟩)
  have hθ := theta_lemma T.γ₁ T.through T.γ₂ hγq hthq hγq₂
  rw [hω0] at hθ
  have hε2 : loopIndex T.ω₂ q = - loopIndex T.ω₁ q := by
    have : loopIndex (T.γ₁.trans T.through) q + loopIndex (T.through.symm.trans T.γ₂) q = 0 := hθ.symm
    show loopIndex (T.through.symm.trans T.γ₂) q = - loopIndex (T.γ₁.trans T.through) q
    linarith
  have hε20 : loopIndex T.ω₂ q ≠ 0 := by rw [hε2]; exact neg_ne_zero.2 hε0
  -- far point: the ray ends below everything
  obtain ⟨z₀, hz₀, hz₀min⟩ := T.isCompact_curve.exists_isMinOn ⟨T.P, T.P_mem_curve⟩
    (Complex.continuous_im.continuousOn)
  have hz₀min' : ∀ z ∈ T.curve, z₀.im ≤ z.im := fun z hz => hz₀min hz
  set T₀ : ℝ := q.im - z₀.im + 1 with hT₀
  have hT₀0 : 0 ≤ T₀ := by have := hqabove _ hz₀; rw [hT₀]; linarith
  have hseg_im : ∀ z ∈ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω, z₀.im ≤ z.im := by
    rintro z (hz | hz)
    · have := im_segment_ge hz
      have h1 := hz₀min' _ T.P_mem_curve
      have h2 : T.P.im ≤ T.Ω.im := by rw [hT.hΩ]; simp
      exact le_trans (le_min h1 (h1.trans h2)) this
    · have := im_segment_ge hz
      have h1 := hz₀min' _ T.Q_mem_curve
      have h2 : T.P.im ≤ T.Ω.im := by rw [hT.hΩ]; simp
      exact le_trans (le_min h1 (le_trans (hz₀min' _ T.P_mem_curve) h2)) this
  have hfar : ∀ z ∈ T.curve ∪ (segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω), (ray q T₀).im < z.im := by
    intro z hz
    rw [ray_im, hT₀]
    rcases hz with hz | hz
    · linarith [hz₀min' z hz]
    · linarith [hseg_im z hz]
  have hrange₁ : range T.ω₁ = range T.γ₁ ∪ (segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω) := T.range_ω₁
  have hrange₂ : range T.ω₂ = range T.γ₂ ∪ (segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω) := T.range_ω₂
  have hfar₁ : ∀ z ∈ range T.ω₁, (ray q T₀).im < z.im := by
    intro z hz
    rw [hrange₁] at hz
    exact hfar z (by rcases hz with h | h; exacts [Or.inl (Or.inl h), Or.inr h])
  have hfar₂ : ∀ z ∈ range T.ω₂, (ray q T₀).im < z.im := by
    intro z hz
    rw [hrange₂] at hz
    exact hfar z (by rcases hz with h | h; exacts [Or.inl (Or.inr h), Or.inr h])
  -- the ray meets both arcs
  obtain ⟨t₁, ht₁, hr₁⟩ := ray_hit T.ω₁ q hT₀0 hfar₁ hε0
  obtain ⟨t₂, ht₂, hr₂⟩ := ray_hit T.ω₂ q hT₀0 hfar₂ hε20
  rw [hrange₁] at hr₁
  rw [hrange₂] at hr₂
  have hr₁' : ray q t₁ ∈ range T.γ₁ := hr₁.resolve_right (hseg t₁ ht₁.1)
  have hr₂' : ray q t₂ ∈ range T.γ₂ := hr₂.resolve_right (hseg t₂ ht₂.1)
  -- the first and last points of the ray on the curve
  set H : Set ℝ := {t | t ∈ Icc 0 T₀ ∧ ray q t ∈ T.curve} with hH
  have hHc : IsClosed H := by
    have hrc : Continuous (ray q) := by unfold ray; fun_prop
    exact isClosed_Icc.inter (T.isCompact_curve.isClosed.preimage hrc)
  have hHne : H.Nonempty := ⟨t₁, ht₁, Or.inl hr₁'⟩
  have hHbdd : BddBelow H := ⟨0, fun t ht => ht.1.1⟩
  have hHbdd' : BddAbove H := ⟨T₀, fun t ht => ht.1.2⟩
  have htf : sInf H ∈ H := hHc.csInf_mem hHne hHbdd
  have htl : sSup H ∈ H := hHc.csSup_mem hHne hHbdd'
  set tf := sInf H with htfdef
  set tl := sSup H with htldef
  have hbefore : ∀ t : ℝ, 0 ≤ t → t < tf → ray q t ∉ T.curve := fun t ht0 htlt hmem =>
    absurd (csInf_le hHbdd ⟨⟨ht0, by linarith [htf.1.2]⟩, hmem⟩) (not_le.2 htlt)
  have hafter : ∀ t : ℝ, tl < t → t ≤ T₀ → ray q t ∉ T.curve := fun t htlt htT hmem =>
    absurd (le_csSup hHbdd' ⟨⟨by linarith [htl.1.1], htT⟩, hmem⟩) (not_le.2 htlt)
  -- ray points are never the ends `P`, `Q`, so a ray point on one arc is not on the other
  have hnot12 : ∀ t : ℝ, 0 ≤ t → ray q t ∈ range T.γ₁ → ray q t ∉ range T.γ₂ := by
    intro t ht h1 h2
    have : ray q t ∈ ({T.P, T.Q} : Set ℂ) := T.disj ▸ ⟨h1, h2⟩
    rcases this with h | h
    · exact hseg t ht (Or.inl (h ▸ left_mem_segment ℝ _ _))
    · exact hseg t ht (Or.inr (h ▸ left_mem_segment ℝ _ _))
  have hnot21 : ∀ t : ℝ, 0 ≤ t → ray q t ∈ range T.γ₂ → ray q t ∉ range T.γ₁ := fun t ht h2 h1 =>
    hnot12 t ht h1 h2
  have hx₂ : x ∉ range T.γ₂ := fun h => by
    have : x ∈ ({T.P, T.Q} : Set ℂ) := T.disj ▸ ⟨hx, h⟩
    rcases this with h' | h' <;> [exact hxP h'; exact hxQ h']
  have hy₁ : y ∉ range T.γ₁ := fun h => by
    have : y ∈ ({T.P, T.Q} : Set ℂ) := T.disj ▸ ⟨h, hy⟩
    rcases this with h' | h' <;> [exact hyP h'; exact hyQ h']
  -- constancy of the index on the open arcs
  have const₂ : ∀ x' ∈ range T.γ₁, x' ∉ range T.γ₂ → loopIndex T.ω₂ x' = loopIndex T.ω₂ x := fun x' hx' hx'₂ =>
    index_const_arc T.γ₂ T.γ₁ T.inj₁ (Set.pair_comm _ _) (by rw [Set.inter_comm, T.disj, Set.pair_comm])
      T.ω₂ T.range_ω₂ (fun w hw => T.segP ▸ (by rwa [Set.union_comm] at hw))
      (fun w hw => T.segQ ▸ (by rwa [Set.union_comm] at hw)) hx' hx'₂ hx hx₂
  have const₁ : ∀ y' ∈ range T.γ₂, y' ∉ range T.γ₁ → loopIndex T.ω₁ y' = loopIndex T.ω₁ y := fun y' hy' hy'₁ =>
    index_const_arc T.γ₁ T.γ₂ T.inj₂ rfl T.disj T.ω₁ T.range_ω₁ (fun w hw => T.segP ▸ hw)
      (fun w hw => T.segQ ▸ hw) hy' hy'₁ hy hy₁
  have hcurve : ∀ z, z ∈ T.curve ↔ z ∈ range T.γ₁ ∨ z ∈ range T.γ₂ := fun z => Iff.rfl
  -- the four consequences of the first and last hits
  have first₁ : ray q tf ∈ range T.γ₁ → loopIndex T.ω₂ x = loopIndex T.ω₂ q := by
    intro h
    have hh := ray_index_first T.ω₂ q hrange₂ hseg htf.1.1
      (fun t ht0 htlt hm => hbefore t ht0 htlt (Or.inr hm)) (hnot12 tf htf.1.1 h)
    exact (const₂ _ h (hnot12 tf htf.1.1 h)).symm.trans hh
  have first₂ : ray q tf ∈ range T.γ₂ → loopIndex T.ω₁ y = loopIndex T.ω₁ q := by
    intro h
    have hh := ray_index_first T.ω₁ q hrange₁ hseg htf.1.1
      (fun t ht0 htlt hm => hbefore t ht0 htlt (Or.inl hm)) (hnot21 tf htf.1.1 h)
    exact (const₁ _ h (hnot21 tf htf.1.1 h)).symm.trans hh
  have last₁ : ray q tl ∈ range T.γ₁ → loopIndex T.ω₂ x = 0 := by
    intro h
    have hh := ray_index_last T.ω₂ q hrange₂ hseg (htl.1.1) htl.1.2
      (fun t htlt htT hm => hafter t htlt htT (Or.inr hm)) (hnot12 tl htl.1.1 h) hfar₂
    exact (const₂ _ h (hnot12 tl htl.1.1 h)).symm.trans hh
  have last₂ : ray q tl ∈ range T.γ₂ → loopIndex T.ω₁ y = 0 := by
    intro h
    have hh := ray_index_last T.ω₁ q hrange₁ hseg (htl.1.1) htl.1.2
      (fun t htlt htT hm => hafter t htlt htT (Or.inl hm)) (hnot21 tl htl.1.1 h) hfar₁
    exact (const₁ _ h (hnot21 tl htl.1.1 h)).symm.trans hh
  -- the four cases
  have hF : ray q tf ∈ range T.γ₁ ∨ ray q tf ∈ range T.γ₂ := htf.2
  have hL : ray q tl ∈ range T.γ₁ ∨ ray q tl ∈ range T.γ₂ := htl.2
  intro hsum
  rcases hF with hF | hF <;> rcases hL with hL | hL
  · have h1 := first₁ hF
    have h2 := last₁ hL
    exact hε20 (by rw [← h1, h2])
  · have h1 := first₁ hF
    have h2 := last₂ hL
    rw [h2, h1, hε2] at hsum
    simp at hsum
    exact hε0 hsum
  · have h1 := first₂ hF
    have h2 := last₁ hL
    rw [h1, h2] at hsum
    simp at hsum
    exact hε0 hsum
  · have h1 := first₂ hF
    have h2 := last₂ hL
    exact hε0 (by rw [← h1, h2])

end Theta

namespace Theta

variable (T : Theta)

/-- The curve as a loop: `ω₀ = γ₁ * γ₂` of the notes. -/
noncomputable def ω₀ : Path T.P T.P := T.γ₁.trans T.γ₂

lemma range_ω₀ : range T.ω₀ = T.curve := by
  rw [ω₀, Path.trans_range]; rfl

/-- A point joined to `Ω` in the complement of the curve has index zero about the curve. -/
theorem iota_of_joined (hT : Setting T) {R : ℂ} (hR : JoinedIn T.curveᶜ R T.Ω) : loopIndex T.ω₀ R = 0 := by
  have hj : JoinedIn (range T.ω₀)ᶜ R T.Ω := by rw [range_ω₀]; exact hR
  rw [loopIndex_eq_of_joinedIn T.ω₀ hj]
  refine loopIndex_eq_zero_of_below _ fun t => ?_
  have hmem : T.ω₀ t ∈ T.curve := by rw [← range_ω₀]; exact ⟨t, rfl⟩
  have := hT.htop _ hmem
  rw [hT.hΩ]; simp; linarith

/-- **A point not joined to `Ω` has nonzero index about the curve** (Lemma 9.14 and the nonvanishing computation): a
point `R` off the curve and the two segments that is not joined to `Ω` in the complement of the curve. -/
theorem iota_ne_zero (hT : Setting T) {R : ℂ}
    (hR : R ∉ T.curve ∪ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω) (hnj : ¬ JoinedIn T.curveᶜ R T.Ω) :
    loopIndex T.ω₀ R ≠ 0 := by
  -- points on the open arcs
  obtain ⟨x, hx, hxP, hxQ⟩ : ∃ x ∈ range T.γ₁, x ≠ T.P ∧ x ≠ T.Q := by
    refine ⟨T.γ₁ ⟨1 / 2, by norm_num, by norm_num⟩, ⟨_, rfl⟩, ?_, ?_⟩
    · intro h
      have := T.inj₁ (h.trans T.γ₁.source.symm)
      have := congrArg Subtype.val this
      norm_num at this
    · intro h
      have := T.inj₁ (h.trans T.γ₁.target.symm)
      have := congrArg Subtype.val this
      norm_num at this
  obtain ⟨y, hy, hyP, hyQ⟩ : ∃ y ∈ range T.γ₂, y ≠ T.P ∧ y ≠ T.Q := by
    refine ⟨T.γ₂ ⟨1 / 2, by norm_num, by norm_num⟩, ⟨_, rfl⟩, ?_, ?_⟩
    · intro h
      have := T.inj₂ (h.trans T.γ₂.target.symm)
      have := congrArg Subtype.val this
      norm_num at this
    · intro h
      have := T.inj₂ (h.trans T.γ₂.source.symm)
      have := congrArg Subtype.val this
      norm_num at this
  have hne := T.sum_ne_zero hT hx hxP hxQ hy hyP hyQ
  -- Lemma 9.14, contrapositive
  have h914 := T.lemma_9_14 hx hxP hxQ hy hyP hyQ hR
  have hpair : ¬ (loopIndex T.ω₁ R ≠ loopIndex T.ω₁ y ∨ loopIndex T.ω₂ R ≠ loopIndex T.ω₂ x) :=
    fun h => hnj (h914 h)
  push Not at hpair
  -- the Theta lemma at `R`
  have hRγ₁ : ∀ t, T.γ₁ t ≠ R := fun t h => hR (Or.inl (Or.inl (Or.inl ⟨t, h⟩)))
  have hRγ₂ : ∀ t, T.γ₂ t ≠ R := fun t h => hR (Or.inl (Or.inl (Or.inr ⟨t, h⟩)))
  have hRth : ∀ t, T.through t ≠ R := fun t h => by
    have : R ∈ range T.through := ⟨t, h⟩
    rw [T.range_through] at this
    rcases this with h' | h'
    · exact hR (Or.inl (Or.inr h'))
    · exact hR (Or.inr h')
  have hθ := theta_lemma T.γ₁ T.through T.γ₂ hRγ₁ hRth hRγ₂
  have : loopIndex T.ω₀ R = loopIndex T.ω₁ y + loopIndex T.ω₂ x := by
    show loopIndex (T.γ₁.trans T.γ₂) R = _
    rw [hθ]
    have e1 : loopIndex (T.γ₁.trans T.through) R = loopIndex T.ω₁ R := rfl
    have e2 : loopIndex (T.through.symm.trans T.γ₂) R = loopIndex T.ω₂ R := rfl
    rw [e1, e2, hpair.1, hpair.2]
  rw [this]
  exact hne

end Theta

/-- **The θ configuration with the point above the curve**: `P` the topmost point of the curve, `Ω = P + i`, `Q` the first
point of the curve on a segment from `Ω` to a point off the vertical line through `P`. -/
theorem exists_theta_top {f : Circle → ℂ} (hc : Continuous f) (hi : Function.Injective f) :
    ∃ T : Theta, Theta.Setting T ∧ range T.γ₁ ∪ range T.γ₂ = range f ∧
      ∃ a b : ℝ, a < b ∧ b < a + 2 * π ∧ (∀ t : I, T.γ₁ t = f (Circle.exp (a + (t : ℝ) * (b - a)))) ∧
        (∀ t : I, T.γ₂ t = f (Circle.exp (b + (t : ℝ) * (a + 2 * π - b)))) := by
  obtain ⟨w₀, hw₀⟩ := exists_top hc
  obtain ⟨a₀, rfl⟩ := Circle.exp_surjective w₀
  set P := f (Circle.exp a₀) with hP
  have htop : ∀ z ∈ range f, z.im ≤ P.im := by rintro _ ⟨w, rfl⟩; exact hw₀ w
  obtain ⟨wc, hwc⟩ := exists_off_vertical hc hi P.re
  set Ω := P + Complex.I with hΩdef
  have hΩJ : Ω ∉ range f := by
    rintro h
    have := htop _ h
    simp [hΩdef] at this
    norm_num at this
  have hvis : ∀ z ∈ segment ℝ P Ω, z ∈ range f → z = P := by
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩ hzJ
    have him := htop _ hzJ
    have hb0 : b = 0 := by
      have h1 : (a • P + b • Ω).im = P.im + b := by
        have hb'' : a = 1 - b := by linarith
        simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, hΩdef, Complex.I_im]
        rw [hb'']; ring
      linarith [him, hb]
    subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simp
  have hline : ∀ s : ℝ, 0 < s → Ω + (s : ℂ) * (f wc - Ω) ≠ P := by
    intro s hs h
    have h1 : (s : ℂ) * (f wc - Ω) = -Complex.I := by rw [hΩdef] at h ⊢; linear_combination h
    have h2 := congrArg Complex.re h1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re,
      hΩdef, Complex.add_re, Complex.I_re, add_zero, Complex.neg_re] at h2
    have : s * ((f wc).re - P.re) = 0 := by linarith
    rcases mul_eq_zero.1 this with h3 | h3
    · exact hs.ne' h3
    · exact hwc (by linarith)
  obtain ⟨T, hunion, hTP, hTΩ, ⟨s₀, hs₀, hQ⟩, hrest⟩ :=
    exists_theta_gen hc hi hΩJ a₀ hvis ⟨wc, rfl⟩ hline
  refine ⟨T, ⟨?_, ?_, ?_⟩, hunion, hrest⟩
  · rw [hTΩ, hTP]
  · intro z hz
    rw [Theta.curve, hunion] at hz
    rw [hTP]; exact htop z hz
  · intro hre
    have h1 : (s₀ : ℂ) * (f wc - Ω) = T.Q - Ω := by rw [hQ]; ring
    have h2 := congrArg Complex.re h1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re] at h2
    have h3 : Ω.re = P.re := by rw [hΩdef]; simp
    have hre' : T.Q.re = P.re := by rw [hre, hTP]
    have : s₀ * ((f wc).re - P.re) = 0 := by
      rw [← h3] at hre' ⊢
      linarith
    rcases mul_eq_zero.1 this with h4 | h4
    · exact hs₀.ne' h4
    · exact hwc (by linarith)

/-- **The θ configuration at any point off the curve**: `P` the point of the curve nearest to `Ω`, and `Q` the first
point of the curve on a segment from `Ω` to a point not on the line through `Ω` and `P`. -/
theorem exists_theta_at {f : Circle → ℂ} (hc : Continuous f) (hi : Function.Injective f) {Ω : ℂ}
    (hΩJ : Ω ∉ range f) :
    ∃ T : Theta, T.Ω = Ω ∧ range T.γ₁ ∪ range T.γ₂ = range f ∧
      ∃ a b : ℝ, a < b ∧ b < a + 2 * π ∧ (∀ t : I, T.γ₁ t = f (Circle.exp (a + (t : ℝ) * (b - a)))) ∧
        (∀ t : I, T.γ₂ t = f (Circle.exp (b + (t : ℝ) * (a + 2 * π - b)))) := by
  -- the nearest point
  obtain ⟨w₀, -, hw₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Circle))
    (f := fun w => ‖f w - Ω‖) ((hc.sub continuous_const).norm.continuousOn)
  obtain ⟨a₀, rfl⟩ := Circle.exp_surjective w₀
  set P := f (Circle.exp a₀) with hP
  have hmin : ∀ w, ‖P - Ω‖ ≤ ‖f w - Ω‖ := fun w => hw₀ (mem_univ w)
  have hPΩ : P - Ω ≠ 0 := fun h => hΩJ ⟨Circle.exp a₀, (sub_eq_zero.1 h)⟩
  have hvis : ∀ z ∈ segment ℝ P Ω, z ∈ range f → z = P := by
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩ ⟨w, hw⟩
    have h1 : a • P + b • Ω - Ω = (a : ℂ) * (P - Ω) := by
      have : (b : ℂ) = 1 - a := by
        have : (a : ℂ) + b = 1 := by exact_mod_cast hab
        linear_combination this
      simp only [Complex.real_smul]
      rw [this]; ring
    have h2 := hmin w
    rw [hw, h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha] at h2
    have hpos : 0 < ‖P - Ω‖ := norm_pos_iff.2 hPΩ
    have : 1 ≤ a := by
      by_contra hlt
      push Not at hlt
      nlinarith
    have ha1 : a = 1 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha1; subst hb0
    simp
  -- a point of the curve off the line through `Ω` and `P`
  have hoff : ∃ w, ((f w - Ω) * (starRingEnd ℂ) (P - Ω)).im ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine not_injective_circle_real (fun w => ((f w - Ω) * (starRingEnd ℂ) (P - Ω)).re)
      (Complex.continuous_re.comp ((hc.sub continuous_const).mul continuous_const)) fun w w' h => hi ?_
    have e1 := Complex.ext h (hcon w |>.trans (hcon w').symm)
    have hconj : (starRingEnd ℂ) (P - Ω) ≠ 0 := (map_ne_zero _).2 hPΩ
    have := mul_right_cancel₀ hconj e1
    linear_combination this
  obtain ⟨wc, hwc⟩ := hoff
  have hline : ∀ s : ℝ, 0 < s → Ω + (s : ℂ) * (f wc - Ω) ≠ P := by
    intro s hs h
    have h1 : (s : ℂ) * (f wc - Ω) = P - Ω := by linear_combination h
    have h2 : ((f wc - Ω) * (starRingEnd ℂ) (P - Ω)).im = 0 := by
      have : (f wc - Ω) * (starRingEnd ℂ) (P - Ω) = ((1 / s : ℝ) : ℂ) * ((P - Ω) * (starRingEnd ℂ) (P - Ω)) := by
        have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
        rw [← h1]
        push_cast
        field_simp
      rw [this, Complex.mul_im, Complex.mul_conj]
      simp
    exact hwc h2
  obtain ⟨T, hunion, hTP, hTΩ, -, hrest⟩ := exists_theta_gen hc hi hΩJ a₀ hvis ⟨wc, rfl⟩ hline
  exact ⟨T, hTΩ, hunion, hrest⟩

end Lightlike.PL
