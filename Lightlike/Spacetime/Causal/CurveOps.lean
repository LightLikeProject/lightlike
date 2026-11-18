import Lightlike.Spacetime.Causal.Relations

/-!
# Operations on curves with a velocity condition

Restriction to a subinterval, translation of the parameter and gluing at a common endpoint of curves
`γ : ℝ → M` with a velocity condition (`Causal.IsCurveWith`). These are the tools for the
transitivity of the causal and chronological futures. The velocity condition `P` is arbitrary: only
its holding almost everywhere is used.

## Main statements

* `Causal.IsCurveWith.mono`: restriction to a nondegenerate subinterval.
* `Causal.IsCurveWith.shift`: translation of the parameter.
* `Causal.IsCurveWith.glue`: two curves meeting at an endpoint form one curve.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {P : ∀ x : M, TangentSpace I x → Prop}

omit [IsManifold I ∞ M] in
/-- **Restriction**: a curve with velocity in `P` on `[a, b]` is one on every nondegenerate
subinterval `[c, d]`. -/
theorem IsCurveWith.mono {γ : ℝ → M} {a b c d : ℝ} (h : IsCurveWith (I := I) P γ (Icc a b))
    (hc : a ≤ c) (hd : d ≤ b) (hcd : c < d) : IsCurveWith (I := I) P γ (Icc c d) := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hc hd
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    obtain ⟨K, U, hU, hm, hl⟩ := h.lipschitz t (hsub ht)
    exact ⟨K, U, nhdsWithin_mono t hsub hU, hm, hl⟩
  · have h1 := ae_mono (Measure.restrict_mono hsub le_rfl) h.ae_velocity
    filter_upwards [ae_restrict_mem measurableSet_Icc, h1] with t ht ⟨h2, h3⟩
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc c d) t :=
      (uniqueDiffOn_Icc hcd t ht).uniqueMDiffWithinAt
    refine ⟨h2.mono hsub, ?_⟩
    have : velocity I γ (Icc c d) t = velocity I γ (Icc a b) t := by
      unfold velocity
      rw [h2.mfderivWithin_mono hu hsub]
    rw [this]
    exact h3

omit [IsManifold I ∞ M] in
/-- **Restriction to a compact subinterval of any interval**: a curve with velocity in `P` on `s`
is one on every nondegenerate `[c, d] ⊆ s`. -/
theorem IsCurveWith.restrict {γ : ℝ → M} {s : Set ℝ} {c d : ℝ} (h : IsCurveWith (I := I) P γ s)
    (hsub : Icc c d ⊆ s) (hcd : c < d) : IsCurveWith (I := I) P γ (Icc c d) := by
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    obtain ⟨K, U, hU, hm, hl⟩ := h.lipschitz t (hsub ht)
    exact ⟨K, U, nhdsWithin_mono t hsub hU, hm, hl⟩
  · have h1 := ae_mono (Measure.restrict_mono hsub le_rfl) h.ae_velocity
    filter_upwards [ae_restrict_mem measurableSet_Icc, h1] with t ht ⟨h2, h3⟩
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc c d) t :=
      (uniqueDiffOn_Icc hcd t ht).uniqueMDiffWithinAt
    refine ⟨h2.mono hsub, ?_⟩
    have : velocity I γ (Icc c d) t = velocity I γ s t := by
      unfold velocity
      rw [h2.mfderivWithin_mono hu hsub]
    rw [this]
    exact h3

omit [IsManifold I ∞ M] in
/-- **Translation of the parameter**: if `γ` has its velocity in `P` on `[a, b]` then
`t ↦ γ (t + k)` has it on `[a - k, b - k]`. -/
theorem IsCurveWith.shift {γ : ℝ → M} {a b : ℝ} (h : IsCurveWith (I := I) P γ (Icc a b)) (hab : a < b)
    (k : ℝ) : IsCurveWith (I := I) P (fun t => γ (t + k)) (Icc (a - k) (b - k)) := by
  have hmem : ∀ t, t ∈ Icc (a - k) (b - k) → t + k ∈ Icc a b := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    obtain ⟨K, U, hU, hm, hl⟩ := h.lipschitz (t + k) (hmem t ht)
    refine ⟨K, (fun s => s + k) ⁻¹' U, ?_, fun s hs => hm hs, ?_⟩
    · refine (continuous_id.add continuous_const : Continuous fun s : ℝ => s + k).continuousWithinAt.preimage_mem_nhdsWithin' ?_
      refine nhdsWithin_mono _ ?_ hU
      rintro _ ⟨s, hs, rfl⟩
      exact hmem s hs
    · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have := hl.dist_le_mul (x + k) hx (y + k) hy
      simpa [dist_add_right] using this
  · have h1 := (measurePreserving_add_right volume k).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Icc).1 h.ae_velocity)
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h1] with t ht h2
    obtain ⟨h3, h4⟩ := h2 (hmem t ht)
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (a - k) (b - k)) t :=
      (uniqueDiffOn_Icc (by linarith) t ht).uniqueMDiffWithinAt
    have hτ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + k) (Icc (a - k) (b - k)) t := by
      rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact (differentiableWithinAt_id.add_const k)
    have hmaps : Icc (a - k) (b - k) ⊆ (fun s : ℝ => s + k) ⁻¹' Icc a b := fun s hs => hmem s hs
    refine ⟨h3.comp t hτ hmaps, ?_⟩
    have hc := mfderivWithin_comp t h3 hτ hmaps hu
    have hd : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s + k) (Icc (a - k) (b - k)) t 1 = 1 := by
      rw [mfderivWithin_eq_fderivWithin]
      have : HasFDerivWithinAt (fun s : ℝ => s + k) (ContinuousLinearMap.id ℝ ℝ)
          (Icc (a - k) (b - k)) t := (hasFDerivWithinAt_id t _).add_const k
      rw [this.fderivWithin (uniqueDiffOn_Icc (by linarith) t ht)]
      rfl
    have : velocity I (fun t => γ (t + k)) (Icc (a - k) (b - k)) t =
        velocity I γ (Icc a b) (t + k) := by
      unfold velocity
      rw [show (fun t => γ (t + k)) = γ ∘ (fun s : ℝ => s + k) from rfl, hc]
      exact congrArg (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc a b) (t + k)) hd
    rw [this]
    exact h4

omit [IsManifold I ∞ M] in
/-- Transport of a velocity condition along an equality of base points: the tangent spaces at equal
points are identified by the identity (`TangentSpace I x` is `E`). -/
theorem velocity_cast {x y : M} (h : x = y) (v : TangentSpace I x) (hv : P x v) :
    P y (tangentSpaceCast (I := I) x y v) := by
  subst h
  exact hv

omit [IsManifold I ∞ M] in
/-- **Local nature of the velocity condition**: if the set `s'` and the curve `G` agree near `t`
with `s` and `γ`, the velocity condition at `t` passes from `γ` along `s` to `G` along `s'`. -/
theorem velocity_congr {γ G : ℝ → M} {s s' : Set ℝ} {t : ℝ} (hs : s' =ᶠ[𝓝 t] s)
    (hG : G =ᶠ[𝓝 t] γ) (hd : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hP : P (γ t) (velocity I γ s t)) :
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) I G s' t ∧ P (G t) (velocity I G s' t) := by
  have hx : G t = γ t := hG.self_of_nhds
  have hL : G =ᶠ[𝓝[s'] t] γ := nhdsWithin_le_nhds hG
  have hd' : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s' t := (mdifferentiableWithinAt_congr_set hs).2 hd
  refine ⟨hd'.congr_of_eventuallyEq hL hx, ?_⟩
  have h1 := Filter.EventuallyEq.mfderivWithin_eq (I := 𝓘(ℝ, ℝ)) (I' := I) hL hx
  have h2 : velocity I G s' t = tangentSpaceCast (I := I) (γ t) (G t) (velocity I γ s t) := by
    unfold velocity
    rw [h1, mfderivWithin_congr_set hs]
    rfl
  rw [h2]
  exact velocity_cast hx.symm _ hP

omit [IsManifold I ∞ M] in
/-- **Gluing**: two curves with velocity in `P`, on `[a, b]` and on `[b, c]`, that meet at `b`
form one curve with velocity in `P` on `[a, c]`. The velocity is not asked to match at the
junction, which is a null set. -/
theorem IsCurveWith.glue {γ₁ γ₂ : ℝ → M} {a b c : ℝ} (h₁ : IsCurveWith (I := I) P γ₁ (Icc a b))
    (h₂ : IsCurveWith (I := I) P γ₂ (Icc b c)) (hab : a < b) (hbc : b < c) (hj : γ₁ b = γ₂ b) :
    IsCurveWith (I := I) P (fun t => if t ≤ b then γ₁ t else γ₂ t) (Icc a c) := by
  set G : ℝ → M := fun t => if t ≤ b then γ₁ t else γ₂ t with hGdef
  have hGl : ∀ t, t ≤ b → G t = γ₁ t := fun t ht => by simp [G, ht]
  have hGr : ∀ t, b ≤ t → G t = γ₂ t := by
    intro t ht
    by_cases h : t ≤ b
    · have : t = b := le_antisymm h ht
      subst this
      simp [G, hj]
    · simp [G, h]
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    rcases lt_trichotomy t b with htb | heq | htb
    · obtain ⟨K, U, hU, hm, hl⟩ := h₁.lipschitz t ⟨ht.1, htb.le⟩
      have hmem : Icc a b ∈ 𝓝[Icc a c] t :=
        mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, htb, fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
      have e : 𝓝[Icc a b] t = 𝓝[Icc a c] t := by
        rw [← nhdsWithin_inter_of_mem' hmem, inter_eq_right.2 (Icc_subset_Icc_right hbc.le)]
      have hU' : U ∩ Iio b ∈ 𝓝[Icc a c] t :=
        inter_mem (e ▸ hU) (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htb))
      refine ⟨K, U ∩ Iio b, hU', ?_, ?_⟩
      · rw [hGl t htb.le]
        intro s hs
        rw [hGl s hs.2.le]
        exact hm hs.1
      · rw [hGl t htb.le]
        refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
        simp only [Function.comp, hGl x hx.2.le, hGl y hy.2.le]
        exact hl.dist_le_mul x hx.1 y hy.1
    · rw [heq]
      obtain ⟨K₁, U₁, hU₁, hm₁, hl₁⟩ := h₁.lipschitz b ⟨hab.le, le_rfl⟩
      obtain ⟨K₂, U₂, hU₂, hm₂, hl₂⟩ := h₂.lipschitz b ⟨le_rfl, hbc.le⟩
      rw [← hj] at hm₂ hl₂
      have hb1 : b ∈ U₁ := mem_of_mem_nhdsWithin (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩) hU₁
      have hb2 : b ∈ U₂ := mem_of_mem_nhdsWithin (show b ∈ Icc b c from ⟨le_rfl, hbc.le⟩) hU₂
      refine ⟨K₁ + K₂, (U₁ ∩ Iic b) ∪ (U₂ ∩ Ici b), ?_, ?_, ?_⟩
      · rw [← Icc_union_Icc_eq_Icc hab.le hbc.le, nhdsWithin_union, mem_sup]
        have s1 : Icc a b ⊆ Iic b := fun y hy => hy.2
        have s2 : Icc b c ⊆ Ici b := fun y hy => hy.1
        exact ⟨mem_of_superset (inter_mem hU₁ (mem_of_superset self_mem_nhdsWithin s1))
          subset_union_left,
          mem_of_superset (inter_mem hU₂ (mem_of_superset self_mem_nhdsWithin s2))
          subset_union_right⟩
      · rw [hGl b le_rfl]
        rintro s (hs | hs)
        · rw [hGl s hs.2]; exact hm₁ hs.1
        · rw [hGr s hs.2]; exact hm₂ hs.1
      · rw [hGl b le_rfl]
        have hx1 : ∀ x ∈ (U₁ ∩ Iic b) ∪ (U₂ ∩ Ici b), x ≤ b → x ∈ U₁ := by
          rintro x (hx | hx) hxb
          · exact hx.1
          · rw [le_antisymm hxb hx.2]; exact hb1
        have hx2 : ∀ x ∈ (U₁ ∩ Iic b) ∪ (U₂ ∩ Ici b), b ≤ x → x ∈ U₂ := by
          rintro x (hx | hx) hxb
          · have : x = b := le_antisymm hx.2 hxb
            rw [this]; exact hb2
          · exact hx.1
        set e := extChartAt I (γ₁ b) with he
        have Fl : ∀ x ∈ (U₁ ∩ Iic b) ∪ (U₂ ∩ Ici b), x ≤ b →
            (e ∘ G) x = (e ∘ γ₁) x := fun x _ hxb => by simp only [Function.comp, hGl x hxb]
        have Fr : ∀ x ∈ (U₁ ∩ Iic b) ∪ (U₂ ∩ Ici b), b ≤ x →
            (e ∘ G) x = (e ∘ γ₂) x := fun x _ hxb => by simp only [Function.comp, hGr x hxb]
        have Fb : (e ∘ G) b = (e ∘ γ₁) b := Fl b (Or.inl ⟨hb1, mem_Iic.2 le_rfl⟩) le_rfl
        have K1 := K₁.coe_nonneg
        have K2 := K₂.coe_nonneg
        have mixed : ∀ x ∈ (U₁ ∩ Iic b) ∪ (U₂ ∩ Ici b), ∀ y ∈ (U₁ ∩ Iic b) ∪ (U₂ ∩ Ici b),
            x ≤ b → b ≤ y → dist ((e ∘ G) x) ((e ∘ G) y) ≤ ((K₁ + K₂ : NNReal) : ℝ) * dist x y := by
          intro x hx y hy hxb hby
          have d1 := hl₁.dist_le_mul x (hx1 x hx hxb) b hb1
          have d2 := hl₂.dist_le_mul b hb2 y (hx2 y hy hby)
          have := dist_triangle ((e ∘ G) x) ((e ∘ G) b) ((e ∘ G) y)
          rw [Fl x hx hxb, Fb, Fr y hy hby] at this
          rw [Fl x hx hxb, Fr y hy hby]
          have hb2' : (e ∘ γ₁) b = (e ∘ γ₂) b := by simp [hj]
          rw [hb2'] at d1 this
          rw [Real.dist_eq] at d1 d2 ⊢
          rw [abs_of_nonpos (by linarith : x - b ≤ 0)] at d1
          rw [abs_of_nonpos (by linarith : b - y ≤ 0)] at d2
          rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
          push_cast
          nlinarith
        refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
        rcases le_total x b with hxb | hbx <;> rcases le_total y b with hyb | hby
        · rw [Fl x hx hxb, Fl y hy hyb]
          have := hl₁.dist_le_mul x (hx1 x hx hxb) y (hx1 y hy hyb)
          push_cast
          nlinarith [dist_nonneg (x := x) (y := y)]
        · exact mixed x hx y hy hxb hby
        · rw [dist_comm, dist_comm x y]; exact mixed y hy x hx hyb hbx
        · rw [Fr x hx hbx, Fr y hy hby]
          have := hl₂.dist_le_mul x (hx2 x hx hbx) y (hx2 y hy hby)
          push_cast
          nlinarith [dist_nonneg (x := x) (y := y)]
    · obtain ⟨K, U, hU, hm, hl⟩ := h₂.lipschitz t ⟨htb.le, ht.2⟩
      have hmem : Icc b c ∈ 𝓝[Icc a c] t :=
        mem_nhdsWithin.2 ⟨Ioi b, isOpen_Ioi, htb, fun y hy => ⟨hy.1.le, hy.2.2⟩⟩
      have e : 𝓝[Icc b c] t = 𝓝[Icc a c] t := by
        rw [← nhdsWithin_inter_of_mem' hmem, inter_eq_right.2 (Icc_subset_Icc_left hab.le)]
      have hU' : U ∩ Ioi b ∈ 𝓝[Icc a c] t :=
        inter_mem (e ▸ hU) (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htb))
      refine ⟨K, U ∩ Ioi b, hU', ?_, ?_⟩
      · rw [hGr t htb.le]
        intro s hs
        rw [hGr s hs.2.le]
        exact hm hs.1
      · rw [hGr t htb.le]
        refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
        simp only [Function.comp, hGr x hx.2.le, hGr y hy.2.le]
        exact hl.dist_le_mul x hx.1 y hy.1
  · have hae : ∀ᵐ t ∂(volume.restrict (Icc a b ∪ Icc b c)),
        MDifferentiableWithinAt 𝓘(ℝ, ℝ) I G (Icc a c) t ∧ P (G t) (velocity I G (Icc a c) t) := by
      have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({b} : Set ℝ) :=
        (countable_singleton b).ae_notMem _
      refine (ae_restrict_union_iff _ _ _).2 ⟨?_, ?_⟩
      · filter_upwards [ae_restrict_mem measurableSet_Icc, h₁.ae_velocity,
          ae_restrict_of_ae hne] with t ht ⟨hd, hP⟩ hn
        have htb : t < b := lt_of_le_of_ne ht.2 hn
        exact velocity_congr (P := P) (s := Icc a b)
          ((Filter.eventuallyEqSet_iff).2 (Filter.eventually_of_mem (Iio_mem_nhds htb) fun y hy =>
            ⟨fun h => ⟨h.1, hy.le⟩, fun h => ⟨h.1, h.2.trans hbc.le⟩⟩))
          (Filter.eventually_of_mem (Iio_mem_nhds htb) fun y hy => hGl y (le_of_lt hy)) hd hP
      · filter_upwards [ae_restrict_mem measurableSet_Icc, h₂.ae_velocity,
          ae_restrict_of_ae hne] with t ht ⟨hd, hP⟩ hn
        have htb : b < t := lt_of_le_of_ne ht.1 (fun h => hn h.symm)
        exact velocity_congr (P := P) (s := Icc b c)
          ((Filter.eventuallyEqSet_iff).2 (Filter.eventually_of_mem (Ioi_mem_nhds htb) fun y hy =>
            ⟨fun h => ⟨hy.le, h.2⟩, fun h => ⟨hab.le.trans hy.le, h.2⟩⟩))
          (Filter.eventually_of_mem (Ioi_mem_nhds htb) fun y hy => hGr y (le_of_lt hy)) hd hP
    rwa [Icc_union_Icc_eq_Icc hab.le hbc.le] at hae

end Causal

end Lightlike
