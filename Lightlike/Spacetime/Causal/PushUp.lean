import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.CausalLadder.CurveContinuity

/-!
# Push-up: the global step, time reversal

* `IsCurveWith.reverse`: reversal of a curve; `TimeOrientation.neg`, `chronFuture_neg_iff`, `causalFuture_neg_iff`: the opposite time
  orientation exchanges `I⁺`, `J⁺` with `I⁻`, `J⁻`.
* `LocalPushUp T`: the local push-up property (a timelike curve in a small neighbourhood followed in it by a causal curve can be replaced
  by a timelike curve).
* `chronFuture_causalFuture_trans_of`: **push-up, first form**, from the openness of `I⁺(x)` and `LocalPushUp T`, by connectedness
  along the causal curve (the supremum of the parameters whose point is in `I⁺(x)`).
* `causalFuture_chronFuture_trans_of`: push-up, second form, by time reversal, under the same two hypotheses for the opposite orientation.

**Limits.** The two hypotheses (the openness of the chronological futures and `LocalPushUp`) are *not* proved here; the statements of the
tasks `T-GE2-P5` and `T-GE2-P6` stay open until they are discharged.

**References.** S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University Press (1973),
Section 6.4; E. Minguzzi, *Lorentzian causality theory*, Living Reviews in Relativity 22 (2019), Section 2.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff
noncomputable section
namespace Lightlike
namespace Causal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {P : ∀ x : M, TangentSpace I x → Prop}

omit [IsManifold I ∞ M] in
/-- **Reflection of a curve**: if `γ` has its velocity in `P` on `[c, d]`, then `t ↦ γ (k - t)` has its velocity in
`fun x v => P x (-v)` on `[k - d, k - c]`. -/
theorem IsCurveWith.reflect {γ : ℝ → M} {c d : ℝ} (h : IsCurveWith (I := I) P γ (Icc c d)) (hcd : c < d) (k : ℝ) :
    IsCurveWith (I := I) (fun x v => P x (-v)) (fun t => γ (k - t)) (Icc (k - d) (k - c)) := by
  have hmem : ∀ t, t ∈ Icc (k - d) (k - c) → k - t ∈ Icc c d := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hab : k - d < k - c := by linarith
  refine ⟨ordConnected_Icc, ?_, ?_⟩
  · intro t ht
    obtain ⟨K, U, hU, hm, hl⟩ := h.lipschitz (k - t) (hmem t ht)
    refine ⟨K, (fun s => k - s) ⁻¹' U, ?_, fun s hs => hm hs, ?_⟩
    · refine (continuous_const.sub continuous_id : Continuous fun s : ℝ => k - s).continuousWithinAt.preimage_mem_nhdsWithin' ?_
      refine nhdsWithin_mono _ ?_ hU
      rintro _ ⟨s, hs, rfl⟩
      exact hmem s hs
    · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have := hl.dist_le_mul (k - x) hx (k - y) hy
      have e : dist (k - x) (k - y) = dist x y := dist_sub_left _ _ _
      rw [e] at this
      exact this
  · have hm : MeasurePreserving (fun s : ℝ => k - s) volume volume := Measure.measurePreserving_sub_left volume k
    have h1 := hm.quasiMeasurePreserving.ae ((ae_restrict_iff' measurableSet_Icc).1 h.ae_velocity)
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h1] with t ht h2
    obtain ⟨h3, h4⟩ := h2 (hmem t ht)
    have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (k - d) (k - c)) t := (uniqueDiffOn_Icc hab t ht).uniqueMDiffWithinAt
    have hτ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => k - s) (Icc (k - d) (k - c)) t := by
      rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact (differentiableWithinAt_const _).sub differentiableWithinAt_id
    have hmaps : Icc (k - d) (k - c) ⊆ (fun s : ℝ => k - s) ⁻¹' Icc c d := fun s hs => hmem s hs
    refine ⟨h3.comp t hτ hmaps, ?_⟩
    have hc := mfderivWithin_comp t h3 hτ hmaps hu
    have hd : mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => k - s) (Icc (k - d) (k - c)) t 1 =
        -(1 : TangentSpace 𝓘(ℝ, ℝ) (k - t)) := by
      rw [mfderivWithin_eq_fderivWithin]
      have : HasFDerivWithinAt (fun s : ℝ => k - s) (-(ContinuousLinearMap.id ℝ ℝ)) (Icc (k - d) (k - c)) t :=
        ((hasFDerivWithinAt_id t _).neg).const_add k
      rw [this.fderivWithin (uniqueDiffOn_Icc hab t ht)]
      rfl
    have : velocity I (fun t => γ (k - t)) (Icc (k - d) (k - c)) t = -velocity I γ (Icc c d) (k - t) := by
      unfold velocity
      rw [show (fun t => γ (k - t)) = γ ∘ (fun s : ℝ => k - s) from rfl, hc]
      show (mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc c d) (k - t))
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => k - s) (Icc (k - d) (k - c)) t 1) = _
      rw [hd, map_neg]
      rfl
    rw [this]
    simpa using h4

omit [IsManifold I ∞ M] in
/-- **Reversal of a curve**: the reflection about the middle of the interval. -/
theorem IsCurveWith.reverse {γ : ℝ → M} {a b : ℝ} (h : IsCurveWith (I := I) P γ (Icc a b)) (hab : a < b) :
    IsCurveWith (I := I) (fun x v => P x (-v)) (fun t => γ (a + b - t)) (Icc a b) := by
  have := h.reflect hab (a + b)
  have e1 : a + b - b = a := by ring
  have e2 : a + b - a = b := by ring
  rw [e1, e2] at this
  exact this

variable {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **The opposite time orientation**: the timelike field `-X`. -/
def TimeOrientation.neg : TimeOrientation g where
  X x := -T.X x
  contMDiff := by
    have := T.contMDiff.neg_section
    simpa using this
  timelike x := by simpa using T.timelike x

/-- Negating the orientation and the vector preserves future-directed timelike. -/
theorem TimeOrientation.neg_isFutureTimelike_neg_iff {x : M} (v : TangentSpace I x) :
    T.neg.IsFutureTimelike (-v) ↔ T.IsFutureTimelike v := by
  unfold TimeOrientation.IsFutureTimelike
  simp [TimeOrientation.neg]

/-- Negating the orientation and the vector preserves future-directed causal. -/
theorem TimeOrientation.neg_isFutureCausal_neg_iff {x : M} (v : TangentSpace I x) :
    T.neg.IsFutureCausal (-v) ↔ T.IsFutureCausal v := by
  unfold TimeOrientation.IsFutureCausal
  simp [TimeOrientation.neg]


/-- Future-directed timelike for `T` at `-v` is future-directed timelike for the opposite orientation at `v`. -/
theorem TimeOrientation.isFutureTimelike_neg_iff {x : M} (v : TangentSpace I x) :
    T.IsFutureTimelike (-v) ↔ T.neg.IsFutureTimelike v := by
  unfold TimeOrientation.IsFutureTimelike
  simp [TimeOrientation.neg]

/-- Future-directed causal for `T` at `-v` is future-directed causal for the opposite orientation at `v`. -/
theorem TimeOrientation.isFutureCausal_neg_iff {x : M} (v : TangentSpace I x) :
    T.IsFutureCausal (-v) ↔ T.neg.IsFutureCausal v := by
  unfold TimeOrientation.IsFutureCausal
  simp [TimeOrientation.neg]

/-- Negating the orientation and the vector preserves the margin condition. -/
theorem TimeOrientation.neg_isFutureTimelikeWith_neg_iff (ε : ℝ) {x : M} (v : TangentSpace I x) :
    T.neg.IsFutureTimelikeWith ε (-v) ↔ T.IsFutureTimelikeWith ε v := by
  unfold TimeOrientation.IsFutureTimelikeWith
  simp [TimeOrientation.neg]

/-- The margin condition for `T` at `-v` is the one for the opposite orientation at `v`. -/
theorem TimeOrientation.isFutureTimelikeWith_neg_iff (ε : ℝ) {x : M} (v : TangentSpace I x) :
    T.IsFutureTimelikeWith ε (-v) ↔ T.neg.IsFutureTimelikeWith ε v := by
  unfold TimeOrientation.IsFutureTimelikeWith
  simp [TimeOrientation.neg]

/-- **Restriction of a timelike curve** to a nondegenerate subinterval. -/
theorem IsFutureTimelikeCurve.restrictIcc {γ : ℝ → M} {a b c d : ℝ} (h : IsFutureTimelikeCurve T γ (Icc a b))
    (hc : a ≤ c) (hd : d ≤ b) (hcd : c < d) : IsFutureTimelikeCurve T γ (Icc c d) :=
  ⟨h.1.mono hc hd hcd, fun a' b' hab' hsub => h.2 a' b' hab' (hsub.trans (Icc_subset_Icc hc hd))⟩

/-- **Reversal of a timelike curve** between two orientations related by `T₁.IsFutureTimelike (-v) → T₂.IsFutureTimelike v` and the
same for the margin condition. -/
theorem IsFutureTimelikeCurve.reverse_of {n : ℕ} {g : LorentzianMetric I M n} (T₁ T₂ : TimeOrientation g)
    (h1 : ∀ (x : M) (v : TangentSpace I x), T₁.IsFutureTimelike (-v) → T₂.IsFutureTimelike v)
    (h2 : ∀ (ε : ℝ) (x : M) (v : TangentSpace I x), T₁.IsFutureTimelikeWith ε (-v) → T₂.IsFutureTimelikeWith ε v)
    {γ : ℝ → M} {a b : ℝ} (h : IsFutureTimelikeCurve T₁ γ (Icc a b)) (hab : a < b) :
    IsFutureTimelikeCurve T₂ (fun t => γ (a + b - t)) (Icc a b) := by
  refine ⟨(h.1.reverse hab).mono_velocity fun x v hv => h1 x v hv, fun a' b' hab' hsub => ?_⟩
  have hc : a ≤ a + b - b' := by linarith [(hsub ⟨le_rfl, hab'.le⟩).2, (hsub ⟨hab'.le, le_rfl⟩).2]
  obtain ⟨ε, hε, hm⟩ := h.2 (a + b - b') (a + b - a') (by linarith) (by
    intro t ht
    exact ⟨by linarith [(hsub ⟨le_rfl, hab'.le⟩).2, (hsub ⟨hab'.le, le_rfl⟩).2, ht.1, (hsub ⟨le_rfl, hab'.le⟩).1],
      by linarith [(hsub ⟨le_rfl, hab'.le⟩).1, ht.2, (hsub ⟨hab'.le, le_rfl⟩).1]⟩)
  have := hm.reflect (by linarith) (a + b)
  have e1 : a + b - (a + b - a') = a' := by ring
  have e2 : a + b - (a + b - b') = b' := by ring
  rw [e1, e2] at this
  exact ⟨ε, hε, this.mono_velocity fun x v hv => h2 ε x v hv⟩

/-- **Time reversal**: `y ∈ I⁺(x)` for the opposite orientation iff `x ∈ I⁺(y)` for the given one. -/
theorem chronFuture_neg_iff {x y : M} : y ∈ chronFuture T.neg x ↔ x ∈ chronFuture T y := by
  constructor
  · rintro ⟨γ, a, b, hab, h, hx, hy⟩
    refine ⟨fun t => γ (a + b - t), a, b, hab,
      IsFutureTimelikeCurve.reverse_of T.neg T (fun x v hv => (T.neg_isFutureTimelike_neg_iff v).1 hv)
        (fun ε x v hv => (T.neg_isFutureTimelikeWith_neg_iff ε v).1 hv) h hab, by simp [hy], by simp [hx]⟩
  · rintro ⟨γ, a, b, hab, h, hx, hy⟩
    refine ⟨fun t => γ (a + b - t), a, b, hab,
      IsFutureTimelikeCurve.reverse_of T T.neg (fun x v hv => (T.isFutureTimelike_neg_iff v).1 hv)
        (fun ε x v hv => (T.isFutureTimelikeWith_neg_iff ε v).1 hv) h hab, by simp [hy], by simp [hx]⟩

/-- **Time reversal**: `y ∈ J⁺(x)` for the opposite orientation iff `x ∈ J⁺(y)` for the given one. -/
theorem causalFuture_neg_iff {x y : M} : y ∈ causalFuture T.neg x ↔ x ∈ causalFuture T y := by
  constructor
  · rintro ⟨γ, a, b, hab, h, hx, hy⟩
    rcases hab.eq_or_lt with rfl | hab'
    · have : x = y := by rw [← hx, ← hy]
      subst this
      exact self_mem_causalFuture T x
    refine ⟨fun t => γ (a + b - t), a, b, hab, ?_, by simp [hy], by simp [hx]⟩
    exact (h.reverse hab').mono_velocity fun x v hv => (T.neg_isFutureCausal_neg_iff v).1 hv
  · rintro ⟨γ, a, b, hab, h, hx, hy⟩
    rcases hab.eq_or_lt with rfl | hab'
    · have : x = y := by rw [← hx, ← hy]
      subst this
      exact self_mem_causalFuture T.neg x
    refine ⟨fun t => γ (a + b - t), a, b, hab, ?_, by simp [hy], by simp [hx]⟩
    exact (h.reverse hab').mono_velocity fun x v hv => (T.isFutureCausal_neg_iff v).1 hv



/-- **The local push-up property**: every point has a neighbourhood `U` such that a future-directed timelike curve in `U`, followed in
`U` by a future-directed causal curve, can be replaced by one timelike curve: the end of the causal curve is in the chronological future of
the start of the timelike curve. This is the local lift (first form of the push-up) in a neighbourhood. -/
def LocalPushUp : Prop :=
  ∀ p : M, ∃ U ∈ 𝓝 p, ∀ (α β : ℝ → M) (a b c d : ℝ), a < b → c ≤ d →
    IsFutureTimelikeCurve T α (Icc a b) → IsFutureCausalCurve T β (Icc c d) →
    α b = β c → MapsTo α (Icc a b) U → MapsTo β (Icc c d) U → β d ∈ chronFuture T (α a)

/-- **Push-up, first form, from the openness of `I⁺` and the local push-up property.** -/
theorem chronFuture_causalFuture_trans_of (hopen : ∀ x : M, IsOpen (chronFuture T x)) (hloc : LocalPushUp T)
    {x y z : M} (hxy : y ∈ chronFuture T x) (hyz : z ∈ causalFuture T y) : z ∈ chronFuture T x := by
  obtain ⟨β, c, d, hcd, hβ, hβc, hβd⟩ := hyz
  have hcont : ContinuousOn β (Icc c d) := hβ.lipschitz.continuousOn
  set S : Set ℝ := {s | s ∈ Icc c d ∧ β s ∈ chronFuture T x} with hS
  have hcS : c ∈ S := ⟨⟨le_rfl, hcd⟩, by rw [hβc]; exact hxy⟩
  have hbdd : BddAbove S := ⟨d, fun s hs => hs.1.2⟩
  set s' := sSup S with hs'
  have hs'mem : s' ∈ Icc c d := ⟨le_csSup hbdd hcS, csSup_le ⟨c, hcS⟩ fun s hs => hs.1.2⟩
  -- the point at `s'` is in `I⁺(x)`
  have hA : β s' ∈ chronFuture T x := by
    obtain ⟨U, hU, hloc'⟩ := hloc (β s')
    set V := interior U with hV
    have hVn : V ∈ 𝓝 (β s') := interior_mem_nhds.2 hU
    have h1 : ∃ δ > 0, ∀ s ∈ Icc c d, |s - s'| < δ → β s ∈ V := by
      have := (hcont s' hs'mem).eventually (isOpen_interior.mem_nhds (mem_of_mem_nhds hVn) |> fun _ => hVn)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at this
      obtain ⟨δ, hδ, hδ'⟩ := this
      exact ⟨δ, hδ, fun s hs hs2 => hδ' (by simpa [Real.dist_eq] using hs2) hs⟩
    obtain ⟨δ, hδ, hδV⟩ := h1
    obtain ⟨s₀, hs₀, hs₀lt⟩ := exists_lt_of_lt_csSup ⟨c, hcS⟩ (show s' - δ < sSup S by linarith)
    have hs₀le : s₀ ≤ s' := le_csSup hbdd hs₀
    rcases hs₀le.eq_or_lt with h0 | h0
    · rw [← h0]; exact hs₀.2
    · -- `β s₀ ∈ I⁺(x)`: a timelike curve `α` from `x` to `β s₀`
      obtain ⟨α, a', b', hab', hα, hαa, hαb⟩ := hs₀.2
      have hVo : IsOpen V := isOpen_interior
      have hβs₀V : β s₀ ∈ V := hδV s₀ hs₀.1 (by rw [abs_lt]; constructor <;> linarith)
      have hαcont : ContinuousOn α (Icc a' b') := hα.1.lipschitz.continuousOn
      have h2 : ∀ᶠ u in 𝓝[Icc a' b'] b', α u ∈ V := by
        refine (hαcont b' ⟨hab'.le, le_rfl⟩).eventually (hVo.mem_nhds ?_)
        rw [hαb]; exact hβs₀V
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
      obtain ⟨ε, hε, hε'⟩ := h2
      set r := max a' (b' - ε / 2) with hr
      have har : a' ≤ r := le_max_left _ _
      have hrb : r < b' := max_lt hab' (by linarith)
      have hr2 : b' - ε / 2 ≤ r := le_max_right _ _
      have hαV : MapsTo α (Icc r b') U := fun u hu =>
        interior_subset (hε' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
          ⟨har.trans hu.1, hu.2⟩)
      have hβV : MapsTo β (Icc s₀ s') U := fun s hs =>
        interior_subset (hδV s ⟨hs₀.1.1.trans hs.1, hs.2.trans hs'mem.2⟩ (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]))
      have hα' : IsFutureTimelikeCurve T α (Icc r b') := IsFutureTimelikeCurve.restrictIcc T hα har le_rfl hrb
      have hβ' : IsFutureCausalCurve T β (Icc s₀ s') := hβ.mono hs₀.1.1 hs'mem.2 h0
      have hjoin : α b' = β s₀ := hαb
      have hlift := hloc' α β r b' s₀ s' hrb h0.le hα' hβ' hjoin hαV hβV
      have hxr : α r ∈ chronFuture T x ∨ α r = x := by
        rcases har.eq_or_lt with h | h
        · right; rw [← h]; exact hαa
        · left; exact ⟨α, a', r, h, IsFutureTimelikeCurve.restrictIcc T hα le_rfl hrb.le h, hαa, rfl⟩
      rcases hxr with h | h
      · exact chron_trans T h hlift
      · rw [h] at hlift; exact hlift
  -- `s' = d`
  have hd : s' = d := by
    by_contra hne
    have hlt : s' < d := lt_of_le_of_ne hs'mem.2 hne
    have hopen' := (hopen x).mem_nhds hA
    have := (hcont s' hs'mem).eventually hopen'
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at this
    obtain ⟨δ, hδ, hδ'⟩ := this
    have h3 : s' < min d (s' + δ / 2) := lt_min hlt (by linarith)
    have h4 : c ≤ min d (s' + δ / 2) := hs'mem.1.trans h3.le
    have hs2 : min d (s' + δ / 2) ∈ S :=
      ⟨⟨h4, min_le_left _ _⟩, hδ' (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_right d (s' + δ / 2)])
        ⟨h4, min_le_left _ _⟩⟩
    have := le_csSup hbdd hs2
    linarith
  rw [← hβd, ← hd]; exact hA

/-- **Push-up, second form, from the same two hypotheses for the opposite orientation**: `y ∈ J⁺(x)` and `z ∈ I⁺(y)` give `z ∈ I⁺(x)`. -/
theorem causalFuture_chronFuture_trans_of (hopen : ∀ x : M, IsOpen (chronFuture T.neg x)) (hloc : LocalPushUp T.neg)
    {x y z : M} (hxy : y ∈ causalFuture T x) (hyz : z ∈ chronFuture T y) : z ∈ chronFuture T x := by
  have h1 : y ∈ chronFuture T.neg z := (chronFuture_neg_iff T).2 hyz
  have h2 : x ∈ causalFuture T.neg y := (causalFuture_neg_iff T).2 hxy
  exact (chronFuture_neg_iff T).1 (chronFuture_causalFuture_trans_of T.neg hopen hloc h1 h2)

end Causal
end Lightlike
