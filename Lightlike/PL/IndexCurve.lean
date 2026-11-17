import Lightlike.PL.ThetaRay

/-!
# The index about a Jordan curve does not depend on the splitting

A global logarithm of `s ↦ f (exp s) - R` over the line shows the logarithm increment of the loop around the curve is the same for every splitting into two arcs of the circle, so the index about the curve is well defined.

## Main results

* `Theta.iota_eq`: independence of the splitting
* `Theta.iota_const`: constancy off the component of `Ω`

## References

* McCleary, *A First Course in Topology: Continuity and Dimension* (2006), `mccleary-2006`, Chapter 9: the chapter location is verified, the lemma-level numbering is not.
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

/-- **A global logarithm of a periodic loop**: for a point `R` off the curve, `s ↦ f (exp s) - R` has a continuous
logarithm on the whole line (lifting through `exp` from the simply connected line). -/
theorem exists_global_log {f : Circle → ℂ} (hc : Continuous f) {R : ℂ} (hR : R ∉ range f) :
    ∃ F : ℝ → ℂ, Continuous F ∧ ∀ s, exp (F s) = f (Circle.exp s) - R := by
  have hne : ∀ s : ℝ, f (Circle.exp s) - R ≠ 0 := fun s h => hR ⟨_, sub_eq_zero.1 h⟩
  let γ : C(ℝ, {w : ℂ // w ≠ 0}) :=
    ⟨fun s => ⟨f (Circle.exp s) - R, hne s⟩,
      ((hc.comp Circle.exp.continuous).sub continuous_const).subtype_mk _⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts γ 0
    (Complex.log (f (Circle.exp 0) - R)) (Subtype.ext (exp_log (hne 0)))
  exact ⟨F, F.continuous, fun s => congrArg Subtype.val (congrFun hF s)⟩

/-- **The period increment of a global logarithm is constant**: `F (s + 2π) = F s + κ`. -/
theorem global_log_period {f : Circle → ℂ} {R : ℂ} {F : ℝ → ℂ} (hFc : Continuous F)
    (hF : ∀ s, exp (F s) = f (Circle.exp s) - R) : ∀ s, F (s + 2 * π) = F s + (F (2 * π) - F 0) := by
  have hper : ∀ s : ℝ, f (Circle.exp (s + 2 * π)) = f (Circle.exp s) := fun s => by
    congr 1; rw [Circle.exp_eq_exp]; exact ⟨1, by simp⟩
  have hk : exp (F (2 * π) - F 0) = 1 := by
    rw [Complex.exp_sub, hF, hF]
    have := hper 0
    simp only [zero_add] at this
    rw [this]
    have hne : f (Circle.exp 0) - R ≠ 0 := by
      intro h
      have := hF 0
      rw [h] at this
      exact exp_ne_zero _ this
    exact div_self hne
  have hcov := Complex.isCoveringMap_exp
  have hmain : (fun s => F (s + 2 * π)) = fun s => F s + (F (2 * π) - F 0) := by
    refine hcov.eq_of_comp_eq (A := ℝ) (f := fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {w : ℂ // w ≠ 0}))
      (hFc.comp (continuous_id.add continuous_const)) (hFc.add continuous_const) ?_ 0 (by simp)
    funext s
    apply Subtype.ext
    simp only [Function.comp_apply]
    rw [hF, Complex.exp_add, hF, hk, mul_one, hper]
  exact fun s => congrFun hmain s

/-- **The increment along an arc of the circle**, for a global logarithm. -/
theorem logInc_arc {f : Circle → ℂ} {R : ℂ} {F : ℝ → ℂ} (hFc : Continuous F)
    (hF : ∀ s, exp (F s) = f (Circle.exp s) - R) {a b : ℝ} {P Q : ℂ} (γ : Path P Q)
    (hγ : ∀ t : I, γ t = f (Circle.exp (a + (t : ℝ) * (b - a)))) :
    logInc γ R = F b - F a := by
  have hav : ∀ t, γ t ≠ R := fun t h => by
    have := hF (a + (t : ℝ) * (b - a))
    rw [← hγ t, h, sub_self] at this
    exact exp_ne_zero _ this
  let ℓ : C(I, ℂ) := ⟨fun t => F (a + (t : ℝ) * (b - a)), hFc.comp (by fun_prop)⟩
  have hlog : IsLog (γ : C(I, ℂ)) R ℓ := fun t => by
    show exp (F (a + (t : ℝ) * (b - a))) = γ t - R
    rw [hF, hγ]
  rw [logInc_eq γ hav hlog]
  show F (a + ((1 : I) : ℝ) * (b - a)) - F (a + ((0 : I) : ℝ) * (b - a)) = _
  simp

namespace Theta

variable (T : Theta)

/-- **The increment of the curve loop about `R` does not depend on how the curve is split** (a global logarithm). -/
theorem logInc_ω₀ {f : Circle → ℂ} {R : ℂ} {F : ℝ → ℂ} (hFc : Continuous F)
    (hF : ∀ s, exp (F s) = f (Circle.exp s) - R) {a b : ℝ}
    (hγ₁ : ∀ t : I, T.γ₁ t = f (Circle.exp (a + (t : ℝ) * (b - a))))
    (hγ₂ : ∀ t : I, T.γ₂ t = f (Circle.exp (b + (t : ℝ) * (a + 2 * π - b)))) :
    logInc T.ω₀ R = F (2 * π) - F 0 := by
  have hav : ∀ (u : ℝ), f (Circle.exp u) ≠ R := fun u h => by
    have := hF u
    rw [h, sub_self] at this
    exact exp_ne_zero _ this
  have h1 : ∀ t, T.γ₁ t ≠ R := fun t => by rw [hγ₁]; exact hav _
  have h2 : ∀ t, T.γ₂ t ≠ R := fun t => by rw [hγ₂]; exact hav _
  rw [ω₀, logInc_trans _ _ h1 h2, logInc_arc hFc hF T.γ₁ hγ₁, logInc_arc hFc hF T.γ₂ hγ₂]
  have := global_log_period hFc hF a
  linear_combination this

end Theta

namespace Theta

variable (T : Theta)

/-- **The points of the segments, off the curve, lie in the component of `Ω`**. -/
theorem segments_subset_component {z : ℂ} (hz : z ∈ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω) :
    z ∈ T.curve ∨ z ∈ connectedComponentIn T.curveᶜ T.Ω := by
  by_cases hzC : z ∈ T.curve
  · exact Or.inl hzC
  right
  have hj : JoinedIn T.curveᶜ z T.Ω := by
    rcases hz with hz | hz
    · refine JoinedIn.of_segment_subset (fun w hw hwC => ?_)
      have hsub : segment ℝ z T.Ω ⊆ segment ℝ T.P T.Ω :=
        (convex_segment T.P T.Ω).segment_subset hz (right_mem_segment ℝ T.P T.Ω)
      have hwP : w ∈ ({T.P} : Set ℂ) := T.segP.subset (⟨hsub hw, hwC⟩ : w ∈ segment ℝ T.P T.Ω ∩ (range T.γ₁ ∪ range T.γ₂))
      have hzP : z ≠ T.P := fun h => hzC (h ▸ T.P_mem_curve)
      exact start_not_mem_segment T.P_ne_Ω hz hzP (by rw [Set.mem_singleton_iff] at hwP; exact hwP ▸ hw)
    · refine JoinedIn.of_segment_subset (fun w hw hwC => ?_)
      have hsub : segment ℝ z T.Ω ⊆ segment ℝ T.Q T.Ω :=
        (convex_segment T.Q T.Ω).segment_subset hz (right_mem_segment ℝ T.Q T.Ω)
      have hwQ : w ∈ ({T.Q} : Set ℂ) := T.segQ.subset (⟨hsub hw, hwC⟩ : w ∈ segment ℝ T.Q T.Ω ∩ (range T.γ₁ ∪ range T.γ₂))
      have hzQ : z ≠ T.Q := fun h => hzC (h ▸ T.Q_mem_curve)
      exact start_not_mem_segment T.Q_ne_Ω hz hzQ (by rw [Set.mem_singleton_iff] at hwQ; exact hwQ ▸ hw)
  obtain ⟨γ, hγ⟩ := hj
  have hzc : z ∈ T.curveᶜ := hzC
  have hΩz : T.Ω ∈ connectedComponentIn T.curveᶜ z :=
    (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn ⟨0, γ.source⟩
      (by rintro _ ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩
  rw [← connectedComponentIn_eq hΩz]
  exact mem_connectedComponentIn hzc

end Theta

/-- A point joined to another in a set lies in the connected component of the other. -/
lemma joinedIn_mem_connectedComponentIn {F : Set ℂ} {x y : ℂ} (_hx : x ∈ F) (h : JoinedIn F x y) :
    y ∈ connectedComponentIn F x := by
  obtain ⟨γ, hγ⟩ := h
  exact (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn ⟨0, γ.source⟩
    (by rintro _ ⟨t, rfl⟩; exact hγ t) ⟨1, γ.target⟩

namespace Theta

variable (T : Theta)

/-- **The index about the curve is constant on the points not joined to `Ω`** (Lemma 9.14 and the Theta Lemma, for any
θ configuration). -/
theorem iota_const : ∃ K : ℤ, ∀ R : ℂ, R ∉ T.curve ∪ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω →
    ¬ JoinedIn T.curveᶜ R T.Ω → loopIndex T.ω₀ R = K := by
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
  refine ⟨loopIndex T.ω₁ y + loopIndex T.ω₂ x, fun R hR hnj => ?_⟩
  have h914 := T.lemma_9_14 hx hxP hxQ hy hyP hyQ hR
  have hpair : ¬ (loopIndex T.ω₁ R ≠ loopIndex T.ω₁ y ∨ loopIndex T.ω₂ R ≠ loopIndex T.ω₂ x) :=
    fun h => hnj (h914 h)
  push Not at hpair
  have hRγ₁ : ∀ t, T.γ₁ t ≠ R := fun t h => hR (Or.inl (Or.inl (Or.inl ⟨t, h⟩)))
  have hRγ₂ : ∀ t, T.γ₂ t ≠ R := fun t h => hR (Or.inl (Or.inl (Or.inr ⟨t, h⟩)))
  have hRth : ∀ t, T.through t ≠ R := fun t h => by
    have : R ∈ range T.through := ⟨t, h⟩
    rw [T.range_through] at this
    rcases this with h' | h'
    · exact hR (Or.inl (Or.inr h'))
    · exact hR (Or.inr h')
  have hθ := theta_lemma T.γ₁ T.through T.γ₂ hRγ₁ hRth hRγ₂
  have e1 : loopIndex (T.γ₁.trans T.through) R = loopIndex T.ω₁ R := rfl
  have e2 : loopIndex (T.through.symm.trans T.γ₂) R = loopIndex T.ω₂ R := rfl
  show loopIndex (T.γ₁.trans T.γ₂) R = _
  rw [hθ, e1, e2, hpair.1, hpair.2]

/-- **The index about the curve does not depend on the θ configuration**: two configurations that split the same curve
`f` by arcs of the circle have the same index about every point off the curve. -/
theorem iota_eq {f : Circle → ℂ} (hc : Continuous f) (T T' : Theta) {R : ℂ} (hR : R ∉ range f)
    {a b a' b' : ℝ}
    (hγ₁ : ∀ t : I, T.γ₁ t = f (Circle.exp (a + (t : ℝ) * (b - a))))
    (hγ₂ : ∀ t : I, T.γ₂ t = f (Circle.exp (b + (t : ℝ) * (a + 2 * π - b))))
    (hγ₁' : ∀ t : I, T'.γ₁ t = f (Circle.exp (a' + (t : ℝ) * (b' - a'))))
    (hγ₂' : ∀ t : I, T'.γ₂ t = f (Circle.exp (b' + (t : ℝ) * (a' + 2 * π - b')))) :
    loopIndex T.ω₀ R = loopIndex T'.ω₀ R := by
  obtain ⟨F, hFc, hF⟩ := exists_global_log hc hR
  have h1 := logInc_ω₀ T hFc hF hγ₁ hγ₂
  have h2 := logInc_ω₀ T' hFc hF hγ₁' hγ₂'
  have hav : ∀ (u : ℝ), f (Circle.exp u) ≠ R := fun u h => by
    have := hF u
    rw [h, sub_self] at this
    exact exp_ne_zero _ this
  have hT : ∀ t, T.ω₀ t ≠ R := avoid_trans (fun t => by rw [hγ₁]; exact hav _) (fun t => by rw [hγ₂]; exact hav _)
  have hT' : ∀ t, T'.ω₀ t ≠ R :=
    avoid_trans (fun t => by rw [hγ₁']; exact hav _) (fun t => by rw [hγ₂']; exact hav _)
  have s1 := loopIndex_spec T.ω₀ hT
  have s2 := loopIndex_spec T'.ω₀ hT'
  rw [h1] at s1
  rw [h2] at s2
  have hne : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((loopIndex T.ω₀ R : ℤ) : ℂ) = ((loopIndex T'.ω₀ R : ℤ) : ℂ) := by
    apply mul_right_cancel₀ hne
    rw [← s1, ← s2]
  exact_mod_cast this

end Theta

end Lightlike.PL
