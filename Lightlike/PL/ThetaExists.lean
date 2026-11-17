import Lightlike.PL.IndexTriangle
import Lightlike.PL.IndexTheta

/-!
# A θ configuration on a Jordan curve

Splitting a Jordan curve given as an injective continuous map from the circle into two arcs by a point `P` of the curve that is visible from a point `Ω` off it and the first point `Q` of the curve on a segment from `Ω`: this is the `Theta` configuration of the Theta Lemma, with the arcs images of arcs of the circle.

## Main results

* `exists_theta_gen`: a θ configuration with prescribed visible `P` and a direction for `Q`
* `not_injective_circle_real`: no continuous injective map from the circle to the line

## References

* McCleary, *A First Course in Topology: Continuity and Dimension* (2006), `mccleary-2006`, Chapter 9: the chapter location is verified, the lemma-level numbering is not.
-/

open Set Real unitInterval

namespace Lightlike.PL

/-- **There is no continuous injective map from the circle to the line.** -/
theorem not_injective_circle_real (g : Circle → ℝ) (hc : Continuous g) : ¬ Function.Injective g := by
  intro hinj
  -- the minimum and the maximum
  obtain ⟨z₁, hz₁⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Circle)) hc.continuousOn
  obtain ⟨z₂, hz₂⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := Circle)) hc.continuousOn
  have hz₁' : ∀ z, g z₁ ≤ g z := fun z => hz₁.2 (mem_univ z)
  have hz₂' : ∀ z, g z ≤ g z₂ := fun z => hz₂.2 (mem_univ z)
  have hne : z₁ ≠ z₂ := by
    intro h
    -- all values equal: then g is constant, contradicting injectivity
    have : ∀ z, g z = g z₁ := fun z => le_antisymm (h ▸ hz₂' z) (hz₁' z)
    exact absurd (hinj ((this 1).trans (this (-1)).symm)) (by
      intro h'
      have := congrArg (fun z : Circle => (z : ℂ)) h'
      norm_num at this)
  obtain ⟨a, rfl⟩ := Circle.exp_surjective z₁
  obtain ⟨b₀, rfl⟩ := Circle.exp_surjective z₂
  -- a representative `b` of the second point in `(a, a + 2π)`
  set b : ℝ := toIcoMod Real.two_pi_pos a b₀ with hb
  have hbmem : b ∈ Ico a (a + 2 * π) := toIcoMod_mem_Ico Real.two_pi_pos a b₀
  have hbexp : Circle.exp b = Circle.exp b₀ := by
    rw [Circle.exp_eq_exp]
    refine ⟨-(toIcoDiv Real.two_pi_pos a b₀), ?_⟩
    have := self_sub_toIcoMod Real.two_pi_pos a b₀
    rw [← hb] at this
    simp only [zsmul_eq_mul] at this
    push_cast
    linarith
  have hmax : ∀ z, g z ≤ g (Circle.exp b) := by rw [hbexp]; exact hz₂'
  have hne' : Circle.exp a ≠ Circle.exp b := by rw [hbexp]; exact hne
  have hab : a < b := by
    rcases hbmem.1.eq_or_lt with h | h
    · exact absurd (by rw [← h]) hne'
    · exact h
  have hb2 : b < a + 2 * π := hbmem.2
  have hmM : g (Circle.exp a) < g (Circle.exp b) := lt_of_le_of_ne (hz₁' _) (fun h => hne' (hinj h))
  set h : ℝ → ℝ := fun s => g (Circle.exp s) with hh
  have hhc : Continuous h := hc.comp Circle.exp.continuous
  have h2π : h (a + 2 * π) = h a := by
    simp only [hh]
    congr 1
    rw [Circle.exp_eq_exp]
    exact ⟨1, by simp⟩
  have hv : (h a + h b) / 2 ∈ Icc (h a) (h b) := ⟨by simp only [hh]; linarith, by simp only [hh]; linarith⟩
  obtain ⟨s, hs, hsv⟩ := intermediate_value_Icc hab.le hhc.continuousOn hv
  have hv' : (h a + h b) / 2 ∈ Icc (h (a + 2 * π)) (h b) := by
    rw [h2π]; exact ⟨by simp only [hh] at hmM ⊢; linarith, by simp only [hh] at hmM ⊢; linarith⟩
  obtain ⟨s', hs', hs'v⟩ := intermediate_value_Icc' (by linarith : b ≤ a + 2 * π) hhc.continuousOn hv'
  have hss : Circle.exp s = Circle.exp s' := hinj (hsv.trans hs'v.symm)
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 hss
  have hπ := Real.pi_pos
  have hk1 : (k : ℝ) ≤ 0 := by nlinarith [hs.1, hs.2, hs'.1, hs'.2]
  have hk2 : (-1 : ℝ) ≤ k := by nlinarith [hs.1, hs.2, hs'.1, hs'.2]
  have hk3 : k = 0 ∨ k = -1 := by
    have : k ≤ 0 := by exact_mod_cast hk1
    have : -1 ≤ k := by exact_mod_cast hk2
    omega
  rcases hk3 with rfl | rfl
  · -- s = s'
    have hs0 : s = s' := by simpa using hk
    have : s = b := le_antisymm hs.2 (hs0 ▸ hs'.1)
    rw [this] at hsv
    simp only [hh] at hsv hmM
    linarith
  · have hsa : s = a := by
      have : s' = s + 2 * π := by simp at hk; linarith
      linarith [hs.1, hs'.2]
    rw [hsa] at hsv
    simp only [hh] at hsv hmM
    linarith

/-- The path along the arc of the circle from `exp s` to `exp t`, composed with `f`. -/
noncomputable def arcPath (f : Circle → ℂ) (hc : Continuous f) (s t : ℝ) : Path (f (Circle.exp s)) (f (Circle.exp t)) where
  toFun τ := f (Circle.exp (s + (τ : ℝ) * (t - s)))
  source' := by simp
  target' := by simp
  continuous_toFun := by
    have : Continuous fun τ : I => s + (τ : ℝ) * (t - s) := by fun_prop
    exact hc.comp (Circle.exp.continuous.comp this)

lemma range_arcPath (f : Circle → ℂ) (hc : Continuous f) {s t : ℝ} (hst : s < t) :
    range (arcPath f hc s t) = f '' (Circle.exp '' Icc s t) := by
  ext z
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨_, ⟨s + (τ : ℝ) * (t - s), ⟨by nlinarith [τ.2.1], by nlinarith [τ.2.2]⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨⟨(u - s) / (t - s), ⟨div_nonneg (by linarith [hu.1]) (by linarith), ?_⟩⟩, ?_⟩
    · rw [div_le_one (by linarith)]; linarith [hu.2]
    · show f (Circle.exp (s + (u - s) / (t - s) * (t - s))) = f (Circle.exp u)
      rw [div_mul_cancel₀ _ (by linarith : (t - s) ≠ 0)]; simp

lemma injective_arcPath (f : Circle → ℂ) (hc : Continuous f) (hi : Function.Injective f) {s t : ℝ}
    (hst : s < t) (hlen : t - s < 2 * π) : Function.Injective (arcPath f hc s t) := by
  intro x y h
  have h1 := hi h
  have hm : ∀ τ : I, s + (τ : ℝ) * (t - s) ∈ Icc s t := fun τ =>
    ⟨by nlinarith [τ.2.1], by nlinarith [τ.2.2]⟩
  have h2 := Circle.exp_injOn_Icc hlen (hm x) (hm y) h1
  apply Subtype.ext
  have : (x : ℝ) * (t - s) = y * (t - s) := by linarith
  exact mul_right_cancel₀ (by linarith) this

/-- **The topmost point of a Jordan curve**: a point of the curve with maximal imaginary part. -/
lemma exists_top {f : Circle → ℂ} (hc : Continuous f) : ∃ w, ∀ z, (f z).im ≤ (f w).im := by
  obtain ⟨w, -, hw⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := Circle))
    (Complex.continuous_im.comp hc).continuousOn
  exact ⟨w, fun z => hw (mem_univ z)⟩

/-- A Jordan curve is not contained in a vertical line. -/
lemma exists_off_vertical {f : Circle → ℂ} (hc : Continuous f) (hi : Function.Injective f) (x : ℝ) :
    ∃ z, (f z).re ≠ x := by
  by_contra hcon
  push Not at hcon
  refine not_injective_circle_real (fun z => (f z).im) (Complex.continuous_im.comp hc) fun z w h => hi ?_
  exact Complex.ext ((hcon z).trans (hcon w).symm) h

/-- **The first point of a compact set on a segment**: from a point `Ω` off a closed set `J` towards a point `c` of `J`
there is a first point `Q` of `J`, and the segment from `Q` back to `Ω` meets `J` only at `Q`. -/
lemma exists_visible {J : Set ℂ} (hJ : IsClosed J) {Ω c : ℂ} (hΩ : Ω ∉ J) (hc : c ∈ J) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ Ω + s₀ * (c - Ω) ∈ J ∧
      ∀ z ∈ segment ℝ (Ω + s₀ * (c - Ω)) Ω, z ∈ J → z = Ω + s₀ * (c - Ω) := by
  set K : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ Ω + s * (c - Ω) ∈ J} with hK
  have hKc : IsClosed K := by
    refine isClosed_Icc.inter (hJ.preimage ?_)
    fun_prop
  have h1K : (1 : ℝ) ∈ K := ⟨⟨zero_le_one, le_rfl⟩, by simpa using hc⟩
  have hs₀ : sInf K ∈ K := hKc.csInf_mem ⟨1, h1K⟩ ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf K with hs₀def
  have hs₀pos : 0 < s₀ := by
    rcases hs₀.1.1.eq_or_lt with h | h
    · exfalso
      have := hs₀.2
      rw [← h] at this
      simp at this
      exact hΩ this
    · exact h
  refine ⟨s₀, hs₀pos, hs₀.1.2, hs₀.2, ?_⟩
  rintro z ⟨a, b, ha, hb, hab, rfl⟩ hzJ
  have hz : a • (Ω + (s₀ : ℂ) * (c - Ω)) + b • Ω = Ω + ((a * s₀ : ℝ) : ℂ) * (c - Ω) := by
    have hb' : (b : ℂ) = 1 - a := by
      have : (a : ℂ) + b = 1 := by exact_mod_cast hab
      linear_combination this
    simp only [Complex.real_smul]
    push_cast
    rw [hb']
    ring
  rw [hz] at hzJ ⊢
  have hmem : a * s₀ ∈ K := ⟨⟨by positivity, by nlinarith [hs₀.1.2]⟩, hzJ⟩
  have hle : s₀ ≤ a * s₀ := csInf_le ⟨0, fun s hs => hs.1.1⟩ hmem
  have ha1 : a = 1 := by nlinarith
  have hb0 : b = 0 := by linarith
  subst ha1; subst hb0
  simp

/-- **A θ configuration at a prescribed point** (the geometry the notes leave to a picture): given a point `Ω` off a Jordan
curve, a point `P = f (exp a₀)` of the curve visible from `Ω` (the segment `PΩ` meets the curve only at `P`) and a point `c`
of the curve such that no point of the ray from `Ω` through `c` is `P`, the curve is split at `P` and at the first point
`Q` of the curve on the segment from `Ω` to `c` into two arcs `γ₁`, `γ₂`, giving a θ configuration with the point `Ω`. The
arcs are the images of the arcs `[a₀, b]` and `[b, a₀ + 2π]` of the circle. -/
theorem exists_theta_gen {f : Circle → ℂ} (hc : Continuous f) (hi : Function.Injective f) {Ω : ℂ}
    (hΩJ : Ω ∉ range f) (a₀ : ℝ)
    (hvis : ∀ z ∈ segment ℝ (f (Circle.exp a₀)) Ω, z ∈ range f → z = f (Circle.exp a₀))
    {c : ℂ} (hcJ : c ∈ range f) (hline : ∀ s : ℝ, 0 < s → Ω + (s : ℂ) * (c - Ω) ≠ f (Circle.exp a₀)) :
    ∃ T : Theta, range T.γ₁ ∪ range T.γ₂ = range f ∧ T.P = f (Circle.exp a₀) ∧ T.Ω = Ω ∧
      (∃ s₀ : ℝ, 0 < s₀ ∧ T.Q = Ω + (s₀ : ℂ) * (c - Ω)) ∧
      ∃ a b : ℝ, a < b ∧ b < a + 2 * π ∧ (∀ t : I, T.γ₁ t = f (Circle.exp (a + (t : ℝ) * (b - a)))) ∧
        (∀ t : I, T.γ₂ t = f (Circle.exp (b + (t : ℝ) * (a + 2 * π - b)))) := by
  classical
  set P := f (Circle.exp a₀) with hP
  have hJ : IsClosed (range f) := (isCompact_range hc).isClosed
  obtain ⟨s₀, hs₀pos, hs₀le, hQJ, hseg⟩ := exists_visible hJ hΩJ hcJ
  set Q := Ω + (s₀ : ℂ) * (c - Ω) with hQ
  obtain ⟨w₁, hw₁⟩ := hQJ
  obtain ⟨b₁, rfl⟩ := Circle.exp_surjective w₁
  have hQP : Q ≠ P := fun h => hline s₀ hs₀pos h
  -- the second representative in `(a₀, a₀ + 2π)`
  set b : ℝ := toIcoMod Real.two_pi_pos a₀ b₁ with hb
  have hbmem : b ∈ Ico a₀ (a₀ + 2 * π) := toIcoMod_mem_Ico Real.two_pi_pos a₀ b₁
  have hbexp : Circle.exp b = Circle.exp b₁ := by
    rw [Circle.exp_eq_exp]
    refine ⟨-(toIcoDiv Real.two_pi_pos a₀ b₁), ?_⟩
    have := self_sub_toIcoMod Real.two_pi_pos a₀ b₁
    rw [← hb] at this
    simp only [zsmul_eq_mul] at this
    push_cast
    linarith
  have hQb : Q = f (Circle.exp b) := by rw [hbexp]; exact hw₁.symm
  have hPb : P = f (Circle.exp (a₀ + 2 * π)) := by
    rw [hP]; congr 1; rw [Circle.exp_eq_exp]; exact ⟨-1, by simp⟩
  have hab : a₀ < b := by
    rcases hbmem.1.eq_or_lt with h | h
    · exfalso; apply hQP; rw [hQb, ← h]
    · exact h
  have hb2 : b < a₀ + 2 * π := hbmem.2
  let γ₁ : Path P Q := (arcPath f hc a₀ b).cast rfl hQb
  let γ₂ : Path Q P := (arcPath f hc b (a₀ + 2 * π)).cast hQb hPb
  have hr₁ : range γ₁ = f '' (Circle.exp '' Icc a₀ b) := range_arcPath f hc hab
  have hr₂ : range γ₂ = f '' (Circle.exp '' Icc b (a₀ + 2 * π)) := range_arcPath f hc hb2
  have hunion : range γ₁ ∪ range γ₂ = range f := by
    rw [hr₁, hr₂]
    ext z
    constructor
    · rintro (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> exact ⟨_, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨φ, rfl⟩ := Circle.exp_surjective w
      set φ' := toIcoMod Real.two_pi_pos a₀ φ with hφ'
      have hφmem : φ' ∈ Ico a₀ (a₀ + 2 * π) := toIcoMod_mem_Ico Real.two_pi_pos a₀ φ
      have hφexp : Circle.exp φ = Circle.exp φ' := by
        rw [Circle.exp_eq_exp]
        refine ⟨toIcoDiv Real.two_pi_pos a₀ φ, ?_⟩
        have := self_sub_toIcoMod Real.two_pi_pos a₀ φ
        rw [← hφ'] at this
        simp only [zsmul_eq_mul] at this
        linarith
      rw [hφexp]
      rcases le_total φ' b with h | h
      · exact Or.inl ⟨_, ⟨φ', ⟨hφmem.1, h⟩, rfl⟩, rfl⟩
      · exact Or.inr ⟨_, ⟨φ', ⟨h, hφmem.2.le⟩, rfl⟩, rfl⟩
  have hdisj : range γ₁ ∩ range γ₂ = {P, Q} := by
    rw [hr₁, hr₂]
    ext z
    constructor
    · rintro ⟨⟨_, ⟨u, hu, rfl⟩, rfl⟩, ⟨_, ⟨v, hv, rfl⟩, hvz⟩⟩
      have hss : Circle.exp v = Circle.exp u := hi hvz
      obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 hss
      have hπ := Real.pi_pos
      have hk1 : (k : ℝ) ≤ 1 := by nlinarith [hu.1, hu.2, hv.1, hv.2]
      have hk0 : (0 : ℝ) ≤ k := by nlinarith [hu.1, hu.2, hv.1, hv.2]
      have hk3 : k = 0 ∨ k = 1 := by
        have : k ≤ 1 := by exact_mod_cast hk1
        have : 0 ≤ k := by exact_mod_cast hk0
        omega
      rcases hk3 with rfl | rfl
      · have huv : v = u := by simpa using hk
        have hub : u = b := le_antisymm hu.2 (huv ▸ hv.1)
        right; rw [hub, ← hQb]; rfl
      · have huv : v = u + 2 * π := by simpa using hk
        have hua : u = a₀ := by linarith [hu.1, hv.2]
        left; rw [hua]
    · rintro (rfl | rfl)
      · exact ⟨⟨_, ⟨a₀, ⟨le_rfl, hab.le⟩, rfl⟩, rfl⟩, ⟨_, ⟨a₀ + 2 * π, ⟨hb2.le, le_rfl⟩, rfl⟩, hPb.symm⟩⟩
      · exact ⟨⟨_, ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, hQb.symm⟩, ⟨_, ⟨b, ⟨le_rfl, hb2.le⟩, rfl⟩, hQb.symm⟩⟩
  have hsegP : segment ℝ P Ω ∩ (range γ₁ ∪ range γ₂) = {P} := by
    rw [hunion]
    ext z
    constructor
    · rintro ⟨hz, hzJ⟩
      exact hvis z hz hzJ
    · rintro rfl
      exact ⟨left_mem_segment ℝ _ _, ⟨Circle.exp a₀, rfl⟩⟩
  have hsegQ : segment ℝ Q Ω ∩ (range γ₁ ∪ range γ₂) = {Q} := by
    rw [hunion]
    ext z
    constructor
    · rintro ⟨hz, hzJ⟩
      exact hseg z hz hzJ
    · rintro rfl
      exact ⟨left_mem_segment ℝ _ _, ⟨_, hw₁⟩⟩
  have hΩ : Ω ∉ range γ₁ ∪ range γ₂ := by rw [hunion]; exact hΩJ
  refine ⟨⟨P, Q, Ω, γ₁, γ₂, injective_arcPath f hc hi hab (by linarith), injective_arcPath f hc hi hb2 (by linarith),
    hdisj, hsegP, hsegQ, hΩ⟩, hunion, rfl, rfl, ⟨s₀, hs₀pos, rfl⟩, a₀, b, hab, hb2, ?_, ?_⟩
  · intro t; rfl
  · intro t; rfl

end Lightlike.PL
