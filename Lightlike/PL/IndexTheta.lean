import Lightlike.PL.ArcNotSeparating
import Lightlike.PL.IndexConstancy

/-!
# The θ configuration and Lemma 9.14

A Jordan curve `C` is split at two of its points `P`, `Q` into arcs `γ₁` from `P` to `Q` and `γ₂` from `Q` to `P`, and
`Ω` is a point off `C` such that the segments `PΩ` and `QΩ` meet `C` only at `P` and `Q` (`Theta`). The loops of the notes
are `ω₁ = γ₁ * (QΩ * ΩP)` and `ω₂ = (QΩ * ΩP)⁻¹ * γ₂`. **Lemma 9.14** (`Theta.lemma_9_14`): a point `R` off
`C ∪ PΩ ∪ QΩ` whose index about `ω₁` differs from that of a point of `γ₂`, or whose index about `ω₂` differs from that of
a point of `γ₁`, is joined to `Ω` by a path in the complement of `C`.

The proof is the notes': an arc does not separate the plane (`arc_not_separating`, transported to `ℂ` by
`joinedIn_compl_range`), so a path from `R` to `Ω` misses the arc; follow it to its first hit with the two segments
(`theta_core`); before it the index of the loop is constant (Lemma 9.13, `loopIndex_eq_of_joinedIn`), so the path cannot
meet the other arc, whose points all have the index of the given point, because the open arc is connected and avoids the
loop (`theta_arc`); then join to `Ω` along the segment.

This is Lemma 9.14 of chapter 9 of J. McCleary, *A First Course in Topology: Continuity and Dimension* (AMS, 2006); the
numbering is that of the lecture-notes version of the chapter
(`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`), not checked against the printed book. The notes
prove the case of `ω₁` and leave `ω₂` as symmetric; both are proved here. The statements and proofs are Lean's own.

## Main results

* `Theta`: the θ configuration, with the loops `Theta.ω₁`, `Theta.ω₂` and the curve `Theta.curve`.
* `joinedIn_compl_range`: an arc in `ℂ` does not separate two points off it.
* `theta_core`, `theta_arc`: the first-hit argument and its use for one arc.
* `Theta.lemma_9_14`: Lemma 9.14.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (the chapter location is verified with
  `scripts/sources.py verify`; the lemma-level numbering quoted above is that of the lecture-notes version and is
  not checked).
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

/-- The straight path from `a` to `b`. -/
noncomputable def segPath (a b : ℂ) : Path a b where
  toFun t := a + ((t : ℝ) : ℂ) * (b - a)
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop

lemma range_segPath (a b : ℂ) : Set.range (segPath a b) = segment ℝ a b := by
  rw [segment_eq_image']
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(t : ℝ), t.2, by simp [segPath, Complex.real_smul]⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, by simp [segPath, Complex.real_smul]⟩

lemma isClosed_segment_complex (a b : ℂ) : IsClosed (segment ℝ a b) := by
  rw [← range_segPath]; exact (isCompact_range (segPath a b).continuous).isClosed

/-- The starting point of a segment is not on the segment from any other point of it to the far end. -/
lemma start_not_mem_segment {P Ω z : ℂ} (hPΩ : P ≠ Ω) (hz : z ∈ segment ℝ P Ω) (hzP : z ≠ P) :
    P ∉ segment ℝ z Ω := by
  intro hP
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  obtain ⟨c, d, hc, hd, hcd, hP'⟩ := hP
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hzP
    obtain rfl : a = 1 := by linarith
    simp
  -- P = c (a P + b Ω) + d Ω
  have h1 : ((1 - c * a : ℝ) : ℂ) * P = ((c * b + d : ℝ) : ℂ) * Ω := by
    have h2 := hP'
    simp only [Complex.real_smul] at h2
    push_cast
    linear_combination -h2
  have h3 : (1 - c * a : ℝ) = c * b + d := by nlinarith
  have h4 : ((c * b + d : ℝ) : ℂ) * (P - Ω) = 0 := by
    rw [mul_sub, ← h1, h3]; ring
  rcases mul_eq_zero.1 h4 with h5 | h5
  · have h6 : c * b + d = 0 := by exact_mod_cast h5
    have h7 : d = 0 := by nlinarith [mul_nonneg hc hb]
    have h8 : c = 1 := by linarith
    have : b = 0 := by rw [h8, h7] at h6; linarith
    exact hb0 this
  · exact hPΩ (sub_eq_zero.1 h5)

/-- An initial piece of a path stays in a set: its start is joined to its value at the end of the piece. -/
lemma joinedIn_of_forall_le {a b : ℂ} (ζ : Path a b) (t₁ : I) {F : Set ℂ}
    (hF : ∀ t, t ≤ t₁ → ζ t ∈ F) : JoinedIn F a (ζ t₁) := by
  have hmul : Continuous fun s : I => s * t₁ := continuous_id.mul continuous_const
  let η : Path a (ζ t₁) := ⟨⟨fun s => ζ (s * t₁), ζ.continuous.comp hmul⟩, by simp, by simp⟩
  refine ⟨η, fun s => hF _ ?_⟩
  exact unitInterval.mul_le_right

/-- **The core of Lemma 9.14**: a path `ζ` from `R` to `Ω` that misses the arc `A`, followed to its first hit with the
two segments, cannot meet the other arc `B` before that hit if `R` and the points of `B` have different indices. -/
theorem theta_core {P Q Ω R y : ℂ} {A B : Set ℂ} (ω : Path P P)
    (hPΩ : P ≠ Ω) (hQΩ : Q ≠ Ω) (hPA : P ∈ A) (hQA : Q ∈ A)
    (hrange : Set.range ω = A ∪ (segment ℝ P Ω ∪ segment ℝ Q Ω))
    (hsegP : segment ℝ P Ω ∩ (A ∪ B) ⊆ {P}) (hsegQ : segment ℝ Q Ω ∩ (A ∪ B) ⊆ {Q})
    (hconst : ∀ z ∈ B, z ∉ A → loopIndex ω z = loopIndex ω y)
    (hA : JoinedIn Aᶜ R Ω) (hne : loopIndex ω R ≠ loopIndex ω y) :
    JoinedIn (A ∪ B)ᶜ R Ω := by
  classical
  set ζ := hA.somePath with hζ
  have hζA : ∀ t, ζ t ∉ A := fun t => hA.somePath_mem t
  set S : Set ℂ := segment ℝ P Ω ∪ segment ℝ Q Ω with hS
  have hSc : IsClosed S := (isClosed_segment_complex P Ω).union (isClosed_segment_complex Q Ω)
  set T : Set I := {t | ζ t ∈ S} with hT
  have hTc : IsClosed T := hSc.preimage ζ.continuous
  have h1T : (1 : I) ∈ T := by
    show ζ 1 ∈ S
    rw [ζ.target]; exact Or.inl (right_mem_segment ℝ P Ω)
  set t₁ := sInf T with ht₁
  have ht₁T : t₁ ∈ T := hTc.csInf_mem ⟨1, h1T⟩ (OrderBot.bddBelow T)
  have hlt : ∀ t, t < t₁ → ζ t ∉ S := fun t ht hS' =>
    absurd (csInf_le (OrderBot.bddBelow T) hS') (not_le.2 ht)
  have havoid : ∀ t, t < t₁ → ζ t ∉ Set.range ω := by
    intro t ht hmem
    rw [hrange] at hmem
    rcases hmem with h | h
    · exact hζA t h
    · exact hlt t ht h
  have hAB : ∀ t, t ≤ t₁ → ζ t ∉ A ∪ B := by
    intro t ht hmem
    rcases hmem with hA' | hB'
    · exact hζA t hA'
    · rcases lt_or_eq_of_le ht with hlt' | heq
      · have hj : JoinedIn (Set.range ω)ᶜ R (ζ t) :=
          joinedIn_of_forall_le ζ t (fun s hs => havoid s (lt_of_le_of_lt hs hlt'))
        have := loopIndex_eq_of_joinedIn ω hj
        exact hne (this.trans (hconst _ hB' (hζA t)))
      · subst heq
        rcases ht₁T with h | h
        · have := hsegP ⟨h, Or.inr hB'⟩
          rw [Set.mem_singleton_iff] at this
          exact hζA _ (this ▸ hPA)
        · have := hsegQ ⟨h, Or.inr hB'⟩
          rw [Set.mem_singleton_iff] at this
          exact hζA _ (this ▸ hQA)
  have hfirst : JoinedIn (A ∪ B)ᶜ R (ζ t₁) := by
    have := joinedIn_of_forall_le ζ t₁ (F := (A ∪ B)ᶜ) (fun s hs => hAB s hs)
    simpa using this
  refine hfirst.trans ?_
  rcases ht₁T with h | h
  · refine JoinedIn.of_segment_subset (fun w hw hwAB => ?_)
    have hsub : segment ℝ (ζ t₁) Ω ⊆ segment ℝ P Ω :=
      (convex_segment P Ω).segment_subset h (right_mem_segment ℝ P Ω)
    have hwP := hsegP ⟨hsub hw, hwAB⟩
    rw [Set.mem_singleton_iff] at hwP
    have hzP : ζ t₁ ≠ P := fun h' => hζA t₁ (h' ▸ hPA)
    exact start_not_mem_segment hPΩ h hzP (hwP ▸ hw)
  · refine JoinedIn.of_segment_subset (fun w hw hwAB => ?_)
    have hsub : segment ℝ (ζ t₁) Ω ⊆ segment ℝ Q Ω :=
      (convex_segment Q Ω).segment_subset h (right_mem_segment ℝ Q Ω)
    have hwQ := hsegQ ⟨hsub hw, hwAB⟩
    rw [Set.mem_singleton_iff] at hwQ
    have hzQ : ζ t₁ ≠ Q := fun h' => hζA t₁ (h' ▸ hQA)
    exact start_not_mem_segment hQΩ h hzQ (hwQ ▸ hw)

/-- **An arc in `ℂ` does not separate two points off it** (the arc theorem, transported from `ℝ × ℝ` to `ℂ`). -/
theorem joinedIn_compl_range {a b : ℂ} (γ : Path a b) (hγ : Function.Injective γ) {x y : ℂ}
    (hx : x ∉ range γ) (hy : y ∉ range γ) : JoinedIn (range γ)ᶜ x y := by
  let e := Complex.equivRealProdCLM
  let g : ℝ → ℝ × ℝ := fun r => e (γ (Set.projIcc (0 : ℝ) 1 zero_le_one r))
  have hgc : Continuous g :=
    e.continuous.comp (γ.continuous.comp (continuous_projIcc (h := zero_le_one)))
  have hg : IsArc (g '' Icc 0 1) (e a) (e b) := by
    refine ⟨g, hgc.continuousOn, ?_, ?_, ?_, rfl⟩
    · intro r hr s hs h
      have h1 := hγ (e.injective h)
      have h2 := congrArg Subtype.val h1
      simpa [Set.projIcc_of_mem _ hr, Set.projIcc_of_mem _ hs] using h2
    · simp [g]
    · simp [g]
  have himg : g '' Icc 0 1 = e '' range γ := by
    ext z
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨(t : ℝ), t.2, by simp [g, Set.projIcc_val]⟩
  have hpre := arc_not_separating hg
  rw [himg] at hpre
  have hpre' : IsPreconnected (range γ)ᶜ := by
    have h1 := (e.toHomeomorph.isPreconnected_preimage (s := (e '' range γ)ᶜ)).2 hpre
    have h2 : e.toHomeomorph ⁻¹' (e '' range γ)ᶜ = (range γ)ᶜ := by
      ext z
      simp [e.injective.eq_iff]
    rwa [h2] at h1
  have hopen : IsOpen (range γ)ᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hconn : IsConnected (range γ)ᶜ := ⟨⟨x, hx⟩, hpre'⟩
  exact (hopen.isConnected_iff_isPathConnected.1 hconn).joinedIn x hx y hy

/-- **The core of Lemma 9.14 for one arc**: in the θ configuration, with `A = γA` the arc that the path `ζ` avoids and
`B = γB` the other arc, if `R` has an index about the loop `ω` different from that of a point `y` of `B`, then `R` is
joined to `Ω` in the complement of the whole curve. -/
theorem theta_arc {a b P Q Ω R y : ℂ} (γA : Path a b) (γB : Path b a)
    (hA_inj : Function.Injective γA) (hB_inj : Function.Injective γB)
    (hends : ({a, b} : Set ℂ) = {P, Q}) (disj : range γA ∩ range γB = {a, b})
    (hPΩ : P ≠ Ω) (hQΩ : Q ≠ Ω) (ω : Path P P)
    (hrange : range ω = range γA ∪ (segment ℝ P Ω ∪ segment ℝ Q Ω))
    (hsegP : segment ℝ P Ω ∩ (range γA ∪ range γB) ⊆ {P})
    (hsegQ : segment ℝ Q Ω ∩ (range γA ∪ range γB) ⊆ {Q})
    (hy : y ∈ range γB) (hyA : y ∉ range γA) (hR : R ∉ range γA) (hΩ : Ω ∉ range γA)
    (hne : loopIndex ω R ≠ loopIndex ω y) : JoinedIn (range γA ∪ range γB)ᶜ R Ω := by
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
  have hconst : ∀ z ∈ range γB, z ∉ range γA → loopIndex ω z = loopIndex ω y := by
    intro z hz hzA
    obtain ⟨r, hr, rfl⟩ := hinner z hz hzA
    obtain ⟨s, hs, rfl⟩ := hinner y hy hyA
    have hpc : IsPathConnected (g '' Ioo (0 : ℝ) 1) :=
      ((convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by norm_num, by norm_num⟩).image hgc
    have hj : JoinedIn (g '' Ioo (0 : ℝ) 1) (g r) (g s) := hpc.joinedIn _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    exact loopIndex_eq_of_joinedIn ω (hj.mono (by
      rintro _ ⟨t, ht, rfl⟩; exact havoid t ht))
  have hA : JoinedIn (range γA)ᶜ R Ω := joinedIn_compl_range γA hA_inj hR hΩ
  exact theta_core ω hPΩ hQΩ hPA hQA hrange hsegP hsegQ hconst hA hne

/-- **The θ configuration** (chapter 9 of the notes, before Lemma 9.14): a Jordan curve split at two of its points `P`, `Q`
into an arc `γ₁` from `P` to `Q` and an arc `γ₂` from `Q` to `P` that meet only at `P` and `Q`, and a point `Ω` off the
curve such that the segments `PΩ` and `QΩ` meet the curve only at `P` and `Q`. -/
structure Theta where
  /-- The first end of the arcs. -/
  P : ℂ
  /-- The second end of the arcs. -/
  Q : ℂ
  /-- The point off the curve. -/
  Ω : ℂ
  /-- The arc from `P` to `Q`. -/
  γ₁ : Path P Q
  /-- The arc from `Q` to `P`. -/
  γ₂ : Path Q P
  /-- The first arc is injective. -/
  inj₁ : Function.Injective γ₁
  /-- The second arc is injective. -/
  inj₂ : Function.Injective γ₂
  /-- The two arcs meet only at their ends. -/
  disj : range γ₁ ∩ range γ₂ = {P, Q}
  /-- The segment from `P` to `Ω` meets the curve only at `P`. -/
  segP : segment ℝ P Ω ∩ (range γ₁ ∪ range γ₂) = {P}
  /-- The segment from `Q` to `Ω` meets the curve only at `Q`. -/
  segQ : segment ℝ Q Ω ∩ (range γ₁ ∪ range γ₂) = {Q}
  /-- The point `Ω` is not on the curve. -/
  hΩ : Ω ∉ range γ₁ ∪ range γ₂

namespace Theta

variable (T : Theta)

/-- The curve `C = γ₁ ∪ γ₂`. -/
def curve : Set ℂ := range T.γ₁ ∪ range T.γ₂

/-- The path `l₁ * l₂` of the notes, from `Q` through `Ω` to `P`. -/
noncomputable def through : Path T.Q T.P := (segPath T.Q T.Ω).trans (segPath T.Ω T.P)

/-- The loop `ω₁ = γ₁ * (l₁ * l₂)` of the notes: along the curve from `P` to `Q`, then through `Ω` back to `P`. -/
noncomputable def ω₁ : Path T.P T.P := T.γ₁.trans T.through

/-- The loop `ω₂ = (l₁ * l₂)⁻¹ * γ₂` of the notes: from `P` through `Ω` to `Q`, then along the curve back to `P`. -/
noncomputable def ω₂ : Path T.P T.P := T.through.symm.trans T.γ₂

lemma P_mem : T.P ∈ range T.γ₁ := ⟨0, T.γ₁.source⟩
lemma Q_mem : T.Q ∈ range T.γ₁ := ⟨1, T.γ₁.target⟩

lemma P_ne_Ω : T.P ≠ T.Ω := fun h => T.hΩ (Or.inl (h ▸ T.P_mem))
lemma Q_ne_Ω : T.Q ≠ T.Ω := fun h => T.hΩ (Or.inl (h ▸ T.Q_mem))

lemma range_through : range T.through = segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω := by
  rw [through, Path.trans_range, range_segPath, range_segPath, segment_symm ℝ T.Ω T.P, Set.union_comm]

lemma range_ω₁ : range T.ω₁ = range T.γ₁ ∪ (segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω) := by
  rw [ω₁, Path.trans_range, range_through]

lemma range_ω₂ : range T.ω₂ = range T.γ₂ ∪ (segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω) := by
  rw [ω₂, Path.trans_range, Path.symm_range, range_through, Set.union_comm]

/-- **Lemma 9.14 of the notes** (chapter 9, the lemma that joins a point to `Ω` when its indices differ from those of
a point on each arc). Let `x` be a point of `γ₁` and `y` a point of `γ₂`, both different from `P` and `Q`. If `R` is a point
off `C ∪ PΩ ∪ QΩ` with `ind_R(ω₁) ≠ ind_y(ω₁)` or `ind_R(ω₂) ≠ ind_x(ω₂)`, then `R` is joined to `Ω` by a path in the
complement of `C`. The proof is the notes': an arc does not separate the plane (`arc_not_separating`), so a path from `R` to
`Ω` avoids the arc `γ₁` (resp. `γ₂`); follow it to its first hit with the segments; before it, the index of `ω₁` (resp.
`ω₂`) is constant (Lemma 9.13), so it cannot meet the other arc, whose points have the index of `y` (resp. `x`);
then join to `Ω` along the segment. -/
theorem lemma_9_14 {x y R : ℂ} (hx : x ∈ range T.γ₁) (hxP : x ≠ T.P) (hxQ : x ≠ T.Q)
    (hy : y ∈ range T.γ₂) (hyP : y ≠ T.P) (hyQ : y ≠ T.Q)
    (hR : R ∉ T.curve ∪ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω)
    (hne : loopIndex T.ω₁ R ≠ loopIndex T.ω₁ y ∨ loopIndex T.ω₂ R ≠ loopIndex T.ω₂ x) :
    JoinedIn T.curveᶜ R T.Ω := by
  have hy₁ : y ∉ range T.γ₁ := fun h => by
    have : y ∈ ({T.P, T.Q} : Set ℂ) := T.disj ▸ ⟨h, hy⟩
    rcases this with h' | h' <;> [exact hyP h'; exact hyQ h']
  have hx₂ : x ∉ range T.γ₂ := fun h => by
    have : x ∈ ({T.P, T.Q} : Set ℂ) := T.disj ▸ ⟨hx, h⟩
    rcases this with h' | h' <;> [exact hxP h'; exact hxQ h']
  have hR₁ : R ∉ range T.γ₁ := fun h => hR (Or.inl (Or.inl (Or.inl h)))
  have hR₂ : R ∉ range T.γ₂ := fun h => hR (Or.inl (Or.inl (Or.inr h)))
  have hΩ₁ : T.Ω ∉ range T.γ₁ := fun h => T.hΩ (Or.inl h)
  have hΩ₂ : T.Ω ∉ range T.γ₂ := fun h => T.hΩ (Or.inr h)
  rcases hne with h | h
  · exact theta_arc T.γ₁ T.γ₂ T.inj₁ T.inj₂ rfl T.disj T.P_ne_Ω T.Q_ne_Ω T.ω₁ T.range_ω₁
      (fun w hw => T.segP ▸ hw) (fun w hw => T.segQ ▸ hw) hy hy₁ hR₁ hΩ₁ h
  · have := theta_arc T.γ₂ T.γ₁ T.inj₂ T.inj₁ (Set.pair_comm _ _) (by rw [Set.inter_comm, T.disj, Set.pair_comm])
      T.P_ne_Ω T.Q_ne_Ω T.ω₂ T.range_ω₂
      (fun w hw => T.segP ▸ (by rwa [Set.union_comm] at hw)) (fun w hw => T.segQ ▸ (by rwa [Set.union_comm] at hw))
      hx hx₂ hR₂ hΩ₂ h
    rwa [Set.union_comm] at this

end Theta

end Lightlike.PL
