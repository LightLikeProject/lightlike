import Lightlike.PL.ArcTrim
import Lightlike.PL.K33

/-!
# No drawing of `K₃,₃` by continuous arcs

## Main results

* `ContDrawing`: a drawing of `K₃,₃` in the plane by continuous injective arcs.
* `no_K33`: there is none.
-/

open Set

namespace Lightlike.PL

/-- Two segments from the same centre to two different points of the sphere of radius `r` meet only
at the centre. -/
lemma segment_inter_sphere {c q q' y : ℝ × ℝ} {r : ℝ} (hr : 0 < r) (hq : dist q c = r)
    (hq' : dist q' c = r) (hne : q ≠ q') (h1 : y ∈ segment ℝ c q) (h2 : y ∈ segment ℝ c q') :
    y = c := by
  rw [segment_eq_image'] at h1 h2
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := h1
  obtain ⟨s', ⟨hs0', hs1'⟩, hs⟩ := h2
  have hn : s * r = s' * r := by
    have := congrArg (fun z => ‖z - c‖) hs
    simp only [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0, Real.norm_of_nonneg hs0'] at this
    rw [← dist_eq_norm, ← dist_eq_norm, hq, hq'] at this
    exact this.symm
  have hss : s = s' := mul_right_cancel₀ hr.ne' hn
  subst hss
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; simp
  · exfalso
    apply hne
    have : s • (q - c) = s • (q' - c) := by
      have := hs
      simpa using this.symm
    have := smul_right_injective _ h.ne' this
    simpa using this

/-- The set of the chain `x, h, y`, when `h` goes from `α` to `β`. -/
lemma chainSet_ends {x y α β : ℝ × ℝ} {h : List (ℝ × ℝ)} (h1 : h.head? = some α)
    (h2 : h.getLast? = some β) :
    chainSet (x :: h ++ [y]) = segment ℝ x α ∪ chainSet h ∪ segment ℝ β y := by
  obtain ⟨m, rfl⟩ : ∃ m, h = α :: m := by
    rcases h with _ | ⟨a, m⟩
    · simp at h1
    · simp only [List.head?_cons, Option.some.injEq] at h1; subst h1; exact ⟨m, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m', α :: m = m' ++ [β] := by
    rcases List.eq_nil_or_concat (α :: m) with h | ⟨L, b, hL⟩
    · simp at h
    · rw [hL] at h2
      rw [List.concat_eq_append, List.getLast?_concat, Option.some.injEq] at h2
      subst h2
      exact ⟨L, by rw [hL, List.concat_eq_append]⟩
  have e2 : α :: (m ++ [y]) = m' ++ β :: [y] := by
    have := congrArg (· ++ [y]) hm'
    simpa using this
  have e3 : chainSet (x :: α :: m ++ [y]) = segment ℝ x α ∪ chainSet (α :: (m ++ [y])) := by
    have : x :: α :: m ++ [y] = x :: α :: (m ++ [y]) := by simp
    rw [this]; rfl
  rw [e3, e2, chainSet_append m' β [y], chainSet_pair, ← hm', union_assoc]

/-- A **drawing of `K₃,₃` by continuous arcs**: six distinct points `u i`, `v j` and nine injective
continuous arcs `γ i j : [0, 1] → ℝ²` from `u i` to `v j` that meet only in common endpoints. -/
structure ContDrawing where
  /-- The three points of the first class. -/
  u : Fin 3 → ℝ × ℝ
  /-- The three points of the second class. -/
  v : Fin 3 → ℝ × ℝ
  /-- The arc from `u i` to `v j`, as a map on `[0, 1]`. -/
  γ : Fin 3 → Fin 3 → ℝ → ℝ × ℝ
  /-- Each arc is continuous. -/
  cont : ∀ i j, ContinuousOn (γ i j) (Icc 0 1)
  /-- Each arc is injective. -/
  inj : ∀ i j, InjOn (γ i j) (Icc 0 1)
  /-- Each arc starts at `u i`. -/
  start : ∀ i j, γ i j 0 = u i
  /-- Each arc ends at `v j`. -/
  stop : ∀ i j, γ i j 1 = v j
  /-- Two different arcs meet only in common endpoints. -/
  disj : ∀ i j i' j', (i, j) ≠ (i', j') →
    γ i j '' Icc 0 1 ∩ γ i' j' '' Icc 0 1 ⊆ {u i, v j} ∩ {u i', v j'}
  /-- The three points of the first class are distinct. -/
  inj_u : Function.Injective u
  /-- The three points of the second class are distinct. -/
  inj_v : Function.Injective v
  /-- The two classes are disjoint. -/
  uv_ne : ∀ i j, u i ≠ v j

namespace ContDrawing

variable (D : ContDrawing)

/-- The six points, indexed by the two classes. -/
def w : Fin 3 ⊕ Fin 3 → ℝ × ℝ := Sum.elim D.u D.v

lemma w_inj : Function.Injective D.w := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (D.inj_u h)
  · exact absurd h (D.uv_ne _ _)
  · exact absurd h.symm (D.uv_ne _ _)
  · exact congrArg Sum.inr (D.inj_v h)

/-- The ends of the edge `e`: the vertex `inl e.1` for `false`, `inr e.2` for `true`. -/
def ep (e : Fin 3 × Fin 3) : Bool → Fin 3 ⊕ Fin 3
  | false => Sum.inl e.1
  | true => Sum.inr e.2

/-- A vertex that is not an end of the edge `e` is not on the arc `e`. -/
lemma w_notMem {e : Fin 3 × Fin 3} {x : Fin 3 ⊕ Fin 3} (h : ∀ k, x ≠ ep e k) :
    D.w x ∉ D.γ e.1 e.2 '' Icc 0 1 := by
  intro hx
  rcases x with i | j
  · have h0 : D.w (Sum.inl i) ∈ D.γ i 0 '' Icc 0 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, D.start i 0⟩
    have hne : (e.1, e.2) ≠ (i, 0) := fun h' => h false (by simp [ep]; exact (congrArg Prod.fst h').symm)
    have := D.disj _ _ _ _ hne ⟨hx, h0⟩
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at this
    rcases this.1 with h1 | h1
    · exact h false (by simp [ep]; exact D.inj_u h1)
    · exact D.uv_ne _ _ (by simpa [w] using h1)
  · have h0 : D.w (Sum.inr j) ∈ D.γ 0 j '' Icc 0 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, D.stop 0 j⟩
    have hne : (e.1, e.2) ≠ (0, j) := fun h' => h true (by simp [ep]; exact (congrArg Prod.snd h').symm)
    have := D.disj _ _ _ _ hne ⟨hx, h0⟩
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at this
    rcases this.1 with h1 | h1
    · exact D.uv_ne _ _ (by simpa [w] using h1.symm)
    · exact h true (by simp [ep]; exact D.inj_v h1)

/-- A radius `r` such that the closed balls of radius `r` around the six points are disjoint and an
arc keeps a distance larger than `r` from the points that are not its ends. -/
lemma exists_radius : ∃ r : ℝ, 0 < r ∧ (∀ x x', x ≠ x' → 2 * r < dist (D.w x) (D.w x')) ∧
    ∀ e x, (∀ k, x ≠ ep e k) → ∀ t ∈ Icc (0 : ℝ) 1, r < dist (D.γ e.1 e.2 t) (D.w x) := by
  have hpos : ∀ p : ((Fin 3 ⊕ Fin 3) × (Fin 3 ⊕ Fin 3)) ⊕ ((Fin 3 × Fin 3) × (Fin 3 ⊕ Fin 3)),
      ∃ m : ℝ, 0 < m ∧ (∀ x x', p = Sum.inl (x, x') → x ≠ x' → m ≤ dist (D.w x) (D.w x')) ∧
        ∀ e x, p = Sum.inr (e, x) → (∀ k, x ≠ ep e k) → ∀ t ∈ Icc (0 : ℝ) 1,
          m ≤ dist (D.γ e.1 e.2 t) (D.w x) := by
    rintro (⟨x, x'⟩ | ⟨e, x⟩)
    · by_cases hx : x = x'
      · exact ⟨1, one_pos, fun a b h h' => by
          simp only [Sum.inl.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact absurd hx h',
          fun _ _ h => by simp at h⟩
      · exact ⟨dist (D.w x) (D.w x'), dist_pos.2 (fun h => hx (D.w_inj h)), fun a b h _ => by
          simp only [Sum.inl.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact le_rfl,
          fun _ _ h => by simp at h⟩
    · by_cases hx : ∀ k, x ≠ ep e k
      · have hc : IsCompact (D.γ e.1 e.2 '' Icc 0 1) := isCompact_Icc.image_of_continuousOn (D.cont _ _)
        have hcont : ContinuousOn (fun t => dist (D.γ e.1 e.2 t) (D.w x)) (Icc 0 1) :=
          (by fun_prop : Continuous fun p : ℝ × ℝ => dist p (D.w x)).comp_continuousOn (D.cont _ _)
        obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, zero_le_one⟩ hcont
        refine ⟨dist (D.γ e.1 e.2 t0) (D.w x), dist_pos.2 ?_, fun _ _ h => by simp at h, ?_⟩
        · intro h
          exact D.w_notMem hx ⟨t0, ht0, h⟩
        · intro a b h _ t ht
          simp only [Sum.inr.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hmin ht
      · exact ⟨1, one_pos, fun _ _ h => by simp at h, fun a b h h' => absurd (by
          simp only [Sum.inr.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact h') hx⟩
  choose m hm0 hm1 hm2 using hpos
  obtain ⟨p0, hp0⟩ := Finite.exists_min m
  refine ⟨m p0 / 3, by have := hm0 p0; positivity, fun x x' hxx => ?_, fun e x hx t ht => ?_⟩
  · have := hm1 (Sum.inl (x, x')) x x' rfl hxx
    have := hp0 (Sum.inl (x, x'))
    have := hm0 p0
    linarith
  · have := hm2 (Sum.inr (e, x)) e x rfl hx t ht
    have := hp0 (Sum.inr (e, x))
    have := hm0 p0
    linarith

/-- The trimmed subarcs: a subarc of each arc that starts and ends on the spheres of radius `r` around
its ends and keeps distance at least `r` from all six points. -/
lemma exists_trims {r : ℝ} (hr : 0 < r) (h2 : ∀ x x', x ≠ x' → 2 * r < dist (D.w x) (D.w x'))
    (h3 : ∀ e x, (∀ k, x ≠ ep e k) → ∀ t ∈ Icc (0 : ℝ) 1, r < dist (D.γ e.1 e.2 t) (D.w x)) :
    ∃ s t : Fin 3 × Fin 3 → ℝ, ∀ e, 0 ≤ s e ∧ s e < t e ∧ t e ≤ 1 ∧
      dist (D.γ e.1 e.2 (s e)) (D.w (ep e false)) = r ∧
      dist (D.γ e.1 e.2 (t e)) (D.w (ep e true)) = r ∧
      ∀ τ ∈ Icc (s e) (t e), ∀ x, r ≤ dist (D.γ e.1 e.2 τ) (D.w x) := by
  have : ∀ e : Fin 3 × Fin 3, ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
      dist (D.γ e.1 e.2 s) (D.w (ep e false)) = r ∧
      dist (D.γ e.1 e.2 t) (D.w (ep e true)) = r ∧
      ∀ τ ∈ Icc s t, ∀ x, r ≤ dist (D.γ e.1 e.2 τ) (D.w x) := fun e => by
    obtain ⟨s, t, hs0, hst, ht1, hs, ht, hu⟩ := exists_trim (D.cont e.1 e.2)
      (pa := D.w (ep e false)) (pb := D.w (ep e true)) (r := r)
      (by simpa [ep, w] using D.start e.1 e.2) (by simpa [ep, w] using D.stop e.1 e.2) hr
      (h2 _ _ (by simp [ep]))
    refine ⟨s, t, hs0, hst, ht1, hs, ht, fun τ hτ x => ?_⟩
    by_cases hx : ∀ k, x ≠ ep e k
    · exact (h3 e x hx τ ⟨le_trans hs0 hτ.1, le_trans hτ.2 ht1⟩).le
    · push Not at hx
      obtain ⟨k, rfl⟩ := hx
      cases k
      · exact (hu τ hτ).1
      · exact (hu τ hτ).2
  choose s t hs using this
  exact ⟨s, t, hs⟩

/-- Two different trimmed subarcs are at positive distance. -/
lemma exists_eps {r : ℝ} (hr : 0 < r) (s t : Fin 3 × Fin 3 → ℝ)
    (hst : ∀ e, 0 ≤ s e ∧ s e < t e ∧ t e ≤ 1 ∧
      ∀ τ ∈ Icc (s e) (t e), ∀ x, r ≤ dist (D.γ e.1 e.2 τ) (D.w x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ e e', e ≠ e' → ∀ y ∈ D.γ e.1 e.2 '' Icc (s e) (t e),
      ∀ y' ∈ D.γ e'.1 e'.2 '' Icc (s e') (t e'), 2 * ε < dist y y' := by
  have hsub : ∀ e, Icc (s e) (t e) ⊆ Icc (0 : ℝ) 1 := fun e =>
    Icc_subset_Icc (hst e).1 (hst e).2.2.1
  have hcomp : ∀ e, IsCompact (D.γ e.1 e.2 '' Icc (s e) (t e)) := fun e =>
    isCompact_Icc.image_of_continuousOn ((D.cont _ _).mono (hsub e))
  have hpos : ∀ p : (Fin 3 × Fin 3) × (Fin 3 × Fin 3), ∃ η : ℝ, 0 < η ∧ (p.1 ≠ p.2 →
      ∀ y ∈ D.γ p.1.1 p.1.2 '' Icc (s p.1) (t p.1), ∀ y' ∈ D.γ p.2.1 p.2.2 '' Icc (s p.2) (t p.2),
        η ≤ dist y y') := by
    rintro ⟨e, e'⟩
    by_cases he : e = e'
    · exact ⟨1, one_pos, fun h => absurd he h⟩
    · have hne : (D.γ e.1 e.2 '' Icc (s e) (t e)).Nonempty :=
        ⟨_, ⟨s e, ⟨le_rfl, (hst e).2.1.le⟩, rfl⟩⟩
      have hne' : (D.γ e'.1 e'.2 '' Icc (s e') (t e')).Nonempty :=
        ⟨_, ⟨s e', ⟨le_rfl, (hst e').2.1.le⟩, rfl⟩⟩
      obtain ⟨⟨y0, y0'⟩, ⟨hy0, hy0'⟩, hmin⟩ := ((hcomp e).prod (hcomp e')).exists_isMinOn
        (hne.prod hne') (by fun_prop : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) => dist q.1 q.2).continuousOn
      refine ⟨dist y0 y0', dist_pos.2 fun h => ?_, fun _ y hy y' hy' => hmin (⟨hy, hy'⟩ :
        (y, y') ∈ (D.γ e.1 e.2 '' Icc (s e) (t e)) ×ˢ (D.γ e'.1 e'.2 '' Icc (s e') (t e')))⟩
      subst h
      obtain ⟨τ, hτ, rfl⟩ := hy0
      obtain ⟨τ', hτ', hτ'e⟩ := hy0'
      have hmem := D.disj e.1 e.2 e'.1 e'.2 (fun h => he (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)))
        ⟨⟨τ, hsub e hτ, rfl⟩, ⟨τ', hsub e' hτ', hτ'e⟩⟩
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hmem
      rcases hmem.1 with h1 | h1
      · have := (hst e).2.2.2 τ hτ (Sum.inl e.1)
        rw [h1] at this
        simp [w] at this; linarith
      · have := (hst e).2.2.2 τ hτ (Sum.inr e.2)
        rw [h1] at this
        simp [w] at this; linarith
  choose η hη0 hη using hpos
  obtain ⟨p0, hp0⟩ := Finite.exists_min η
  refine ⟨η p0 / 3, by have := hη0 p0; positivity, fun e e' hee y hy y' hy' => ?_⟩
  have := hη (e, e') hee y hy y' hy'
  have := hp0 (e, e')
  have := hη0 p0
  linarith

end ContDrawing

end Lightlike.PL
