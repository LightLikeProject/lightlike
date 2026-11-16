import Lightlike.PL.ArcDensity
import Lightlike.PL.ContK33
import Lightlike.PL.WeakJordanLink
import Lightlike.PL.WeakJordanCircle
import Lightlike.PL.TwoArcs

/-!
# A Jordan curve is approximated by a simple polygon

For every `ε > 0`, the image of a continuous injective map of the circle into the plane has a
simple closed polygon whose carrier is within `ε` of the curve in both directions
(`exists_polygon_near`). The circle is cut into two arcs; each is trimmed near the two cut points,
approximated by a simple chain, joined to the cut points by segments, and loop erased; the two chains
meet only at the cut points (`exists_two_chains`), and the loop erasure does not lose any part of the
arc (`two_way_near`, from `arc_density`).

## Main results

* `exists_two_chains`: two arcs from `a` to `b` that meet only at their ends have two simple chains
  from `a` to `b` that meet only at their ends, each within `ε` of its arc in both directions.
* `exists_polygon_near`: the approximation of a Jordan curve by a simple polygon.
-/

open Set

namespace Lightlike.PL

/-- A chain is compact. -/
lemma isCompact_chainSet : ∀ l : List (ℝ × ℝ), IsCompact (chainSet l)
  | [] => by simp [chainSet]
  | [a] => by simp [chainSet]
  | a :: b :: l => by
    simp only [chainSet]
    exact (isCompact_segment' ..).union (isCompact_chainSet (b :: l))

/-- The first point of a chain is in its set. -/
lemma head_mem_chainSet {l : List (ℝ × ℝ)} {a : ℝ × ℝ} (h : l.head? = some a) : a ∈ chainSet l := by
  rcases l with _ | ⟨x, c⟩
  · simp at h
  · simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact mem_chainSet_head _ _

/-- The last point of a chain is in its set. -/
lemma last_mem_chainSet' {l : List (ℝ × ℝ)} {b : ℝ × ℝ} (h : l.getLast? = some b) :
    b ∈ chainSet l := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, c, hL⟩
  · simp at h
  · rw [hL, List.concat_eq_append, List.getLast?_concat, Option.some.injEq] at h
    subst h
    rw [hL, List.concat_eq_append]
    exact mem_chainSet_last L c

/-- A simple chain close to a subarc. -/
lemma exists_chain_on {γ : ℝ → ℝ × ℝ} (hc : ContinuousOn γ (Icc 0 1)) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (ht : t ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : List (ℝ × ℝ), IsSimpleChain h ∧ h.head? = some (γ s) ∧ h.getLast? = some (γ t) ∧
      ∀ y ∈ chainSet h, ∃ τ ∈ Icc s t, dist y (γ τ) < ε := by
  have hmap : ∀ τ ∈ Icc (0 : ℝ) 1, s + τ * (t - s) ∈ Icc s t := fun τ hτ =>
    ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs ht
  have hc' : ContinuousOn (fun τ => γ (s + τ * (t - s))) (Icc 0 1) :=
    (hc.mono hsub).comp (by fun_prop) hmap
  obtain ⟨l, hl, h1, h2, h3⟩ := exists_simple_chain_near hc' hε
  refine ⟨l, hl, by simpa using h1, by simpa using h2, fun y hy => ?_⟩
  obtain ⟨τ, hτ, hd⟩ := h3 y hy
  exact ⟨_, hmap τ hτ, hd⟩

/-- A simple chain from `a` to `b` inside the segment, the chain `h` and the segment. -/
lemma exists_join_chain {a b α β : ℝ × ℝ} {h : List (ℝ × ℝ)} (hl : h.head? = some α)
    (hl2 : h.getLast? = some β) :
    ∃ c : List (ℝ × ℝ), IsSimpleChain c ∧ c.head? = some a ∧ c.getLast? = some b ∧
      chainSet c ⊆ segment ℝ a α ∪ chainSet h ∪ segment ℝ β b := by
  have hset := chainSet_ends (x := a) (y := b) hl hl2
  obtain ⟨c, hc, hc1, hc2, hc3⟩ := exists_simple_sub (a :: h ++ [b]) a b (by simp)
    (List.getLast?_concat ..)
  exact ⟨c, hc, hc1, hc2, hset ▸ hc3⟩

/-- Uniform continuity of an arc, in the form used for scales. -/
lemma arc_unif {γ : ℝ → ℝ × ℝ} (hc : ContinuousOn γ (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| < θ →
      dist (γ s) (γ t) < ε := by
  obtain ⟨θ, hθ, h⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  exact ⟨θ, hθ, fun s hs t ht hst => h s hs t ht (by rwa [Real.dist_eq])⟩

/-- Two disjoint nonempty compact sets are at positive distance. -/
lemma exists_sep {K L : Set (ℝ × ℝ)} (hK : IsCompact K) (hL : IsCompact L) (hKn : K.Nonempty)
    (hLn : L.Nonempty) (hd : ∀ y ∈ K, y ∉ L) : ∃ η : ℝ, 0 < η ∧ ∀ y ∈ K, ∀ y' ∈ L, η ≤ dist y y' := by
  obtain ⟨⟨y, y'⟩, ⟨hy, hy'⟩, hmin⟩ := (hK.prod hL).exists_isMinOn (hKn.prod hLn)
    (by fun_prop : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) => dist q.1 q.2).continuousOn
  refine ⟨dist y y', dist_pos.2 fun h => hd y hy (h ▸ hy'), fun u hu v hv => ?_⟩
  exact hmin (show (u, v) ∈ K ×ˢ L from ⟨hu, hv⟩)

/-- A point of a chain near the trimmed subarc cannot lie on the segment from a vertex to the end
of a different trimmed subarc. -/
lemma chain_not_on_segment {p α g y : ℝ × ℝ} {r η ε'' : ℝ} (hα : dist α p = r)
    (hgp : r ≤ dist g p) (hgα : η ≤ dist g α) (hε : 3 * ε'' ≤ η) (hη : 0 < η)
    (hy : dist y g < ε'') (hseg : y ∈ segment ℝ p α) : False := by
  have hsum := dist_add_dist_of_mem_segment hseg
  have c1 := dist_comm p α
  have c2 := dist_comm g p
  have h1 := dist_triangle g y p
  have h2 := dist_triangle g y α
  have c3 := dist_comm y g
  have c4 := dist_comm y p
  have c5 := dist_comm y α
  have c6 := dist_comm p y
  have : 0 < ε'' := by linarith
  linarith

/-- **The pieces of the two chains meet only at the ends.** -/
lemma pieces_inter {a b α₀ β₀ α₁ β₁ : ℝ × ℝ} {h₀ h₁ : List (ℝ × ℝ)} {G₀ G₁ : Set (ℝ × ℝ)}
    {r η ε'' : ℝ} (hr : 0 < r) (h2r : 2 * r < dist a b) (hη : 0 < η) (hε : 3 * ε'' ≤ η)
    (ha₀ : dist α₀ a = r) (ha₁ : dist α₁ a = r) (hb₀ : dist β₀ b = r) (hb₁ : dist β₁ b = r)
    (hα₀G : α₀ ∈ G₀) (hα₁G : α₁ ∈ G₁) (hβ₀G : β₀ ∈ G₀) (hβ₁G : β₁ ∈ G₁)
    (hGa₀ : ∀ y ∈ G₀, r ≤ dist y a) (hGa₁ : ∀ y ∈ G₁, r ≤ dist y a)
    (hGb₀ : ∀ y ∈ G₀, r ≤ dist y b) (hGb₁ : ∀ y ∈ G₁, r ≤ dist y b)
    (hsep : ∀ y ∈ G₀, ∀ y' ∈ G₁, η ≤ dist y y')
    (hn₀ : ∀ y ∈ chainSet h₀, ∃ g ∈ G₀, dist y g < ε'')
    (hn₁ : ∀ y ∈ chainSet h₁, ∃ g ∈ G₁, dist y g < ε'') :
    (segment ℝ a α₀ ∪ chainSet h₀ ∪ segment ℝ β₀ b) ∩ (segment ℝ a α₁ ∪ chainSet h₁ ∪ segment ℝ β₁ b)
      ⊆ {a, b} := by
  have hsep' : ∀ y ∈ G₁, ∀ y' ∈ G₀, η ≤ dist y y' := fun y hy y' hy' => by
    rw [dist_comm]; exact hsep y' hy' y hy
  have hne : α₀ ≠ α₁ := fun h => by
    have := hsep α₀ hα₀G α₁ hα₁G
    rw [h, dist_self] at this; linarith
  have hne' : β₀ ≠ β₁ := fun h => by
    have := hsep β₀ hβ₀G β₁ hβ₁G
    rw [h, dist_self] at this; linarith
  -- the end segments are in the closed balls
  have ball_a : ∀ {α z : ℝ × ℝ}, dist α a = r → z ∈ segment ℝ a α → dist z a ≤ r := by
    intro α z hα hz
    have := dist_add_dist_of_mem_segment hz
    have := dist_nonneg (x := z) (y := α)
    rw [dist_comm a α, hα] at *
    rw [dist_comm z a]; linarith
  have ball_b : ∀ {β z : ℝ × ℝ}, dist β b = r → z ∈ segment ℝ β b → dist z b ≤ r := by
    intro β z hβ hz
    have := dist_add_dist_of_mem_segment hz
    have := dist_nonneg (x := β) (y := z)
    rw [hβ] at *
    linarith
  rintro z ⟨hz₀, hz₁⟩
  rcases hz₀ with (hz₀ | hz₀) | hz₀ <;> rcases hz₁ with (hz₁ | hz₁) | hz₁
  · exact Or.inl (segment_inter_sphere hr ha₀ ha₁ hne hz₀ hz₁)
  · obtain ⟨g, hg, hd⟩ := hn₁ z hz₁
    exact (chain_not_on_segment ha₀ (hGa₁ g hg) (hsep' g hg α₀ hα₀G) hε hη hd hz₀).elim
  · exfalso
    have h1 := ball_a ha₀ hz₀
    have h2 := ball_b hb₁ hz₁
    have := dist_triangle a z b
    rw [dist_comm a z] at this
    linarith
  · obtain ⟨g, hg, hd⟩ := hn₀ z hz₀
    exact (chain_not_on_segment ha₁ (hGa₀ g hg) (hsep g hg α₁ hα₁G) hε hη hd hz₁).elim
  · obtain ⟨g, hg, hd⟩ := hn₀ z hz₀
    obtain ⟨g', hg', hd'⟩ := hn₁ z hz₁
    have := hsep g hg g' hg'
    have := dist_triangle g z g'
    have c1 := dist_comm g z
    have c2 := dist_comm z g'
    have : 0 < ε'' := by linarith
    linarith
  · obtain ⟨g, hg, hd⟩ := hn₀ z hz₀
    have hz₁' : z ∈ segment ℝ b β₁ := by rw [segment_symm]; exact hz₁
    exact (chain_not_on_segment hb₁ (hGb₀ g hg) (hsep g hg β₁ hβ₁G) hε hη hd hz₁').elim
  · exfalso
    have h1 := ball_b hb₀ hz₀
    have h2 := ball_a ha₁ hz₁
    have := dist_triangle a z b
    rw [dist_comm z a] at h2
    linarith
  · obtain ⟨g, hg, hd⟩ := hn₁ z hz₁
    have hz₀' : z ∈ segment ℝ b β₀ := by rw [segment_symm]; exact hz₀
    exact (chain_not_on_segment hb₀ (hGb₁ g hg) (hsep' g hg β₀ hβ₀G) hε hη hd hz₀').elim
  · have hz₀' : z ∈ segment ℝ b β₀ := by rw [segment_symm]; exact hz₀
    have hz₁' : z ∈ segment ℝ b β₁ := by rw [segment_symm]; exact hz₁
    exact Or.inr (segment_inter_sphere hr hb₀ hb₁ hne' hz₀' hz₁')

/-- **A chain from `a` to `b` that is near its arc is Hausdorff-near it.** -/
lemma two_way_near {γ : ℝ → ℝ × ℝ} (hc : ContinuousOn γ (Icc 0 1)) {a b : ℝ × ℝ}
    (hs : γ 0 = a) (ht : γ 1 = b) (hab : a ≠ b) {ε θ δ ε' : ℝ} (hθ : 0 < θ)
    (hunif : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| < θ → dist (γ s) (γ t) < ε / 4)
    (hinv : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ s) (γ t) < δ → |s - t| < θ)
    (hε' : 2 * ε' < δ) (hε'ε : ε' ≤ ε / 4) (hε : 0 < ε) {C : List (ℝ × ℝ)} (hC : IsSimpleChain C)
    (hC1 : C.head? = some a) (hC2 : C.getLast? = some b)
    (hnear : ∀ z ∈ chainSet C, ∃ τ ∈ Icc (0 : ℝ) 1, dist z (γ τ) ≤ ε') :
    (∀ z ∈ chainSet C, ∃ w ∈ γ '' Icc 0 1, dist z w < ε) ∧
      (∀ w ∈ γ '' Icc 0 1, ∃ z ∈ chainSet C, dist w z < ε) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨τ, hτ, hd⟩ := hnear z hz
    exact ⟨γ τ, ⟨τ, hτ, rfl⟩, by linarith⟩
  · obtain ⟨γ', hc', -, h0', h1', himg⟩ := IsArc.chain hC hC1 hC2 (two_le_length hC1 hC2 hab)
    have hPc : IsCompact (chainSet C) := himg ▸ isCompact_Icc.image_of_continuousOn hc'
    have hPp : IsPreconnected (chainSet C) := himg ▸ isPreconnected_Icc.image _ hc'
    have ha : a ∈ chainSet C := by rw [← himg, ← h0']; exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    have hb : b ∈ chainSet C := by rw [← himg, ← h1']; exact ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    have hdens := arc_density hc hθ hinv hε' hPc hPp (hs ▸ ha) (ht ▸ hb) hnear
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨τ', hτ', hlt, p, hp, hd⟩ := hdens τ hτ
    refine ⟨p, hp, ?_⟩
    have h1 := hunif τ hτ τ' hτ' hlt
    have h2 := dist_triangle (γ τ) (γ τ') p
    rw [dist_comm (γ τ') p] at h2
    linarith

/-- Two arcs from `a` to `b` meeting only at their ends have two simple chains from `a` to `b`
meeting only at their ends, each Hausdorff `ε`-close to its arc. -/
theorem exists_two_chains {A₀ A₁ : Set (ℝ × ℝ)} {a b : ℝ × ℝ} (h₀ : IsArc A₀ a b)
    (h₁ : IsArc A₁ a b) (hi : A₀ ∩ A₁ = {a, b}) (hab : a ≠ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ C₁ : List (ℝ × ℝ), IsSimpleChain C₀ ∧ C₀.head? = some a ∧ C₀.getLast? = some b ∧
      IsSimpleChain C₁ ∧ C₁.head? = some a ∧ C₁.getLast? = some b ∧
      chainSet C₀ ∩ chainSet C₁ = {a, b} ∧
      (∀ z ∈ chainSet C₀, ∃ w ∈ A₀, dist z w < ε) ∧ (∀ w ∈ A₀, ∃ z ∈ chainSet C₀, dist w z < ε) ∧
      (∀ z ∈ chainSet C₁, ∃ w ∈ A₁, dist z w < ε) ∧ (∀ w ∈ A₁, ∃ z ∈ chainSet C₁, dist w z < ε) := by
  obtain ⟨γ₀, hc₀, hj₀, hs₀, ht₀, rfl⟩ := h₀
  obtain ⟨γ₁, hc₁, hj₁, hs₁, ht₁, rfl⟩ := h₁
  have hab' := dist_pos.2 hab
  -- scales: uniform continuity, the inverse modulus, the radius
  obtain ⟨θ₀, hθ₀, hu₀⟩ := arc_unif hc₀ (by linarith : (0 : ℝ) < ε / 4)
  obtain ⟨θ₁, hθ₁, hu₁⟩ := arc_unif hc₁ (by linarith : (0 : ℝ) < ε / 4)
  have hθ : 0 < min θ₀ θ₁ := lt_min hθ₀ hθ₁
  obtain ⟨δ₀, hδ₀, hm₀⟩ := exists_inverse_modulus hc₀ hj₀ hθ
  obtain ⟨δ₁, hδ₁, hm₁⟩ := exists_inverse_modulus hc₁ hj₁ hθ
  have hδ : 0 < min δ₀ δ₁ := lt_min hδ₀ hδ₁
  set ε' : ℝ := min (ε / 4) (min δ₀ δ₁ / 3) with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) (by linarith)
  have hε'ε : ε' ≤ ε / 4 := min_le_left _ _
  have hε'δ : 3 * ε' ≤ min δ₀ δ₁ := by
    have := min_le_right (ε / 4) (min δ₀ δ₁ / 3)
    linarith
  have hε'δ₀ : 2 * ε' < δ₀ := by
    have := min_le_left δ₀ δ₁
    linarith
  have hε'δ₁ : 2 * ε' < δ₁ := by
    have := min_le_right δ₀ δ₁
    linarith
  set r : ℝ := min ε' (dist a b / 4) with hr
  have hr0 : 0 < r := lt_min hε'0 (by linarith)
  have hrε' : r ≤ ε' := min_le_left _ _
  have hr2 : 2 * r < dist a b := by
    have : r ≤ dist a b / 4 := min_le_right _ _
    linarith
  -- trimmed subarcs
  obtain ⟨s₀, t₀, hs₀0, hst₀, ht₀1, hα₀, hβ₀, hfar₀⟩ := exists_trim hc₀ hs₀ ht₀ hr0 hr2
  obtain ⟨s₁, t₁, hs₁0, hst₁, ht₁1, hα₁, hβ₁, hfar₁⟩ := exists_trim hc₁ hs₁ ht₁ hr0 hr2
  set G₀ : Set (ℝ × ℝ) := γ₀ '' Icc s₀ t₀ with hG₀
  set G₁ : Set (ℝ × ℝ) := γ₁ '' Icc s₁ t₁ with hG₁
  have hsub₀ : Icc s₀ t₀ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs₀0 ht₀1
  have hsub₁ : Icc s₁ t₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs₁0 ht₁1
  have hG₀c : IsCompact G₀ := isCompact_Icc.image_of_continuousOn (hc₀.mono hsub₀)
  have hG₁c : IsCompact G₁ := isCompact_Icc.image_of_continuousOn (hc₁.mono hsub₁)
  have hG₀n : G₀.Nonempty := ⟨_, ⟨s₀, ⟨le_rfl, hst₀.le⟩, rfl⟩⟩
  have hG₁n : G₁.Nonempty := ⟨_, ⟨s₁, ⟨le_rfl, hst₁.le⟩, rfl⟩⟩
  have hGa₀ : ∀ y ∈ G₀, r ≤ dist y a := by
    rintro _ ⟨τ, hτ, rfl⟩; exact (hfar₀ τ hτ).1
  have hGb₀ : ∀ y ∈ G₀, r ≤ dist y b := by
    rintro _ ⟨τ, hτ, rfl⟩; exact (hfar₀ τ hτ).2
  have hGa₁ : ∀ y ∈ G₁, r ≤ dist y a := by
    rintro _ ⟨τ, hτ, rfl⟩; exact (hfar₁ τ hτ).1
  have hGb₁ : ∀ y ∈ G₁, r ≤ dist y b := by
    rintro _ ⟨τ, hτ, rfl⟩; exact (hfar₁ τ hτ).2
  have hdisj : ∀ y ∈ G₀, y ∉ G₁ := by
    intro y hy hy'
    have hA₀ : y ∈ γ₀ '' Icc 0 1 := by
      obtain ⟨τ, hτ, rfl⟩ := hy; exact ⟨τ, hsub₀ hτ, rfl⟩
    have hA₁ : y ∈ γ₁ '' Icc 0 1 := by
      obtain ⟨τ, hτ, rfl⟩ := hy'; exact ⟨τ, hsub₁ hτ, rfl⟩
    have : y ∈ γ₀ '' Icc 0 1 ∩ γ₁ '' Icc 0 1 := ⟨hA₀, hA₁⟩
    rw [hi] at this
    rcases this with h | h
    · have := hGa₀ y hy; rw [h, dist_self] at this; linarith
    · have := hGb₀ y hy; rw [h, dist_self] at this; linarith
  obtain ⟨η, hη, hsep⟩ := exists_sep hG₀c hG₁c hG₀n hG₁n hdisj
  set ε'' : ℝ := min ε' (η / 3) with hε''
  have hε''0 : 0 < ε'' := lt_min hε'0 (by linarith)
  have hε''ε' : ε'' ≤ ε' := min_le_left _ _
  have hε''η : 3 * ε'' ≤ η := by
    have := min_le_right ε' (η / 3)
    linarith
  -- the chains near the trimmed subarcs, joined to the vertices
  obtain ⟨h₀, hh₀, hh₀1, hh₀2, hn₀⟩ := exists_chain_on hc₀ hs₀0 hst₀ ht₀1 hε''0
  obtain ⟨h₁, hh₁, hh₁1, hh₁2, hn₁⟩ := exists_chain_on hc₁ hs₁0 hst₁ ht₁1 hε''0
  obtain ⟨C₀, hC₀, hC₀1, hC₀2, hC₀s⟩ := exists_join_chain (a := a) (b := b) hh₀1 hh₀2
  obtain ⟨C₁, hC₁, hC₁1, hC₁2, hC₁s⟩ := exists_join_chain (a := a) (b := b) hh₁1 hh₁2
  have hn₀' : ∀ y ∈ chainSet h₀, ∃ g ∈ G₀, dist y g < ε'' := fun y hy => by
    obtain ⟨τ, hτ, hd⟩ := hn₀ y hy; exact ⟨_, ⟨τ, hτ, rfl⟩, hd⟩
  have hn₁' : ∀ y ∈ chainSet h₁, ∃ g ∈ G₁, dist y g < ε'' := fun y hy => by
    obtain ⟨τ, hτ, hd⟩ := hn₁ y hy; exact ⟨_, ⟨τ, hτ, rfl⟩, hd⟩
  have hα₀G : γ₀ s₀ ∈ G₀ := ⟨s₀, ⟨le_rfl, hst₀.le⟩, rfl⟩
  have hβ₀G : γ₀ t₀ ∈ G₀ := ⟨t₀, ⟨hst₀.le, le_rfl⟩, rfl⟩
  have hα₁G : γ₁ s₁ ∈ G₁ := ⟨s₁, ⟨le_rfl, hst₁.le⟩, rfl⟩
  have hβ₁G : γ₁ t₁ ∈ G₁ := ⟨t₁, ⟨hst₁.le, le_rfl⟩, rfl⟩
  have hinter := pieces_inter hr0 hr2 hη hε''η hα₀ hα₁ hβ₀ hβ₁ hα₀G hα₁G hβ₀G hβ₁G hGa₀ hGa₁
    hGb₀ hGb₁ hsep hn₀' hn₁'
  -- the nearness of the pieces
  have hnear : ∀ (γ : ℝ → ℝ × ℝ) (s t : ℝ), γ 0 = a → γ 1 = b → 0 ≤ s → s < t → t ≤ 1 →
      dist (γ s) a = r → dist (γ t) b = r → ∀ h : List (ℝ × ℝ),
      (∀ y ∈ chainSet h, ∃ τ ∈ Icc s t, dist y (γ τ) < ε'') →
      ∀ z ∈ segment ℝ a (γ s) ∪ chainSet h ∪ segment ℝ (γ t) b,
        ∃ τ ∈ Icc (0 : ℝ) 1, dist z (γ τ) ≤ ε' := by
    intro γ s t h0 h1 hs0 hst ht1 hα hβ h hh z hz
    rcases hz with (hz | hz) | hz
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have := dist_add_dist_of_mem_segment hz
      rw [dist_comm a (γ s), hα] at this
      rw [h0, dist_comm z a]
      have := dist_nonneg (x := z) (y := γ s)
      rw [dist_comm a z] at *
      linarith
    · obtain ⟨τ, hτ, hd⟩ := hh z hz
      exact ⟨τ, ⟨le_trans hs0 hτ.1, le_trans hτ.2 ht1⟩, by linarith⟩
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      have := dist_add_dist_of_mem_segment hz
      rw [hβ] at this
      rw [h1]
      have := dist_nonneg (x := γ t) (y := z)
      linarith
  have hnear₀ := hnear γ₀ s₀ t₀ hs₀ ht₀ hs₀0 hst₀ ht₀1 hα₀ hβ₀ h₀ hn₀
  have hnear₁ := hnear γ₁ s₁ t₁ hs₁ ht₁ hs₁0 hst₁ ht₁1 hα₁ hβ₁ h₁ hn₁
  refine ⟨C₀, C₁, hC₀, hC₀1, hC₀2, hC₁, hC₁1, hC₁2, ?_, ?_⟩
  · apply Set.eq_of_subset_of_subset
    · intro z ⟨hz₀, hz₁⟩
      exact hinter ⟨hC₀s hz₀, hC₁s hz₁⟩
    · rintro z (rfl | rfl)
      · exact ⟨head_mem_chainSet hC₀1, head_mem_chainSet hC₁1⟩
      · exact ⟨last_mem_chainSet' hC₀2, last_mem_chainSet' hC₁2⟩
  · have h0n := two_way_near hc₀ hs₀ ht₀ hab (θ := min θ₀ θ₁) (δ := δ₀) (ε' := ε') hθ
      (fun s hs t ht hst => hu₀ s hs t ht (lt_of_lt_of_le hst (min_le_left _ _))) hm₀ hε'δ₀ hε'ε
      hε hC₀ hC₀1 hC₀2 (fun z hz => hnear₀ z (hC₀s hz))
    have h1n := two_way_near hc₁ hs₁ ht₁ hab (θ := min θ₀ θ₁) (δ := δ₁) (ε' := ε') hθ
      (fun s hs t ht hst => hu₁ s hs t ht (lt_of_lt_of_le hst (min_le_right _ _))) hm₁ hε'δ₁ hε'ε
      hε hC₁ hC₁1 hC₁2 (fun z hz => hnear₁ z (hC₁s hz))
    exact ⟨h0n.1, h0n.2, h1n.1, h1n.2⟩

/-- **A Jordan curve is approximated by a simple polygon.** For every `ε > 0`, a continuous injective
map of the circle into the plane has a simple closed polygon whose carrier is within `ε` of the image
in both directions (every point of the carrier is within `ε` of the curve, and every point of the curve
is within `ε` of the carrier). -/
theorem exists_polygon_near {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × ℝ), (Polygon.ofList l).IsSimple ∧
      (∀ z ∈ (Polygon.ofList l).carrier, ∃ w, dist z (f w) < ε) ∧
      (∀ w, ∃ z ∈ (Polygon.ofList l).carrier, dist (f w) z < ε) := by
  have hw : (-1 : Circle) ≠ 1 := Circle.neg_ne_self 1
  obtain ⟨A₀, A₁, h₀, h₁, hint, hun⟩ := exists_two_arcs f hc hi hw
  have hab : f 1 ≠ f (-1) := fun h => hw (hi h).symm
  obtain ⟨C₀, C₁, hC₀, hC₀1, hC₀2, hC₁, hC₁1, hC₁2, hCi, hn₀, hn₀', hn₁, hn₁'⟩ :=
    exists_two_chains h₀ h₁ hint hab hε
  -- the chains as `a :: m ++ [b]` and the reverse of the second
  have hC₁r1 : C₁.reverse.head? = some (f (-1)) := by rw [List.head?_reverse]; exact hC₁2
  have hC₁r2 : C₁.reverse.getLast? = some (f 1) := by rw [List.getLast?_reverse]; exact hC₁1
  obtain ⟨m₀, hm₀⟩ := PLDrawing.chain_split hC₀1 hC₀2 (two_le_length hC₀1 hC₀2 hab)
  obtain ⟨m₁, hm₁⟩ := PLDrawing.chain_split hC₁r1 hC₁r2
    (by rw [List.length_reverse]; exact two_le_length hC₁1 hC₁2 hab)
  have hP : IsSimpleChain (f 1 :: m₀ ++ [f (-1)]) := hm₀ ▸ hC₀
  have hQ : IsSimpleChain (f (-1) :: m₁ ++ [f 1]) := hm₁ ▸ isSimpleChain_reverse hC₁
  have hSet₀ : chainSet (f 1 :: m₀ ++ [f (-1)]) = chainSet C₀ := by rw [← hm₀]
  have hSet₁ : chainSet (f (-1) :: m₁ ++ [f 1]) = chainSet C₁ := by
    rw [← hm₁, chainSet_reverse]
  have hPQ : chainSet (f 1 :: m₀ ++ [f (-1)]) ∩ chainSet (f (-1) :: m₁ ++ [f 1]) =
      {f 1, f (-1)} := by rw [hSet₀, hSet₁]; exact hCi
  refine ⟨f 1 :: m₀ ++ f (-1) :: m₁, isSimple_two_arcs hP hQ hPQ hab, ?_, ?_⟩
  · intro z hz
    rw [carrier_two_arcs, hSet₀, hSet₁] at hz
    rcases hz with hz | hz
    · obtain ⟨y, hy, hd⟩ := hn₀ z hz
      have : y ∈ range f := hun ▸ Or.inl hy
      obtain ⟨w, rfl⟩ := this
      exact ⟨w, hd⟩
    · obtain ⟨y, hy, hd⟩ := hn₁ z hz
      have : y ∈ range f := hun ▸ Or.inr hy
      obtain ⟨w, rfl⟩ := this
      exact ⟨w, hd⟩
  · intro w
    have : f w ∈ A₀ ∪ A₁ := hun ▸ mem_range_self w
    rcases this with hy | hy
    · obtain ⟨z, hz, hd⟩ := hn₀' _ hy
      exact ⟨z, by rw [carrier_two_arcs, hSet₀]; exact Or.inl hz, hd⟩
    · obtain ⟨z, hz, hd⟩ := hn₁' _ hy
      exact ⟨z, by rw [carrier_two_arcs, hSet₁]; exact Or.inr hz, hd⟩

end Lightlike.PL
