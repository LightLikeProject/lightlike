import Lightlike.Spacetime.Causal.BasicRelations

/-!
# From local to global reachability along a curve

A curve `γ` on `[a, b]` is **locally reaching** (`LocalReach`) if every parameter `s` has a window
`[s - δ, s + δ]` such that `γ t'` lies in the chronological future of `γ t` whenever `t < t'` lie in the
window. Then the end point of the curve is in the chronological future of its start
(`chronFuture_of_localReach`): the set of parameters that can be reached from the start is an interval
containing the start, and the local hypothesis together with the transitivity of `I⁺` shows that its
supremum is attained and equals `b`.

This is the global half of the reduction of `T-GE2-P19` (a curve with timelike velocity almost
everywhere, without a margin, joins its end points in the timelike future) to a local statement; the
local hypothesis is not proved here, and nothing is claimed about `T-GE2-P19`.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- A curve is **locally reaching** on `[a, b]` if around every parameter `s` there is a window in which
later points of the curve lie in the chronological future of earlier ones. -/
def LocalReach (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, ∃ δ > 0, ∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, s - δ ≤ t → t < t' → t' ≤ s + δ →
    γ t' ∈ chronFuture T (γ t)

/-- **A locally reaching curve reaches its end point in the chronological future of its start.** -/
theorem chronFuture_of_localReach {γ : ℝ → M} {a b : ℝ} (hab : a < b) (h : LocalReach T γ a b) :
    γ b ∈ chronFuture T (γ a) := by
  set A : Set ℝ := {t | t ∈ Icc a b ∧ ∀ u ∈ Ioc a t, γ u ∈ chronFuture T (γ a)} with hA
  have haA : a ∈ A := ⟨⟨le_rfl, hab.le⟩, fun u hu => absurd hu.1 (not_lt.2 hu.2)⟩
  have hbdd : BddAbove A := ⟨b, fun t ht => ht.1.2⟩
  set c := sSup A with hc
  have hac : a ≤ c := le_csSup hbdd haA
  have hcb : c ≤ b := csSup_le ⟨a, haA⟩ fun t ht => ht.1.2
  have hcI : c ∈ Icc a b := ⟨hac, hcb⟩
  -- the reach from the start at parameters in `(a, c)`
  have hlt : ∀ u, a < u → u < c → γ u ∈ chronFuture T (γ a) := by
    intro u hau huc
    obtain ⟨t, htA, hut⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ huc
    exact htA.2 u ⟨hau, hut.le⟩
  -- `c > a`
  have hca : a < c := by
    by_contra hnot
    have hc_eq : c = a := le_antisymm (not_lt.1 hnot) hac
    obtain ⟨δ, hδ, hreach⟩ := h a ⟨le_rfl, hab.le⟩
    set u := min (a + δ) b with hu
    have hua : a < u := lt_min (by linarith) hab
    have huA : u ∈ A := by
      refine ⟨⟨hua.le, min_le_right _ _⟩, fun v hv => ?_⟩
      exact hreach a ⟨le_rfl, hab.le⟩ v ⟨hv.1.le, hv.2.trans (min_le_right _ _)⟩ (by linarith) hv.1
        (by have := hv.2.trans (min_le_left _ _); linarith)
    have := le_csSup hbdd huA
    linarith
  -- `c ∈ A`
  have hcA : c ∈ A := by
    refine ⟨hcI, fun u hu => ?_⟩
    rcases lt_or_eq_of_le hu.2 with hlt' | heq
    · exact hlt u hu.1 hlt'
    · rw [heq]
      obtain ⟨δ, hδ, hreach⟩ := h c hcI
      obtain ⟨t, htA, hct⟩ := exists_lt_of_lt_csSup ⟨a, haA⟩ (show max a (c - δ) < c from
        max_lt hca (by linarith))
      have htI : t ∈ Icc a b := htA.1
      have htle : t ≤ c := le_csSup hbdd htA
      rcases htle.lt_or_eq with htc | htc
      · have hreach' := hreach t htI c hcI (by have := le_max_right a (c - δ); linarith) htc
          (by linarith)
        by_cases hta : t = a
        · rw [← hta]; exact hreach'
        · have hat : a < t := lt_of_le_of_ne htI.1 (Ne.symm hta)
          exact chron_trans T (htA.2 t ⟨hat, le_rfl⟩) hreach'
      · exact htA.2 c ⟨hca, htc.ge⟩
  -- `c = b`
  have hcb' : c = b := by
    by_contra hne
    have hcltb : c < b := lt_of_le_of_ne hcb hne
    obtain ⟨δ, hδ, hreach⟩ := h c hcI
    set u := min (c + δ) b with hu
    have huc : c < u := lt_min (by linarith) hcltb
    have huA : u ∈ A := by
      refine ⟨⟨(hac.trans huc.le), min_le_right _ _⟩, fun v hv => ?_⟩
      by_cases hvc : v ≤ c
      · exact hcA.2 v ⟨hv.1, hvc⟩
      · have hcv : c < v := not_le.1 hvc
        have hvb : v ∈ Icc a b := ⟨hv.1.le, hv.2.trans (min_le_right _ _)⟩
        have h1 := hreach c hcI v hvb (by linarith) hcv (by have := hv.2.trans (min_le_left _ _); linarith)
        exact chron_trans T (hcA.2 c ⟨hca, le_rfl⟩) h1
    have := le_csSup hbdd huA
    linarith
  exact hcA.2 b ⟨hab, hcb'.symm.le⟩

/-- **Non-vacuity**: a future-directed timelike curve (with the margin of the library's definition) is locally
reaching, so `chronFuture_of_localReach` recovers the end point statement for the library's curves. -/
theorem localReach_of_isFutureTimelikeCurve {γ : ℝ → M} {a b : ℝ}
    (hγ : IsFutureTimelikeCurve T γ (Icc a b)) : LocalReach T γ a b := by
  intro s _
  refine ⟨1, one_pos, fun t ht t' ht' _ htt' _ => ?_⟩
  obtain ⟨ε, hε, hm⟩ := hγ.2 a b (lt_of_le_of_lt ht.1 (htt'.trans_le ht'.2)) subset_rfl
  exact ⟨γ, t, t', htt', isFutureTimelikeCurve_of_margin T hε (hm.mono ht.1 ht'.2 htt'), rfl, rfl⟩

end Lightlike.Causal
