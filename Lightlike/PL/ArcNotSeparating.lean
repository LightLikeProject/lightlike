import Lightlike.PL.UnionLemma
import Lightlike.PL.ArcSet

/-!
# An arc does not separate the plane

If `A` is the image of an injective continuous map of `[0, 1]` into the plane (`IsArc A p q`), the
complement of `A` is connected (`arc_not_separating`).

The proof is the bisection of the notes: if the image of `γ` separates `P` from `Q`, one of the images of
the two halves of the parameter interval does, by `joinedIn_union_compl` (the two halves are compact and
meet only in `γ` of the midpoint), and so on; the nested intervals shrink to a parameter `t`
(`exists_small_separating`), and a small neighbourhood of `γ t` does not separate two points different
from `γ t` (`not_separates_of_small`: a path in the plane minus a point has a compact image at positive
distance from it), a contradiction.

This is the Separation Theorem for Jordan arcs of chapter 9 of J. McCleary, *A First Course in
Topology: Continuity and Dimension* (AMS, 2006), after M. H. A. Newman; the numbering is that of the
lecture-notes version of the chapter (`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`),
not checked against the printed book. The statements and proofs are Lean's own.

## Main results

* `Separates`: a set separates two points when they are not joined in its complement.
* `exists_small_separating`: the nested bisection.
* `arc_not_separating`: the complement of an arc is connected.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (checked as a chapter with `scripts/sources.py verify`; the lemma-level numbering quoted above is that of the lecture-notes version and is not checked).
-/

open Set Metric Filter Topology

namespace Lightlike.PL

/-- `K` **separates** `P` from `Q`: there is no path from `P` to `Q` in the complement of `K`. -/
def Separates (K : Set (ℝ × ℝ)) (P Q : ℝ × ℝ) : Prop := ¬ JoinedIn Kᶜ P Q

/-- A separating union has a separating half. -/
theorem separates_half {K₁ K₂ : Set (ℝ × ℝ)} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂) {R : ℝ × ℝ}
    (hR : K₁ ∩ K₂ = {R}) {P Q : ℝ × ℝ} (h : Separates (K₁ ∪ K₂) P Q) :
    Separates K₁ P Q ∨ Separates K₂ P Q := by
  by_contra hc
  rw [not_or] at hc
  exact h (joinedIn_union_compl h₁ h₂ hR (not_not.1 hc.1) (not_not.1 hc.2))

/-- **A small ball does not separate**: if `P` and `Q` are different from `R`, every set inside a
small enough ball around `R` fails to separate them. -/
theorem not_separates_of_small {P Q R : ℝ × ℝ} (hP : P ≠ R) (hQ : Q ≠ R) :
    ∃ ε > 0, ∀ K : Set (ℝ × ℝ), K ⊆ closedBall R ε → ¬ Separates K P Q := by
  have hconn : IsPathConnected ({R}ᶜ : Set (ℝ × ℝ)) :=
    isPathConnected_compl_singleton_of_one_lt_rank (by rw [rank_prod', Module.rank_self]; norm_num) R
  have hj : JoinedIn ({R}ᶜ : Set (ℝ × ℝ)) P Q := hconn.joinedIn P hP Q hQ
  set γ := hj.somePath
  have hmem : ∀ t, γ t ∈ ({R}ᶜ : Set (ℝ × ℝ)) := hj.somePath_mem
  have hΓ : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨δ, hδ, hth⟩ := hΓ.exists_thickening_subset_open isOpen_compl_singleton
    (by rintro _ ⟨t, rfl⟩; exact hmem t)
  refine ⟨δ / 2, half_pos hδ, fun K hK hsep => hsep ?_⟩
  refine ⟨γ, fun t => ?_⟩
  intro hKt
  have h1 := hK hKt
  have : R ∈ thickening δ (range γ) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨γ t, ⟨t, rfl⟩, ?_⟩
    have := mem_closedBall.1 h1
    rw [dist_comm]; linarith
  exact hth this rfl

/-- **The nested bisection.** If the image of `γ` on `[0, 1]` separates `P` from `Q`, there is a
parameter `t` such that every interval around `t` has a subinterval, still around `t` and as short as
we like, whose image separates `P` from `Q`. -/
theorem exists_small_separating {γ : ℝ → ℝ × ℝ} (hc : ContinuousOn γ (Icc 0 1))
    (hi : InjOn γ (Icc 0 1)) {P Q : ℝ × ℝ} (h : Separates (γ '' Icc 0 1) P Q) :
    ∃ t ∈ Icc (0 : ℝ) 1, ∀ ε > 0, ∃ a b : ℝ, 0 ≤ a ∧ a ≤ t ∧ t ≤ b ∧ b ≤ 1 ∧ b - a < ε ∧
      Separates (γ '' Icc a b) P Q := by
  let X := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧ Separates (γ '' Icc p.1 p.2) P Q}
  have step : ∀ p : X, ∃ p' : X, p.1.1 ≤ p'.1.1 ∧ p'.1.2 ≤ p.1.2 ∧
      p'.1.2 - p'.1.1 = (p.1.2 - p.1.1) / 2 := by
    rintro ⟨⟨a, b⟩, ha, hab, hb, hsep⟩
    simp only at ha hab hb hsep
    set m := (a + b) / 2 with hm
    have ham : a ≤ m := by rw [hm]; linarith
    have hmb : m ≤ b := by rw [hm]; linarith
    have hK1 : IsCompact (γ '' Icc a m) :=
      isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc ha (by linarith)))
    have hK2 : IsCompact (γ '' Icc m b) :=
      isCompact_Icc.image_of_continuousOn (hc.mono (Icc_subset_Icc (by linarith) hb))
    have hunion : γ '' Icc a m ∪ γ '' Icc m b = γ '' Icc a b := by
      rw [← image_union, Icc_union_Icc_eq_Icc ham hmb]
    have hinter : γ '' Icc a m ∩ γ '' Icc m b = {γ m} := by
      ext x
      simp only [mem_inter_iff, mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, ⟨s', hs', hss'⟩⟩
        have : s' = s := hi ⟨by linarith [hs'.1], by linarith [hs'.2]⟩ ⟨by linarith [hs.1], by linarith [hs.2]⟩ hss'
        have : s = m := le_antisymm hs.2 (this ▸ hs'.1)
        rw [this]
      · rintro rfl
        exact ⟨⟨m, ⟨ham, le_rfl⟩, rfl⟩, ⟨m, ⟨le_rfl, hmb⟩, rfl⟩⟩
    rw [← hunion] at hsep
    rcases separates_half hK1 hK2 hinter hsep with h1 | h2
    · exact ⟨⟨(a, m), ha, by simp only; rw [hm]; linarith, by simp only; rw [hm]; linarith, h1⟩,
        le_rfl, by simp only; exact hmb, by simp only; rw [hm]; ring⟩
    · exact ⟨⟨(m, b), by simp only; rw [hm]; linarith, by simp only; rw [hm]; linarith, hb, h2⟩,
        by simp only; exact ham, le_rfl, by simp only; rw [hm]; ring⟩
  choose g hg using step
  let x₀ : X := ⟨(0, 1), le_rfl, zero_lt_one, le_rfl, h⟩
  let seq : ℕ → X := fun n => g^[n] x₀
  have hseq : ∀ n, seq (n + 1) = g (seq n) := fun n => Function.iterate_succ_apply' g n x₀
  have hwidth : ∀ n, (seq n).1.2 - (seq n).1.1 = 1 / 2 ^ n := by
    intro n
    induction n with
    | zero => simp [seq, x₀]
    | succ n ih =>
      rw [hseq, (hg (seq n)).2.2, ih]; field_simp; ring
  have hmono : Monotone fun n => (seq n).1.1 :=
    monotone_nat_of_le_succ fun n => by rw [hseq]; exact (hg (seq n)).1
  have hanti : Antitone fun n => (seq n).1.2 :=
    antitone_nat_of_succ_le fun n => by rw [hseq]; exact (hg (seq n)).2.1
  have hab : ∀ m n, (seq m).1.1 ≤ (seq n).1.2 := by
    intro m n
    calc (seq m).1.1 ≤ (seq (max m n)).1.1 := hmono (le_max_left _ _)
      _ ≤ (seq (max m n)).1.2 := (seq (max m n)).2.2.1.le
      _ ≤ (seq n).1.2 := hanti (le_max_right _ _)
  have hbdd : BddAbove (range fun n => (seq n).1.1) := ⟨(seq 0).1.2, by rintro _ ⟨n, rfl⟩; exact hab n 0⟩
  set t := ⨆ n, (seq n).1.1 with ht
  have hat : ∀ n, (seq n).1.1 ≤ t := fun n => le_ciSup hbdd n
  have htb : ∀ n, t ≤ (seq n).1.2 := fun n => ciSup_le fun m => hab m n
  refine ⟨t, ⟨(seq 0).2.1.trans (hat 0), (htb 0).trans (seq 0).2.2.2.1⟩, fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨(seq n).1.1, (seq n).1.2, (seq n).2.1, hat n, htb n, (seq n).2.2.2.1, ?_, (seq n).2.2.2.2⟩
  rw [hwidth n]
  simpa [one_div, inv_pow] using hn

/-- **An arc does not separate the plane** (the notes' Separation Theorem for Jordan arcs). -/
theorem arc_not_separating {A : Set (ℝ × ℝ)} {p q : ℝ × ℝ} (h : IsArc A p q) :
    IsPreconnected Aᶜ := by
  obtain ⟨γ, hc, hi, -, -, rfl⟩ := h
  have hA : IsCompact (γ '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hc
  have hne : (γ '' Icc 0 1)ᶜ.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hn
    exact NoncompactSpace.noncompact_univ (hn ▸ hA)
  refine (isPathConnected_iff.2 ⟨hne, fun P hP Q hQ => ?_⟩).isConnected.isPreconnected
  by_contra hj
  obtain ⟨t, ht, H⟩ := exists_small_separating hc hi hj
  have hRA : γ t ∈ γ '' Icc 0 1 := ⟨t, ht, rfl⟩
  obtain ⟨ε, hε, hsmall⟩ := not_separates_of_small (P := P) (Q := Q) (R := γ t)
    (fun h => hP (h ▸ hRA)) (fun h => hQ (h ▸ hRA))
  obtain ⟨ρ, hρ, hcont⟩ := Metric.continuousWithinAt_iff.1 (hc t ht) ε hε
  obtain ⟨a, b, ha, hat, htb, hb, hba, hsep⟩ := H ρ hρ
  refine hsmall _ ?_ hsep
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_closedBall]
  refine (hcont ⟨ha.trans hs.1, hs.2.trans hb⟩ ?_).le
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

end Lightlike.PL
