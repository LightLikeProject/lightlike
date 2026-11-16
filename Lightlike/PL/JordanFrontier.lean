import Lightlike.PL.ArcNotSeparating
import Lightlike.PL.WeakJordanCircle

/-!
# Every component of the complement of a Jordan curve has the curve as its frontier

If `f : Circle → ℝ × ℝ` is continuous and injective, every connected component of the complement of
its image has the whole image as its frontier (`jordan_frontier`).

The inclusion of the frontier in the curve holds for every component of the complement of a closed
set. For the other inclusion, a point `p` of the curve outside the frontier of a component `U` gives an
arc `B` of the curve that contains the compact frontier of `U` and misses `p` (`exists_arc_of_compact`);
the complement of `B` is connected by the arc theorem (`arc_not_separating`), and `U` is open and relatively
closed in it, so it is all of it and contains `p`, a contradiction.

This is the clause "each sharing `C` as boundary" of the statement of the Jordan Curve Theorem in the
introduction of chapter 9 of J. McCleary, *A First Course in Topology: Continuity and Dimension*
(AMS, 2006); the statement carries no number in the lecture-notes version of the chapter
(`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`). The proof is Lean's own, not the notes'.

## Main results

* `exists_arc_of_compact`: a compact part of a Jordan curve that misses a point lies in an arc of the curve
  that misses the point.
* `jordan_frontier`: the frontier of every component of the complement is the curve.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (the chapter location is verified with
  `scripts/sources.py verify`; the statement quoted above is read from the lecture-notes version and is not
  checked against the printed book).
-/

open Set Metric Real

namespace Lightlike.PL

/-- **A compact part of a Jordan curve that misses a point lies in an arc of the curve that misses the
point.** -/
theorem exists_arc_of_compact {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {F : Set (ℝ × ℝ)} (hF : IsCompact F) (hFJ : F ⊆ range f) {w : Circle} (hw : f w ∉ F) :
    ∃ (B : Set (ℝ × ℝ)) (s t : ℝ × ℝ), IsArc B s t ∧ F ⊆ B ∧ B ⊆ range f ∧ f w ∉ B := by
  obtain ⟨θ₀, rfl⟩ := Circle.exp_surjective w
  set C : Set ℝ := {θ | θ ∈ Icc 0 (2 * π) ∧ f (Circle.exp (θ₀ + θ)) ∈ F} with hC
  have hclosed : IsClosed C := by
    have h1 : IsClosed {θ : ℝ | f (Circle.exp (θ₀ + θ)) ∈ F} :=
      hF.isClosed.preimage (hc.comp (Circle.exp.continuous.comp (continuous_const.add continuous_id)))
    exact isClosed_Icc.inter h1
  have hCc : IsCompact C := isCompact_Icc.of_isClosed_subset hclosed (fun _ h => h.1)
  have h0 : (0 : ℝ) ∉ C := by
    intro h
    exact hw (by simpa using h.2)
  have h2π : (2 * π) ∉ C := by
    intro h
    have : Circle.exp (θ₀ + 2 * π) = Circle.exp θ₀ := Circle.exp_eq_exp.2 ⟨1, by simp⟩
    exact hw (this ▸ h.2)
  -- bounds
  obtain ⟨a, b, ha, hab, hb, hCab⟩ : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 2 * π ∧ C ⊆ Icc a b := by
    by_cases hne : C.Nonempty
    · obtain ⟨m, hm, hmin⟩ := hCc.exists_isMinOn hne continuousOn_id
      obtain ⟨M, hM, hmax⟩ := hCc.exists_isMaxOn hne continuousOn_id
      have hm0 : 0 < m := lt_of_le_of_ne (hm.1.1) (fun h => h0 (h ▸ hm))
      have hM2 : M < 2 * π := lt_of_le_of_ne (hM.1.2) (fun h => h2π (h ▸ hM))
      have hmM : m ≤ M := hmin hM
      refine ⟨m / 2, (M + 2 * π) / 2, by positivity, ?_, by linarith, fun θ hθ => ⟨?_, ?_⟩⟩
      · linarith [Real.pi_pos]
      · have h1 : m ≤ θ := hmin hθ
        linarith
      · have h1 : θ ≤ M := hmax hθ
        linarith
    · refine ⟨1, 2, one_pos, one_lt_two, ?_, ?_⟩
      · linarith [Real.pi_gt_three]
      · intro θ hθ; exact absurd ⟨θ, hθ⟩ hne
  have hlen : b - a < 2 * π := by linarith
  refine ⟨_, _, _, isArc_circle_arc hc hi (s := θ₀ + a) (t := θ₀ + b) (by linarith) (by linarith), ?_, ?_, ?_⟩
  · -- F ⊆ B
    intro z hz
    obtain ⟨c, rfl⟩ := hFJ hz
    obtain ⟨φ, rfl⟩ := Circle.exp_surjective c
    -- reduce φ - θ₀ to [0, 2π)
    set θ : ℝ := toIcoMod Real.two_pi_pos 0 (φ - θ₀) with hθ
    have hθmem : θ ∈ Ico 0 (2 * π) := by simpa [hθ] using toIcoMod_mem_Ico Real.two_pi_pos 0 (φ - θ₀)
    have hexp : Circle.exp φ = Circle.exp (θ₀ + θ) := by
      rw [Circle.exp_eq_exp]
      refine ⟨toIcoDiv Real.two_pi_pos 0 (φ - θ₀), ?_⟩
      have := self_sub_toIcoMod Real.two_pi_pos 0 (φ - θ₀)
      simp only [zsmul_eq_mul] at this
      rw [← hθ] at this
      linarith
    have hθC : θ ∈ C := ⟨⟨hθmem.1, hθmem.2.le⟩, by rw [← hexp]; exact hz⟩
    exact ⟨_, ⟨θ₀ + θ, ⟨by linarith [(hCab hθC).1], by linarith [(hCab hθC).2]⟩, rfl⟩, by rw [hexp]⟩
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, h⟩
    have h1 := hi h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h1
    have hlo : a ≤ u - θ₀ := by linarith [hu.1]
    have hhi : u - θ₀ ≤ b := by linarith [hu.2]
    have hm' : u - θ₀ = 2 * π * m := by linarith
    have hpos : (0 : ℝ) < m := by
      by_contra hcon; push Not at hcon
      nlinarith [Real.pi_pos]
    have hlt : (m : ℝ) < 1 := by
      by_contra hcon; push Not at hcon
      nlinarith [Real.pi_pos]
    have h1' : (0 : ℤ) < m := by exact_mod_cast hpos
    have h2' : m < (1 : ℤ) := by exact_mod_cast hlt
    omega

/-- **Every component of the complement of a Jordan curve has the whole curve as its frontier**
(the clause "each sharing `C` as boundary" of the Jordan Curve Theorem of the notes' chapter 9). The
proof is Lean's own: the arc theorem makes the complement of an arc of the curve connected, and a
component that missed a point of the curve in its frontier would be clopen in it. -/
theorem jordan_frontier {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {x : ℝ × ℝ} (hx : x ∉ range f) :
    frontier (connectedComponentIn (range f)ᶜ x) = range f := by
  have hJc : IsCompact (range f) := isCompact_range hc
  have hJo : IsOpen (range f)ᶜ := hJc.isClosed.isOpen_compl
  set U := connectedComponentIn (range f)ᶜ x with hU
  have hUo : IsOpen U := hJo.connectedComponentIn
  have hUJ : U ⊆ (range f)ᶜ := connectedComponentIn_subset _ _
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hint : interior U = U := hUo.interior_eq
  -- the frontier is in the curve
  have hfr : frontier U ⊆ range f := by
    intro z hz
    by_contra hzJ
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hJo z hzJ
    obtain ⟨y, hyb, hyU⟩ := mem_closure_iff.1 hz.1 (ball z r) isOpen_ball (mem_ball_self hr)
    have hpre : IsPreconnected (ball z r ∪ U) :=
      (isPreconnected_ball).union y hyb hyU isPreconnected_connectedComponentIn
    have hsub : ball z r ∪ U ⊆ U :=
      hpre.subset_connectedComponentIn (Or.inr hxU) (union_subset hball hUJ)
    have : z ∈ U := hsub (Or.inl (mem_ball_self hr))
    exact hz.2 (by rw [hint]; exact this)
  refine Subset.antisymm hfr ?_
  rintro _ ⟨w, rfl⟩
  by_contra hw
  have hFc : IsCompact (frontier U) := hJc.of_isClosed_subset isClosed_frontier hfr
  obtain ⟨B, s, t, hB, hFB, hBJ, hwB⟩ := exists_arc_of_compact hc hi hFc hfr hw
  have hconn := arc_not_separating hB
  have hsubU : Bᶜ ⊆ U := by
    refine hconn.subset_of_closure_inter_subset hUo ⟨x, fun hxB => hx (hBJ hxB), hxU⟩ ?_
    rintro z ⟨hzc, hzB⟩
    by_contra hzU
    exact hzB (hFB ⟨hzc, by rwa [hint]⟩)
  exact hUJ (hsubU hwB) ⟨w, rfl⟩

end Lightlike.PL
