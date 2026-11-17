import Lightlike.PL.Index

/-!
# The index of a loop is constant on path components of the complement

The index `loopIndex α Ω` of a loop `α` about a point `Ω` does not change when `Ω` moves along a path that avoids the
range of `α` (`loopIndex_eq_of_joinedIn`), and it vanishes when the loop lies in an open half plane seen from `Ω`
(`loopIndex_eq_zero_of_halfplane`).

The first is Lemma 9.13 and the second Lemma 9.12 of chapter 9 of J. McCleary, *A First Course in Topology:
Continuity and Dimension* (AMS, 2006); the numbering is that of the lecture-notes version of the chapter
(`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`), not checked against the printed book. The notes
prove Lemma 9.13 with a homeomorphism of `ℝ² − {Ω}` onto `ℝ² − {Ω'}` fixing the curve; here the logarithms of the loop
about the points of the path are lifted together through the covering map `exp` (`IsLocalHomeomorph.continuous_lift`),
and their increments, which differ by a constant, are compared with the integer at the first point. For Lemma 9.12 the
notes deform the loop into a small circle; here a continuous logarithm of the half plane is composed with the loop. The
statements and proofs are Lean's own.

## Main results

* `loopIndex_eq_of_joinedIn`: Lemma 9.13, the index is constant along a path in the complement of the loop.
* `loopIndex_eq_zero_of_halfplane`: Lemma 9.12, the index of a loop in a half plane is zero.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (the chapter location is verified with
  `scripts/sources.py verify`; the lemma-level numbering quoted above is that of the lecture-notes version and is
  not checked).
-/

open Complex unitInterval Real

namespace Lightlike.PL

/-- **The index of a loop is constant along a path in the complement of the loop** (Lemma 9.13 of the notes):
if `Ω` and `Ω'` are joined by a path that avoids the range of the loop `α`, they have the same index. -/
theorem loopIndex_eq_of_joinedIn {a : ℂ} (α : Path a a) {Ω Ω' : ℂ}
    (h : JoinedIn (Set.range α)ᶜ Ω Ω') : loopIndex α Ω = loopIndex α Ω' := by
  classical
  set lam := h.somePath with hlam
  have hmem : ∀ s, lam s ∉ Set.range α := fun s => h.somePath_mem s
  have hne : ∀ t s, α t - lam s ≠ 0 := fun t s hz =>
    hmem s ⟨t, (sub_eq_zero.1 hz)⟩
  have hcov := Complex.isCoveringMap_exp
  -- the family of paths and the base map
  let F : C(I × I, {w : ℂ // w ≠ 0}) :=
    ⟨fun p => ⟨α p.1 - lam p.2, hne p.1 p.2⟩,
      ((α.continuous.comp continuous_fst).sub (lam.continuous.comp continuous_snd)).subtype_mk
        (fun p => hne p.1 p.2)⟩
  let b : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun s => ⟨a - lam s, by have := hne 0 s; rwa [α.source] at this⟩,
      (continuous_const.sub lam.continuous).subtype_mk (fun s => by have := hne 0 s; rwa [α.source] at this)⟩
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, exp z₀ = a - lam 0 :=
    ⟨Complex.log (a - lam 0), exp_log (by have := hne 0 0; rwa [α.source] at this)⟩
  obtain ⟨e, he, he0⟩ := hcov.exists_path_lifts b z₀ (Subtype.ext hz₀.symm)
  have hexp : ∀ s, exp (e s) = a - lam s := fun s => congrArg Subtype.val (congrFun he s)
  -- the lift of each path of the family, starting at `e s`
  let slice : I → C(I, {w : ℂ // w ≠ 0}) := fun s =>
    ⟨fun t => F (t, s), F.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hstart : ∀ s, slice s 0 = (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) (e s) := by
    intro s
    apply Subtype.ext
    simp only [slice, F, ContinuousMap.coe_mk]
    rw [hexp s]
    simp
  let Γ : I → C(I, ℂ) := fun s => hcov.liftPath (slice s) (e s) (hstart s)
  let g : I × I → ℂ := fun p => Γ p.2 p.1
  have hg_lifts : (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ g = F := by
    funext p
    exact congrFun (hcov.liftPath_lifts (slice p.2) (e p.2) (hstart p.2)) p.1
  have hg_cont : Continuous g := hcov.isLocalHomeomorph.continuous_lift hcov.isSeparatedMap F hg_lifts
    (by
      have : (fun s => g (0, s)) = e := by
        funext s; exact hcov.liftPath_zero (slice s) (e s) (hstart s)
      show Continuous fun s => g (0, s)
      rw [this]; exact e.continuous)
    (fun s => (Γ s).continuous)
  -- the end values are two lifts of the same map
  have hG1 : ∀ s, exp (g (1, s)) = a - lam s := fun s => by
    have := congrArg Subtype.val (congrFun hg_lifts (1, s))
    simpa [F, α.target] using this
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hG1 0).trans (hexp 0).symm)
  have hmain : (fun s => g (1, s)) = fun s => e s + (n : ℂ) * (2 * π * Complex.I) := by
    refine hcov.eq_of_comp_eq (A := I)
      (f := fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {w : ℂ // w ≠ 0}))
      (hg_cont.comp (continuous_const.prodMk continuous_id)) (e.continuous.add continuous_const) ?_ 0 hn
    funext s
    apply Subtype.ext
    simp only [Function.comp_apply]
    rw [hG1 s, Complex.exp_add, hexp s]
    simp [Complex.exp_int_mul_two_pi_mul_I]
  -- the index at every point of the path is `n`
  have hidx : ∀ s, loopIndex α (lam s) = n := by
    intro s
    have hav : ∀ t, α t ≠ lam s := fun t ht => hmem s ⟨t, ht⟩
    have hlog : IsLog (α : C(I, ℂ)) (lam s) (Γ s) := fun t => by
      have := congrArg Subtype.val (congrFun hg_lifts (t, s))
      simpa [F] using this
    have h1 := loopIndex_spec α hav
    rw [logInc_eq α hav hlog] at h1
    have h2 : Γ s 1 - Γ s 0 = (n : ℂ) * (2 * π * Complex.I) := by
      have h3 : Γ s 1 = e s + (n : ℂ) * (2 * π * Complex.I) := congrFun hmain s
      have h4 : Γ s 0 = e s := hcov.liftPath_zero (slice s) (e s) (hstart s)
      rw [h3, h4]; ring
    rw [h2] at h1
    have hne2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_right_cancel₀ hne2 h1
    exact_mod_cast this.symm
  have h0 := hidx 0
  have h1 := hidx 1
  rw [lam.source] at h0
  rw [lam.target] at h1
  rw [h0, h1]

/-- **A loop in an open half plane about a point has index zero** (Lemma 9.12 of the notes: a line that misses the
loop, with the point and the loop on opposite sides, gives index zero). In coordinates, the half plane is
`{w | 0 < re (conj u * w)}` seen from `Ω`: the loop lies in `Ω + {w | 0 < re (conj u * w)}`. The proof: the half plane is
convex, hence simply connected, so `w ↦ w` has a continuous logarithm on it, and this logarithm composed with
`α - Ω` is a logarithm of the loop with equal ends. -/
theorem loopIndex_eq_zero_of_halfplane {a : ℂ} (α : Path a a) {Ω u : ℂ}
    (h : ∀ t, 0 < ((starRingEnd ℂ) u * (α t - Ω)).re) : loopIndex α Ω = 0 := by
  classical
  set S : Set ℂ := {w | 0 < ((starRingEnd ℂ) u * w).re} with hS
  have hlin : IsLinearMap ℝ (fun w : ℂ => ((starRingEnd ℂ) u * w).re) :=
    ⟨fun x y => by simp [mul_add], fun c x => by simp [Complex.real_smul]; ring⟩
  have hconv : Convex ℝ S := convex_halfSpace_gt hlin 0
  have hopen : IsOpen S := isOpen_lt continuous_const (by fun_prop)
  have hmem : ∀ t, α t - Ω ∈ S := h
  have : ContractibleSpace S := hconv.contractibleSpace ⟨_, hmem 0⟩
  have hsc : IsSimplyConnected S := inferInstanceAs (SimplyConnectedSpace S)
  obtain ⟨f, hf, hfe⟩ := Complex.exists_continuousOn_eqOn_exp_comp (U := S) hsc hopen
    (g := fun w : ℂ => w) continuousOn_id (by
      rintro ⟨w, hw, h0⟩
      have hw' : 0 < ((starRingEnd ℂ) u * w).re := hw
      have h00 : w = 0 := h0
      rw [h00] at hw'
      simp at hw')
  let ℓ : C(I, ℂ) := ⟨fun t => f (α t - Ω),
    hf.comp_continuous (α.continuous.sub continuous_const) hmem⟩
  have hav : ∀ t, α t ≠ Ω := fun t ht => by
    have := hmem t
    rw [ht, sub_self] at this
    simp [hS] at this
  have hlog : IsLog (α : C(I, ℂ)) Ω ℓ := fun t => hfe (hmem t)
  have h1 := loopIndex_spec α hav
  rw [logInc_eq α hav hlog] at h1
  have h2 : ℓ 1 - ℓ 0 = 0 := by
    show f (α 1 - Ω) - f (α 0 - Ω) = 0
    rw [α.source, α.target]; ring
  rw [h2] at h1
  have hne2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h3 : ((loopIndex α Ω : ℤ) : ℂ) = 0 := by
    rcases mul_eq_zero.1 h1.symm with h' | h'
    · exact h'
    · exact absurd h' hne2
  exact_mod_cast h3

end Lightlike.PL
