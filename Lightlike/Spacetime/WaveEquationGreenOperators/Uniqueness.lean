import Mathlib
import Lightlike.Spacetime.WaveEquationGreenOperators.Retarded

/-!
# Uniqueness of the retarded Green operator of the `1+1` wave operator

The homogeneous problem `∂_v ∂_u h = 0` for a smooth `h` vanishing on `{u < c}` and on `{v < c}`
has only the zero solution (two integrations).  Since the support of a solution supported in
`J⁺ (supp f)` for a compactly supported `f` vanishes in such regions, the hypothesis of
`IsGreenOperator.unique` holds, and the retarded Green operator is unique
(cf. bgp-2007, §3.4).

## Main results

* `Lightlike.Spacetime.WaveEquationGreenOperators.eq_zero_of_wave_eq_zero`: the homogeneous problem with data vanishing in
  the far past has only the trivial solution.
* `Lightlike.Spacetime.WaveEquationGreenOperators.retarded_unique`: any Green operator for `(wave, causalFuture)` is the
  retarded operator `retarded`.
-/

open Function MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Lightlike.Spacetime.WaveEquationGreenOperators

/-- The slice of a smooth function in the `v` direction has derivative `∂_v g`. -/
theorem hasDerivAt_slice_snd {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (a s : ℝ) :
    HasDerivAt (fun s => g (a, s)) (fderiv ℝ g (a, s) (0, 1)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (a, s)) ((0, 1) : ℝ × ℝ) s :=
    (hasDerivAt_const s a).prodMk (hasDerivAt_id s)
  exact ((hg.differentiable (by simp)) (a, s)).hasFDerivAt.comp_hasDerivAt s h1

/-- The slice of a smooth function in the `u` direction has derivative `∂_u g`. -/
theorem hasDerivAt_slice_fst {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (s b : ℝ) :
    HasDerivAt (fun s => g (s, b)) (fderiv ℝ g (s, b) (1, 0)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s, b)) ((1, 0) : ℝ × ℝ) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s b)
  exact ((hg.differentiable (by simp)) (s, b)).hasFDerivAt.comp_hasDerivAt s h1

/-- **Homogeneous uniqueness**: a smooth solution of `∂_v ∂_u h = 0` vanishing on `{u < c}` and on
`{v < c}` is zero. -/
theorem eq_zero_of_wave_eq_zero {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (hw : ∀ p, fderiv ℝ (fun q => fderiv ℝ h q (1, 0)) p (0, 1) = 0) (c : ℝ)
    (h1 : ∀ p : ℝ × ℝ, p.1 < c → h p = 0) (h2 : ∀ p : ℝ × ℝ, p.2 < c → h p = 0) :
    ∀ p, h p = 0 := by
  have hg : ContDiff ℝ ∞ (fun q => fderiv ℝ h q (1, 0)) := contDiff_dirDeriv hh _
  -- `∂_u h = 0`
  have hg0 : ∀ u v : ℝ, fderiv ℝ h (u, v) (1, 0) = 0 := by
    intro u v
    have hconst : fderiv ℝ h (u, v) (1, 0) = fderiv ℝ h (u, c - 1) (1, 0) := by
      refine is_const_of_deriv_eq_zero (f := fun s => fderiv ℝ h (u, s) (1, 0)) ?_ ?_ v (c - 1)
      · intro s
        exact (((hg.differentiable (by simp)) (u, s)).hasFDerivAt.comp_hasDerivAt s
          ((hasDerivAt_const s u).prodMk (hasDerivAt_id s))).differentiableAt
      · intro s
        have := ((hg.differentiable (by simp)) (u, s)).hasFDerivAt.comp_hasDerivAt s
          ((hasDerivAt_const s u).prodMk (hasDerivAt_id s))
        have h0 := hw (u, s)
        simp only [Function.comp_def] at this
        rw [this.deriv]
        exact h0
    have hz : fderiv ℝ h (u, c - 1) (1, 0) = 0 := by
      have hd := hasDerivAt_slice_fst hh u (c - 1)
      have hfun : (fun s => h (s, c - 1)) = fun _ => 0 :=
        funext fun s => h2 (s, c - 1) (by simp)
      rw [hfun] at hd
      exact hd.unique (hasDerivAt_const u (0 : ℝ))
    rw [hconst, hz]
  rintro ⟨u, v⟩
  have hc : h (u, v) = h (c - 1, v) := by
    refine is_const_of_deriv_eq_zero (f := fun s => h (s, v)) ?_ ?_ u (c - 1)
    · intro s
      exact (hasDerivAt_slice_fst hh s v).differentiableAt
    · intro s
      rw [(hasDerivAt_slice_fst hh s v).deriv]
      exact hg0 s v
  rw [hc]
  exact h1 (c - 1, v) (by simp)

/-- A solution of the homogeneous problem supported in `J⁺ (supp f)` for a test function `f` is
zero. -/
theorem retarded_hU (f : testFns) (h : smoothFns) (hw : wave h = 0)
    (hs : support (h : ℝ × ℝ → ℝ) ⊆ causalFuture (support (f : ℝ × ℝ → ℝ))) : h = 0 := by
  have hcpt : IsCompact (tsupport (f : ℝ × ℝ → ℝ)) := f.2.2
  obtain ⟨b1, hb1⟩ := (hcpt.image continuous_fst).bddBelow
  obtain ⟨b2, hb2⟩ := (hcpt.image continuous_snd).bddBelow
  have hout : ∀ p : ℝ × ℝ, (p.1 < b1 ∨ p.2 < b2) → (h : ℝ × ℝ → ℝ) p = 0 := by
    intro p hp
    by_contra hne
    obtain ⟨s, hsf, hs1, hs2⟩ := hs hne
    have hst : s ∈ tsupport (f : ℝ × ℝ → ℝ) := subset_tsupport _ hsf
    have e1 : b1 ≤ s.1 := hb1 ⟨s, hst, rfl⟩
    have e2 : b2 ≤ s.2 := hb2 ⟨s, hst, rfl⟩
    rcases hp with hp | hp <;> linarith
  have hw' : ∀ p, fderiv ℝ (fun q => fderiv ℝ (h : ℝ × ℝ → ℝ) q (1, 0)) p (0, 1) = 0 := fun p =>
    congrFun (congrArg Subtype.val hw) p
  have hz := eq_zero_of_wave_eq_zero (show ContDiff ℝ ∞ (h : ℝ × ℝ → ℝ) from h.2) hw'
    (min b1 b2) (fun p hp => hout p (Or.inl (lt_of_lt_of_le hp (min_le_left _ _))))
    (fun p hp => hout p (Or.inr (lt_of_lt_of_le hp (min_le_right _ _))))
  exact Subtype.ext (funext hz)

/-- **Uniqueness of the retarded Green operator** of the `1+1` wave operator `∂_v ∂_u`: any
Green operator with support rule `J⁺` equals `retarded` (cf. bgp-2007, §3.4). -/
theorem retarded_unique {G : testFns →ₗ[ℝ] smoothFns}
    (hG : IsGreenOperator smoothFns testFns testFns_le wave causalFuture G) : G = retarded :=
  hG.unique isGreenOperator_retarded retarded_hU

end Lightlike.Spacetime.WaveEquationGreenOperators

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.eq_zero_of_wave_eq_zero := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.eq_zero_of_wave_eq_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.hasDerivAt_slice_fst := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.hasDerivAt_slice_fst
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.hasDerivAt_slice_snd := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.hasDerivAt_slice_snd
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.retarded_hU := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.retarded_hU
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.retarded_unique := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.retarded_unique
