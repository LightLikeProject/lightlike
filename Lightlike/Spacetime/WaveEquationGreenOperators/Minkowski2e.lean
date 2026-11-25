module

public import Mathlib
public import Lightlike.Spacetime.WaveEquationGreenOperators.Minkowski2d

/-!
# The advanced Green operator and the Pauli–Jordan propagator in 1+1 Minkowski (row G1-059)

Mirror of `Minkowski2d.lean` for the advanced operator `Gadv` (BGP key `bgp-2007`, Section 3.4):
the point reflection `p ↦ -p` preserves `box` and `PartDiff`, so Cauchy uniqueness in the past cone
`Jm` follows from the one in the future cone; hence `Gadv` is an advanced Green operator
(`Gadv_isGreen`) and is the only one with `PartDiff` values (`Gadv_unique`).  Finally the
Pauli–Jordan propagator `E = Gret - Gadv` of Minkowski space solves the wave equation and kills
`box f` (`pauliJordan_box_ker`, `pauliJordan_box_comp`).

* `PartDiff.comp_neg`, `Gadv_partDiff`: regularity under the reflection;
* `cauchyUnique_box_adv`: Cauchy uniqueness in the past cone;
* `Gadv_isGreen`, `Gadv_unique`: existence and uniqueness of the advanced operator;
* `pauliJordan_box_ker`, `pauliJordan_box_comp`: the Pauli–Jordan propagator of Minkowski space.
-/

@[expose] public section

open MeasureTheory Set

namespace Lightlike.GreenOps.Mink2

/-- `PartDiff` is stable under the point reflection. -/
lemma PartDiff.comp_neg {h : ℝ × ℝ → ℝ} (hh : PartDiff h) : PartDiff (fun p => h (-p)) := by
  refine ⟨fun u => ?_, fun v => ?_⟩
  · have : Differentiable ℝ fun v : ℝ => h (-u, -v) := (hh.1 (-u)).comp differentiable_neg
    simpa using this
  · have h1 : ∀ u : ℝ, deriv (fun v' => h (-(u, v'))) v =
        -deriv (fun v' => h (-u, v')) (-v) := by
      intro u
      have := deriv_comp_neg (f := fun v' => h (-u, v')) (x := v)
      simpa using this
    have e : (fun u : ℝ => deriv (fun v' => (fun p => h (-p)) (u, v')) v) =
        fun u => -(fun w => deriv (fun v' => h (w, v')) (-v)) (-u) := by
      funext u
      exact h1 u
    rw [e]
    exact ((hh.2 (-v)).comp differentiable_neg).neg

/-- `Gadv f` is `PartDiff` for continuous compactly supported `f`. -/
lemma Gadv_partDiff {f : ℝ × ℝ → ℝ} (hc : Continuous f) (hcs : HasCompactSupport f) :
    PartDiff (Gadv f) :=
  (Gret_partDiff (hc.comp continuous_neg) (hcs.comp_homeomorph (Homeomorph.neg _))).comp_neg

/-- Cauchy uniqueness for `box` among `PartDiff` solutions supported in the past cone
`Jm (supp f)` of a test function. -/
theorem cauchyUnique_box_adv : CauchyUniqueOn PartDiff box Test Jm := by
  intro h f hh hf hb hs
  obtain ⟨R, hR⟩ := exists_bound hf.2
  have hb' : box (fun p => h (-p)) = 0 := by
    rw [box_comp_neg, hb]; rfl
  have h0 := eq_zero_of_box_eq_zero hh.comp_neg (R := R) (fun p hp => ?_) hb'
  · funext p
    have := congrFun h0 (-p)
    simpa using this
  · obtain ⟨q, hq, h1, h2⟩ := hs (show -p ∈ _ from hp)
    have := hR q hq
    simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2
    constructor
    · linarith [(abs_lt.mp this.1).2]
    · linarith [(abs_lt.mp this.2).2]

/-- **Existence** (advanced half): `Gadv` is an advanced Green operator of `box` on the test
functions, with support rule `Jm` (BGP key `bgp-2007`, Section 3.4). -/
theorem Gadv_isGreen : IsGreen box Test Jm Gadv where
  left_inv _ hf := box_Gadv hf.1.continuous hf.2
  right_inv _ hf := Gadv_box hf.1 hf.2
  supp_subset f _ := support_Gadv_subset f

/-- **Uniqueness** (advanced half): an advanced Green operator `G` of `box` whose value on the test
function `f` is `PartDiff` agrees with `Gadv` on `f`. -/
theorem Gadv_unique {G : (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ)} (hG : IsGreen box Test Jm G)
    {f : ℝ × ℝ → ℝ} (hf : Test f) (hGf : PartDiff (G f)) : Gadv f = G f :=
  IsGreen.eq_of_cauchyUniqueOn (fun _ _ hg hh => box_sub hg hh)
    (fun _ _ hg hh => PartDiff.sub hg hh) cauchyUnique_box_adv
    Gadv_isGreen hG hf (Gadv_partDiff hf.1.continuous hf.2) hGf

/-- The Pauli–Jordan propagator `E = Gret - Gadv` of Minkowski space solves the wave equation:
`box (E f) = 0` for every test function `f`. -/
theorem pauliJordan_box_ker {f : ℝ × ℝ → ℝ} (hf : Test f) :
    box (pauliJordan Gret Gadv f) = 0 :=
  by
    unfold pauliJordan
    rw [box_sub (Gret_partDiff hf.1.continuous hf.2) (Gadv_partDiff hf.1.continuous hf.2),
      Gret_isGreen.left_inv f hf, Gadv_isGreen.left_inv f hf, sub_self]

/-- The Pauli–Jordan propagator of Minkowski space kills `box f`: `E (box f) = 0`. -/
theorem pauliJordan_box_comp {f : ℝ × ℝ → ℝ} (hf : Test f) :
    pauliJordan Gret Gadv (box f) = 0 :=
  pauliJordan_comp Gret_isGreen Gadv_isGreen hf

end Lightlike.GreenOps.Mink2
