module

public import Mathlib
public import Lightlike.Rows.G1_059.Abstract

/-!
# A spacetime with closed timelike curves where uniqueness fails (row G1-059, milestone SC6)

Trust check of SC6: the uniqueness half of the Green operator theorem (BGP, Section 3.4, key
`bgp-2007`) needs global hyperbolicity. We exhibit the standard counterexample: the flat cylinder
`M = S¹ × ℝ` with `S¹ = AddCircle 1` the (periodic) time and `ℝ` the space, metric `-dt² + dx²`.
Its closed timelike curves make every point lie in the causal future of every point
(`Jfut_singleton`), and the constant function `1` solves the wave equation with support in
`J⁺ (supp f)` for every nonzero test function `f`. Hence `CauchyUnique` fails
(`not_cauchyUnique_cylinder`).

* `Cyl`: the cylinder; `Jfut`: its causal future (endpoints of future causal curves, lifted to `ℝ`);
* `Jfut_singleton`: `J⁺ {p} = univ`;
* `waveCyl`: the wave operator `-∂ₜ² + ∂ₓ²` in the cylinder coordinates;
* `not_cauchyUnique_cylinder`: `¬ CauchyUnique waveCyl TestCyl Jfut`.
-/

@[expose] public section

namespace Lightlike.GreenOps.CTC

/-- The flat cylinder `S¹ × ℝ`: periodic time, one space dimension. -/
abbrev Cyl : Type := AddCircle (1 : ℝ) × ℝ

/-- Causal future on the cylinder: `q ∈ J⁺ S` if some `p ∈ S` and some lifted time lapse `T ≥ 0`
(representing `q.1 - p.1` modulo `1`) satisfy `|Δx| ≤ T`, i.e. a future causal curve joins them. -/
def Jfut (S : Set Cyl) : Set Cyl :=
  {q | ∃ p ∈ S, ∃ T : ℝ, 0 ≤ T ∧ ((T : ℝ) : AddCircle (1 : ℝ)) = q.1 - p.1 ∧ |q.2 - p.2| ≤ T}

/-- On the cylinder every point lies in the causal future of every point. -/
theorem Jfut_singleton (p : Cyl) : Jfut {p} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨r, hr⟩ : ∃ r : ℝ, ((r : ℝ) : AddCircle (1 : ℝ)) = q.1 - p.1 :=
    QuotientAddGroup.mk_surjective (q.1 - p.1)
  refine ⟨p, rfl, r + (⌈|r| + |q.2 - p.2|⌉ : ℤ), ?_, ?_, ?_⟩
  · have h1 := Int.le_ceil (|r| + |q.2 - p.2|)
    have h2 := neg_abs_le r
    have h3 := abs_nonneg (q.2 - p.2)
    linarith
  · have hz : (((⌈|r| + |q.2 - p.2|⌉ : ℤ) : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨⌈|r| + |q.2 - p.2|⌉, by simp⟩
    rw [QuotientAddGroup.mk_add, hz, add_zero, hr]
  · have h1 := Int.le_ceil (|r| + |q.2 - p.2|)
    have h2 := neg_abs_le r
    linarith

/-- The wave operator `-∂ₜ² + ∂ₓ²` on the cylinder, the time derivative being taken on a lift of
the time to `ℝ` (the value does not depend on the lift for functions of the cylinder). -/
noncomputable def waveCyl (h : Cyl → ℝ) : Cyl → ℝ := fun q =>
  -(deriv (deriv (fun s : ℝ => h ((s : AddCircle (1 : ℝ)), q.2)))
      (Classical.choose (QuotientAddGroup.mk_surjective q.1 :
        ∃ s : ℝ, ((s : ℝ) : AddCircle (1 : ℝ)) = q.1)))
    + deriv (deriv (fun y : ℝ => h (q.1, y))) q.2

/-- Test functions on the cylinder (continuous, compact support; the smoothness is irrelevant for
the counterexample). -/
def TestCyl (f : Cyl → ℝ) : Prop := Continuous f ∧ HasCompactSupport f

/-- A nonzero test function on the cylinder: a tent in the space variable. -/
noncomputable def tent : Cyl → ℝ := fun q => max (1 - |q.2|) 0

theorem tent_test : TestCyl tent := by
  refine ⟨by unfold tent; fun_prop, ?_⟩
  apply HasCompactSupport.intro (K := Set.univ ×ˢ Set.Icc (-1 : ℝ) 1)
  · exact isCompact_univ.prod isCompact_Icc
  · intro q hq
    have : ¬ (q.2 ∈ Set.Icc (-1 : ℝ) 1) := fun h => hq ⟨trivial, h⟩
    simp only [Set.mem_Icc, not_and_or, not_le] at this
    unfold tent
    rcases this with h | h
    · have : 1 - |q.2| < 0 := by
        have := neg_le_abs q.2
        linarith
      simp [max_eq_right this.le]
    · have : 1 - |q.2| < 0 := by have := le_abs_self q.2; linarith
      simp [max_eq_right this.le]

theorem tent_support_nonempty : (Function.support tent).Nonempty :=
  ⟨(0, 0), by simp [tent]⟩

/-- **Uniqueness fails with closed timelike curves**: on the cylinder `S¹ × ℝ`, the constant
function `1` solves `P h = 0` with support in `J⁺ (supp f)` for the nonzero test function `f = tent`,
so `CauchyUnique` does not hold (and the uniqueness half of BGP, Section 3.4 breaks down). -/
theorem not_cauchyUnique_cylinder : ¬ CauchyUnique waveCyl TestCyl Jfut := by
  intro hU
  obtain ⟨p, hp⟩ := tent_support_nonempty
  have hJ : Jfut (Function.support tent) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    have hq : q ∈ Jfut {p} := by rw [Jfut_singleton]; trivial
    obtain ⟨p', hp', T, hT⟩ := hq
    rw [Set.mem_singleton_iff] at hp'
    subst hp'
    exact ⟨p', hp, T, hT⟩
  have h1 : waveCyl (fun _ => (1 : ℝ)) = 0 := by
    funext q
    simp [waveCyl]
  have := hU (fun _ => (1 : ℝ)) tent tent_test h1 (by rw [hJ]; exact Set.subset_univ _)
  have := congrFun this (0, 0)
  simp at this

end Lightlike.GreenOps.CTC
