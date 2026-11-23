import Mathlib
import Lightlike.PL.JordanCurve

/-!
# The closed inner region of a Jordan curve

Row G3-188, milestone PL5 (third pass).  Repackaging of `jordan_curve_theorem` in the form used by the
topological Schoenflies programme: the closed inner region `closure U = U ∪ J` is compact, and its complement is
the connected unbounded open outer component.

* `jordan_inner_closure`: for a Jordan curve `f`, there are an open connected bounded `U` and a connected
  unbounded open `V` with `closure U = U ∪ range f`, `V = (closure U)ᶜ`, `frontier U = range f`.
-/

namespace Lightlike.PL.Schoenflies

open Set

theorem jordan_inner_closure {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) :
    ∃ U V : Set (ℝ × ℝ), IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ IsOpen V ∧ IsConnected V ∧
      ¬ Bornology.IsBounded V ∧ frontier U = range f ∧ closure U = U ∪ range f ∧
      IsCompact (closure U) ∧ V = (closure U)ᶜ ∧ Disjoint U (range f) := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdis, hunion, hUb, hVb, hfU, -⟩ := jordan_curve_theorem hc hi
  have hcl : closure U = U ∪ range f := by
    rw [closure_eq_interior_union_frontier, hUo.interior_eq, hfU]
  have hUJ : Disjoint U (range f) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have : w ∈ U ∪ V := Or.inl hw
    rw [hunion] at this
    exact this hw'
  refine ⟨U, V, hUo, hUc, hUb, hVo, hVc, hVb, hfU, hcl, ?_, ?_, hUJ⟩
  · exact Metric.isCompact_of_isClosed_isBounded isClosed_closure hUb.closure
  · ext w
    rw [hcl, mem_compl_iff, mem_union, not_or]
    constructor
    · intro hw
      have hw' : w ∈ (range f)ᶜ := by rw [← hunion]; exact Or.inr hw
      refine ⟨fun hU => ?_, hw'⟩
      exact Set.disjoint_left.1 hdis hU hw
    · rintro ⟨hU, hJ⟩
      have : w ∈ U ∪ V := by rw [hunion]; exact hJ
      exact this.resolve_left hU

end Lightlike.PL.Schoenflies
