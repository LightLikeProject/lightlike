import Mathlib
import Lightlike.PL.Schoenflies.JordanClosure

/-!
# Filling the holes of a compact subset of the inner region of a Jordan curve

Row G3-188, milestone PL5 (third pass), item 5b (exhaustion of the inner region by polygons).  A compact set
`N` inside the inner region `U` of a Jordan curve can be filled: the bounded components of the complement of
`N` lie in `U`, so the compact set `C` obtained by adding them still lies in `U`, and its complement is open
and connected.  This is the first step towards a simple polygon in `U` that surrounds `N`.

* `exists_filled`: abstract form, for an open bounded `U` and a connected `V` disjoint from `U` whose closure
  contains `Uᶜ`.
* `exists_filled_nhds`: the filled set can be taken to contain a neighbourhood of `N`.
* `jordan_exists_filled`: the form for a Jordan curve.
-/

namespace Lightlike.PL.Schoenflies

open Set Metric

/-- **Filling holes.** Let `U` be open and bounded, `V` connected and disjoint from `U`, with `Uᶜ ⊆ closure V`.
Every compact `N ⊆ U` lies in a compact `C ⊆ U` with open connected complement. -/
theorem exists_filled {U V : Set (ℝ × ℝ)} (hUb : Bornology.IsBounded U)
    (hV : IsConnected V) (hVU : Disjoint V U) (hcov : Uᶜ ⊆ closure V)
    {N : Set (ℝ × ℝ)} (hN : IsCompact N) (hNU : N ⊆ U) :
    ∃ C : Set (ℝ × ℝ), IsCompact C ∧ N ⊆ C ∧ C ⊆ U ∧ IsOpen Cᶜ ∧ IsConnected Cᶜ := by
  obtain ⟨v, hv⟩ := hV.nonempty
  have hNo : IsOpen Nᶜ := hN.isClosed.isOpen_compl
  have hVsub : V ⊆ Nᶜ := fun z hz hzN => Set.disjoint_left.1 hVU hz (hNU hzN)
  have hVO : V ⊆ connectedComponentIn Nᶜ v :=
    hV.isPreconnected.subset_connectedComponentIn hv hVsub
  have hvN : v ∈ Nᶜ := hVsub hv
  have hOo : IsOpen (connectedComponentIn Nᶜ v) := hNo.connectedComponentIn
  have hOc : IsConnected (connectedComponentIn Nᶜ v) := isConnected_connectedComponentIn_iff.2 hvN
  have hCU : (connectedComponentIn Nᶜ v)ᶜ ⊆ U := by
    intro z hz
    by_contra hzU
    apply hz
    have hzf : z ∈ closure V := hcov hzU
    have hzN : z ∈ Nᶜ := fun h => hzU (hNU h)
    obtain ⟨r, hr, hrN⟩ := Metric.isOpen_iff.1 hNo z hzN
    obtain ⟨w, hwV, hwb⟩ := Metric.mem_closure_iff.1 hzf r hr
    have hwb' : w ∈ ball z r := by rw [mem_ball, dist_comm]; exact hwb
    have hwO : w ∈ connectedComponentIn Nᶜ v := hVO hwV
    have hsub := (convex_ball z r).isPreconnected.subset_connectedComponentIn hwb' hrN
    rw [connectedComponentIn_eq hwO]
    exact hsub (mem_ball_self hr)
  refine ⟨(connectedComponentIn Nᶜ v)ᶜ, ?_, ?_, hCU, ?_, ?_⟩
  · exact Metric.isCompact_of_isClosed_isBounded hOo.isClosed_compl (hUb.subset hCU)
  · intro z hz hzO
    exact connectedComponentIn_subset _ _ hzO hz
  · rw [compl_compl]; exact hOo
  · rw [compl_compl]; exact hOc

/-- The filled set can be taken to contain a neighbourhood of `N`. -/
theorem exists_filled_nhds {U V : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hV : IsConnected V) (hVU : Disjoint V U) (hcov : Uᶜ ⊆ closure V)
    {N : Set (ℝ × ℝ)} (hN : IsCompact N) (hNU : N ⊆ U) :
    ∃ C : Set (ℝ × ℝ), IsCompact C ∧ N ⊆ interior C ∧ C ⊆ U ∧ IsOpen Cᶜ ∧ IsConnected Cᶜ := by
  obtain ⟨δ, hδ, hsub⟩ := hN.exists_cthickening_subset_open hUo hNU
  obtain ⟨C, hCc, hNC, hCU, hCo, hCcon⟩ :=
    exists_filled hUb hV hVU hcov (hN.cthickening (r := δ)) hsub
  refine ⟨C, hCc, ?_, hCU, hCo, hCcon⟩
  have : N ⊆ interior (cthickening δ N) := by
    intro x hx
    exact (thickening_subset_interior_cthickening δ N) (self_subset_thickening hδ N hx)
  exact this.trans (interior_mono hNC)

/-- **Jordan curves.** For a Jordan curve with inner component `U`, every compact `N ⊆ U` is contained in the
interior of a compact `C ⊆ U` with open connected complement. -/
theorem jordan_exists_filled {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = range f ∧
      closure U = U ∪ range f ∧ Disjoint U (range f) ∧
      ∀ N : Set (ℝ × ℝ), IsCompact N → N ⊆ U →
        ∃ C : Set (ℝ × ℝ), IsCompact C ∧ N ⊆ interior C ∧ C ⊆ U ∧ IsOpen Cᶜ ∧ IsConnected Cᶜ := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdis, hun, hUb, hVb, hfU, hfV⟩ := jordan_curve_theorem hc hi
  have hcl : closure U = U ∪ range f := by
    rw [closure_eq_interior_union_frontier, hUo.interior_eq, hfU]
  have hUJ : Disjoint U (range f) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have : w ∈ U ∪ V := Or.inl hw
    rw [hun] at this
    exact this hw'
  refine ⟨U, hUo, hUc, hUb, hfU, hcl, hUJ, fun N hN hNU => ?_⟩
  refine exists_filled_nhds hUo hUb hVc hdis.symm ?_ hN hNU
  intro z hz
  have hz' : z ∈ V ∪ range f := by
    by_cases hzJ : z ∈ range f
    · exact Or.inr hzJ
    · left
      have : z ∈ U ∪ V := by rw [hun]; exact hzJ
      exact this.resolve_left hz
  rcases hz' with h | h
  · exact subset_closure h
  · rw [← hfV] at h
    exact frontier_subset_closure h

end Lightlike.PL.Schoenflies
