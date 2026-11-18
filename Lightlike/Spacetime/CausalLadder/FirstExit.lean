import Mathlib

/-!
# The first exit time of a continuous curve from an open set

A continuous path on `[a, b]` that starts in an open set `O` and does not stay in it has a first time
`t*` at which it is outside `O`; before `t*` it is inside `O`, and the point at `t*` lies in the
closure of `O`.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Set Filter Topology

namespace Lightlike.Causal

variable {X : Type*} [TopologicalSpace X]

/-- **First exit time.** See the module docstring. -/
theorem exists_first_exit {γ : ℝ → X} {a b : ℝ} (hcont : ContinuousOn γ (Icc a b)) {O : Set X}
    (hO : IsOpen O) (ha : γ a ∈ O) (hex : ∃ t ∈ Icc a b, γ t ∉ O) :
    ∃ t ∈ Ioc a b, γ t ∉ O ∧ (∀ s ∈ Ico a t, γ s ∈ O) ∧ γ t ∈ closure O := by
  set E : Set ℝ := Icc a b ∩ γ ⁻¹' Oᶜ with hE
  have hEc : IsClosed E := hcont.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hEne : E.Nonempty := by
    obtain ⟨t, ht, hnot⟩ := hex
    exact ⟨t, ht, hnot⟩
  have hEb : BddBelow E := ⟨a, fun t ht => ht.1.1⟩
  have hmem : sInf E ∈ E := hEc.csInf_mem hEne hEb
  set t₀ := sInf E with ht₀
  have hat : a < t₀ := by
    refine lt_of_le_of_ne hmem.1.1 fun h => ?_
    rw [← h] at hmem
    exact hmem.2 ha
  have hbefore : ∀ s ∈ Ico a t₀, γ s ∈ O := by
    intro s hs
    by_contra hnot
    have hsE : s ∈ E := ⟨⟨hs.1, hs.2.le.trans hmem.1.2⟩, hnot⟩
    exact absurd (csInf_le hEb hsE) (not_le.2 hs.2)
  refine ⟨t₀, ⟨hat, hmem.1.2⟩, hmem.2, hbefore, ?_⟩
  have hcw : ContinuousWithinAt γ (Ico a t₀) t₀ :=
    (hcont t₀ hmem.1).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hmem.1.2))
  have hne : (𝓝[Ico a t₀] t₀).NeBot := by
    rw [nhdsWithin_Ico_eq_nhdsLT hat]; infer_instance
  have := hcw.mem_closure_image (by rw [closure_Ico hat.ne]; exact right_mem_Icc.2 hat.le)
  exact closure_mono (image_subset_iff.2 fun s hs => hbefore s hs) this

end Lightlike.Causal
