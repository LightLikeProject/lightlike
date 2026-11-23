import Mathlib

/-!
# Uniform local connectedness

Row G3-188, milestone PL5 (third pass).  The limit argument of the topological Schoenflies theorem needs the
closure of the bounded Jordan component to be *uniformly locally connected* (the "UE property"): points of the set
that are close can be joined by a small connected subset of the set.  This file records the definition and the
elementary reduction: a compact set that is locally connected (small connected relative neighbourhoods) is
uniformly locally connected, by the Lebesgue number lemma.

* `UnifLocConn`: the definition.
* `unifLocConn_of_isCompact`: compact + locally connected ⇒ `UnifLocConn`.
-/

namespace Lightlike.PL.Schoenflies

open Set Metric Filter Topology

variable {α : Type*} [PseudoMetricSpace α]

/-- A set `s` is *uniformly locally connected*: for every `ε > 0` there is `δ > 0` such that any two points of `s`
at distance `< δ` lie in a connected subset of `s` of radius `< ε` around the first point. -/
def UnifLocConn (s : Set α) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ s, dist x y < δ →
    ∃ C : Set α, C ⊆ s ∧ C ⊆ ball x ε ∧ IsConnected C ∧ x ∈ C ∧ y ∈ C

/-- A compact set with small connected relative neighbourhoods at each of its points is uniformly locally
connected. -/
theorem unifLocConn_of_isCompact {s : Set α} (hs : IsCompact s)
    (hloc : ∀ x ∈ s, ∀ ε > 0, ∃ C : Set α, C ⊆ s ∧ C ⊆ ball x ε ∧ IsConnected C ∧ C ∈ 𝓝[s] x) :
    UnifLocConn s := by
  intro ε hε
  have h2 : ∀ x : s, ∃ C : Set α, C ⊆ s ∧ C ⊆ ball (x : α) (ε / 2) ∧ IsConnected C ∧ C ∈ 𝓝[s] (x : α) :=
    fun x => hloc x x.2 (ε / 2) (half_pos hε)
  choose C hCs hCb hCc hCn using h2
  have h3 : ∀ x : s, ∃ O : Set α, IsOpen O ∧ (x : α) ∈ O ∧ O ∩ s ⊆ C x := by
    intro x
    obtain ⟨O, hO, hxO, hOC⟩ := mem_nhdsWithin.1 (hCn x)
    exact ⟨O, hO, hxO, hOC⟩
  choose O hOo hxO hOC using h3
  obtain ⟨δ, hδ, hδO⟩ := lebesgue_number_lemma_of_metric hs (c := O) hOo
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxO ⟨x, hx⟩⟩)
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  obtain ⟨i, hi⟩ := hδO x hx
  have hxC : x ∈ C i := hOC i ⟨hi (mem_ball_self hδ), hx⟩
  have hyC : y ∈ C i := hOC i ⟨hi (by simpa [mem_ball, dist_comm] using hxy), hy⟩
  refine ⟨C i, hCs i, fun z hz => ?_, hCc i, hxC, hyC⟩
  have h1 := hCb i hz
  have h2 := hCb i hxC
  rw [mem_ball] at h1 h2 ⊢
  calc dist z x ≤ dist z i + dist (i : α) x := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm (i : α) x]; exact add_lt_add h1 h2
    _ = ε := by ring

end Lightlike.PL.Schoenflies
