import Mathlib
import Lightlike.TemperleyLieb.Complete
import Lightlike.TemperleyLieb.Reduction

/-!
# The finite window of the model

`Win N` is the span of the basis sequences that vanish from position `N` on: a finite-dimensional subspace of
`ModelSpace k` of dimension `2^N`.  The generators `e_j` with `j + 2 ≤ N` preserve it, hence so does every element
of `tlSub (modelE q) (N - 1)`.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- The sequences vanishing from position `N` on. -/
def tailZero (N : ℕ) : Set (ℕ → Bool) := {σ | ∀ j, N ≤ j → σ j = false}

/-- The window: combinations of sequences with zero tail beyond `N`. -/
noncomputable def Win (k : Type*) [Field k] (N : ℕ) : Submodule k (ModelSpace k) :=
  Finsupp.supported k k (tailZero N)

/-- The set of window sequences is finite. -/
lemma tailZero_finite (N : ℕ) : (tailZero N).Finite := by
  have : tailZero N ⊆ Set.range (fun f : Fin N → Bool => fun j : ℕ => if h : j < N then f ⟨j, h⟩ else false) := by
    intro σ hσ
    refine ⟨fun i => σ i, ?_⟩
    funext j
    by_cases h : j < N
    · simp [h]
    · simp [h, hσ j (by omega)]
  exact Set.Finite.subset (Set.finite_range _) this

/-- The window is finite-dimensional. -/
instance (N : ℕ) : Module.Finite k (Win k N) := by
  have : Finite (tailZero N) := (tailZero_finite N).to_subtype
  unfold Win
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp (M := k) (R := k) (tailZero N)).symm

/-- A basis vector of the window. -/
lemma single_mem_Win {N : ℕ} {σ : ℕ → Bool} (h : σ ∈ tailZero N) (c : k) : single σ c ∈ Win k N :=
  Finsupp.single_mem_supported k c h

/-- Setting bits below `N` keeps a sequence in the window. -/
lemma set2_mem_tailZero {N j : ℕ} (hj : j + 2 ≤ N) {σ : ℕ → Bool} (h : σ ∈ tailZero N) (x y : Bool) :
    set2 σ j x y ∈ tailZero N := by
  intro n hn
  simp only [set2, Function.update_apply]
  split_ifs with h1 h2 <;> first | exact h n hn | (exfalso; omega)

/-- The generator `e_j` preserves the window when `j + 2 ≤ N`. -/
theorem modelE_preserves (q : kˣ) {N j : ℕ} (hj : j + 2 ≤ N) :
    ∀ v ∈ Win k N, modelE q j v ∈ Win k N := by
  intro v hv
  have hv' : v ∈ Submodule.span k ((fun σ => single σ (1 : k)) '' tailZero N) := by
    rw [Win, Finsupp.supported_eq_span_single] at hv; exact hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    simp only [modelE_single, one_smul, eBasis]
    rcases h0 : σ j with _ | _ <;> rcases h1 : σ (j + 1) with _ | _ <;> simp only []
    · exact Submodule.zero_mem _
    · exact Submodule.sub_mem _ (single_mem_Win (set2_mem_tailZero hj hσ _ _) _)
        (Submodule.smul_mem _ _ (single_mem_Win hσ _))
    · exact Submodule.sub_mem _ (single_mem_Win (set2_mem_tailZero hj hσ _ _) _)
        (Submodule.smul_mem _ _ (single_mem_Win hσ _))
    · exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Every element of the Temperley–Lieb subalgebra `C m` with `m + 1 ≤ N` preserves the window. -/
theorem preserves_of_mem (q : kˣ) {N m : ℕ} (hm : m + 1 ≤ N) {x : Module.End k (ModelSpace k)}
    (hx : x ∈ CSub q m) : ∀ v ∈ Win k N, x v ∈ Win k N := by
  unfold CSub tlSub at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact modelE_preserves q (by omega)
  | algebraMap r =>
    intro v hv
    rw [Algebra.algebraMap_eq_smul_one]
    simpa using Submodule.smul_mem _ r hv
  | add x y _ _ hx hy => intro v hv; rw [LinearMap.add_apply]; exact Submodule.add_mem _ (hx v hv) (hy v hv)
  | mul x y _ _ hx hy => intro v hv; rw [Module.End.mul_apply]; exact hx _ (hy v hv)

end Lightlike.TemperleyLieb
