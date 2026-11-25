import Mathlib

/-!
# The polymer Hilbert space

Row G2-017 (milestone CA7).  In loop quantum cosmology the kinematical Hilbert space of the flat FRW
model is the *polymer Hilbert space*: the Hilbert space spanned by orthonormal kets `|μ⟩`, `μ ∈ ℝ`, one for
every real number, with `⟨μ|ν⟩ = δ_{μν}` (the Kronecker, not the Dirac, delta); it is `L²` of the Bohr
compactification of `ℝ` for its Haar measure, and the almost periodic functions `e^{iλb}` act on it by the
shifts `|μ⟩ ↦ |μ + λ⟩`.  Mathlib has no Bohr compactification, so here the space is *defined* by its kets, as
`ℓ²(ℝ)`, the Hilbert sum of uncountably many copies of `ℂ` (Mathlib's `lp`); the identification with
`L²(bohr ℝ)` is not proved.

## Main definitions and statements

* `PolymerSpace`: `ℓ²(ℝ, ℂ)`, and `ket v = |v⟩`;
* `inner_ket`: `⟨μ|ν⟩ = δ_{μν}`;
* `polymerDomain`: the span of the kets (the finitely supported vectors), `dense_polymerDomain`: it is dense;

References: Ashtekar–Pawlowski–Singh 2006 (`aps-2006`), Kamiński–Lewandowski 2008
(`kaminski-lewandowski-2008`).
-/

open scoped InnerProductSpace

namespace Lightlike.Canonical.PolymerEvolution

noncomputable section

/-- **The polymer Hilbert space** `ℓ²(ℝ, ℂ)`: square-summable complex functions on the real line
(of the "volume" label `μ`), with the inner product `⟨ψ, φ⟩ = ∑_μ conj ψ(μ) φ(μ)`. -/
abbrev PolymerSpace : Type := lp (fun _ : ℝ => ℂ) 2

/-- **The ket `|v⟩`** of the polymer Hilbert space: the function `1` at `v` and `0` elsewhere. -/
def ket (v : ℝ) : PolymerSpace := by
  classical
  exact lp.single 2 v (1 : ℂ)

/-- The ket `|v⟩` takes the value `1` at `v` and `0` elsewhere. -/
theorem ket_apply (v w : ℝ) : ket v w = if w = v then 1 else 0 := by
  classical
  unfold ket
  rw [lp.coeFn_single]
  by_cases h : w = v
  · subst h; simp
  · simp [h]

/-- **Orthonormality of the kets**: `⟨μ|ν⟩ = δ_{μν}`, the Kronecker delta. -/
theorem inner_ket (μ ν : ℝ) : ⟪ket μ, ket ν⟫_ℂ = if μ = ν then 1 else 0 := by
  classical
  unfold ket
  rw [lp.inner_single_left]
  simp only [lp.coeFn_single]
  by_cases h : μ = ν
  · subst h; simp
  · simp [h]

/-- **The domain of finite linear combinations of kets**: the span of the `|v⟩`. -/
def polymerDomain : Submodule ℂ PolymerSpace :=
  Submodule.span ℂ (Set.range ket)

/-- **The finite linear combinations of kets are dense** in the polymer Hilbert space. -/
theorem dense_polymerDomain : Dense (polymerDomain : Set PolymerSpace) := by
  classical
  have h := (default : HilbertBasis ℝ ℂ (lp (fun _ : ℝ => ℂ) 2)).dense_span
  have hb : (⇑(default : HilbertBasis ℝ ℂ (lp (fun _ : ℝ => ℂ) 2))) = ket := by
    funext v
    rfl
  rw [hb] at h
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr h

end

end Lightlike.Canonical.PolymerEvolution

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.PolymerSpace := _root_.Lightlike.Canonical.PolymerEvolution.PolymerSpace
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.dense_polymerDomain := _root_.Lightlike.Canonical.PolymerEvolution.dense_polymerDomain
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.inner_ket := _root_.Lightlike.Canonical.PolymerEvolution.inner_ket
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.ket := _root_.Lightlike.Canonical.PolymerEvolution.ket
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.ket_apply := _root_.Lightlike.Canonical.PolymerEvolution.ket_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.polymerDomain := _root_.Lightlike.Canonical.PolymerEvolution.polymerDomain
