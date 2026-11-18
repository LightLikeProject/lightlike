module

public import Physlib.Relativity.LorentzGroup.Boosts.Apply
public import Physlib.Relativity.LorentzGroup.Boosts.Basic
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# Little groups of the standard momenta

Signature `(+,−,−,−)`, in Physlib's `Lorentz.Vector d`. The *little group* of a momentum `q` is the stabiliser
`{Λ ∈ LorentzGroup d | Λ • q = q}`. For the standard tachyonic momentum `(0, 0, 0, κ)` the boosts along the first
axis lie in it, with matrix entry `γ(β)` unbounded, so the little group is not compact
(`not_isCompact_littleGroup_tachyon`): the check of T-HA6 that a tachyonic orbit has a non-compact little group.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2 (stabilisers) and §5.4 (tachyonic representations).
-/

@[expose] public section

open Lorentz LorentzGroup

namespace Lightlike.Poincare

/-- The little group of a momentum `q`: the Lorentz transformations fixing it. -/
def littleGroup {d : ℕ} (q : Lorentz.Vector d) : Set (LorentzGroup d) := {Λ | Λ • q = q}

/-- The standard tachyonic momentum `(0, 0, 0, κ)` (the third spatial axis). -/
def tachyonStd (κ : ℝ) : Lorentz.Vector 3 := fun μ => if μ = Sum.inr 2 then κ else 0

/-- Boosts along the first spatial axis fix the standard tachyonic momentum. -/
theorem boost_mem_littleGroup_tachyon (κ β : ℝ) (hβ : |β| < 1) :
    boost (0 : Fin 3) β hβ ∈ littleGroup (tachyonStd κ) := by
  show boost (0 : Fin 3) β hβ • tachyonStd κ = tachyonStd κ
  rw [Lorentz.Vector.boost_toCoord_eq]
  funext μ
  rcases μ with ⟨i⟩ | j
  · fin_cases i
    simp [tachyonStd]
  · by_cases hj : j = 0
    · subst hj
      simp [tachyonStd]
    · simp [tachyonStd, hj]

/-- **The little group of a tachyonic momentum is not compact.** -/
theorem not_isCompact_littleGroup_tachyon (κ : ℝ) : ¬ IsCompact (littleGroup (tachyonStd κ)) := by
  intro hc
  have hcont : Continuous fun Λ : LorentzGroup 3 => Λ.1 (Sum.inl 0) (Sum.inl 0) := by
    have h1 : Continuous fun Λ : LorentzGroup 3 => Λ.1 := continuous_subtype_val
    exact (continuous_apply _).comp ((continuous_apply _).comp h1)
  obtain ⟨C, hC⟩ := (hc.image hcont).bddAbove
  set r : ℝ := 2 * |C| + 2 with hr
  have hβ : |Real.tanh r| < 1 := abs_lt.2 ⟨Real.neg_one_lt_tanh r, Real.tanh_lt_one r⟩
  have hmem := boost_mem_littleGroup_tachyon κ (Real.tanh r) hβ
  have hle := hC ⟨_, hmem, rfl⟩
  rw [boost_inl_0_inl_0, γ_tanh] at hle
  have h1 : r + 1 ≤ Real.exp r := Real.add_one_le_exp r
  have h2 : 0 ≤ Real.exp (-r) := (Real.exp_pos _).le
  have h3 : Real.cosh r = (Real.exp r + Real.exp (-r)) / 2 := Real.cosh_eq r
  have h4 : C ≤ |C| := le_abs_self C
  nlinarith [abs_nonneg C]

end Lightlike.Poincare
