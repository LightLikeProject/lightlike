import Mathlib

/-!
# The index of a loop about a point, and the Theta Lemma

The **index** of a loop `α` in the plane (identified with `ℂ`) about a point `Ω` that it avoids is the integer
`n` with `logInc α Ω = n * 2πi`, where `logInc α Ω = ℓ 1 - ℓ 0` is the **increment** of a continuous logarithm `ℓ`
of `α - Ω` (`exp (ℓ t) = α t - Ω`). Such a logarithm exists by path lifting through the covering map
`exp : ℂ → ℂ ∖ {0}`, and two of them differ by a constant multiple of `2πi`, so the increment does not depend on
the choice (`logInc_eq`). The increment is additive under concatenation of paths (`logInc_trans`) and changes
sign under reversal (`logInc_symm`); for a loop it is `2πi` times an integer (`exists_int_logInc`), and the
**Theta Lemma** (`theta_lemma`) follows: `ind(α * γ) = ind(α * β) + ind(β⁻¹ * γ)`.

This is the index of a point not on a Jordan curve and the Theta Lemma of chapter 9 of J. McCleary,
*A First Course in Topology: Continuity and Dimension* (AMS, 2006); the numbering is that of the lecture-notes
version of the chapter (`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`), not checked against
the printed book. The notes read the index off `π₁(ℝ² − {Ω}) ≅ ℤ`; here it is read off a lift, as in
`AddCircle.windingNumber_eq_div`. The Theta Lemma is stated for loops of the notes' form but proved through path
increments: the notes use the homotopy `β * β⁻¹ ≃ const` in the fundamental group, and here the increment of `β⁻¹`
is minus that of `β`, so the contributions of `β` and `β⁻¹` cancel. The statements and proofs are Lean's own.

## Main results

* `exists_isLog`, `isLog_unique`: a path avoiding `Ω` has a continuous logarithm, unique up to `2πi k`.
* `logInc`, `logInc_eq`, `logInc_trans`, `logInc_symm`: the increment of a logarithm and its properties.
* `ind`, `ind_spec`: the index of a loop about a point.
* `theta_lemma`: the Theta Lemma of the notes.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (the chapter location is verified with
  `scripts/sources.py verify`; the lemma-level numbering quoted above is that of the lecture-notes version and is
  not checked).
-/

open Complex unitInterval Real

namespace Lightlike.PL

/-- A **continuous logarithm** of the path `α` about the point `Ω`: a continuous map `ℓ : I → ℂ` with
`exp (ℓ t) = α t - Ω` for all `t`. -/
def IsLog (α : C(I, ℂ)) (Ω : ℂ) (ℓ : C(I, ℂ)) : Prop := ∀ t, exp (ℓ t) = α t - Ω

/-- A path that avoids `Ω` has a continuous logarithm about `Ω`, with any prescribed start among the
logarithms of `α 0 - Ω`. (Path lifting through the covering map `exp : ℂ → {z ≠ 0}`.) -/
theorem exists_isLog_start (α : C(I, ℂ)) {Ω : ℂ} (h : ∀ t, α t ≠ Ω) {z₀ : ℂ}
    (hz₀ : exp z₀ = α 0 - Ω) : ∃ ℓ, IsLog α Ω ℓ ∧ ℓ 0 = z₀ := by
  let γ : C(I, {w : ℂ // w ≠ 0}) :=
    ⟨fun t => ⟨α t - Ω, sub_ne_zero.2 (h t)⟩, (α.continuous.sub continuous_const).subtype_mk _⟩
  obtain ⟨Γ, hΓ, h0⟩ := Complex.isCoveringMap_exp.exists_path_lifts γ z₀ (Subtype.ext hz₀.symm)
  exact ⟨Γ, fun t => congrArg Subtype.val (congrFun hΓ t), h0⟩

/-- A path that avoids `Ω` has a continuous logarithm about `Ω`. -/
theorem exists_isLog (α : C(I, ℂ)) {Ω : ℂ} (h : ∀ t, α t ≠ Ω) : ∃ ℓ, IsLog α Ω ℓ := by
  obtain ⟨ℓ, hℓ, -⟩ := exists_isLog_start α h
    (z₀ := Complex.log (α 0 - Ω)) (exp_log (sub_ne_zero.2 (h 0)))
  exact ⟨ℓ, hℓ⟩

/-- Two continuous logarithms of one path differ by a constant integer multiple of `2πi`. -/
theorem isLog_unique {α : C(I, ℂ)} {Ω : ℂ} {ℓ ℓ' : C(I, ℂ)} (hℓ : IsLog α Ω ℓ) (hℓ' : IsLog α Ω ℓ') :
    ∃ n : ℤ, ∀ t, ℓ t = ℓ' t + (n : ℂ) * (2 * π * Complex.I) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hℓ 0).trans (hℓ' 0).symm)
  refine ⟨n, fun t => ?_⟩
  have hcov := Complex.isCoveringMap_exp
  have hmain : (fun t => ℓ t) = fun t => ℓ' t + (n : ℂ) * (2 * π * Complex.I) := by
    refine hcov.eq_of_comp_eq (A := I) (f := fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {w : ℂ // w ≠ 0}))
      ℓ.continuous ((ℓ'.continuous).add continuous_const) ?_ 0 hn
    funext s
    apply Subtype.ext
    simp only [Function.comp_apply]
    rw [hℓ s, Complex.exp_add, ← hℓ' s]
    simp [Complex.exp_int_mul_two_pi_mul_I]
  exact congrFun hmain t

/-- The **increment of the logarithm** of a path `α` from `a` to `b` about `Ω`: `ℓ 1 - ℓ 0` for a continuous
logarithm `ℓ` of `α` about `Ω` (`0` if `α` meets `Ω`). -/
noncomputable def logInc {a b : ℂ} (α : Path a b) (Ω : ℂ) : ℂ := by
  classical
  exact if h : ∀ t, α t ≠ Ω then
    (Classical.choose (exists_isLog (α : C(I, ℂ)) h)) 1 - (Classical.choose (exists_isLog (α : C(I, ℂ)) h)) 0
  else 0

/-- **The increment is computed by any continuous logarithm.** -/
theorem logInc_eq {a b : ℂ} (α : Path a b) {Ω : ℂ} (h : ∀ t, α t ≠ Ω) {ℓ : C(I, ℂ)}
    (hℓ : IsLog (α : C(I, ℂ)) Ω ℓ) : logInc α Ω = ℓ 1 - ℓ 0 := by
  classical
  unfold logInc
  split_ifs
  obtain ⟨n, hn⟩ := isLog_unique (Classical.choose_spec (exists_isLog (α : C(I, ℂ)) h)) hℓ
  rw [hn 1, hn 0]; ring

lemma avoid_trans {a b c : ℂ} {α : Path a b} {β : Path b c} {Ω : ℂ} (hα : ∀ t, α t ≠ Ω)
    (hβ : ∀ t, β t ≠ Ω) : ∀ t, (α.trans β) t ≠ Ω := by
  intro t
  rw [Path.trans_apply]
  split_ifs
  · exact hα _
  · exact hβ _

lemma avoid_symm {a b : ℂ} {α : Path a b} {Ω : ℂ} (hα : ∀ t, α t ≠ Ω) : ∀ t, α.symm t ≠ Ω := by
  intro t
  rw [Path.symm_apply]
  exact hα _

/-- **Additivity of the increment** under concatenation of paths: the logarithm of `α * β` is that of `α`
followed by that of `β` shifted to start where the first ends. -/
theorem logInc_trans {a b c : ℂ} (α : Path a b) (β : Path b c) {Ω : ℂ}
    (hα : ∀ t, α t ≠ Ω) (hβ : ∀ t, β t ≠ Ω) :
    logInc (α.trans β) Ω = logInc α Ω + logInc β Ω := by
  obtain ⟨ℓ₁, h₁⟩ := exists_isLog (α : C(I, ℂ)) hα
  obtain ⟨ℓ₂, h₂⟩ := exists_isLog (β : C(I, ℂ)) hβ
  have hjoin : exp (ℓ₁ 1) = exp (ℓ₂ 0) := by
    rw [h₁ 1, h₂ 0]
    simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hjoin
  let ℓ₂' : C(I, ℂ) := ⟨fun t => ℓ₂ t + (n : ℂ) * (2 * π * Complex.I), by fun_prop⟩
  have h₂' : IsLog (β : C(I, ℂ)) Ω ℓ₂' := by
    intro t
    show exp (ℓ₂ t + (n : ℂ) * (2 * π * Complex.I)) = β t - Ω
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact h₂ t
  let P₁ : Path (ℓ₁ 0) (ℓ₁ 1) := ⟨ℓ₁, rfl, rfl⟩
  let P₂ : Path (ℓ₁ 1) (ℓ₂' 1) := ⟨ℓ₂', by simp [ℓ₂', hn], rfl⟩
  have hlog : IsLog ((α.trans β : Path a c) : C(I, ℂ)) Ω ((P₁.trans P₂ : Path _ _) : C(I, ℂ)) := by
    intro t
    show exp ((P₁.trans P₂) t) = (α.trans β) t - Ω
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact h₁ _
    · exact h₂' _
  rw [logInc_eq (α.trans β) (avoid_trans hα hβ) hlog, logInc_eq α hα h₁, logInc_eq β hβ h₂]
  have e1 : (P₁.trans P₂) 1 = ℓ₂ 1 + (n : ℂ) * (2 * π * Complex.I) := by
    rw [Path.target]
    rfl
  have e0 : (P₁.trans P₂) 0 = ℓ₁ 0 := Path.source _
  show (P₁.trans P₂) 1 - (P₁.trans P₂) 0 = _
  rw [e1, e0]
  linear_combination (-1 : ℂ) * hn

/-- The increment changes sign when the path is reversed. -/
theorem logInc_symm {a b : ℂ} (α : Path a b) {Ω : ℂ} (hα : ∀ t, α t ≠ Ω) :
    logInc α.symm Ω = - logInc α Ω := by
  obtain ⟨ℓ, hℓ⟩ := exists_isLog (α : C(I, ℂ)) hα
  let P : Path (ℓ 0) (ℓ 1) := ⟨ℓ, rfl, rfl⟩
  have hlog : IsLog ((α.symm : Path b a) : C(I, ℂ)) Ω ((P.symm : Path _ _) : C(I, ℂ)) := by
    intro t
    show exp (P.symm t) = α.symm t - Ω
    rw [Path.symm_apply, Path.symm_apply]
    exact hℓ _
  rw [logInc_eq α.symm (avoid_symm hα) hlog, logInc_eq α hα hℓ]
  show P.symm 1 - P.symm 0 = _
  rw [Path.target, Path.source]
  show ℓ 0 - ℓ 1 = _
  ring

/-- The increment along a loop is `2πi` times an integer. -/
theorem exists_int_logInc {a : ℂ} (α : Path a a) {Ω : ℂ} (hα : ∀ t, α t ≠ Ω) :
    ∃ n : ℤ, logInc α Ω = (n : ℂ) * (2 * π * Complex.I) := by
  obtain ⟨ℓ, hℓ⟩ := exists_isLog (α : C(I, ℂ)) hα
  have h : exp (ℓ 1) = exp (ℓ 0) := by
    rw [hℓ 1, hℓ 0]
    simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  exact ⟨n, by rw [logInc_eq α hα hℓ, hn]; ring⟩

/-- The **index of a loop about a point**: the integer `n` with `logInc α Ω = n * 2πi`
(`0` if the loop meets `Ω`). -/
noncomputable def ind {a : ℂ} (α : Path a a) (Ω : ℂ) : ℤ := by
  classical
  exact if h : ∀ t, α t ≠ Ω then Classical.choose (exists_int_logInc α h) else 0

/-- The index is read off the increment. -/
theorem ind_spec {a : ℂ} (α : Path a a) {Ω : ℂ} (h : ∀ t, α t ≠ Ω) :
    logInc α Ω = (ind α Ω : ℂ) * (2 * π * Complex.I) := by
  classical
  unfold ind
  split_ifs
  exact Classical.choose_spec (exists_int_logInc α h)

/-- **The Theta Lemma of the notes** (chapter 9, the lemma named for the shape of the letter θ): for a curve parametrized
in two parts `α` from `a` to `b` and `γ` from `b` to `a`, and an arc `β` from `b` to `a`, the loops `ω₀ = α * γ`,
`ω₁ = α * β` and `ω₂ = β⁻¹ * γ` satisfy `ind ω₀ = ind ω₁ + ind ω₂` about every point `Ω` off the three paths.
It is stated for loops of the notes' form and proved through path increments rather than through the homotopy
`β * β⁻¹ ≃ const`: the increment of `β⁻¹` is minus that of `β` (`logInc_symm`), so the contributions of `β` and
`β⁻¹` cancel. -/
theorem theta_lemma {a b : ℂ} (α : Path a b) (β γ : Path b a) {Ω : ℂ}
    (hα : ∀ t, α t ≠ Ω) (hβ : ∀ t, β t ≠ Ω) (hγ : ∀ t, γ t ≠ Ω) :
    ind (α.trans γ) Ω = ind (α.trans β) Ω + ind (β.symm.trans γ) Ω := by
  have h0 := ind_spec (α.trans γ) (avoid_trans hα hγ)
  have h1 := ind_spec (α.trans β) (avoid_trans hα hβ)
  have h2 := ind_spec (β.symm.trans γ) (avoid_trans (avoid_symm hβ) hγ)
  rw [logInc_trans α γ hα hγ] at h0
  rw [logInc_trans α β hα hβ] at h1
  rw [logInc_trans β.symm γ (avoid_symm hβ) hγ, logInc_symm β hβ] at h2
  have hne : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((ind (α.trans γ) Ω : ℤ) : ℂ) =
      ((ind (α.trans β) Ω + ind (β.symm.trans γ) Ω : ℤ) : ℂ) := by
    apply mul_right_cancel₀ hne
    push_cast
    linear_combination -h0 + h1 + h2
  exact_mod_cast this

end Lightlike.PL
