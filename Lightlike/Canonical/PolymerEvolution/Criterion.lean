import Mathlib
import Lightlike.OperatorAlgebras.Spectral.Unbounded.Spectrum

/-!
# Essential self-adjointness of a semibounded symmetric operator

Row G2-017 (milestone CA7).  The abstract criterion used for the `μ̄` evolution operator of loop
quantum cosmology: a densely defined symmetric operator `T` which is bounded below,
`Re ⟨x, T x⟩ ≥ -C ‖x‖²`, and such that `T† - μ` is injective for one real `μ < -C`, is essentially
self-adjoint.  (The classical Carleman/limit-point criterion does not apply to the evolution operator,
whose Jacobi coefficients grow quadratically; the maximum principle of the maximum principle (`MaxPrinciple`) gives the
injectivity hypothesis instead.)

## Main statements

* `isEssentiallySelfAdjoint_of_semibounded`: the criterion.

Reference: Kamiński–Lewandowski 2008 (`kaminski-lewandowski-2008`); the criterion is the
Friedrichs/von Neumann semibounded one (Reed–Simon X.26 type argument, proved here from the
existing unbounded-operator API).
-/

open scoped InnerProductSpace LinearPMap
open Filter Topology Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Canonical.PolymerEvolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A coercivity bound on the real part of an inner product gives a norm bound. -/
theorem norm_lower_bound_of_re_inner {x y : H} {δ : ℝ}
    (h : δ * ‖x‖ ^ 2 ≤ (⟪x, y⟫_ℂ).re) : δ * ‖x‖ ≤ ‖y‖ := by
  by_cases hx : ‖x‖ = 0
  · rw [hx]; simp
  · have hx' : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have h1 : (⟪x, y⟫_ℂ).re ≤ ‖x‖ * ‖y‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm x y)
    have : ‖x‖ * (δ * ‖x‖) ≤ ‖x‖ * ‖y‖ := by nlinarith
    exact le_of_mul_le_mul_left this hx'

/-- **Criterion for essential self-adjointness (semibounded case).**  Let `T` be a densely defined
symmetric operator with `Re ⟨x, T x⟩ ≥ -C ‖x‖²`.  If `T† - μ` is injective for a real `μ < -C`,
then `T` is essentially self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_semibounded {T : H →ₗ.[ℂ] H} (hT : HasDenseDomain T)
    (hsym : IsSymmetric T) {C : ℝ}
    (hC : ∀ x : T.domain, -C * ‖(x : H)‖ ^ 2 ≤ (⟪(x : H), T x⟫_ℂ).re) {μ : ℝ} (hμ : μ < -C)
    (hk : ker (subSmul (T†) (μ : ℂ)) = ⊥) : IsEssentiallySelfAdjoint T := by
  have hc := isClosable_of_isSymmetric hT hsym
  have hsymS := isSymmetric_closure hsym hc
  have hleS : T.closure ≤ T.closure† :=
    (isSymmetric_iff_le_adjoint (hasDenseDomain_closure hT hc)).mp hsymS
  set δ : ℝ := -C - μ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  -- lower bound on `T`
  have hboundT : ∀ x : T.domain, δ * ‖(x : H)‖ ≤ ‖T x - (μ : ℂ) • (x : H)‖ := by
    intro x
    refine norm_lower_bound_of_re_inner ?_
    have hxx : (⟪(x : H), (x : H)⟫_ℂ).re = ‖(x : H)‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x : H)
    rw [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul, hxx]
    have h := hC x
    rw [hδdef]; nlinarith
  -- lower bound on the closure
  have hboundS : ∀ ψ : T.closure.domain,
      δ * ‖(ψ : H)‖ ≤ ‖T.closure ψ - (μ : ℂ) • (ψ : H)‖ := by
    intro ψ
    obtain ⟨χ, η, hχ, hTχ⟩ := (mem_domain_closure_iff hc (ψ : H)).mp ψ.2
    have hSψ : T.closure ψ = η := closure_apply_eq_of_tendsto hc hχ hTχ ψ.2
    rw [hSψ]
    have h1 : Tendsto (fun n => δ * ‖(χ n : H)‖) atTop (𝓝 (δ * ‖(ψ : H)‖)) :=
      (hχ.norm).const_mul δ
    have h2 : Tendsto (fun n => ‖T (χ n) - (μ : ℂ) • (χ n : H)‖) atTop
        (𝓝 ‖η - (μ : ℂ) • (ψ : H)‖) :=
      (hTχ.sub (hχ.const_smul (μ : ℂ))).norm
    exact le_of_tendsto_of_tendsto' h1 h2 fun n => hboundT (χ n)
  have hclosed := isClosed_range_subSmul hc.closure_isClosed (μ : ℂ) hδ hboundS
  -- the range of `T - μ` is dense
  have hd : Dense ((range (subSmul T (μ : ℂ)) : Submodule ℂ H) : Set H) := by
    refine dense_iff_orthogonal_eq_bot.mpr ?_
    rw [orthogonal_range_subSmul hT, Complex.conj_ofReal]
    exact hk
  have hle : range (subSmul T (μ : ℂ)) ≤ range (subSmul T.closure (μ : ℂ)) := by
    rintro _ ⟨x, rfl⟩
    refine mem_range.mpr ⟨⟨x, T.le_closure.1 x.2⟩, ?_⟩
    change T.closure _ - (μ : ℂ) • (x : H) = T x - (μ : ℂ) • (x : H)
    rw [T.le_closure.2 (x := x) (y := ⟨x, T.le_closure.1 x.2⟩) rfl]
    rfl
  have hr : range (subSmul T.closure (μ : ℂ)) = ⊤ := by
    rw [← hclosed.submodule_topologicalClosure_eq]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mp (hd.mono hle)
  have hk' : ker (subSmul (T.closure†) (μ : ℂ)) = ⊥ := by
    rw [adjoint_closure_eq_adjoint hT hc]; exact hk
  exact ⟨hsym, hc, LinearPMap.isSelfAdjoint_def.mpr (adjoint_eq_of_range_eq_top hleS hr hk')⟩

end Lightlike.Canonical.PolymerEvolution

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.isEssentiallySelfAdjoint_of_semibounded := _root_.Lightlike.Canonical.PolymerEvolution.isEssentiallySelfAdjoint_of_semibounded
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_017.norm_lower_bound_of_re_inner := _root_.Lightlike.Canonical.PolymerEvolution.norm_lower_bound_of_re_inner
