import Lightlike.ODE.InvolutiveFrame
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Frobenius theorem: integral manifolds of an involutive family of vector fields

Let `X k`, for `k` in a finite type `ι`, be `C¹` vector fields near a point `x₀` of a
finite-dimensional real normed space `E`, linearly independent at `x₀`, and involutive: every Lie
bracket `[X i, X j] (y)` lies in the span of the `X k (y)`, for `y` near `x₀`. Then through every
point `x` near `x₀` there is an integral manifold of the span of the `X k`, of dimension the
number of fields: a map `t ↦ f (t, x)` of `t ∈ ι → ℝ` near `0` with `f (0, x) = x` whose
derivative at every `t` is injective with range the span of the `X k (f (t, x))`
(`Lightlike.ODE.exists_integral_manifold_of_involutive`). The map `f` is differentiable in
`(t, x)`, and at `t = 0` its derivative in `x` is the identity.

The proof is Michor's: replace the `X k` by a commuting frame `Y i` of the same span
(`Lightlike.ODE.exists_commuting_frame`) and compose the flows of the `Y i`
(`Lightlike.ODE.exists_flowComp_of_commuting`).

## References

* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, 3.18, local version of
  Frobenius's theorem, pages 32–33 of the author's version. Differences from the source: the
  source has a smooth integrable subbundle of the tangent bundle of a manifold and concludes with a
  chart `u` whose plaques `u⁻¹(V × {y})` are integral manifolds; here the fields are `C¹` on an
  open subset of a finite-dimensional normed space, the subbundle is given by a frame, and the
  conclusion is the family of integral manifolds `t ↦ f (t, x)` (the plaques, parametrised).
  The statement that `f`, restricted to a transversal, is a chart is
  `Lightlike.ODE.exists_frobenius_chart` in `Lightlike.ODE.FrobeniusChart`.
-/

open Set Metric Filter Topology VectorField

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a linearly independent finite family in a finite-dimensional space there is a continuous
linear map to `ι → ℝ` that sends the family to the standard basis. -/
theorem exists_clm_apply_eq_single [FiniteDimensional ℝ E] {v : ι → E}
    (hv : LinearIndependent ℝ v) : ∃ π : E →L[ℝ] (ι → ℝ), ∀ j, π (v j) = Pi.single j 1 := by
  set L : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ v with hL
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun g hg => ?_
    have h1 : ∑ i, g i • v i = 0 := by simpa [hL, Fintype.linearCombination_apply] using hg
    exact funext (Fintype.linearIndependent_iff.1 hv g h1)
  obtain ⟨g, hg⟩ := L.exists_leftInverse_of_injective hker
  refine ⟨LinearMap.toContinuousLinearMap g, fun j => ?_⟩
  have h2 := LinearMap.congr_fun hg (Pi.single j 1)
  simpa [hL, Fintype.linearCombination_apply_single] using h2

/-- **The Frobenius theorem for a family that is involutive on an invariant set.**

Let the fields `X k` be `C¹` at a point `x₀` of a real Banach space, let `π` be a continuous
linear map with `π (X j x₀) = e_j` (so the `X k (x₀)` are linearly independent), and let `Γ` be a
set such that, near `x₀`, the brackets `[X i, X j] (y)` lie in the span of the `X k (y)` for
`y ∈ Γ`, and the integral curves of the normalised fields `normalFrame π X i` that start in `Γ`
stay in `Γ`. Then there are `ε > 0` and a map `f` of `(t, x)`, differentiable at every `(t, x)`
with `‖t‖ < ε` and `‖x - x₀‖ < ε`, with `f (0, x) = x` and derivative the identity in `x` at
`t = 0`, and with a derivative continuous at `(t, x)`, such that for `x ∈ Γ`: `f (t, x) ∈ Γ`, and
the derivative of `f` in `t` at `(t, x)` is a right inverse of `π` (so it is injective) with
range the span of the `X k (f (t, x))`.

This is the form needed when the brackets close only on a constraint surface (Wipf's remark after
his Theorem 5). For `Γ = univ` it is `exists_integral_manifold_of_involutive`. -/
theorem exists_integral_manifold_of_involutive_on [CompleteSpace E] {X : ι → E → E} {x₀ : E}
    {Γ : Set E} {π : E →L[ℝ] (ι → ℝ)}
    (hX : ∀ k, ContDiffAt ℝ 1 (X k) x₀) (hπ : ∀ j, π (X j x₀) = Pi.single j 1)
    (hinv : ∀ᶠ y in 𝓝 x₀, y ∈ Γ → ∀ i j,
      lieBracket ℝ (X i) (X j) y ∈ Submodule.span ℝ (range fun k => X k y))
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hΓ : ∀ i, ∀ (γ : ℝ → E) (T : ℝ), (∀ t ∈ Icc (-T) T,
      HasDerivAt γ (normalFrame π X i (γ t)) t ∧ γ t ∈ ball x₀ a₀) → γ 0 ∈ Γ →
      ∀ t ∈ Icc (-T) T, γ t ∈ Γ) :
    ∃ (ε : ℝ) (f : (ι → ℝ) × E → E) (f' : (ι → ℝ) × E → ((ι → ℝ) × E →L[ℝ] E)), 0 < ε ∧
      (∀ x ∈ ball x₀ ε, f (0, x) = x ∧ ∀ ξ : E, f' (0, x) (0, ξ) = ξ) ∧
      ∀ t ∈ ball (0 : ι → ℝ) ε, ∀ x ∈ ball x₀ ε,
        (HasFDerivAt f (f' (t, x)) (t, x) ∧ ContinuousAt f' (t, x)) ∧
        (x ∈ Γ → f (t, x) ∈ Γ ∧ (∀ τ : ι → ℝ, π (f' (t, x) (τ, 0)) = τ) ∧
          range (fun τ : ι → ℝ => f' (t, x) (τ, 0)) =
            (Submodule.span ℝ (range fun k => X k (f (t, x))) : Set E)) := by
  obtain ⟨hY, hYY, hYe⟩ := exists_commuting_frame_on (Γ := Γ) hX hπ hinv
  set Y : ι → E → E := normalFrame π X with hYdef
  obtain ⟨ε₁, f, f', hε₁, h0, hd⟩ := exists_flowComp_of_commuting_on hY hYY ha₀ hΓ
  have hx₀ : x₀ ∈ ball x₀ ε₁ := mem_ball_self hε₁
  have hcont : ContinuousAt f (0, x₀) := (hd 0 (mem_ball_self hε₁) x₀ hx₀).1.1.continuousAt
  have hpre : f ⁻¹' {y | Submodule.span ℝ (range fun k => Y k y) =
      Submodule.span ℝ (range fun k => X k y) ∧ ∀ i, π (Y i y) = Pi.single i 1} ∈
      𝓝 ((0 : ι → ℝ), x₀) := by
    refine hcont.preimage_mem_nhds ?_
    rw [(h0 x₀ hx₀).1]
    exact hYe
  obtain ⟨ε₂, hε₂, hsub⟩ := Metric.mem_nhds_iff.1 hpre
  refine ⟨min ε₁ ε₂, f, f', lt_min hε₁ hε₂,
    fun x hx => h0 x (ball_subset_ball (min_le_left _ _) hx), fun t ht x hx => ?_⟩
  have ht₁ : t ∈ ball (0 : ι → ℝ) ε₁ := ball_subset_ball (min_le_left _ _) ht
  have hx₁ : x ∈ ball x₀ ε₁ := ball_subset_ball (min_le_left _ _) hx
  have hmem : ((t, x) : (ι → ℝ) × E) ∈ ball ((0 : ι → ℝ), x₀) ε₂ := by
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (lt_of_lt_of_le (mem_ball.1 ht) (min_le_right _ _))
      (lt_of_lt_of_le (mem_ball.1 hx) (min_le_right _ _))
  obtain ⟨hspan, hπY⟩ := hsub hmem
  obtain ⟨hder, hΓform⟩ := hd t ht₁ x hx₁
  refine ⟨hder, fun hxΓ => ?_⟩
  obtain ⟨hfΓ, hform⟩ := hΓform hxΓ
  have hπsum : ∀ τ : ι → ℝ, π (f' (t, x) (τ, 0)) = τ := by
    intro τ
    rw [hform τ, map_sum]
    simp only [map_smul, hπY]
    exact sum_smul_single τ
  refine ⟨hfΓ, hπsum, ?_⟩
  ext u
  constructor
  · rintro ⟨τ, rfl⟩
    show f' (t, x) (τ, 0) ∈ Submodule.span ℝ (range fun k => X k (f (t, x)))
    rw [hform τ, ← hspan]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hu
    have hu' : u ∈ Submodule.span ℝ (range fun k => Y k (f (t, x))) := by
      rw [hspan]; exact hu
    obtain ⟨τ, hτ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu'
    exact ⟨τ, by rw [← hτ]; exact hform τ⟩

/-- **The Frobenius theorem, local form with parametrised integral manifolds** (Michor, 3.18).

Let the fields `X k` be `C¹` at a point `x₀` of a finite-dimensional real normed space, linearly
independent at `x₀`, with every bracket `[X i, X j] (y)` in the span of the `X k (y)` for `y`
near `x₀`. Then there are `ε > 0` and a map `f` of `(t, x)`, differentiable at every `(t, x)`
with `‖t‖ < ε` and `‖x - x₀‖ < ε`, such that `f (0, x) = x`, the derivative of `f` in `x` at
`t = 0` is the identity, and at every such `(t, x)` the derivative of `f` in `t` is injective
with range the span of the `X k (f (t, x))`. So `t ↦ f (t, x)` parametrises an integral manifold
through `x` of dimension the number of fields.

The chart whose plaques are these integral manifolds, as in the source, is
`exists_frobenius_chart`. -/
theorem exists_integral_manifold_of_involutive [FiniteDimensional ℝ E] {X : ι → E → E} {x₀ : E}
    (hX : ∀ k, ContDiffAt ℝ 1 (X k) x₀) (hli : LinearIndependent ℝ fun k => X k x₀)
    (hinv : ∀ᶠ y in 𝓝 x₀, ∀ i j,
      lieBracket ℝ (X i) (X j) y ∈ Submodule.span ℝ (range fun k => X k y)) :
    ∃ (ε : ℝ) (f : (ι → ℝ) × E → E) (f' : (ι → ℝ) × E → ((ι → ℝ) × E →L[ℝ] E)), 0 < ε ∧
      (∀ x ∈ ball x₀ ε, f (0, x) = x ∧ ∀ ξ : E, f' (0, x) (0, ξ) = ξ) ∧
      ∀ t ∈ ball (0 : ι → ℝ) ε, ∀ x ∈ ball x₀ ε, HasFDerivAt f (f' (t, x)) (t, x) ∧
        Function.Injective (fun τ : ι → ℝ => f' (t, x) (τ, 0)) ∧
        range (fun τ : ι → ℝ => f' (t, x) (τ, 0)) =
          (Submodule.span ℝ (range fun k => X k (f (t, x))) : Set E) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨π, hπ⟩ := exists_clm_apply_eq_single hli
  obtain ⟨ε, f, f', hε, h0, hd⟩ := exists_integral_manifold_of_involutive_on (Γ := univ) hX hπ
    (hinv.mono fun y hy _ => hy) one_pos (fun _ _ _ _ _ _ _ => mem_univ _)
  refine ⟨ε, f, f', hε, h0, fun t ht x hx => ?_⟩
  obtain ⟨-, hπsum, hrange⟩ := (hd t ht x hx).2 (mem_univ x)
  refine ⟨(hd t ht x hx).1.1, fun τ τ' hττ => ?_, hrange⟩
  have h' : f' (t, x) (τ, 0) = f' (t, x) (τ', 0) := hττ
  rw [← hπsum τ, ← hπsum τ', h']

end Lightlike.ODE
