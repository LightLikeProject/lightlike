import Lightlike.ODE.Frobenius
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# The Frobenius theorem: the chart

For an involutive family of `C¹` vector fields `X k` (`k` in a finite type `ι`), linearly
independent at a point `x₀` of a finite-dimensional real normed space `E`, there is a chart about
`x₀` whose plaques are integral manifolds of the span of the `X k`
(`Lightlike.ODE.exists_frobenius_chart`): a continuous linear map `π : E → (ι → ℝ)` and an open
partial homeomorphism `φ` from `(ι → ℝ) × ker π` to `E` with `φ (0, 0) = x₀`, differentiable on
its source, such that at every point `p` of the source the derivative of `φ` along the first
factor has range the span of the `X k (φ p)`. The slices `{(t, w) : w fixed}` are the plaques.

This is the statement of Michor's local Frobenius theorem with `u = φ⁻¹`: his chart
`u : U → V × W ⊂ ℝᵏ × ℝ^{m−k}` has `T (u⁻¹ (V × {y})) = E` on the plaque. The map is the one of
his proof, `φ (t, w) = (Fl^{Y₁}_{t₁} ∘ … ∘ Fl^{Y_k}_{t_k}) (x₀ + w)`, and it is a local
homeomorphism by the inverse function theorem, its derivative at `(0, 0)` being
`(τ, w) ↦ ∑ τ i • Y i (x₀) + w`.

## References

* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, 3.18, local version of
  Frobenius's theorem, pages 32–33 of the author's version. Differences: `C¹` fields on an open
  subset of a finite-dimensional normed space instead of a smooth subbundle on a manifold; the
  subbundle is given by a frame with pointwise involutivity; the source of the chart is an open set
  that is not stated to be a product `V × W` (it contains one).
-/

open Set Metric Filter Topology VectorField

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Frobenius theorem, local version** (Michor, 3.18).

Let the fields `X k` be `C¹` at a point `x₀` of a finite-dimensional real normed space, linearly
independent at `x₀`, with every bracket `[X i, X j] (y)` in the span of the `X k (y)` for `y`
near `x₀`. Then there are a continuous linear map `π : E → (ι → ℝ)` and an open partial
homeomorphism `φ` from `(ι → ℝ) × ker π` to `E`, with `(0, 0)` in its source and
`φ (0, 0) = x₀`, such that at every point `p` of the source `φ` is differentiable and the range
of its derivative along the first factor is the span of the `X k (φ p)`. So each plaque
`t ↦ φ (t, w)` is an integral manifold of the span of the `X k`, and the plaques fill a
neighbourhood of `x₀`. -/
theorem exists_frobenius_chart {X : ι → E → E} {x₀ : E}
    (hX : ∀ k, ContDiffAt ℝ 1 (X k) x₀) (hli : LinearIndependent ℝ fun k => X k x₀)
    (hinv : ∀ᶠ y in 𝓝 x₀, ∀ i j,
      lieBracket ℝ (X i) (X j) y ∈ Submodule.span ℝ (range fun k => X k y)) :
    ∃ (π : E →L[ℝ] (ι → ℝ)) (φ : OpenPartialHomeomorph ((ι → ℝ) × LinearMap.ker (π : E →ₗ[ℝ] (ι → ℝ))) E),
      ((0 : ι → ℝ), (0 : LinearMap.ker (π : E →ₗ[ℝ] (ι → ℝ)))) ∈ φ.source ∧ φ (0, 0) = x₀ ∧
      ∀ p ∈ φ.source, ∃ φ' : (ι → ℝ) × LinearMap.ker (π : E →ₗ[ℝ] (ι → ℝ)) →L[ℝ] E, HasFDerivAt (𝕜 := ℝ) φ φ' p ∧
        range (fun τ : ι → ℝ => φ' (τ, 0)) =
          (Submodule.span ℝ (range fun k => X k (φ p)) : Set E) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨π, hπ⟩ := exists_clm_apply_eq_single hli
  obtain ⟨ε, f, f', hε, h0, hd⟩ := exists_integral_manifold_of_involutive_on (Γ := univ) hX hπ
    (hinv.mono fun y hy _ => hy) one_pos (fun _ _ _ _ _ _ _ => mem_univ _)
  refine ⟨π, ?_⟩
  set W := LinearMap.ker (π : E →ₗ[ℝ] (ι → ℝ)) with hW
  have : CompleteSpace W := FiniteDimensional.complete ℝ W
  have h00 := hd 0 (mem_ball_self hε) x₀ (mem_ball_self hε)
  -- the embedding of the transversal `x₀ + ker π`
  set j : (ι → ℝ) × W → (ι → ℝ) × E := fun p => (p.1, x₀ + (p.2 : E)) with hjdef
  set J : (ι → ℝ) × W →L[ℝ] (ι → ℝ) × E :=
    (ContinuousLinearMap.fst ℝ (ι → ℝ) W).prod
      (W.subtypeL.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) W)) with hJdef
  have hj : ∀ p, HasStrictFDerivAt j J p := fun p =>
    hasStrictFDerivAt_fst.prodMk
      ((HasStrictFDerivAt.comp p (f := Prod.snd) W.subtypeL.hasStrictFDerivAt
        hasStrictFDerivAt_snd).const_add x₀)
  have hjc : Continuous j :=
    continuous_fst.prodMk (continuous_const.add (continuous_subtype_val.comp continuous_snd))
  have hj0 : j (0, 0) = (0, x₀) := by simp [hjdef]
  -- `f` is strictly differentiable at `(0, x₀)`
  have hev : ∀ᶠ q in 𝓝 ((0 : ι → ℝ), x₀), HasFDerivAt f (f' q) q := by
    filter_upwards [Metric.ball_mem_nhds ((0 : ι → ℝ), x₀) hε] with q hq
    obtain ⟨t, x⟩ := q
    rw [mem_ball, Prod.dist_eq, max_lt_iff] at hq
    exact (hd t (mem_ball.2 hq.1) x (mem_ball.2 hq.2)).1.1
  have hstrict : HasStrictFDerivAt f (f' (0, x₀)) (0, x₀) :=
    hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt hev h00.1.2
  have hg : HasStrictFDerivAt (fun p => f (j p)) ((f' (0, x₀)).comp J) (0, 0) :=
    HasStrictFDerivAt.comp (0, 0) (f := j) (by rw [hj0]; exact hstrict) (hj (0, 0))
  -- its derivative `(τ, w) ↦ f' (τ, 0) + w` is invertible
  obtain ⟨-, hπ0, -⟩ := h00.2 (mem_univ _)
  have h0ξ := (h0 x₀ (mem_ball_self hε)).2
  have hsplit : ∀ (τ : ι → ℝ) (w : W),
      (f' (0, x₀)).comp J (τ, w) = f' (0, x₀) (τ, 0) + (w : E) := by
    intro τ w
    have h1 : ((τ, (w : E)) : (ι → ℝ) × E) = (τ, 0) + (0, (w : E)) := by simp
    show f' (0, x₀) (τ, (w : E)) = _
    rw [h1, map_add, h0ξ]
  set S : (ι → ℝ) →L[ℝ] E :=
    (f' (0, x₀)).comp (ContinuousLinearMap.inl ℝ (ι → ℝ) E) with hSdef
  have hS : ∀ τ, S τ = f' (0, x₀) (τ, 0) := fun τ => rfl
  have hker : ∀ u : E, (ContinuousLinearMap.id ℝ E - S.comp π) u ∈ W := by
    intro u
    rw [hW, LinearMap.mem_ker]
    show π ((ContinuousLinearMap.id ℝ E - S.comp π) u) = 0
    have h1 : (ContinuousLinearMap.id ℝ E - S.comp π) u = u - f' (0, x₀) (π u, 0) := rfl
    rw [h1, map_sub, hπ0, sub_self]
  set inv : E →L[ℝ] (ι → ℝ) × W :=
    π.prod ((ContinuousLinearMap.id ℝ E - S.comp π).codRestrict W hker) with hinvdef
  have hinv_fst : ∀ u, (inv u).1 = π u := fun u => rfl
  have hinv_snd : ∀ u, ((inv u).2 : E) = u - f' (0, x₀) (π u, 0) := fun u => rfl
  have hleft : Function.LeftInverse inv ((f' (0, x₀)).comp J) := by
    rintro ⟨τ, w⟩
    have hw : π (w : E) = 0 := LinearMap.mem_ker.1 w.2
    have h1 : π ((f' (0, x₀)).comp J (τ, w)) = τ := by
      rw [hsplit, map_add, hπ0, hw, add_zero]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · rw [hinv_fst]; exact h1
    · rw [hinv_snd, h1, hsplit]
      exact add_sub_cancel_left _ _
  have hright : Function.RightInverse inv ((f' (0, x₀)).comp J) := by
    intro u
    have h1 : (f' (0, x₀)).comp J (inv u) = f' (0, x₀) ((inv u).1, 0) + ((inv u).2 : E) :=
      hsplit (inv u).1 (inv u).2
    rw [h1, hinv_fst, hinv_snd]
    exact add_sub_cancel _ _
  set e : ((ι → ℝ) × W) ≃L[ℝ] E :=
    ContinuousLinearEquiv.equivOfInverse ((f' (0, x₀)).comp J) inv hleft hright with hedef
  have hg' : HasStrictFDerivAt (fun p => f (j p)) (e : (ι → ℝ) × W →L[ℝ] E) (0, 0) := hg
  -- the chart, restricted to the points whose image under `j` is in the domain of `f`
  set s : Set ((ι → ℝ) × W) := j ⁻¹' ball ((0 : ι → ℝ), x₀) ε with hsdef
  have hs : IsOpen s := isOpen_ball.preimage hjc
  refine ⟨(hg'.toOpenPartialHomeomorph (fun p => f (j p))).restrOpen s hs, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨hg'.mem_toOpenPartialHomeomorph_source, ?_⟩
    show j (0, 0) ∈ ball ((0 : ι → ℝ), x₀) ε
    rw [hj0]
    exact mem_ball_self hε
  · show f (j (0, 0)) = x₀
    rw [hj0]
    exact (h0 x₀ (mem_ball_self hε)).1
  · rintro ⟨t, w⟩ hp
    rw [OpenPartialHomeomorph.restrOpen_source] at hp
    have hq : j (t, w) ∈ ball ((0 : ι → ℝ), x₀) ε := hp.2
    have hq' : dist t 0 < ε ∧ dist (x₀ + (w : E)) x₀ < ε := by
      have := hq
      rw [mem_ball, Prod.dist_eq, max_lt_iff] at this
      exact this
    obtain ⟨⟨hder, -⟩, hΓ⟩ := hd t (mem_ball.2 hq'.1) (x₀ + (w : E)) (mem_ball.2 hq'.2)
    obtain ⟨-, -, hrange⟩ := hΓ (mem_univ _)
    refine ⟨(f' (t, x₀ + (w : E))).comp J, ?_, ?_⟩
    · exact HasFDerivAt.comp (t, w) (f := j) hder (hj (t, w)).hasFDerivAt
    · exact hrange

end Lightlike.ODE
