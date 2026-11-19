import Lightlike.ODE.CommutingFrame
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Ring.Units

/-!
# A commuting frame for an involutive family of vector fields

Let `X k`, for `k` in a finite type `ι`, be `C¹` vector fields near a point `x₀` of a real normed
space `E`, involutive in the sense that every Lie bracket `[X i, X j] (y)` lies in the span of the
vectors `X k (y)`, and let `π : E → (ι → ℝ)` be a continuous linear map with `π (X j x₀) = e_j`.
Then the fields

`Y i = ∑ k, c i k • X k`, with `(c i k (y))` the inverse of the matrix `(π (X k (y)))`,

satisfy `π ∘ Y i = e_i`, span the same subspaces as the `X k`, and commute:
`[Y i, Y j] = 0` near `x₀` (`Lightlike.ODE.exists_commuting_frame`).

This is the first step of the proof of the local Frobenius theorem in Michor's book: there `π` is
the projection to the first `k` coordinates of a chart, and the argument is the same. The bracket
`[Y i, Y j]` lies in the span of the `X k` by involutivity and in the kernel of `π` because
`π ∘ Y i` is constant, and `π` is injective on the span.

## References

* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, 3.18 (proof of the local version
  of Frobenius's theorem, equation (1) and the claim after it), pages 32–33 of the author's
  version.
-/

open Set Metric Filter Topology VectorField
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The Lie bracket of `V` with a finite combination `∑ k, c k • X k` lies in a subspace `S` at `y`
if the `X k (y)` and the brackets `[V, X k] (y)` do. -/
theorem lieBracket_sum_smul_mem {V : E → E} {c : ι → E → ℝ} {X : ι → E → E} {y : E}
    (S : Submodule ℝ E) (s : Finset ι) (hc : ∀ k, DifferentiableAt ℝ (c k) y)
    (hX : ∀ k, DifferentiableAt ℝ (X k) y) (hXS : ∀ k, X k y ∈ S)
    (hVX : ∀ k, lieBracket ℝ V (X k) y ∈ S) :
    lieBracket ℝ V (fun z => ∑ k ∈ s, c k z • X k z) y ∈ S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (fun z : E => ∑ k ∈ (∅ : Finset ι), c k z • X k z) = 0 := by
      funext z; simp
    rw [this, lieBracket_zero_right]
    exact S.zero_mem
  | insert a s ha ih =>
    have h1 : (fun z => ∑ k ∈ insert a s, c k z • X k z) =
        (fun z => c a z • X a z) + fun z => ∑ k ∈ s, c k z • X k z := by
      funext z
      simp [Finset.sum_insert ha]
    have hd : DifferentiableAt ℝ (fun z => ∑ k ∈ s, c k z • X k z) y :=
      DifferentiableAt.fun_sum fun k _ => (hc k).smul (hX k)
    have hda : DifferentiableAt ℝ (fun z => c a z • X a z) y := (hc a).smul (hX a)
    rw [h1, lieBracket_add_right (W := fun z => c a z • X a z)
      (W₁ := fun z => ∑ k ∈ s, c k z • X k z) hda hd, lieBracket_smul_right (hc a) (hX a)]
    exact S.add_mem (S.add_mem (S.smul_mem _ (hXS a)) (S.smul_mem _ (hVX a))) ih

/-- A field `W` whose image under a continuous linear map `π` is constant near `y` has
`π (DW(y) v) = 0`. -/
theorem map_fderiv_eq_zero_of_eventually_const {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (π : E →L[ℝ] F) {W : E → E} {y : E} {c : F}
    (hW : DifferentiableAt ℝ W y) (hc : ∀ᶠ z in 𝓝 y, π (W z) = c) (v : E) :
    π (fderiv ℝ W y v) = 0 := by
  have h1 : HasFDerivAt (π ∘ W) (π.comp (fderiv ℝ W y)) y := π.hasFDerivAt.comp y hW.hasFDerivAt
  have h2 : HasFDerivAt (π ∘ W) (0 : E →L[ℝ] F) y :=
    (hasFDerivAt_const c y).congr_of_eventuallyEq hc
  have h3 := h1.unique h2
  have h4 := congrArg (fun L : E →L[ℝ] F => L v) h3
  simpa using h4

variable [Fintype ι] [DecidableEq ι]

/-- A vector of `ι → ℝ` is the combination of the standard basis vectors with its coordinates. -/
lemma sum_smul_single (τ : ι → ℝ) : ∑ i, τ i • (Pi.single i (1 : ℝ) : ι → ℝ) = τ := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- The linear map `τ ↦ ∑ j, τ j • X j z` of a family of vector fields at the point `z`. -/
def frameSum (X : ι → E → E) (z : E) : (ι → ℝ) →L[ℝ] E :=
  ∑ j, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).smulRight (X j z)

omit [DecidableEq ι] in
lemma frameSum_apply (X : ι → E → E) (z : E) (τ : ι → ℝ) :
    frameSum X z τ = ∑ j, τ j • X j z := by
  simp [frameSum]

lemma frameSum_single (X : ι → E → E) (z : E) (k : ι) :
    frameSum X z (Pi.single k 1) = X k z := by
  simp [frameSum_apply, Pi.single_apply]

/-- The matrix `(π (X k z))` of a family of vector fields at `z` under `π`, as an endomorphism of
`ι → ℝ`. -/
def frameGram (π : E →L[ℝ] (ι → ℝ)) (X : ι → E → E) (z : E) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  π.comp (frameSum X z)

/-- The coefficients of the normalised frame: the inverse of the matrix `frameGram`. -/
def frameCoeff (π : E →L[ℝ] (ι → ℝ)) (X : ι → E → E) (i k : ι) (z : E) : ℝ :=
  (Ring.inverse (frameGram π X z) (Pi.single i 1)) k

/-- The normalised frame `Y i = ∑ k, c i k • X k` of a family `X` with respect to `π`: where the
matrix `(π (X k z))` is invertible, `π (Y i z) = e_i`. -/
def normalFrame (π : E →L[ℝ] (ι → ℝ)) (X : ι → E → E) (i : ι) (z : E) : E :=
  ∑ k, frameCoeff π X i k z • X k z

variable {π : E →L[ℝ] (ι → ℝ)} {X : ι → E → E} {x₀ y : E}

lemma normalFrame_eq (i : ι) (z : E) :
    normalFrame π X i z = frameSum X z (Ring.inverse (frameGram π X z) (Pi.single i 1)) := by
  simp [normalFrame, frameSum_apply, frameCoeff]

lemma frameGram_eq_one (hπ : ∀ j, π (X j x₀) = Pi.single j 1) : frameGram π X x₀ = 1 := by
  refine ContinuousLinearMap.ext fun τ => ?_
  simp only [frameGram, ContinuousLinearMap.comp_apply, frameSum_apply, map_sum, map_smul, hπ]
  exact sum_smul_single τ

omit [DecidableEq ι] in
lemma contDiffAt_frameGram (hX : ∀ k, ContDiffAt ℝ 1 (X k) y) :
    ContDiffAt ℝ 1 (fun z => frameGram π X z) y := by
  have hS : ContDiffAt ℝ 1 (fun z => frameSum X z) y := by
    unfold frameSum
    exact ContDiffAt.sum fun j _ => contDiffAt_const.smulRight (hX j)
  exact (ContinuousLinearMap.compL ℝ (ι → ℝ) E (ι → ℝ) π).contDiff.contDiffAt.comp y hS

lemma contDiffAt_frameCoeff (hX : ∀ k, ContDiffAt ℝ 1 (X k) y) (hu : IsUnit (frameGram π X y))
    (i k : ι) : ContDiffAt ℝ 1 (frameCoeff π X i k) y := by
  have h1 : ContDiffAt ℝ 1 Ring.inverse (frameGram π X y) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    exact contDiffAt_ringInverse ℝ u
  have h2 : ContDiffAt ℝ 1 (fun z => Ring.inverse (frameGram π X z)) y :=
    h1.comp y (contDiffAt_frameGram hX)
  have h3 : ContDiffAt ℝ 1 (fun z => Ring.inverse (frameGram π X z) (Pi.single i 1)) y :=
    h2.clm_apply contDiffAt_const
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) k).contDiff.contDiffAt.comp y h3

lemma contDiffAt_normalFrame (hX : ∀ k, ContDiffAt ℝ 1 (X k) y) (hu : IsUnit (frameGram π X y))
    (i : ι) : ContDiffAt ℝ 1 (normalFrame π X i) y := by
  show ContDiffAt ℝ 1 (fun z => ∑ k, frameCoeff π X i k z • X k z) y
  exact ContDiffAt.sum fun k _ => (contDiffAt_frameCoeff hX hu i k).smul (hX k)

lemma eventually_isUnit_frameGram (hX : ∀ k, ContDiffAt ℝ 1 (X k) x₀)
    (hπ : ∀ j, π (X j x₀) = Pi.single j 1) : ∀ᶠ z in 𝓝 x₀, IsUnit (frameGram π X z) := by
  have hc : ContinuousAt (fun z => frameGram π X z) x₀ := (contDiffAt_frameGram hX).continuousAt
  have hmem : {L : (ι → ℝ) →L[ℝ] (ι → ℝ) | IsUnit L} ∈ 𝓝 (frameGram π X x₀) :=
    Units.isOpen.mem_nhds (by rw [frameGram_eq_one hπ]; exact isUnit_one)
  exact hc.preimage_mem_nhds hmem

/-- Where the matrix `(π (X k z))` is invertible, `π (Y i z) = e_i`. -/
lemma map_normalFrame (hu : IsUnit (frameGram π X y)) (i : ι) :
    π (normalFrame π X i y) = Pi.single i 1 := by
  rw [normalFrame_eq]
  show (frameGram π X y * Ring.inverse (frameGram π X y)) (Pi.single i 1) = _
  rw [Ring.mul_inverse_cancel _ hu]
  rfl

omit [DecidableEq ι] in
/-- Where the matrix `(π (X k z))` is invertible, `π` is injective on the span of the `X k z`. -/
lemma eq_zero_of_mem_span_of_map_eq_zero (hu : IsUnit (frameGram π X y)) {u : E}
    (hu1 : u ∈ Submodule.span ℝ (range fun k => X k y)) (hu2 : π u = 0) : u = 0 := by
  obtain ⟨τ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu1
  have h1 : frameGram π X y τ = 0 := by
    simpa [frameGram, frameSum_apply] using hu2
  have h3 : (Ring.inverse (frameGram π X y) * frameGram π X y) τ = τ := by
    rw [Ring.inverse_mul_cancel _ hu]
    rfl
  have h4 : Ring.inverse (frameGram π X y) (frameGram π X y τ) = τ := h3
  rw [h1, map_zero] at h4
  simp [← h4]

/-- Where the matrix `(π (X k z))` is invertible, the normalised frame spans the same subspace. -/
lemma span_normalFrame (hu : IsUnit (frameGram π X y)) :
    Submodule.span ℝ (range fun k => normalFrame π X k y) =
      Submodule.span ℝ (range fun k => X k y) := by
  apply le_antisymm
  · refine Submodule.span_le.2 (range_subset_iff.2 fun i => ?_)
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · refine Submodule.span_le.2 (range_subset_iff.2 fun k => ?_)
    set G := frameGram π X y with hG
    set a : ι → ℝ := G (Pi.single k 1) with ha
    have hinv : Ring.inverse G (G (Pi.single k 1)) = Pi.single k 1 := by
      show (Ring.inverse G * G) (Pi.single k 1) = _
      rw [Ring.inverse_mul_cancel _ hu]
      rfl
    have hk : X k y = ∑ i, a i • normalFrame π X i y := by
      calc X k y = frameSum X y (Pi.single k 1) := (frameSum_single X y k).symm
        _ = frameSum X y (Ring.inverse G a) := by rw [ha, hinv]
        _ = frameSum X y (Ring.inverse G (∑ i, a i • (Pi.single i (1 : ℝ) : ι → ℝ))) := by
          rw [sum_smul_single]
        _ = ∑ i, a i • frameSum X y (Ring.inverse G (Pi.single i 1)) := by
          simp only [map_sum, map_smul]
        _ = ∑ i, a i • normalFrame π X i y := by
          simp only [normalFrame_eq, hG]
    show X k y ∈ Submodule.span ℝ (range fun k => normalFrame π X k y)
    rw [hk]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- **The normalised frame of an involutive family commutes.** At a point `y` near which the
`X k` are `C¹` and the matrix `(π (X k))` is invertible, if the brackets `[X i, X j] (y)` lie in
the span of the `X k (y)`, then `[Y i, Y j] (y) = 0`. -/
theorem lieBracket_normalFrame_eq_zero (hX : ∀ k, ContDiffAt ℝ 1 (X k) y)
    (hu : IsUnit (frameGram π X y)) (hue : ∀ᶠ z in 𝓝 y, IsUnit (frameGram π X z))
    (hinv : ∀ i j, lieBracket ℝ (X i) (X j) y ∈ Submodule.span ℝ (range fun k => X k y))
    (i j : ι) : lieBracket ℝ (normalFrame π X i) (normalFrame π X j) y = 0 := by
  set S := Submodule.span ℝ (range fun k => X k y) with hS
  have hXd : ∀ k, DifferentiableAt ℝ (X k) y := fun k => (hX k).differentiableAt (by simp)
  have hcd : ∀ i k, DifferentiableAt ℝ (frameCoeff π X i k) y := fun i k =>
    (contDiffAt_frameCoeff hX hu i k).differentiableAt (by simp)
  have hXS : ∀ k, X k y ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hYd : ∀ i, DifferentiableAt ℝ (normalFrame π X i) y := fun i =>
    (contDiffAt_normalFrame hX hu i).differentiableAt (by simp)
  have hconst : ∀ i, ∀ᶠ z in 𝓝 y, π (normalFrame π X i z) = Pi.single i 1 := fun i =>
    hue.mono fun z hz => map_normalFrame hz i
  refine eq_zero_of_mem_span_of_map_eq_zero hu ?_ ?_
  · -- the bracket lies in the span, by involutivity
    have hstep : ∀ k, lieBracket ℝ (normalFrame π X i) (X k) y ∈ S := by
      intro k
      rw [lieBracket_swap]
      refine S.neg_mem ?_
      show lieBracket ℝ (X k) (fun z => ∑ l ∈ Finset.univ, frameCoeff π X i l z • X l z) y ∈ S
      exact lieBracket_sum_smul_mem S Finset.univ (hcd i) hXd hXS (fun l => hinv k l)
    show lieBracket ℝ (normalFrame π X i)
      (fun z => ∑ l ∈ Finset.univ, frameCoeff π X j l z • X l z) y ∈ S
    exact lieBracket_sum_smul_mem S Finset.univ (hcd j) hXd hXS hstep
  · -- the bracket is killed by `π`, because `π ∘ Y i` is constant
    rw [lieBracket, map_sub,
      map_fderiv_eq_zero_of_eventually_const π (hYd j) (hconst j),
      map_fderiv_eq_zero_of_eventually_const π (hYd i) (hconst i), sub_zero]

/-- **A commuting frame for a family that is involutive on a set** (Michor, 3.18, equation (1)
and the claim after it). Let the fields `X k` be `C¹` at `x₀`, with every bracket
`[X i, X j] (y)` in the span of the `X k (y)` for `y ∈ Γ` near `x₀`, and let `π` be a continuous
linear map with `π (X j x₀) = e_j`. Then there are fields `Y i`, `C¹` at `x₀`, with
`[Y i, Y j] = 0` on `Γ` near `x₀`, spanning the same subspace as the `X k` at every point near
`x₀`, and with `π (Y i y) = e_i` there. The `Y i` are the fields `normalFrame π X i`. -/
theorem exists_commuting_frame_on {Γ : Set E} (hX : ∀ k, ContDiffAt ℝ 1 (X k) x₀)
    (hπ : ∀ j, π (X j x₀) = Pi.single j 1)
    (hinv : ∀ᶠ y in 𝓝 x₀, y ∈ Γ → ∀ i j,
      lieBracket ℝ (X i) (X j) y ∈ Submodule.span ℝ (range fun k => X k y)) :
    (∀ i, ContDiffAt ℝ 1 (normalFrame π X i) x₀) ∧
      (∀ i j, ∀ᶠ y in 𝓝 x₀, y ∈ Γ →
        lieBracket ℝ (normalFrame π X i) (normalFrame π X j) y = 0) ∧
      ∀ᶠ y in 𝓝 x₀, Submodule.span ℝ (range fun k => normalFrame π X k y) =
          Submodule.span ℝ (range fun k => X k y) ∧
        ∀ i, π (normalFrame π X i y) = Pi.single i 1 := by
  have hXe : ∀ᶠ y in 𝓝 x₀, ∀ k, ContDiffAt ℝ 1 (X k) y :=
    eventually_all.2 fun k => (hX k).eventually (by simp)
  have hUe : ∀ᶠ y in 𝓝 x₀, IsUnit (frameGram π X y) := eventually_isUnit_frameGram hX hπ
  have hgood := hXe.and (hUe.and hinv)
  refine ⟨fun i => contDiffAt_normalFrame hX hUe.self_of_nhds i, fun i j => ?_, ?_⟩
  · filter_upwards [hgood.eventually_nhds] with y hy hyΓ
    have hy0 := hy.self_of_nhds
    exact lieBracket_normalFrame_eq_zero hy0.1 hy0.2.1 (hy.mono fun z hz => hz.2.1)
      (hy0.2.2 hyΓ) i j
  · filter_upwards [hUe] with y hy
    exact ⟨span_normalFrame hy, fun i => map_normalFrame hy i⟩

/-- **A commuting frame for an involutive family** (Michor, 3.18, equation (1) and the claim after
it). Let the fields `X k` be `C¹` at `x₀`, with every bracket `[X i, X j] (y)` in the span of the
`X k (y)` for `y` near `x₀`, and let `π` be a continuous linear map with `π (X j x₀) = e_j`. Then
there are fields `Y i`, `C¹` at `x₀`, with `[Y i, Y j] = 0` near `x₀`, spanning the same subspace
as the `X k` at every point near `x₀`, and with `π (Y i y) = e_i` there. -/
theorem exists_commuting_frame (hX : ∀ k, ContDiffAt ℝ 1 (X k) x₀)
    (hπ : ∀ j, π (X j x₀) = Pi.single j 1)
    (hinv : ∀ᶠ y in 𝓝 x₀, ∀ i j,
      lieBracket ℝ (X i) (X j) y ∈ Submodule.span ℝ (range fun k => X k y)) :
    ∃ Y : ι → E → E, (∀ i, ContDiffAt ℝ 1 (Y i) x₀) ∧
      (∀ i j, ∀ᶠ y in 𝓝 x₀, lieBracket ℝ (Y i) (Y j) y = 0) ∧
      ∀ᶠ y in 𝓝 x₀, Submodule.span ℝ (range fun k => Y k y) =
          Submodule.span ℝ (range fun k => X k y) ∧ ∀ i, π (Y i y) = Pi.single i 1 := by
  obtain ⟨h1, h2, h3⟩ := exists_commuting_frame_on (Γ := univ) hX hπ
    (hinv.mono fun y hy _ => hy)
  exact ⟨normalFrame π X, h1, fun i j => (h2 i j).mono fun y hy => hy (mem_univ y), h3⟩

end Lightlike.ODE
