import Mathlib.MeasureTheory.Function.L2Space
import Lightlike.OperatorAlgebras.Spectral.OperatorIntegral

/-!
# The cyclic subspace of a projection-valued measure

For a projection-valued measure `μ` on `X` and a vector `ψ`, the bounded Borel functions `f` give the vectors
`μ.integral f ψ`, and `⟨∫ f ψ, ∫ g ψ⟩ = ∫ conj f · g dμ_ψ` for the scalar measure `μ_ψ = μ.assoc ψ`
(`inner_integral_integral`). In particular `‖∫ f ψ‖² = ∫ |f|² dμ_ψ` (`norm_sq_integral_apply`): `f ↦ ∫ f ψ` is an
isometry from the bounded Borel functions in `L²(μ_ψ)` to `H`. The bounded Borel functions are dense in `L²(μ_ψ)`
(`denseRange_toL2`), so it extends to a linear isometry `cycIso : L²(μ_ψ) → H` whose range is the cyclic subspace of
`ψ` (the closure of `{∫ f ψ}`); it sends `1` to `ψ` (`cycIso_one`) and intertwines `μ.integral g` with the multiplication
by `g` (`integral_cycIso_toL2`).

Supporting results for the converse of the Wigner classification; no catalogue entry.
-/

open scoped InnerProductSpace
open MeasureTheory

namespace Lightlike.OperatorAlgebras.Spectral

noncomputable section

variable {X : Type*} [MeasurableSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The inner product of two vectors of the cyclic subspace.** -/
theorem inner_integral_integral (μ : ProjectionValuedMeasure X H) {f g : X → ℂ} (hf : f ∈ BddMeasurable X)
    (hg : g ∈ BddMeasurable X) (ψ : H) :
    ⟪μ.integral f ψ, μ.integral g ψ⟫_ℂ = ∫ x, (starRingEnd ℂ (f x)) * g x ∂(μ.assoc ψ) := by
  have hfc : (fun x => (starRingEnd ℂ) (f x)) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    rcases hf with ⟨hfmeas, C, hC⟩
    refine ⟨?_, ⟨C, ?_⟩⟩
    · simpa [Function.comp_def] using (Complex.continuous_conj.measurable.comp hfmeas)
    · intro x
      simpa using hC x
  have h1 : ⟪μ.integral f ψ, μ.integral g ψ⟫_ℂ =
      ⟪ψ, (μ.integral (fun x => (starRingEnd ℂ) (f x)) * μ.integral g) ψ⟫_ℂ := by
    rw [μ.integral_conj hf, ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]
  have hm : ((fun x => (starRingEnd ℂ) (f x)) * g) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable] at hfc hg ⊢
    obtain ⟨hm1, C1, h1⟩ := hfc
    obtain ⟨hm2, C2, h2⟩ := hg
    exact ⟨hm1.mul hm2, C1 * C2, fun x => by
      simpa [norm_mul] using mul_le_mul (h1 x) (h2 x) (norm_nonneg _) ((norm_nonneg _).trans (h1 x))⟩
  rw [h1, ← μ.integral_mul hfc hg, μ.inner_integral hm ψ]
  rfl

/-- **The norm of a vector of the cyclic subspace**: `‖∫ f ψ‖² = ∫ |f|² dμ_ψ`. -/
theorem norm_sq_integral_apply (μ : ProjectionValuedMeasure X H) {f : X → ℂ} (hf : f ∈ BddMeasurable X)
    (ψ : H) : (‖μ.integral f ψ‖ ^ 2 : ℝ) = ∫ x, ‖f x‖ ^ 2 ∂(μ.assoc ψ) := by
  have h := inner_integral_integral μ hf hf ψ
  rw [inner_self_eq_norm_sq_to_K] at h
  have : ∀ x, (starRingEnd ℂ (f x)) * f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [this] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by simpa using h)

/-! ## The isometry of `L²(μ_ψ)` onto the cyclic subspace -/

/-- A bounded Borel function is in `L²` of a finite measure. -/
lemma memLp_of_bddMeasurable (ν : Measure X) [IsFiniteMeasure ν] {f : X → ℂ} (hf : f ∈ BddMeasurable X) :
    MemLp f 2 ν := by
  obtain ⟨C, hC⟩ := hf.2
  exact MemLp.of_bound hf.1.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- The bounded Borel functions in `L²(ν)`. -/
def toL2 (ν : Measure X) [IsFiniteMeasure ν] : BddMeasurable X →ₗ[ℂ] Lp ℂ 2 ν where
  toFun f := (memLp_of_bddMeasurable ν f.2).toLp f
  map_add' f g := by
    have h := MemLp.toLp_add (memLp_of_bddMeasurable ν f.2) (memLp_of_bddMeasurable ν g.2)
    exact h
  map_smul' c f := by
    have h := MemLp.toLp_const_smul c (memLp_of_bddMeasurable ν f.2)
    exact h

lemma coeFn_toL2 (ν : Measure X) [IsFiniteMeasure ν] (f : BddMeasurable X) : toL2 ν f =ᵐ[ν] f :=
  MemLp.coeFn_toLp (memLp_of_bddMeasurable ν f.2)

/-- The vector `∫ f ψ` as a linear map of the bounded Borel function `f`. -/
def cycMap (μ : ProjectionValuedMeasure X H) (ψ : H) : BddMeasurable X →ₗ[ℂ] H where
  toFun f := μ.integral f ψ
  map_add' f g := by
    show μ.integral ((f : X → ℂ) + g) ψ = _
    rw [μ.integral_add f.2 g.2]; rfl
  map_smul' c f := by
    show μ.integral (c • (f : X → ℂ)) ψ = _
    rw [μ.integral_smul c f.2]; rfl

/-- The norm of `∫ f ψ` is the `L²(μ_ψ)` norm of `f`. -/
lemma norm_cycMap (μ : ProjectionValuedMeasure X H) (ψ : H) (f : BddMeasurable X) :
    ‖cycMap μ ψ f‖ = ‖toL2 (μ.assoc ψ) f‖ := by
  have h1 := norm_sq_integral_apply μ f.2 ψ
  have h2 : ‖toL2 (μ.assoc ψ) f‖ ^ 2 = ∫ x, ‖(f : X → ℂ) x‖ ^ 2 ∂(μ.assoc ψ) := by
    have hin := L2.inner_def (𝕜 := ℂ) (toL2 (μ.assoc ψ) f) (toL2 (μ.assoc ψ) f)
    rw [inner_self_eq_norm_sq_to_K] at hin
    have hae : ∀ᵐ x ∂(μ.assoc ψ), ⟪(toL2 (μ.assoc ψ) f) x, (toL2 (μ.assoc ψ) f) x⟫_ℂ = ((‖(f : X → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
      filter_upwards [coeFn_toL2 (μ.assoc ψ) f] with x hx
      rw [hx, inner_self_eq_norm_sq_to_K]
      push_cast; rfl
    rw [integral_congr_ae hae, integral_complex_ofReal] at hin
    exact Complex.ofReal_injective (by simpa using hin)
  have h3 : ‖cycMap μ ψ f‖ ^ 2 = ‖toL2 (μ.assoc ψ) f‖ ^ 2 := by
    rw [h2]; exact h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

/-- The bounded Borel functions are dense in `L²(ν)` of a finite measure. -/
theorem denseRange_toL2 (ν : Measure X) [IsFiniteMeasure ν] : DenseRange (toL2 ν) := by
  have hd : DenseRange ((↑) : Lp.simpleFunc ℂ 2 ν → Lp ℂ 2 ν) :=
    (Lp.simpleFunc.isDenseEmbedding (p := 2) (by simp)).dense
  refine hd.mono ?_
  rintro _ ⟨F, rfl⟩
  have hs : (⇑(Lp.simpleFunc.toSimpleFunc F) : X → ℂ) ∈ BddMeasurable X := by
    rw [mem_bddMeasurable]
    refine ⟨(Lp.simpleFunc.toSimpleFunc F).measurable, ?_⟩
    set s := Lp.simpleFunc.toSimpleFunc F
    obtain ⟨C, hC⟩ := (s.range.image fun z => ‖z‖).exists_le
    refine ⟨C, fun x => hC _ ?_⟩
    exact Finset.mem_image.2 ⟨s x, s.mem_range_self x, rfl⟩
  refine ⟨⟨_, hs⟩, ?_⟩
  ext1
  filter_upwards [coeFn_toL2 ν ⟨_, hs⟩, Lp.simpleFunc.toSimpleFunc_eq_toFun F] with x h1 h2
  rw [h1]
  exact h2

/-- **The cyclic subspace of `ψ` is `L²(μ_ψ)`**: the linear isometry `L²(μ_ψ) → H` extending
`f ↦ ∫ f dμ ψ` on the bounded Borel functions. -/
def cycIso (μ : ProjectionValuedMeasure X H) (ψ : H) : Lp ℂ 2 (μ.assoc ψ) →ₗᵢ[ℂ] H :=
  (cycMap μ ψ).extendOfIsometry (denseRange_toL2 (μ.assoc ψ)) (norm_cycMap μ ψ)

lemma cycIso_toL2 (μ : ProjectionValuedMeasure X H) (ψ : H) (f : BddMeasurable X) :
    cycIso μ ψ (toL2 (μ.assoc ψ) f) = μ.integral f ψ :=
  LinearMap.extendOfIsometry_eq (cycMap μ ψ) (denseRange_toL2 (μ.assoc ψ)) (norm_cycMap μ ψ) f

/-- The vector `ψ` is the image of the constant function `1`. -/
lemma cycIso_one (μ : ProjectionValuedMeasure X H) (ψ : H) :
    cycIso μ ψ (toL2 (μ.assoc ψ) ⟨1, by rw [mem_bddMeasurable]; exact ⟨measurable_const, 1, by simp⟩⟩) = ψ := by
  rw [cycIso_toL2]
  have : ((⟨1, by rw [mem_bddMeasurable]; exact ⟨measurable_const, 1, by simp⟩⟩ : BddMeasurable X) : X → ℂ) = 1 := rfl
  rw [this, μ.integral_one]; rfl

/-- **The projection-valued measure acts on `L²(μ_ψ)` by multiplication**: `μ(g) U f = U (g f)`. -/
lemma integral_cycIso_toL2 (μ : ProjectionValuedMeasure X H) (ψ : H) (g f : BddMeasurable X)
    (hgf : (g : X → ℂ) * f ∈ BddMeasurable X) :
    μ.integral g (cycIso μ ψ (toL2 (μ.assoc ψ) f)) = cycIso μ ψ (toL2 (μ.assoc ψ) ⟨_, hgf⟩) := by
  rw [cycIso_toL2, cycIso_toL2]
  show μ.integral g (μ.integral f ψ) = μ.integral ((g : X → ℂ) * f) ψ
  rw [μ.integral_mul g.2 f.2]; rfl

end

end Lightlike.OperatorAlgebras.Spectral
