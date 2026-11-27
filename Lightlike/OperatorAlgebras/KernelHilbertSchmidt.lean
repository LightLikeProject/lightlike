import Mathlib
import Lightlike.OperatorAlgebras.KernelOperator
import Lightlike.OperatorAlgebras.HilbertSchmidtBasis

/-!
# Integral operators with continuous kernels are Hilbert–Schmidt

For a compact space `X` with a finite Borel measure `μ`, a continuous kernel `K` and any Hilbert basis
`(b_i)` of `L²(X, μ)`, `Σ_i ‖T_K b_i‖² = ∫∫ |K(x, y)|² dμ(y) dμ(x)` (`hasSum_norm_sq_kernelOp`).
For each `x`, Parseval's identity for `k_x = conj K(x, ·)` gives
`Σ_i |(T_K b_i)(x)|² = ‖k_x‖²`; the finite partial sums are continuous and increase to the
continuous limit, so by Dini's theorem they converge uniformly on the compact `X`, and the integrals
converge. No countability of the basis is needed.

## Main results

* `hasSum_norm_sq_kernelOp`

## References

* A. Gheondea, *Mercer's theorem* (arXiv:2512.06475), Proposition 4.1(iv), pp. 25–26, eq. (4.10)
  (same statement; the proof there uses the bounded convergence theorem over a countable basis).
* P. Garrett, *Compact operators* (notes 09b, 2020), §2 [2.5].
-/

open MeasureTheory Filter Topology

namespace Lightlike.OperatorAlgebras

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
/-- `‖f‖² = ∫ ‖f x‖² dμ` in `L²`. -/
lemma norm_sq_Lp_two_eq (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner f f)]
  congr 1
  funext x
  exact inner_self_eq_norm_sq (f x)

/-- `‖toLp g‖² = ∫ ‖g x‖² dμ` for continuous `g`. -/
lemma norm_sq_toLp_eq (g : C(X, ℂ)) :
    ‖ContinuousMap.toLp (E := ℂ) 2 μ ℂ g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  rw [norm_sq_Lp_two_eq]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (μ := μ) (𝕜 := ℂ) g] with x hx
  rw [hx]

lemma integrable_of_continuous {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **Integral operators with continuous kernels are Hilbert–Schmidt**: for every Hilbert basis
`(b_i)` of `L²(X, μ)`, `Σ_i ‖T_K b_i‖² = ∫∫ |K(x, y)|²`. -/
theorem hasSum_norm_sq_kernelOp (K : C(X × X, ℂ)) {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    HasSum (fun i => ‖kernelOp μ K (b i)‖ ^ 2) (∫ x, ∫ y, ‖K (x, y)‖ ^ 2 ∂μ ∂μ) := by
  set F : Finset ι → X → ℝ := fun s x => ∑ i ∈ s, ‖kernelToC μ K (b i) x‖ ^ 2 with hFdef
  set f : X → ℝ := fun x => ‖kernelVecOf μ K x‖ ^ 2 with hfdef
  have hF_cont : ∀ s, Continuous (F s) := fun s =>
    continuous_finsetSum _ fun i _ => ((kernelToC μ K (b i)).continuous.norm).pow 2
  have hF_mono : Monotone F := fun s t hst x =>
    Finset.sum_le_sum_of_subset_of_nonneg hst fun _ _ _ => by positivity
  have hf : Continuous f := ((continuous_kernelVecOf μ K).norm).pow 2
  have ht : ∀ x, Tendsto (F · x) atTop (𝓝 (f x)) := fun x => by
    have h := hasSum_norm_sq_inner_basis b (kernelVecOf μ K x)
    have e : ∀ i, ‖kernelToC μ K (b i) x‖ ^ 2 = ‖inner ℂ (b i) (kernelVecOf μ K x)‖ ^ 2 := fun i => by
      rw [kernelToC_apply, norm_inner_symm]
    show Tendsto (fun s => ∑ i ∈ s, ‖kernelToC μ K (b i) x‖ ^ 2) atTop (𝓝 (f x))
    simp_rw [e]
    exact h
  have hU := Monotone.tendstoUniformly_of_forall_tendsto hF_cont hF_mono hf ht
  have hI : Tendsto (fun s => ∫ x, F s x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c := μ.real Set.univ + 1 with hc
    have hc0 : 0 < c := by positivity
    filter_upwards [Metric.tendstoUniformly_iff.1 hU (ε / c) (by positivity)] with s hs
    rw [dist_eq_norm, ← integral_sub (integrable_of_continuous μ (hF_cont s))
      (integrable_of_continuous μ hf)]
    calc ‖∫ x, (F s x - f x) ∂μ‖ ≤ ε / c * μ.real Set.univ := by
          refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => ?_)
          have := hs x
          rw [dist_comm, dist_eq_norm] at this
          exact this.le
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hc0]
          nlinarith [measureReal_nonneg (μ := μ) (s := Set.univ)]
  have hsum : ∀ s, ∫ x, F s x ∂μ = ∑ i ∈ s, ‖kernelOp μ K (b i)‖ ^ 2 := by
    intro s
    show ∫ x, ∑ i ∈ s, ‖kernelToC μ K (b i) x‖ ^ 2 ∂μ = _
    rw [integral_finsetSum s fun i _ => integrable_of_continuous μ
      (show Continuous fun x => ‖kernelToC μ K (b i) x‖ ^ 2 from
        ((kernelToC μ K (b i)).continuous.norm).pow 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kernelOp, ContinuousLinearMap.comp_apply, norm_sq_toLp_eq]
  have hfI : ∫ x, f x ∂μ = ∫ x, ∫ y, ‖K (x, y)‖ ^ 2 ∂μ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hfdef, kernelVecOf, norm_sq_toLp_eq, kernelCurry_apply, Complex.norm_conj]
  rw [← hfI]
  exact hI.congr hsum

end

end Lightlike.OperatorAlgebras
