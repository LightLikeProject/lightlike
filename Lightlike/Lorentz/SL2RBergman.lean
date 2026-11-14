module

public import Lightlike.Lorentz.SL2RDiscrete

/-!
# The weighted Bergman spaces of the upper half-plane

The holomorphic discrete series `D_n⁺` of `SL(2,ℝ)` acts on the **weighted Bergman space**
`A²_n ⊆ L²(ℍ, yⁿ dμ_ℍ)` of holomorphic square-integrable functions (`SL2RDiscrete.lean` defines
the action on the whole `L²` space and proves that it preserves the holomorphic classes). This
file proves that `A²_n` is a closed subspace, hence a Hilbert space, and restricts the action
to it.

## Main results

* `norm_sq_le_ball`: the **area mean-value inequality**
  `π r² |ψ(c)|² ≤ ∫_{B(c,r)} |ψ|²` for `ψ` holomorphic on the disc `B(c,r)`.
* `norm_sq_le_bergman`: the **pointwise Bergman bound**
  `|φ(z)|² ≤ C (Im z)⁻ⁿ ∫ |φ|² yⁿ dμ_ℍ` for holomorphic `φ` on `ℍ`.
* `isClosed_holoSubmodule`: `A²_n` is closed in `L²(ℍ, μ_n)`, hence complete.
* `discreteSeries n : ContRepresentation ℂ SL2R (holoSubmodule n)`: the **holomorphic discrete
  series** `D_n⁺`, unitary (`discreteSeries_norm`, `discreteSeries_inner`,
  `discreteSeries_mem_unitary`), strongly and jointly continuous (`continuous_discreteSeries`,
  `continuous_discreteSeries_action`).
* `holoSubmodule_ne_bot`: for `n ≥ 2`, `(z + i)⁻ⁿ` is a nonzero element of `A²_n`
  (`memLp_lowestVec`, `lowestClass_ne_zero`), so `D_n⁺` is not the zero representation.

The proof of the area inequality applies the mean-value property
(`DiffContOnCl.circleAverage`) to `ψ²` on every circle `|w - c| = s < r` and integrates over
`s` in polar coordinates.

## References

* A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton (1986), §II.5.
* S. Lang, *SL₂(ℝ)*, Graduate Texts in Mathematics 105, Springer (1985), Ch. IX §2.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology Metric Set
open scoped ENNReal NNReal Real

noncomputable section

namespace Lightlike.Lorentz

/-! ### Mean-value inequalities for holomorphic functions -/

/-- `c + polarCoord.symm (s, θ)` is the point of the circle of radius `s` about `c` at
angle `θ`. -/
lemma circleMap_eq_polar (c : ℂ) (s θ : ℝ) :
    circleMap c s θ = c + Complex.polarCoord.symm (s, θ) := by
  simp only [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- **Circle mean-value inequality**: for `ψ` holomorphic on the closed disc `B̄(c,s)`,
`2π |ψ(c)|² ≤ ∫_{-π}^{π} |ψ(c + s e^{iθ})|² dθ`. -/
theorem norm_sq_le_circle {ψ : ℂ → ℂ} {c : ℂ} {s : ℝ} (hs : 0 < s)
    (hψ : DifferentiableOn ℂ ψ (closedBall c s)) :
    ENNReal.ofReal (2 * π) * ‖ψ c‖ₑ ^ 2 ≤
      ∫⁻ θ in Ioo (-π) π, ‖ψ (c + Complex.polarCoord.symm (s, θ))‖ₑ ^ 2 := by
  have hdc : DiffContOnCl ℂ (fun z => ψ z ^ 2) (ball c |s|) := by
    rw [abs_of_pos hs]
    exact (hψ.pow 2).diffContOnCl_ball subset_rfl
  have hmean := hdc.circleAverage
  rw [Real.circleAverage_def] at hmean
  have hper : ∫ θ in (0 : ℝ)..2 * π, ψ (circleMap c s θ) ^ 2 =
      ∫ θ in Ioo (-π) π, ψ (c + Complex.polarCoord.symm (s, θ)) ^ 2 := by
    have h := ((periodic_circleMap c s).comp (fun z => ψ z ^ 2)).intervalIntegral_add_eq 0 (-π)
    simp only [zero_add, Function.comp_def] at h
    rw [h, show -π + 2 * π = π by ring, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
    simp only [circleMap_eq_polar]
  rw [hper] at hmean
  calc ENNReal.ofReal (2 * π) * ‖ψ c‖ₑ ^ 2
      = ENNReal.ofReal (2 * π) * ‖ψ c ^ 2‖ₑ := by rw [enorm_pow]
    _ = ‖∫ θ in Ioo (-π) π, ψ (c + Complex.polarCoord.symm (s, θ)) ^ 2‖ₑ := by
        rw [← hmean, enorm_smul, ← mul_assoc, Real.enorm_eq_ofReal (by positivity),
          ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
          ENNReal.ofReal_one, one_mul]
    _ ≤ ∫⁻ θ in Ioo (-π) π, ‖ψ (c + Complex.polarCoord.symm (s, θ)) ^ 2‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ θ in Ioo (-π) π, ‖ψ (c + Complex.polarCoord.symm (s, θ))‖ₑ ^ 2 := by
        simp only [enorm_pow]

/-- `∫_0^r s ds = r²/2`, as a lower Lebesgue integral. -/
lemma lintegral_Ioo_ofReal_id {r : ℝ} (hr : 0 < r) :
    ∫⁻ s in Ioo 0 r, ENNReal.ofReal s = ENNReal.ofReal (r ^ 2 / 2) := by
  have hint : IntegrableOn (fun s : ℝ => s) (Ioo 0 r) :=
    (continuous_id.integrableOn_Icc (a := 0) (b := r)).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun s hs => hs.1.le)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le, integral_id]
  ring_nf

/-- **Area mean-value inequality**: for `ψ` holomorphic on the open disc `B(c,r)`,
`π r² |ψ(c)|² ≤ ∫_{B(c,r)} |ψ|²`. -/
theorem norm_sq_le_ball {ψ : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hψ : DifferentiableOn ℂ ψ (ball c r)) :
    ENNReal.ofReal (π * r ^ 2) * ‖ψ c‖ₑ ^ 2 ≤ ∫⁻ z in ball c r, ‖ψ z‖ₑ ^ 2 := by
  set F : ℂ → ℝ≥0∞ := fun z => ‖ψ z‖ₑ ^ 2 with hF
  set S : Set (ℝ × ℝ) := Ioo 0 r ×ˢ Ioo (-π) π with hS
  have hSm : MeasurableSet S := measurableSet_Ioo.prod measurableSet_Ioo
  have hmem : ∀ p ∈ S, c + Complex.polarCoord.symm p ∈ ball c r := by
    rintro ⟨s, θ⟩ ⟨hs, -⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_polarCoord_symm,
      abs_of_pos hs.1]
    exact hs.2
  set G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * F (c + Complex.polarCoord.symm p)
    with hG
  have hFc : ContinuousOn (fun p => F (c + Complex.polarCoord.symm p)) S := by
    have hpol : Continuous fun p : ℝ × ℝ => c + Complex.polarCoord.symm p := by
      simp only [Complex.polarCoord_symm_apply]; fun_prop
    refine ((ENNReal.continuous_pow 2).comp continuous_enorm).comp_continuousOn ?_
    exact hψ.continuousOn.comp hpol.continuousOn hmem
  have hGm : AEMeasurable G ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-π) π))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable.mul (hFc.aemeasurable hSm)
  calc ENNReal.ofReal (π * r ^ 2) * F c
      = ∫⁻ s in Ioo 0 r, ENNReal.ofReal s * (ENNReal.ofReal (2 * π) * F c) := by
        rw [lintegral_mul_const _ ENNReal.measurable_ofReal, lintegral_Ioo_ofReal_id hr,
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring
    _ ≤ ∫⁻ s in Ioo 0 r, ∫⁻ θ in Ioo (-π) π, G (s, θ) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ ?_))
        intro s hs
        simp only [hG]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact norm_sq_le_circle hs.1 (hψ.mono (closedBall_subset_ball hs.2))
    _ = ∫⁻ p in S, G p := by
        rw [← lintegral_prod G hGm, Measure.prod_restrict, ← Measure.volume_eq_prod]
    _ = ∫⁻ p in S, ENNReal.ofReal p.1 •
          (ball c r).indicator F (c + Complex.polarCoord.symm p) := by
        refine setLIntegral_congr_fun hSm fun p hp => ?_
        rw [indicator_of_mem (hmem p hp), smul_eq_mul]
    _ ≤ ∫⁻ p in Complex.polarCoord.target, ENNReal.ofReal p.1 •
          (ball c r).indicator F (c + Complex.polarCoord.symm p) := by
        refine lintegral_mono_set ?_
        rw [Complex.polarCoord_target]
        exact prod_mono Ioo_subset_Ioi_self subset_rfl
    _ = ∫⁻ w, (ball c r).indicator F (c + w) :=
        Complex.lintegral_comp_polarCoord_symm fun w => (ball c r).indicator F (c + w)
    _ = ∫⁻ z in ball c r, F z := by
        rw [lintegral_add_left_eq_self (fun w => (ball c r).indicator F w) c,
          lintegral_indicator measurableSet_ball]

/-! ### The pointwise Bergman bound -/

namespace SL2R

open UpperHalfPlane
open scoped Manifold InnerProductSpace

/-- The hyperbolic measure on `ℍ` as Lebesgue measure with density `y⁻²`, written with
`ENNReal.ofReal`. -/
lemma volume_eq_withDensity :
    (volume : Measure ℍ) =
      (volume.comap UpperHalfPlane.coe).withDensity fun z => ENNReal.ofReal (z.im ^ 2)⁻¹ := by
  rw [volume_def]
  congr 1; funext z
  rw [ENNReal.ofReal]; congr 1; ext
  simp [Real.coe_toNNReal _ (inv_nonneg.2 (sq_nonneg z.im))]

lemma measurable_im_density : Measurable fun z : ℍ => ENNReal.ofReal (z.im ^ 2)⁻¹ :=
  ENNReal.measurable_ofReal.comp (UpperHalfPlane.continuous_im.pow 2).measurable.inv

/-- An integral against `yⁿ dμ_ℍ` as an integral against Lebesgue measure pulled back to `ℍ`,
with density `yⁿ⁻²`. -/
lemma lintegral_μn_eq (n : ℕ) {F : ℍ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ z, F z ∂μn n = ∫⁻ z, ENNReal.ofReal (z.im ^ 2)⁻¹ * (wt n z * F z)
      ∂(volume.comap UpperHalfPlane.coe) := by
  rw [lintegral_μn n hF, volume_eq_withDensity]
  exact lintegral_withDensity_eq_lintegral_mul _ measurable_im_density ((measurable_wt n).mul hF)

/-- **Pointwise Bergman bound**: a holomorphic `φ` on `ℍ` satisfies
`(π/9) (Im z₀ / 2)ⁿ |φ(z₀)|² ≤ ∫ |φ|² yⁿ dμ_ℍ`. The proof applies `norm_sq_le_ball` on the disc of
radius `Im z₀ / 2` about `z₀`, on which `yⁿ⁻² ≥ (Im z₀/2)ⁿ (2/(3 Im z₀))²`. -/
theorem bergman_bound (n : ℕ) {φ : ℍ → ℂ} (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (z₀ : ℍ) :
    ENNReal.ofReal (π / 9 * (z₀.im / 2) ^ n) * ‖φ z₀‖ₑ ^ 2 ≤ ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂μn n := by
  set y₀ := z₀.im with hy₀
  have hy : 0 < y₀ := z₀.im_pos
  set r := y₀ / 2 with hr
  have hr0 : 0 < r := by positivity
  set ψ : ℂ → ℂ := φ ∘ ofComplex with hψ
  have him : ∀ w ∈ ball (z₀ : ℂ) r, y₀ / 2 < w.im ∧ w.im < 3 * y₀ / 2 := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h := (Complex.abs_im_le_norm (w - z₀)).trans_lt hw
    rw [Complex.sub_im, abs_lt] at h
    have : (z₀ : ℂ).im = y₀ := rfl
    constructor <;> linarith [h.1, h.2]
  have hsub : ball (z₀ : ℂ) r ⊆ range UpperHalfPlane.coe := fun w hw =>
    ⟨⟨w, by linarith [(him w hw).1]⟩, rfl⟩
  have hdiff : DifferentiableOn ℂ ψ (ball (z₀ : ℂ) r) :=
    (UpperHalfPlane.mdifferentiable_iff.1 hφ).mono fun w hw => by
      change 0 < w.im; linarith [(him w hw).1]
  have hmean := norm_sq_le_ball hr0 hdiff
  have hψ0 : ψ z₀ = φ z₀ := by simp [hψ]
  set m : ℝ := (y₀ / 2) ^ n * (2 / (3 * y₀)) ^ 2 with hm
  have hφm : Measurable fun z => ‖φ z‖ₑ ^ 2 :=
    (hφ.continuous.measurable.enorm).pow_const 2
  have hpt : ∀ z : ℍ, ENNReal.ofReal m * (ball (z₀ : ℂ) r).indicator (fun w => ‖ψ w‖ₑ ^ 2) z ≤
      ENNReal.ofReal (z.im ^ 2)⁻¹ * (wt n z * ‖φ z‖ₑ ^ 2) := by
    intro z
    by_cases hz : (z : ℂ) ∈ ball (z₀ : ℂ) r
    · rw [indicator_of_mem hz, ← mul_assoc]
      simp only [hψ, Function.comp_apply, ofComplex_apply]
      gcongr
      rw [wt, ← ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      obtain ⟨h1, h2⟩ := him z hz
      have h1' : y₀ / 2 < z.im := h1
      have h2' : z.im < 3 * y₀ / 2 := h2
      have hz0 : 0 < z.im := z.im_pos
      have hinv : 2 / (3 * y₀) ≤ z.im⁻¹ := by
        rw [le_inv_comm₀ (by positivity) hz0, inv_div]; linarith
      calc m ≤ z.im ^ n * z.im⁻¹ ^ 2 :=
            mul_le_mul (pow_le_pow_left₀ (by positivity) h1'.le n)
              (pow_le_pow_left₀ (by positivity) hinv 2) (by positivity) (by positivity)
        _ = (z.im ^ 2)⁻¹ * z.im ^ n := by rw [inv_pow, mul_comm]
    · rw [indicator_of_notMem hz, mul_zero]; exact zero_le
  calc ENNReal.ofReal (π / 9 * (y₀ / 2) ^ n) * ‖φ z₀‖ₑ ^ 2
      = ENNReal.ofReal m * (ENNReal.ofReal (π * r ^ 2) * ‖ψ z₀‖ₑ ^ 2) := by
        rw [hψ0, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [hm, hr]; field_simp; ring
    _ ≤ ENNReal.ofReal m * ∫⁻ w in ball (z₀ : ℂ) r, ‖ψ w‖ₑ ^ 2 := by gcongr
    _ = ENNReal.ofReal m * ∫⁻ z : ℍ, (ball (z₀ : ℂ) r).indicator (fun w => ‖ψ w‖ₑ ^ 2) z
          ∂(volume.comap UpperHalfPlane.coe) := by
        rw [← measurableEmbedding_coe.lintegral_map, measurableEmbedding_coe.map_comap,
          lintegral_indicator measurableSet_ball, Measure.restrict_restrict measurableSet_ball,
          inter_eq_left.2 hsub]
    _ = ∫⁻ z : ℍ, ENNReal.ofReal m * (ball (z₀ : ℂ) r).indicator (fun w => ‖ψ w‖ₑ ^ 2) z
          ∂(volume.comap UpperHalfPlane.coe) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (z.im ^ 2)⁻¹ * (wt n z * ‖φ z‖ₑ ^ 2)
          ∂(volume.comap UpperHalfPlane.coe) := lintegral_mono hpt
    _ = ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂μn n := (lintegral_μn_eq n hφm).symm

/-- The squared `L²` norm of a class as the integral of a representative. -/
lemma enorm_sq_eq_lintegral {n : ℕ} (f : Hn n) {φ : ℍ → ℂ} (hf : f =ᵐ[μn n] φ) :
    ‖f‖ₑ ^ 2 = ∫⁻ z, ‖φ z‖ₑ ^ 2 ∂μn n := by
  rw [Lp.enorm_def, eLpNorm_congr_ae hf]
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero
    ((Lp.aestronglyMeasurable f).congr hf)
  simpa using h

/-- **Pointwise Bergman bound** for a class `f ∈ A²_n` with holomorphic representative `φ`:
`(π/9) (Im z/2)ⁿ |φ(z)|² ≤ ‖f‖²`. -/
theorem norm_sq_le_bergman {n : ℕ} (f : Hn n) {φ : ℍ → ℂ}
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hf : f =ᵐ[μn n] φ) (z : ℍ) :
    π / 9 * (z.im / 2) ^ n * ‖φ z‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := bergman_bound n hφ z
  rw [← enorm_sq_eq_lintegral f hf, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by have := z.im_pos; positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- The Bergman bound as a bound on `|φ(z)|`: `|φ(z)| ≤ √(9/π · (2/Im z)ⁿ) ‖f‖`. -/
theorem norm_le_bergman {n : ℕ} (f : Hn n) {φ : ℍ → ℂ}
    (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hf : f =ᵐ[μn n] φ) (z : ℍ) :
    ‖φ z‖ ≤ Real.sqrt (9 / π * (2 / z.im) ^ n) * ‖f‖ := by
  have hz := z.im_pos
  have h := norm_sq_le_bergman f hφ hf z
  rw [← Real.sqrt_sq (norm_nonneg f), ← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  have hc : 0 < π / 9 * (z.im / 2) ^ n := by positivity
  calc ‖φ z‖ ^ 2 = (π / 9 * (z.im / 2) ^ n)⁻¹ * (π / 9 * (z.im / 2) ^ n * ‖φ z‖ ^ 2) := by
        field_simp
    _ ≤ (π / 9 * (z.im / 2) ^ n)⁻¹ * ‖f‖ ^ 2 := by gcongr
    _ = 9 / π * (2 / z.im) ^ n * ‖f‖ ^ 2 := by
        congr 1; rw [mul_inv, inv_div, ← inv_pow, inv_div]

/-! ### Closedness of the Bergman space -/

/-- **The Bergman space is closed**: an `L²` limit of holomorphic classes is holomorphic. By the
pointwise bound, an `L²`-Cauchy sequence of holomorphic functions converges uniformly on every
half-plane `Im z ≥ δ`; its limit is holomorphic and is the `L²` limit almost everywhere. -/
theorem isClosed_holoSubmodule (n : ℕ) : IsClosed (holoSubmodule n : Set (Hn n)) := by
  refine IsSeqClosed.isClosed fun {u} {f} hu hlim => ?_
  choose φ hφ hφu using hu
  have hcs : CauchySeq u := hlim.cauchySeq
  have hUC : ∀ δ > 0, UniformCauchySeqOn φ atTop {z : ℍ | δ ≤ z.im} := by
    intro δ hδ
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set C := Real.sqrt (9 / π * (2 / δ) ^ n) with hC
    have hC0 : 0 ≤ C := Real.sqrt_nonneg _
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hcs (ε / (C + 1)) (by positivity)
    refine ⟨N, fun k hk l hl z hz => ?_⟩
    have hsub : u k - u l =ᵐ[μn n] φ k - φ l := by
      filter_upwards [Lp.coeFn_sub (u k) (u l), hφu k, hφu l] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, Pi.sub_apply]
    have hb := norm_le_bergman (u k - u l) ((hφ k).sub (hφ l)) hsub z
    have hz0 : 0 < z.im := z.im_pos
    have hzδ : δ ≤ z.im := hz
    have hCz : Real.sqrt (9 / π * (2 / z.im) ^ n) ≤ C := by
      refine Real.sqrt_le_sqrt ?_
      gcongr
    have hd := hN k hk l hl
    rw [dist_eq_norm] at hd ⊢
    calc ‖φ k z - φ l z‖ ≤ Real.sqrt (9 / π * (2 / z.im) ^ n) * ‖u k - u l‖ := hb
      _ ≤ C * (ε / (C + 1)) := mul_le_mul hCz hd.le (norm_nonneg _) hC0
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hpt : ∀ z, CauchySeq fun k => φ k z := fun z =>
    (hUC z.im z.im_pos).cauchySeq (le_refl z.im)
  set ψ : ℍ → ℂ := fun z => limUnder atTop fun k => φ k z with hψdef
  have hψ : ∀ z, Tendsto (fun k => φ k z) atTop (𝓝 (ψ z)) := fun z => (hpt z).tendsto_limUnder
  have hTU : ∀ δ > 0, TendstoUniformlyOn φ ψ atTop {z : ℍ | δ ≤ z.im} := fun δ hδ =>
    (hUC δ hδ).tendstoUniformlyOn_of_tendsto fun z _ => hψ z
  have hψd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
    refine TendstoLocallyUniformlyOn.differentiableOn (φ := atTop)
      (F := fun k => φ k ∘ ofComplex) ?_
      (Eventually.of_forall fun k => UpperHalfPlane.mdifferentiable_iff.1 (hφ k)) hU
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun w hw => ?_
    have hw0 : 0 < w.im := hw
    refine ⟨{w' : ℂ | w.im / 2 < w'.im}, ?_, ?_⟩
    · refine mem_nhdsWithin_of_mem_nhds ((isOpen_lt continuous_const
        Complex.continuous_im).mem_nhds ?_)
      change w.im / 2 < w.im; linarith
    · refine ((hTU (w.im / 2) (by positivity)).comp ofComplex).mono fun w' hw' => ?_
      have hw'0 : 0 < w'.im := by have : w.im / 2 < w'.im := hw'; linarith
      simp only [mem_preimage]
      rw [ofComplex_apply_of_im_pos hw'0]
      exact le_of_lt (show w.im / 2 < w'.im from hw')
  refine ⟨ψ, hψd, ?_⟩
  have hmeas : TendstoInMeasure (μn n) (fun k => (u k : ℍ → ℂ)) atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' u f).1 hlim)
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hall : ∀ᵐ z ∂μn n, ∀ k, u k z = φ k z := ae_all_iff.2 hφu
  filter_upwards [hae, hall] with z h1 h2
  refine tendsto_nhds_unique h1 ?_
  simp only [h2]
  exact (hψ z).comp hns.tendsto_atTop

/-! ### The holomorphic discrete series on the Bergman space -/

/-- `A²_n` is a Hilbert space: a closed subspace of `L²(ℍ, μ_n)`. -/
instance instCompleteSpace_holoSubmodule (n : ℕ) : CompleteSpace (holoSubmodule n) :=
  (isClosed_holoSubmodule n).isComplete.completeSpace_coe

/-- `D_n(g)` restricted to the invariant subspace `A²_n`. -/
def discreteSeriesMap (n : ℕ) (g : SL2R) : holoSubmodule n →L[ℂ] holoSubmodule n :=
  ((discreteAction n g).comp (holoSubmodule n).subtypeL).codRestrict (holoSubmodule n)
    fun f => discreteAction_mem_holoSubmodule n g f.2

/-- **The holomorphic discrete series** `D_n⁺`: the representation of `SL(2,ℝ)` on the weighted
Bergman space `A²_n` (nonzero for `n ≥ 2`, `holoSubmodule_ne_bot`). -/
def discreteSeries (n : ℕ) : ContRepresentation ℂ SL2R (holoSubmodule n) :=
  .ofMonoidHom
    { toFun := discreteSeriesMap n
      map_one' := by
        ext1 f; apply Subtype.ext
        simp [discreteSeriesMap]
      map_mul' := fun g h => by
        ext1 f; apply Subtype.ext
        change discreteAction n (g * h) f = discreteAction n g (discreteAction n h f)
        rw [map_mul, mul_apply_eq_comp] }

@[simp] lemma coe_discreteSeries (n : ℕ) (g : SL2R) (f : holoSubmodule n) :
    (discreteSeries n g f : Hn n) = discreteAction n g f := rfl

/-- **Unitarity of `D_n⁺`** (norm form). -/
theorem discreteSeries_norm (n : ℕ) (g : SL2R) (f : holoSubmodule n) :
    ‖discreteSeries n g f‖ = ‖f‖ :=
  discreteAction_norm n g f

/-- **Unitarity of `D_n⁺`**: the inner product of `A²_n` is preserved. -/
theorem discreteSeries_inner (n : ℕ) (g : SL2R) (f f' : holoSubmodule n) :
    ⟪discreteSeries n g f, discreteSeries n g f'⟫_ℂ = ⟪f, f'⟫_ℂ :=
  discreteAction_inner n g f f'

/-- Each `D_n⁺(g)` is a unitary operator on `A²_n`. -/
theorem discreteSeries_mem_unitary (n : ℕ) (g : SL2R) :
    discreteSeries n g ∈ unitary (holoSubmodule n →L[ℂ] holoSubmodule n) :=
  mem_unitary_of_inner _ (discreteSeries_inner n) g

/-- **Strong continuity of `D_n⁺`.** -/
theorem continuous_discreteSeries (n : ℕ) (f : holoSubmodule n) :
    Continuous fun g => discreteSeries n g f :=
  continuous_induced_rng.2 (continuous_discreteAction n f)

/-- **Joint continuity of `D_n⁺`**: `(g, f) ↦ D_n⁺(g) f` is continuous. -/
theorem continuous_discreteSeries_action (n : ℕ) :
    Continuous fun p : SL2R × holoSubmodule n => discreteSeries n p.1 p.2 :=
  continuous_action_of_norm (discreteSeries n) (discreteSeries_norm n) (continuous_discreteSeries n)

/-! ### A nonzero vector: `(z + i)⁻ⁿ` -/

/-- The function `z ↦ (z + i)⁻ⁿ` on `ℍ`, the standard nonzero element of `A²_n` for `n ≥ 2`
(the lowest `K`-type vector of `D_n⁺` in Knapp, §II.5). -/
def lowestVec (n : ℕ) (z : ℍ) : ℂ := ((z : ℂ) + Complex.I) ^ (-(n : ℤ))

lemma coe_add_I_ne_zero (z : ℍ) : (z : ℂ) + Complex.I ≠ 0 := fun h => by
  have := congrArg Complex.im h
  simp only [Complex.add_im, UpperHalfPlane.coe_im, Complex.I_im, Complex.zero_im] at this
  linarith [z.im_pos]

lemma continuous_lowestVec (n : ℕ) : Continuous (lowestVec n) :=
  (UpperHalfPlane.continuous_coe.add continuous_const).zpow₀ _ fun z =>
    Or.inl (coe_add_I_ne_zero z)

lemma mdifferentiable_lowestVec (n : ℕ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (lowestVec n) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine DifferentiableOn.congr (f := fun w : ℂ => (w + Complex.I) ^ (-(n : ℤ)))
    (fun w hw => ?_) fun w hw => ?_
  · have h0 : w + Complex.I ≠ 0 := coe_add_I_ne_zero ⟨w, hw⟩
    exact (DifferentiableAt.zpow (f := fun w : ℂ => w + Complex.I)
      (differentiableAt_id.add_const _) (Or.inl h0)).differentiableWithinAt
  simp only [Function.comp_apply, lowestVec, ofComplex_apply_of_im_pos hw]

/-- The pointwise bound `yⁿ⁻² |z + i|⁻²ⁿ ≤ (1 + x²)⁻¹ (1 + y²)⁻¹` for `n ≥ 2`. -/
lemma lowestVec_density_le {n : ℕ} (hn : 2 ≤ n) (z : ℍ) :
    ENNReal.ofReal (z.im ^ 2)⁻¹ * (wt n z * ‖lowestVec n z‖ₑ ^ 2) ≤
      ENNReal.ofReal (1 + (z : ℂ).re ^ 2)⁻¹ * ENNReal.ofReal (1 + (z : ℂ).im ^ 2)⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hy : 0 < z.im := z.im_pos
  set x := (z : ℂ).re
  have hyc : (z : ℂ).im = z.im := rfl
  set A := Complex.normSq ((z : ℂ) + Complex.I) with hA
  have hAe : A = x ^ 2 + (z.im + 1) ^ 2 := by
    rw [hA, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, add_zero, hyc]
    ring
  have hA0 : 0 < A := Complex.normSq_pos.2 (coe_add_I_ne_zero z)
  have hnorm : ‖lowestVec (m + 2) z‖ ^ 2 = (A ^ (m + 2))⁻¹ := by
    rw [lowestVec, norm_zpow, _root_.zpow_neg, zpow_natCast, inv_pow, ← pow_mul,
      mul_comm (m + 2) 2, pow_mul, Complex.sq_norm]
  rw [wt, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hnorm,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), hyc]
  apply ENNReal.ofReal_le_ofReal
  have h1 : 1 + x ^ 2 ≤ A := by rw [hAe]; nlinarith
  have h2 : 1 + z.im ^ 2 ≤ A := by rw [hAe]; nlinarith
  have h3 : z.im ≤ A := by rw [hAe]; nlinarith
  have hL : (z.im ^ 2)⁻¹ * (z.im ^ (m + 2) * (A ^ (m + 2))⁻¹) =
      z.im ^ m / A ^ m * (A * A)⁻¹ := by
    have := hy.ne'; have := hA0.ne'
    field_simp; ring
  rw [hL]
  calc z.im ^ m / A ^ m * (A * A)⁻¹ ≤ 1 * (A * A)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_le_one (by positivity)]
        exact pow_le_pow_left₀ hy.le h3 m
    _ = (A * A)⁻¹ := one_mul _
    _ ≤ (1 + x ^ 2)⁻¹ * (1 + z.im ^ 2)⁻¹ := by
        rw [← mul_inv]
        exact inv_anti₀ (by positivity) (mul_le_mul h1 h2 (by positivity) hA0.le)

/-- **`(z + i)⁻ⁿ` is square-integrable** against `yⁿ dμ_ℍ` for `n ≥ 2`. -/
theorem memLp_lowestVec {n : ℕ} (hn : 2 ≤ n) : MemLp (lowestVec n) 2 (μn n) := by
  have hmeas : Measurable fun z => ‖lowestVec n z‖ₑ ^ 2 :=
    ((continuous_lowestVec n).measurable.enorm).pow_const 2
  have hsq := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := μn n) two_ne_zero
    (continuous_lowestVec n).aestronglyMeasurable
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at hsq
  have key : ∫⁻ z, ‖lowestVec n z‖ₑ ^ 2 ∂μn n < ⊤ := by
    set K : ℂ → ℝ≥0∞ := fun w =>
      ENNReal.ofReal (1 + w.re ^ 2)⁻¹ * ENNReal.ofReal (1 + w.im ^ 2)⁻¹ with hK
    have hKm : Measurable K := by
      refine (ENNReal.measurable_ofReal.comp ?_).mul (ENNReal.measurable_ofReal.comp ?_) <;>
        fun_prop
    have hR : ∫⁻ x : ℝ, ENNReal.ofReal (1 + x ^ 2)⁻¹ < ⊤ := integrable_inv_one_add_sq.lintegral_lt_top
    calc ∫⁻ z, ‖lowestVec n z‖ₑ ^ 2 ∂μn n
        = ∫⁻ z, ENNReal.ofReal (z.im ^ 2)⁻¹ * (wt n z * ‖lowestVec n z‖ₑ ^ 2)
            ∂(volume.comap UpperHalfPlane.coe) := lintegral_μn_eq n hmeas
      _ ≤ ∫⁻ z : ℍ, K z ∂(volume.comap UpperHalfPlane.coe) :=
          lintegral_mono fun z => lowestVec_density_le hn z
      _ = ∫⁻ w in range UpperHalfPlane.coe, K w := by
          rw [← measurableEmbedding_coe.lintegral_map, measurableEmbedding_coe.map_comap]
      _ ≤ ∫⁻ w, K w := setLIntegral_le_lintegral _ _
      _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (1 + p.1 ^ 2)⁻¹ * ENNReal.ofReal (1 + p.2 ^ 2)⁻¹ := by
          rw [← Complex.volume_preserving_equiv_real_prod.lintegral_comp]
          · rfl
          · exact (ENNReal.measurable_ofReal.comp
              (by fun_prop : Measurable fun p : ℝ × ℝ => (1 + p.1 ^ 2)⁻¹)).mul
              (ENNReal.measurable_ofReal.comp
                (by fun_prop : Measurable fun p : ℝ × ℝ => (1 + p.2 ^ 2)⁻¹))
      _ = (∫⁻ x : ℝ, ENNReal.ofReal (1 + x ^ 2)⁻¹) * ∫⁻ y : ℝ, ENNReal.ofReal (1 + y ^ 2)⁻¹ := by
          rw [Measure.volume_eq_prod]
          have hm : Measurable fun x : ℝ => ENNReal.ofReal (1 + x ^ 2)⁻¹ :=
            ENNReal.measurable_ofReal.comp (by fun_prop)
          exact lintegral_prod_mul hm.aemeasurable hm.aemeasurable
      _ < ⊤ := ENNReal.mul_lt_top hR hR
  have key' : eLpNorm (lowestVec n) 2 (μn n) ^ (2 : ℝ) < ∞ := by
    rw [hsq]; simpa only [ENNReal.rpow_two] using key
  exact (ENNReal.rpow_lt_top_iff_of_pos two_pos).1 key'

/-- The class of `(z + i)⁻ⁿ` in `L²(ℍ, μ_n)`. -/
def lowestClass {n : ℕ} (hn : 2 ≤ n) : Hn n := (memLp_lowestVec hn).toLp _

lemma lowestClass_mem {n : ℕ} (hn : 2 ≤ n) : lowestClass hn ∈ holoSubmodule n :=
  ⟨lowestVec n, mdifferentiable_lowestVec n, MemLp.coeFn_toLp _⟩

/-- **Non-vacuity**: `(z + i)⁻ⁿ` is a nonzero element of `A²_n`; its norm is bounded below by the
pointwise Bergman bound at `z = i`. -/
theorem lowestClass_ne_zero {n : ℕ} (hn : 2 ≤ n) : lowestClass hn ≠ 0 := by
  intro h0
  have hb := norm_sq_le_bergman (lowestClass hn) (mdifferentiable_lowestVec n)
    (MemLp.coeFn_toLp _) UpperHalfPlane.I
  rw [h0, norm_zero] at hb
  have hv : lowestVec n UpperHalfPlane.I ≠ 0 :=
    zpow_ne_zero _ (coe_add_I_ne_zero UpperHalfPlane.I)
  have : 0 < π / 9 * (UpperHalfPlane.I.im / 2) ^ n * ‖lowestVec n UpperHalfPlane.I‖ ^ 2 := by
    have := UpperHalfPlane.I.im_pos
    have := norm_pos_iff.2 hv
    positivity
  linarith

/-- **The Bergman space `A²_n` is nonzero** for `n ≥ 2`. -/
theorem holoSubmodule_ne_bot {n : ℕ} (hn : 2 ≤ n) : holoSubmodule n ≠ ⊥ := fun h =>
  lowestClass_ne_zero hn ((Submodule.eq_bot_iff _).1 h _ (lowestClass_mem hn))

end SL2R

end Lightlike.Lorentz
