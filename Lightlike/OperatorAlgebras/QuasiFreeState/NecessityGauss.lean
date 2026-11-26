import Lightlike.OperatorAlgebras.QuasiFreeState.NecessityState
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian mixtures of translated quasi-free functionals

For a covariance `η'` and a functional `ρ`, the functions
`κ_h(x) = exp(-¼ η'(x,x)) ∫ h(t) e^{i t ρ(x)} dγ(t)`, with `γ` a centred Gaussian measure and `h` a measurable function
`0 ≤ h ≤ 2`, have positive semidefinite kernels `kernelOf ω κ_h` (`posSemidef_kernelOf_gauss`): the kernel is the
`h γ`-mean of the conjugates of the kernel of `η'` by the diagonal phases `e^{i t ρ(x)}`. For `h = 1` the function is
`exp(-¼ η(x,x))` with `η = η' + 2 Var(γ) ρ ⊗ ρ`.
-/

open scoped InnerProductSpace ComplexConjugate ComplexOrder

open MeasureTheory ProbabilityTheory

universe u

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

variable {V : Type u} [AddCommGroup V] [Module ℝ V] {ω η' : LinearMap.BilinForm ℝ V}

/-- The phase `e^{i t ρ(x)}`. -/
noncomputable def gphase (ρ : V →ₗ[ℝ] ℝ) (t : ℝ) (x : V) : ℂ := Complex.exp (Complex.I * (t : ℂ) * (ρ x : ℂ))

lemma norm_gphase (ρ : V →ₗ[ℝ] ℝ) (t : ℝ) (x : V) : ‖gphase ρ t x‖ = 1 := by
  unfold gphase
  rw [show Complex.I * (t : ℂ) * (ρ x : ℂ) = ((t * ρ x : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma gphase_sub (ρ : V →ₗ[ℝ] ℝ) (t : ℝ) (φ ψ : V) :
    gphase ρ t (ψ - φ) = conj (gphase ρ t φ) * gphase ρ t ψ := by
  unfold gphase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **The Gaussian family**: `κ_h(x) = exp(-¼ η'(x,x)) ∫ h(t) e^{i t ρ(x)} dγ(t)`. -/
noncomputable def gaussFamily (η' : LinearMap.BilinForm ℝ V) (ρ : V →ₗ[ℝ] ℝ) (γ : Measure ℝ) (h : ℝ → ℝ) (x : V) : ℂ :=
  ((gaussVal η' x : ℝ) : ℂ) * ∫ t, ((h t : ℝ) : ℂ) * gphase ρ t x ∂γ

section

variable (ρ : V →ₗ[ℝ] ℝ) (γ : Measure ℝ) [IsProbabilityMeasure γ] {h : ℝ → ℝ}

lemma integrable_gphase (hm : Measurable h) (hb : ∀ t, |h t| ≤ 2) (a : V) :
    Integrable (fun t => ((h t : ℝ) : ℂ) * gphase ρ t a) γ := by
  refine Integrable.mono' (g := fun _ => (2 : ℝ)) (integrable_const 2) ?_ (ae_of_all _ fun t => ?_)
  · have : Measurable fun t => gphase ρ t a := by unfold gphase; fun_prop
    exact (Complex.measurable_ofReal.comp hm |>.mul this).aestronglyMeasurable
  · rw [norm_mul, norm_gphase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hb t

end


section Entry

variable {ρ : V →ₗ[ℝ] ℝ} {γ : Measure ℝ} {h : ℝ → ℝ}

/-- **The kernel of the Gaussian family as an `h γ`-mean of phase-conjugated kernels of `η'`.** -/
lemma kernelOf_gauss_entry (φ ψ : V) :
    kernelOf ω (gaussFamily η' ρ γ h) φ ψ =
      ∫ t, ((h t : ℝ) : ℂ) * (conj (gphase ρ t φ) * qfKer ω η' φ ψ * gphase ρ t ψ) ∂γ := by
  have e1 : ∀ t : ℝ, ((h t : ℝ) : ℂ) * (conj (gphase ρ t φ) * qfKer ω η' φ ψ * gphase ρ t ψ) =
      qfKer ω η' φ ψ * (((h t : ℝ) : ℂ) * gphase ρ t (ψ - φ)) := fun t => by
    rw [gphase_sub]; ring
  simp only [e1]
  rw [integral_const_mul]
  simp only [kernelOf, gaussFamily, Matrix.of_apply, qfKer, gaussVal]
  ring

end Entry


lemma integral_complex_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : ∀ t, 0 ≤ f t) : 0 ≤ ∫ t, f t ∂μ := by
  have h1 : f = fun t => (((f t).re : ℝ) : ℂ) := by
    funext t
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 (hf t)
    apply Complex.ext <;> simp [← h2]
  have h2 : ∫ t, f t ∂μ = ∫ t, (((f t).re : ℝ) : ℂ) ∂μ := by
    congr 1
  rw [h2, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun t => (Complex.nonneg_iff.1 (hf t)).1)

section Psd

variable {ρ : V →ₗ[ℝ] ℝ} {γ : Measure ℝ} [IsProbabilityMeasure γ] {h : ℝ → ℝ}

/-- **The kernel of the Gaussian family is positive semidefinite**: it is the `h γ`-mean of the kernel of `η'` conjugated
by the diagonal phases. -/
theorem posSemidef_kernelOf_gauss (hω : ∀ a b, ω a b = -ω b a) (hη' : IsCovariance ω η')
    (hm : Measurable h) (h0 : ∀ t, 0 ≤ h t) (h2 : ∀ t, h t ≤ 2) :
    (kernelOf ω (gaussFamily η' ρ γ h)).PosSemidef := by
  have hb : ∀ t, |h t| ≤ 2 := fun t => by rw [abs_of_nonneg (h0 t)]; exact h2 t
  have hQ := posSemidef_qfKer hω hη'
  have hint : ∀ φ ψ : V, Integrable (fun t => ((h t : ℝ) : ℂ) *
      (conj (gphase ρ t φ) * qfKer ω η' φ ψ * gphase ρ t ψ)) γ := fun φ ψ => by
    have e1 : (fun t => ((h t : ℝ) : ℂ) * (conj (gphase ρ t φ) * qfKer ω η' φ ψ * gphase ρ t ψ)) =
        fun t => qfKer ω η' φ ψ * (((h t : ℝ) : ℂ) * gphase ρ t (ψ - φ)) := funext fun t => by
      rw [gphase_sub]; ring
    rw [e1]
    exact (integrable_gphase ρ γ hm hb (ψ - φ)).const_mul _
  refine ⟨Matrix.IsHermitian.ext fun φ ψ => ?_, fun c => ?_⟩
  · rw [kernelOf_gauss_entry, kernelOf_gauss_entry, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    have hqh : conj (qfKer ω η' ψ φ) = qfKer ω η' φ ψ := by
      have := hQ.1
      have h3 := congrFun (congrFun this φ) ψ
      simpa [Matrix.conjTranspose_apply] using h3
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hqh]
    ring
  · have hmeas : ∀ t, 0 ≤ ((h t : ℝ) : ℂ) := fun t => Complex.zero_le_real.2 (h0 t)
    -- the integrand for a fixed `t` is `h t` times the quadratic form of `qfKer ω η'` at the phased coefficients
    have hpt : ∀ t : ℝ, 0 ≤ ∑ φ ∈ c.support, ∑ ψ ∈ c.support,
        star (c φ) * (((h t : ℝ) : ℂ) * (conj (gphase ρ t φ) * qfKer ω η' φ ψ * gphase ρ t ψ)) * c ψ := fun t => by
      set ct : V →₀ ℂ := Finsupp.onFinset c.support (fun φ => c φ * gphase ρ t φ) (fun φ hφ => by
        by_contra hn; apply hφ; rw [Finsupp.notMem_support_iff.1 hn]; simp) with hct
      have hsub : ct.support ⊆ c.support := Finsupp.support_onFinset_subset
      have hQt0 := hQ.2 ct
      have hQt : 0 ≤ ∑ φ ∈ c.support, ∑ ψ ∈ c.support, star (ct φ) * qfKer ω η' φ ψ * ct ψ := by
        have e1 : (ct.sum fun φ a => ct.sum fun ψ b => star a * qfKer ω η' φ ψ * b) =
            ∑ φ ∈ c.support, ∑ ψ ∈ c.support, star (ct φ) * qfKer ω η' φ ψ * ct ψ := by
          rw [Finsupp.sum_of_support_subset ct hsub _ (fun i _ => by simp)]
          refine Finset.sum_congr rfl fun φ _ => ?_
          rw [Finsupp.sum_of_support_subset ct hsub _ (fun i _ => by simp)]
        rw [← e1]; exact hQt0
      have e : ∑ φ ∈ c.support, ∑ ψ ∈ c.support,
          star (c φ) * (((h t : ℝ) : ℂ) * (conj (gphase ρ t φ) * qfKer ω η' φ ψ * gphase ρ t ψ)) * c ψ =
          ((h t : ℝ) : ℂ) * ∑ φ ∈ c.support, ∑ ψ ∈ c.support,
            star (ct φ) * qfKer ω η' φ ψ * ct ψ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun φ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        simp only [hct, Finsupp.onFinset_apply, star_mul', Complex.star_def]
        ring
      rw [e]
      exact mul_nonneg (hmeas t) hQt
    have hsum : (c.sum fun φ a => c.sum fun ψ b => star a * kernelOf ω (gaussFamily η' ρ γ h) φ ψ * b) =
        ∫ t, ∑ φ ∈ c.support, ∑ ψ ∈ c.support,
          star (c φ) * (((h t : ℝ) : ℂ) * (conj (gphase ρ t φ) * qfKer ω η' φ ψ * gphase ρ t ψ)) * c ψ ∂γ := by
      rw [integral_finsetSum _ (fun φ _ => integrable_finsetSum _ (fun ψ _ => ?_))]
      · simp only [Finsupp.sum]
        refine Finset.sum_congr rfl fun φ _ => ?_
        rw [integral_finsetSum _ (fun ψ _ => ?_)]
        · refine Finset.sum_congr rfl fun ψ _ => ?_
          rw [kernelOf_gauss_entry, ← integral_const_mul, ← integral_mul_const]
        · exact ((hint φ ψ).const_mul (star (c φ))).mul_const (c ψ)
      · exact ((hint φ ψ).const_mul (star (c φ))).mul_const (c ψ)
    rw [hsum]
    exact integral_complex_nonneg hpt

end Psd


lemma integral_exp_gaussian (v : NNReal) (u : ℝ) :
    ∫ t, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂(gaussianReal 0 v) =
      Complex.exp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  have h := charFun_gaussianReal (μ := 0) (v := v) u
  simp only [charFun, RCLike.inner_apply, conj_trivial] at h
  have e : ∀ t : ℝ, Complex.exp (↑(u * t) * Complex.I) = Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) := fun t => by
    congr 1; push_cast; ring
  simp only [e] at h
  rw [h]
  congr 1
  push_cast
  ring

/-- **The Gaussian family at `h = 1` is the quasi-free Gaussian of `η = η' + ε ρ ⊗ ρ`.** -/
lemma gaussFamily_one {ρ : V →ₗ[ℝ] ℝ} {η : LinearMap.BilinForm ℝ V} {ε : ℝ} (hε : 0 < ε)
    (hη : ∀ x, η x x = η' x x + ε * ρ x ^ 2) (x : V) :
    gaussFamily η' ρ (gaussianReal 0 (ε / 2).toNNReal) (fun _ => 1) x = ((gaussVal η x : ℝ) : ℂ) := by
  have hv : (((ε / 2).toNNReal : NNReal) : ℝ) = ε / 2 := Real.coe_toNNReal _ (by positivity)
  unfold gaussFamily gphase
  simp only [Complex.ofReal_one, one_mul]
  rw [integral_exp_gaussian, hv]
  unfold gaussVal
  rw [hη x]
  have e1 : Real.exp (-((η' x x + ε * ρ x ^ 2) / 4)) =
      Real.exp (-(η' x x / 4)) * Real.exp (-(ε * ρ x ^ 2 / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Complex.exp (-((ε / 2 : ℝ) : ℂ) * (ρ x : ℂ) ^ 2 / 2) = ((Real.exp (-(ε * ρ x ^ 2 / 4)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [e1, Complex.ofReal_mul, e2]


section Analysis

open Complex in
/-- **The half-line density is not the Gaussian**: their characteristic functions differ somewhere. -/
lemma not_charFun_eq (v : NNReal) (hv : v ≠ 0) :
    ¬ ∀ u : ℝ, ∫ t, (((Set.Ioi (0 : ℝ)).indicator (fun _ => (2 : ℝ)) t : ℝ) : ℂ) *
        Complex.exp (Complex.I * t * u) ∂(gaussianReal 0 v) =
      ∫ t, Complex.exp (Complex.I * t * u) ∂(gaussianReal 0 v) := by
  intro h
  set γ := gaussianReal 0 v with hγ
  set μ : Measure ℝ := (2 : NNReal) • γ.restrict (Set.Ioi 0) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; infer_instance
  have hchar : charFun μ = charFun γ := by
    funext u
    have h1 := h u
    simp only [charFun, hμ]
    rw [integral_smul_nnreal_measure]
    have e1 : ∀ t : ℝ, Complex.exp (↑(inner ℝ t u) * Complex.I) = Complex.exp (Complex.I * t * u) := fun t => by
      congr 1
      simp [RCLike.inner_apply]
      ring
    simp only [e1]
    have h3 : (fun t : ℝ => (((Set.Ioi (0 : ℝ)).indicator (fun _ => (2 : ℝ)) t : ℝ) : ℂ) *
        Complex.exp (Complex.I * t * u)) = (Set.Ioi (0 : ℝ)).indicator (fun t => 2 * Complex.exp (Complex.I * t * u)) := by
      funext t
      by_cases ht : t ∈ Set.Ioi (0 : ℝ) <;> simp [Set.indicator, ht]
    rw [h3, integral_indicator measurableSet_Ioi, integral_const_mul] at h1
    rw [← h1]
    rw [NNReal.smul_def, Complex.real_smul]
    norm_num
  have := Measure.ext_of_charFun hchar
  have h2 : μ (Set.Iio 0) = γ (Set.Iio 0) := by rw [this]
  have h3 : μ (Set.Iio 0) = 0 := by
    have hempty : Set.Iio (0 : ℝ) ∩ Set.Ioi 0 = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2; linarith
    simp [hμ, Measure.smul_apply, Measure.restrict_apply measurableSet_Iio, hempty]
  have h4 : γ (Set.Iio 0) ≠ 0 := by
    intro h0
    have := (gaussianReal_absolutelyContinuous' 0 hv) h0
    simp at this
  exact h4 (h2 ▸ h3)

/-- A centred Gaussian puts mass `1/2` on the positive half line. -/
lemma gaussian_Ioi_half (v : NNReal) (hv : v ≠ 0) : (gaussianReal 0 v) (Set.Ioi 0) = 1 / 2 := by
  have hneg : (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
    have := gaussianReal_map_neg (μ := 0) (v := v)
    simpa using this
  have h1 : (gaussianReal 0 v) (Set.Ioi 0) = (gaussianReal 0 v) (Set.Iio 0) := by
    conv_rhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x; simp
  have hns : NullSingletonClass (gaussianReal 0 v) := ⟨fun x => by
    have := (gaussianReal_absolutelyContinuous 0 hv) (show (volume : Measure ℝ) {x} = 0 by simp)
    exact this⟩
  have h2 : (gaussianReal 0 v) (Set.Ici 0) = (gaussianReal 0 v) (Set.Ioi 0) :=
    measure_congr Ioi_ae_eq_Ici.symm
  have htot := prob_add_prob_compl (μ := gaussianReal 0 v) (measurableSet_Iio (a := (0 : ℝ)))
  rw [Set.compl_Iio, h2, ← h1] at htot
  have h3 : (2 : ENNReal) * (gaussianReal 0 v) (Set.Ioi 0) = 1 := by
    rw [two_mul]; exact htot
  rw [one_div]
  exact (ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h3))

end Analysis

end Lightlike.OperatorAlgebras.QuasiFreeState
