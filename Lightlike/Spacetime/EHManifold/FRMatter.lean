import Lightlike.Spacetime.VariationCritical
import Lightlike.Spacetime.EHManifold.FRHessianForm

/-!
# The metric `f(R)` field equations with matter, on a coordinate patch

* `fRTensorUp g f x a b = f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R)`: the left side of
  the metric `f(R)` field equations, with raised indices;
* `fR_variation_tensor`: `d/dt|₀ ∫_T √|g_t| f(R_t) = -∫_T √|g| h_{ab} (fRTensorUp)^{ab}`;
* `symm_part_eq_zero_of_forall_integral`: the fundamental lemma for symmetric test tensors: if
  `∫ w h_{ab} E^{ab} = 0` for all smooth symmetric `h` of compact support, with `w > 0` and `E` continuous,
  then the symmetric part of `E` vanishes;
* `fR_matter_stationary_iff`: for a matter action `S_M` whose variation is
  `d/dt|₀ S_M(g + t h) = ½ ∫ √|g| h_{ab} T^{ab}` (this defines the energy-momentum tensor `T`), the total
  action `(1/2κ) ∫ √|g| f(R) + S_M` is stationary under all smooth symmetric perturbations of compact
  support iff the symmetric part of `fRTensorUp - κ T` vanishes: the field equations
  `f'(R) R_{μν} - ½ f(R) g_{μν} - [∇_μ ∇_ν - g_{μν} □] f'(R) = κ T_{μν}` with raised indices.

## References

* T. P. Sotiriou, V. Faraoni, *f(R) theories of gravity*, Rev. Mod. Phys. 82 (2010) 451,
  arXiv:0805.1726, section II.A, equations (5)–(7), p. 5.
-/

open Matrix Filter Topology MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The left side of the metric `f(R)` field equations with raised indices:
`f'(R) R^{ab} - ½ f(R) g^{ab} - ∇^a ∇^b f'(R) + g^{ab} □ f'(R)`. -/
def fRTensorUp (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (f : ℝ → ℝ) (x : Fin n → ℝ)
    (a b : Fin n) : ℝ :=
  deriv f (scalarCurvature g x) * ricciUp g x a b - (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ a b -
    (covHessUp g (fun y => deriv f (scalarCurvature g y)) a b x -
      (g x)⁻¹ a b * dalembertian g (fun y => deriv f (scalarCurvature g y)) x)

/-- A double sum `∑ H_{ab} E^{ab}` with `H` symmetric vanishes if the symmetric part of `E` vanishes. -/
lemma sum_symm_mul_eq_zero (H E : Fin n → Fin n → ℝ) (hH : ∀ a b, H a b = H b a)
    (hE : ∀ a b, E a b + E b a = 0) : ∑ α, ∑ β, H α β * E α β = 0 := by
  have e : ∑ α, ∑ β, H α β * E α β = ∑ α, ∑ β, H α β * E β α := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [hH α β]
  have h2 : (∑ α, ∑ β, H α β * E α β) + ∑ α, ∑ β, H α β * E β α = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [← mul_add, hE α β, mul_zero]
  rw [← e] at h2
  linarith

/-- **The fundamental lemma for symmetric test tensors.** -/
theorem symm_part_eq_zero_of_forall_integral (w : (Fin n → ℝ) → ℝ) (hw : Continuous w)
    (hwpos : ∀ x, 0 < w x) (E : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (hE : ∀ a b, Continuous fun x => E x a b)
    (hz : ∀ h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ, (∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) →
      (∀ y a b, h y a b = h y b a) → ∀ {T : Set (Fin n → ℝ)}, IsCompact T →
      (∀ a b, tsupport (fun y => h y a b) ⊆ T) →
      ∫ x in T, w x * ∑ α, ∑ β, h x α β * E x α β = 0) :
    ∀ x a b, E x a b + E x b a = 0 := by
  intro x a b
  set c : (Fin n → ℝ) → ℝ := fun y => E y a b + E y b a with hc
  set f : (Fin n → ℝ) → ℝ := fun y => w y * c y with hf
  have hcc : Continuous c := (hE a b).add (hE b a)
  have hfc : Continuous f := hw.mul hcc
  have hzero : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ x, φ x • f x = 0 := by
    intro φ hφ hφc
    set S : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.of fun i j => (if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0) with hS
    set h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun y => φ y • S with hh
    have hhd : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j) := by
      intro i j
      simp only [hh, Matrix.smul_apply, smul_eq_mul]
      exact hφ.mul contDiff_const
    have hhs : ∀ y i j, h y i j = h y j i := by
      intro y i j
      simp only [hh, hS, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      congr 1
      rw [add_comm]
      simp only [and_comm]
    have hsup : ∀ i j, tsupport (fun y => h y i j) ⊆ tsupport φ := by
      intro i j
      refine tsupport_smul_subset_left (fun y => φ y) (fun _ => S i j) |>.trans ?_
      exact subset_rfl
    have hint := hz h hhd hhs hφc hsup
    have hform : ∀ x, w x * ∑ α, ∑ β, h x α β * E x α β = φ x * f x := by
      intro x
      have hsum : ∑ α, ∑ β, h x α β * E x α β = φ x * c x := by
        simp only [hh, hS, hc, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
        simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq']
      rw [hsum, hf]
      ring
    simp only [hform] at hint
    have hsupp : ∀ x, x ∉ tsupport φ → φ x • f x = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    simpa using hint
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hfc.locallyIntegrable) hzero
  have hfz : ∀ x, f x = 0 := fun x => congrFun ((hfc.ae_eq_iff_eq volume continuous_const).1 hae) x
  have h0 := hfz x
  simp only [hf, hc] at h0
  exact (mul_eq_zero.1 h0).resolve_left (hwpos x).ne'

variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)

include hg hdet in
/-- The covariant Hessian of a `C²` function is continuous. -/
lemma continuous_covHessUp (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) (a b : Fin n) :
    Continuous (fun x => covHessUp g φ a b x) := by
  have hp : ∀ μ, Continuous fun x => pd μ φ x := fun μ => (contDiff_pd_one hφ μ).continuous
  have hpp : ∀ α β, Continuous fun x => pd α (fun y => pd β φ y) x := fun α β => by
    unfold pd
    exact ((contDiff_pd_one hφ β).continuous_fderiv (by simp)).clm_apply continuous_const
  unfold covHessUp
  exact continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
    (((contDiff_inv_entry g hg hdet a α).continuous.mul (contDiff_inv_entry g hg hdet b β).continuous)).mul
      ((hpp α β).sub (continuous_finsetSum _ fun μ _ =>
        (contDiff_christoffel g hg hdet μ α β).continuous.mul (hp μ)))

include hg hdet in
/-- The d'Alembertian of a `C²` function is continuous. -/
lemma continuous_dalembertian (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) :
    Continuous (fun x => dalembertian g φ x) := by
  have hp : ∀ μ, Continuous fun x => pd μ φ x := fun μ => (contDiff_pd_one hφ μ).continuous
  have hpp : ∀ α β, Continuous fun x => pd α (fun y => pd β φ y) x := fun α β => by
    unfold pd
    exact ((contDiff_pd_one hφ β).continuous_fderiv (by simp)).clm_apply continuous_const
  unfold dalembertian
  exact continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ =>
    (contDiff_inv_entry g hg hdet α β).continuous.mul
      ((hpp α β).sub (continuous_finsetSum _ fun μ _ =>
        (contDiff_christoffel g hg hdet μ α β).continuous.mul (hp μ)))

include hg in
/-- `√|g| h_{ab} E^{ab}` is continuous for continuous `h` and `E`. -/
lemma continuous_sqrt_det_mul_sum (H E : (Fin n → ℝ) → Fin n → Fin n → ℝ)
    (hH : ∀ a b, Continuous fun x => H x a b) (hE : ∀ a b, Continuous fun x => E x a b) :
    Continuous (fun x => √|(g x).det| * ∑ α, ∑ β, H x α β * E x α β) := by
  have hGc : Continuous g := continuous_matrix fun a b => (hg a b).continuous
  exact (Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det)).mul
    (continuous_finsetSum _ fun α _ => continuous_finsetSum _ fun β _ => (hH α β).mul (hE α β))

include hg hdet in
/-- The entries of the `f(R)` field-equation tensor are continuous. -/
lemma continuous_fRTensorUp (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f))
    (a b : Fin n) : Continuous (fun x => fRTensorUp g f x a b) := by
  have hRc : ContDiff ℝ ∞ (fun y => scalarCurvature g y) := contDiff_scalarCurvature g hg hdet
  have hφ : ContDiff ℝ 2 (fun y => deriv f (scalarCurvature g y)) := hf'.comp (hRc.of_le (by simp))
  have hG := (contDiff_inv_entry g hg hdet a b).continuous
  unfold fRTensorUp
  exact (((hφ.continuous).mul (contDiff_ricciUp g hg hdet a b).continuous).sub
    ((continuous_const.mul (hf.continuous.comp hRc.continuous)).mul hG)).sub
      ((continuous_covHessUp g hg hdet _ hφ a b).sub
        (hG.mul (continuous_dalembertian g hg hdet _ hφ)))

include hg hh hgs hhs hdet in
/-- **The first variation of the `f(R)` action with the field-equation tensor.** -/
theorem fR_variation_tensor (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f))
    {T : Set (Fin n → ℝ)} (hT : IsCompact T) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) :
    HasDerivAt (fun t : ℝ => ∫ x in T, fRDensity g h f t x)
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * fRTensorUp g f x α β) 0 := by
  have hmain := fR_field_equation_variation g h hg hh hgs hhs hdet f hf hf' hT hsupp
  have hRc : ContDiff ℝ ∞ (fun y => scalarCurvature g y) := contDiff_scalarCurvature g hg hdet
  have hφ : ContDiff ℝ 2 (fun y => deriv f (scalarCurvature g y)) := hf'.comp (hRc.of_le (by simp))
  have hhc : ∀ a b, Continuous fun x => h x a b := fun a b => (hh a b).continuous
  have hP : ∀ a b, Continuous fun x => deriv f (scalarCurvature g x) * ricciUp g x a b -
      (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ a b := fun a b =>
    ((hφ.continuous).mul (contDiff_ricciUp g hg hdet a b).continuous).sub
      ((continuous_const.mul (hf.continuous.comp hRc.continuous)).mul
        (contDiff_inv_entry g hg hdet a b).continuous)
  have hQ : ∀ a b, Continuous fun x => covHessUp g (fun y => deriv f (scalarCurvature g y)) a b x -
      (g x)⁻¹ a b * dalembertian g (fun y => deriv f (scalarCurvature g y)) x := fun a b =>
    (continuous_covHessUp g hg hdet _ hφ a b).sub
      ((contDiff_inv_entry g hg hdet a b).continuous.mul (continuous_dalembertian g hg hdet _ hφ))
  have iA := ((continuous_sqrt_det_mul_sum g hg (fun x a b => h x a b) _ hhc hP).continuousOn.integrableOn_compact
    hT : IntegrableOn _ T volume)
  have iB := ((continuous_sqrt_det_mul_sum g hg (fun x a b => h x a b) _ hhc hQ).continuousOn.integrableOn_compact
    hT : IntegrableOn _ T volume)
  have hval : (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * fRTensorUp g f x α β) =
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β)) +
        ∫ x in T, √|(g x).det| * ∑ a, ∑ b, h x a b *
          (covHessUp g (fun y => deriv f (scalarCurvature g y)) a b x -
            (g x)⁻¹ a b * dalembertian g (fun y => deriv f (scalarCurvature g y)) x) := by
    rw [neg_add_eq_sub, ← neg_sub, ← integral_sub iA iB]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show √|(g x).det| * ∑ α, ∑ β, h x α β * fRTensorUp g f x α β =
      √|(g x).det| * (∑ α, ∑ β, h x α β *
          (deriv f (scalarCurvature g x) * ricciUp g x α β -
            (1 / 2) * f (scalarCurvature g x) * (g x)⁻¹ α β)) -
        √|(g x).det| * ∑ α, ∑ β, h x α β *
          (covHessUp g (fun y => deriv f (scalarCurvature g y)) α β x -
            (g x)⁻¹ α β * dalembertian g (fun y => deriv f (scalarCurvature g y)) x)
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold fRTensorUp
    ring
  rw [hval]
  exact hmain

include hg hgs hdet in
/-- **The metric `f(R)` field equations with matter.** The total action `(1/2κ) ∫ √|g| f(R) + S_M` is
stationary under all smooth symmetric perturbations of compact support iff the symmetric part of
`fRTensorUp - κ T` vanishes, where `T` is defined by `d/dt|₀ S_M(g + t h) = ½ ∫ √|g| h_{ab} T^{ab}`. -/
theorem fR_matter_stationary_iff (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hf' : ContDiff ℝ 2 (deriv f))
    (κ : ℝ) (hκ : κ ≠ 0) (SM : ((Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) → ℝ)
    (Tm : (Fin n → ℝ) → Fin n → Fin n → ℝ) (hTm : ∀ a b, Continuous fun x => Tm x a b)
    (hM : ∀ h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ, (∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) →
      (∀ y a b, h y a b = h y b a) → ∀ {T : Set (Fin n → ℝ)}, IsCompact T →
      (∀ a b, tsupport (fun y => h y a b) ⊆ T) →
      HasDerivAt (fun t : ℝ => SM (fun z => g z + t • h z))
        ((1 / 2) * ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * Tm x α β) 0) :
    (∀ h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ, (∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) →
      (∀ y a b, h y a b = h y b a) → ∀ {T : Set (Fin n → ℝ)}, IsCompact T →
      (∀ a b, tsupport (fun y => h y a b) ⊆ T) →
      HasDerivAt (fun t : ℝ => (1 / (2 * κ)) * (∫ x in T, fRDensity g h f t x) +
        SM (fun z => g z + t • h z)) 0 0) ↔
    ∀ x a b, fRTensorUp g f x a b + fRTensorUp g f x b a = κ * (Tm x a b + Tm x b a) := by
  have hEc : ∀ a b, Continuous fun x => fRTensorUp g f x a b := fun a b =>
    continuous_fRTensorUp g hg hdet f hf hf' a b
  have hDc : ∀ a b, Continuous fun x => fRTensorUp g f x a b - κ * Tm x a b := fun a b =>
    (hEc a b).sub (continuous_const.mul (hTm a b))
  -- the derivative of the total action
  have htot : ∀ h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ, (∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) →
      (∀ y a b, h y a b = h y b a) → ∀ {T : Set (Fin n → ℝ)}, IsCompact T →
      (∀ a b, tsupport (fun y => h y a b) ⊆ T) →
      HasDerivAt (fun t : ℝ => (1 / (2 * κ)) * (∫ x in T, fRDensity g h f t x) +
        SM (fun z => g z + t • h z))
        (-(1 / (2 * κ)) * ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (fRTensorUp g f x α β - κ * Tm x α β)) 0 := by
    intro h hh hhs T hT hsupp
    have hhc : ∀ a b, Continuous fun x => h x a b := fun a b => (hh a b).continuous
    have iE := ((continuous_sqrt_det_mul_sum g hg (fun x a b => h x a b) _ hhc hEc).continuousOn.integrableOn_compact
      hT : IntegrableOn _ T volume)
    have iT := ((continuous_sqrt_det_mul_sum g hg (fun x a b => h x a b) _ hhc hTm).continuousOn.integrableOn_compact
      hT : IntegrableOn _ T volume)
    have hI : ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * (fRTensorUp g f x α β - κ * Tm x α β) =
        (∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * fRTensorUp g f x α β) -
          κ * ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * Tm x α β := by
      rw [← integral_const_mul, ← integral_sub iE (iT.const_mul κ)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have e : ∑ α, ∑ β, h x α β * (fRTensorUp g f x α β - κ * Tm x α β) =
          (∑ α, ∑ β, h x α β * fRTensorUp g f x α β) - κ * ∑ α, ∑ β, h x α β * Tm x α β := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun β _ => by ring
      show √|(g x).det| * ∑ α, ∑ β, h x α β * (fRTensorUp g f x α β - κ * Tm x α β) =
        √|(g x).det| * (∑ α, ∑ β, h x α β * fRTensorUp g f x α β) -
          κ * (√|(g x).det| * ∑ α, ∑ β, h x α β * Tm x α β)
      rw [e]
      ring
    have h1 := ((fR_variation_tensor g h hg hh hgs hhs hdet f hf hf' hT hsupp).const_mul
      (1 / (2 * κ))).add (hM h hh hhs hT hsupp)
    refine h1.congr_deriv ?_
    rw [hI]
    field_simp
    ring
  constructor
  · intro hstat
    have hz : ∀ h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ, (∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) →
        (∀ y a b, h y a b = h y b a) → ∀ {T : Set (Fin n → ℝ)}, IsCompact T →
        (∀ a b, tsupport (fun y => h y a b) ⊆ T) →
        ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β * (fRTensorUp g f x α β - κ * Tm x α β) = 0 := by
      intro h hh hhs T hT hsupp
      have hu := (htot h hh hhs hT hsupp).unique (hstat h hh hhs hT hsupp)
      have hne : -(1 / (2 * κ)) ≠ 0 := by
        rw [neg_ne_zero]
        exact one_div_ne_zero (mul_ne_zero two_ne_zero hκ)
      exact (mul_eq_zero.1 hu).resolve_left hne
    have hGc : Continuous g := continuous_matrix fun a b => (hg a b).continuous
    have key := symm_part_eq_zero_of_forall_integral (fun x => √|(g x).det|)
      (Real.continuous_sqrt.comp (continuous_abs.comp hGc.matrix_det))
      (fun x => Real.sqrt_pos.2 (abs_pos.2 (hdet x)))
      (fun x a b => fRTensorUp g f x a b - κ * Tm x a b) hDc hz
    intro x a b
    have hk := key x a b
    linarith
  · intro hfe h hh hhs T hT hsupp
    have h0 : ∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
        (fRTensorUp g f x α β - κ * Tm x α β) = 0 := by
      have hpt : ∀ x, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (fRTensorUp g f x α β - κ * Tm x α β) = 0 := by
        intro x
        rw [sum_symm_mul_eq_zero (fun a b => h x a b)
          (fun a b => fRTensorUp g f x a b - κ * Tm x a b) (hhs x)
          (fun a b => by have := hfe x a b; linarith), mul_zero]
      simp only [hpt, integral_zero]
    have h1 := htot h hh hhs hT hsupp
    rw [h0, mul_zero] at h1
    exact h1

end Lightlike
