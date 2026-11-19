import Lightlike.OperatorAlgebras.MomentumTheta
import Physlib.QuantumMechanics.Operators.SpectralTheory.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The spectrum of the self-adjoint extensions of the momentum on `L²(0, 1)`

Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Section 5.3, p. 8 (read): "the spectra are purely discrete", and eq. (15):
`P_θ φ_n = (2πħ/L) ν φ_n`, `ν = n + θ/2π`, `φ_n(x) = L^{-1/2} e^{2iπνx/L}`, `(φ_m, φ_n) = δ_mn`. Here `ħ = 1`, `L = 1`, and the eigenvalue
`2πν` is written `θ + 2πn`: the plane waves `e^{i(θ + 2πn)x}` lie in `D_θ` and are eigenvectors (`momentumTheta_planeWave`), they are
orthonormal (`orthonormal_planeWave`), there are no other eigenvalues (`eigenvalue_momentumTheta`) and the eigenspaces are one-dimensional
(`eigenvector_momentumTheta`). Off `θ + 2πℤ` the resolvent equation `P_θ y - z y = f` is solved explicitly (`exists_momentumTheta_sub_eq`), so
the spectrum of `P_θ`, in Physlib's sense (`LinearPMap.spectrum`), is `θ + 2πℤ` (`spectrum_momentumTheta`) and equals the point spectrum
(`pointSpectrum_momentumTheta`).
-/

open MeasureTheory Set intervalIntegral
open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

/-- The plane wave `x ↦ e^{i k x}` as a vector of `L²(0, 1)`. -/
noncomputable def planeWave (k : ℝ) : L2I :=
  (MemLp.of_bound (f := fun x : ℝ => Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) (C := 1)
    ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun x => (Complex.norm_exp_ofReal_mul_I (k * x)).le)).toLp (fun x : ℝ => Complex.exp (((k * x : ℝ) : ℂ) * Complex.I))

lemma planeWave_ae (k : ℝ) :
    (planeWave k : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)]
      fun x => Complex.exp (((k * x : ℝ) : ℂ) * Complex.I) :=
  MemLp.coeFn_toLp _

lemma hasDerivAt_planeWave (k x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (((k * x : ℝ) : ℂ) * Complex.I))
      (Complex.I * k * Complex.exp (((k * x : ℝ) : ℂ) * Complex.I)) x := by
  have h1 : HasDerivAt (fun x : ℝ => ((k * x : ℝ) : ℂ) * Complex.I) (k * Complex.I) x := by
    have := ((hasDerivAt_id x).const_mul k).ofReal_comp.mul_const Complex.I
    simpa using this
  convert (h1.cexp) using 1
  ring

/-- `e^{ikx} = 1 + ∫₀ˣ i k e^{ikt}`, almost everywhere on `(0, 1)`. -/
lemma planeWave_primitive (k : ℝ) :
    ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      planeWave k x = 1 + ∫ t in (0 : ℝ)..x, ((Complex.I * k) • planeWave k : L2I) t := by
  have hsm := Lp.coeFn_smul (Complex.I * k) (planeWave k)
  filter_upwards [planeWave_ae k, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [hx]
  have hcongr : ∫ t in (0 : ℝ)..x, ((Complex.I * k) • planeWave k : L2I) t =
      ∫ t in (0 : ℝ)..x, Complex.I * k * Complex.exp (((k * t : ℝ) : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo hsm ⟨hxI.1.le, hxI.2.le⟩, ae_uIoc_of_ae_Ioo (planeWave_ae k) ⟨hxI.1.le, hxI.2.le⟩]
      with t h1 h2 htI
    rw [h1 htI, Pi.smul_apply, h2 htI, smul_eq_mul]
  have hc : Continuous fun t : ℝ => Complex.I * k * Complex.exp (((k * t : ℝ) : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)).mul continuous_const))
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_planeWave k t) (hc.intervalIntegrable _ _)]
  simp

lemma planeWave_mem (k : ℝ) : planeWave k ∈ (momentumMin†).domain :=
  (mem_adjoint_of_primitive _ _ 1 (planeWave_primitive k)).1

/-- **The plane waves are eigenvectors of `A†`**: `A† e^{ikx} = k e^{ikx}`. -/
lemma adjoint_planeWave (k : ℝ) : momentumMin† ⟨planeWave k, planeWave_mem k⟩ = (k : ℂ) • planeWave k := by
  obtain ⟨h, hA⟩ := mem_adjoint_of_primitive _ _ 1 (planeWave_primitive k)
  rw [show (⟨planeWave k, planeWave_mem k⟩ : (momentumMin†).domain) = ⟨planeWave k, h⟩ from rfl, hA, smul_smul]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The boundary values of the plane wave: `e(0) = 1`, `e(1) = e^{ik}`. -/
lemma bv_planeWave (k : ℝ) :
    bv0 ⟨planeWave k, planeWave_mem k⟩ = 1 ∧ bv1 ⟨planeWave k, planeWave_mem k⟩ = Complex.exp ((k : ℂ) * Complex.I) := by
  obtain ⟨h0, h1⟩ := bv_of_primitive _ _ 1 (planeWave_primitive k) (planeWave_mem k)
  refine ⟨h0, ?_⟩
  rw [h1]
  have h := (planeWave_primitive k)
  have hcongr : ∫ t in (0 : ℝ)..1, ((Complex.I * k) • planeWave k : L2I) t =
      ∫ t in (0 : ℝ)..1, Complex.I * k * Complex.exp (((k * t : ℝ) : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo (Lp.coeFn_smul (Complex.I * k) (planeWave k)) ⟨zero_le_one, le_rfl⟩,
      ae_uIoc_of_ae_Ioo (planeWave_ae k) ⟨zero_le_one, le_rfl⟩] with t h1 h2 htI
    rw [h1 htI, Pi.smul_apply, h2 htI, smul_eq_mul]
  have hc : Continuous fun t : ℝ => Complex.I * k * Complex.exp (((k * t : ℝ) : ℂ) * Complex.I) :=
    continuous_const.mul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)).mul continuous_const))
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_planeWave k t) (hc.intervalIntegrable _ _)]
  simp

/-- **The eigenvectors of `P_θ`** (Bonneau-Faraut-Valent, Section 5.3, eq. (15), the eigenvalues, one direction): for every integer `n`,
`e^{i (θ + 2πn) x}` lies in `D_θ` and is an eigenvector of `P_θ` with eigenvalue `θ + 2πn`. -/
theorem momentumTheta_planeWave (θ : ℝ) (n : ℤ) :
    ∃ h : planeWave (θ + 2 * Real.pi * n) ∈ (momentumTheta θ).domain,
      momentumTheta θ ⟨_, h⟩ = ((θ + 2 * Real.pi * n : ℝ) : ℂ) • planeWave (θ + 2 * Real.pi * n) := by
  set k : ℝ := θ + 2 * Real.pi * n with hk
  have hmem : planeWave k ∈ domTheta θ := by
    refine mem_domTheta.mpr ⟨planeWave_mem k, ?_⟩
    obtain ⟨h0, h1⟩ := bv_planeWave k
    rw [h0, h1, mul_one, hk]
    push_cast
    rw [add_mul, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * n * Complex.I) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨n, by ring⟩
    rw [this, mul_one]
  refine ⟨by rw [momentumTheta_domain]; exact hmem, ?_⟩
  rw [momentumTheta_apply]
  exact adjoint_planeWave k

lemma planeWave_ne_zero (k : ℝ) : planeWave k ≠ 0 := by
  intro h
  obtain ⟨h0, -⟩ := bv_planeWave k
  have hz : (⟨planeWave k, planeWave_mem k⟩ : (momentumMin†).domain) = 0 := Subtype.ext h
  have : bv0 (0 : (momentumMin†).domain) = 0 := map_zero bv0L
  rw [← hz] at this
  rw [this] at h0
  exact zero_ne_one h0

lemma ae_ne_zero_one : ∀ᵐ x : ℝ, x ≠ 0 ∧ x ≠ 1 := by
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by rw [ae_iff]; simp
  have h1 : ∀ᵐ x : ℝ, x ≠ 1 := by rw [ae_iff]; simp
  exact h0.and h1

lemma mem_Ioo_of_mem_uIcc {x : ℝ} (hx : x ∈ uIcc (0 : ℝ) 1) (h0 : x ≠ 0) (h1 : x ≠ 1) : x ∈ Ioo (0 : ℝ) 1 := by
  rw [uIcc_of_le zero_le_one] at hx
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm h0), lt_of_le_of_ne hx.2 h1⟩

/-- **An eigenvector of `A†` is an exponential**: if `A† y = μ y`, the continuous representative of `y` is `y(0) e^{iμx}` on `[0, 1]`. Its
representative `f` solves `f = f(0) + ∫₀ˣ i μ f`, so `e^{-iμx} f(x)` is absolutely continuous with derivative zero almost everywhere. -/
theorem bvRep_eigen {μ : ℂ} (y : (momentumMin†).domain) (hA : (momentumMin† y : L2I) = μ • (y : L2I)) :
    ∀ x ∈ Icc (0 : ℝ) 1, bvRep y x = bv0 y * Complex.exp (Complex.I * μ * x) := by
  set f : ℝ → ℂ := bvRep y with hf
  set c : ℂ := bvConst y
  set g : ℝ → ℂ := fun t => Complex.I * μ * f t with hg
  have hfc : ContinuousOn f (Icc 0 1) := continuousOn_rep y
  have hgi : IntervalIntegrable g volume 0 1 :=
    (continuousOn_const.mul hfc).intervalIntegrable_of_Icc zero_le_one
  have hrep : ∀ x ∈ Icc (0 : ℝ) 1, f x = c + ∫ t in (0 : ℝ)..x, g t := by
    intro x hx
    show bvConst y + ∫ t in (0 : ℝ)..x, Complex.I * (momentumMin† y : L2I) t = _
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo (Lp.coeFn_smul μ (y : L2I)) hx, ae_uIoc_of_ae_Ioo (rep_ae y) hx] with t h1 h2 htI
    rw [hA, h1 htI, Pi.smul_apply, smul_eq_mul, h2 htI, hg]
    ring
  set E : ℝ → ℂ := fun x => Complex.exp (-(Complex.I * μ) * (x : ℂ)) with hE
  have hEd : ∀ x, HasDerivAt E (-(Complex.I * μ) * E x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(Complex.I * μ) * (x : ℂ)) (-(Complex.I * μ)) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-(Complex.I * μ))
    convert h1.cexp using 1
    ring
  have hEac : AbsolutelyContinuousOnInterval E 0 1 :=
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp : ContDiff ℝ 1 E).contDiffOn.absolutelyContinuousOnInterval
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
    (contDiff_const (c := c)).contDiffOn.absolutelyContinuousOnInterval
  have hfac : AbsolutelyContinuousOnInterval f 0 1 :=
    (hconst.add (ac_primitive hgi)).congr fun x hx =>
      (hrep x (by rwa [uIcc_of_le zero_le_one] at hx)).symm
  have hder : ∀ᵐ x, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt (E • f) 0 x := by
    filter_upwards [hgi.ae_hasDerivAt_integral, ae_ne_zero_one] with x hx hx01 hxI
    have hxo := mem_Ioo_of_mem_uIcc hxI hx01.1 hx01.2
    have hP := (hx hxI 0 left_mem_uIcc).const_add c
    have hfx : HasDerivAt f (g x) x :=
      hP.congr_of_eventuallyEq (Filter.eventually_of_mem (Ioo_mem_nhds hxo.1 hxo.2) fun z hz =>
        hrep z ⟨hz.1.le, hz.2.le⟩)
    have := (hEd x).smul hfx
    convert this using 1
    simp only [hg, smul_eq_mul]
    ring
  obtain ⟨C, hC⟩ := (hEac.smul hfac).const_of_ae_hasDerivAt_zero hder
  have e0 := hC 0 left_mem_uIcc
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hE, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_mul] at e0
  intro x hx
  have ex := hC x (by rw [uIcc_of_le zero_le_one]; exact hx)
  simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, hE] at ex
  have hf0 : f 0 = bv0 y := rfl
  rw [← e0, hf0] at ex
  have hinv : Complex.exp (Complex.I * μ * x) * Complex.exp (-(Complex.I * μ) * x) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  calc f x = Complex.exp (Complex.I * μ * x) * Complex.exp (-(Complex.I * μ) * x) * f x := by rw [hinv, one_mul]
    _ = bv0 y * Complex.exp (Complex.I * μ * x) := by rw [mul_assoc, ex]; exact mul_comm _ _

/-- A vector of `D(A†)` whose representative vanishes on `(0, 1)` is zero. -/
lemma eq_zero_of_bvRep (y : (momentumMin†).domain) (h : ∀ x ∈ Ioo (0 : ℝ) 1, bvRep y x = 0) : (y : L2I) = 0 := by
  refine (Lp.eq_zero_iff_ae_eq_zero).mpr ?_
  filter_upwards [rep_ae y, ae_restrict_mem measurableSet_Ioo] with x hx hxI
  rw [hx, h x hxI]
  rfl

/-- **The eigenvalues of `P_θ` are the `θ + 2πn`** (Bonneau-Faraut-Valent, Section 5.3, eq. (15), with `ħ = 1`, `L = 1`, the eigenvalue
`2πν = θ + 2πn`): an eigenvector of `P_θ` with eigenvalue `μ ∈ ℂ` forces `μ = θ + 2πn` for an integer `n`, by `bvRep_eigen` and the boundary
condition `y(1) = e^{iθ} y(0)`. -/
theorem eigenvalue_momentumTheta {θ : ℝ} {μ : ℂ} (y : (momentumTheta θ).domain) (hy : (y : L2I) ≠ 0)
    (hμ : momentumTheta θ y = μ • (y : L2I)) : ∃ n : ℤ, μ = θ + 2 * Real.pi * n := by
  have hyθ : (y : L2I) ∈ domTheta θ := (Submodule.mem_inf.mp y.2).1
  obtain ⟨hD, hb⟩ := mem_domTheta.mp hyθ
  set y' : (momentumMin†).domain := ⟨(y : L2I), hD⟩ with hy'
  have hA : (momentumMin† y' : L2I) = μ • (y' : L2I) := by rw [← hμ, momentumTheta_apply]
  have hrep := bvRep_eigen y' hA
  have hb0 : bv0 y' ≠ 0 := by
    intro h0
    apply hy
    refine eq_zero_of_bvRep y' fun x hx => ?_
    rw [hrep x ⟨hx.1.le, hx.2.le⟩, h0, zero_mul]
  have h1 : bv1 y' = bv0 y' * Complex.exp (Complex.I * μ * ((1 : ℝ) : ℂ)) := hrep 1 ⟨zero_le_one, le_rfl⟩
  have h1' : Complex.exp (θ * Complex.I) * bv0 y' = Complex.exp (Complex.I * μ) * bv0 y' := by
    rw [← hb, h1, Complex.ofReal_one, mul_one]
    exact mul_comm _ _
  have hθμ := mul_right_cancel₀ hb0 h1'
  have hexp : Complex.exp (Complex.I * μ - θ * Complex.I) = 1 := by
    rw [Complex.exp_sub, ← hθμ, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : Complex.I * (μ - (θ + 2 * Real.pi * n)) = 0 := by linear_combination hn
  have := (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
  linear_combination this

/-- **The eigenspaces of `P_θ` are one-dimensional**: an eigenvector with eigenvalue `θ + 2πn` is a multiple of `e^{i(θ + 2πn)x}`. -/
theorem eigenvector_momentumTheta {θ : ℝ} (n : ℤ) (y : (momentumTheta θ).domain)
    (hμ : momentumTheta θ y = ((θ + 2 * Real.pi * n : ℝ) : ℂ) • (y : L2I)) :
    ∃ a : ℂ, (y : L2I) = a • planeWave (θ + 2 * Real.pi * n) := by
  have hD : (y : L2I) ∈ (momentumMin†).domain := (Submodule.mem_inf.mp y.2).2
  set y' : (momentumMin†).domain := ⟨(y : L2I), hD⟩
  have hA : (momentumMin† y' : L2I) = ((θ + 2 * Real.pi * n : ℝ) : ℂ) • (y' : L2I) := by rw [← hμ, momentumTheta_apply]
  have hrep := bvRep_eigen y' hA
  refine ⟨bv0 y', ?_⟩
  refine Lp.ext ?_
  filter_upwards [rep_ae y', Lp.coeFn_smul (bv0 y') (planeWave (θ + 2 * Real.pi * n)),
    planeWave_ae (θ + 2 * Real.pi * n), ae_restrict_mem measurableSet_Ioo] with x h1 h2 h3 hxI
  rw [show ((y : L2I) : ℝ → ℂ) x = ((y' : L2I) : ℝ → ℂ) x from rfl, h1, h2, Pi.smul_apply, h3, smul_eq_mul,
    hrep x ⟨hxI.1.le, hxI.2.le⟩]
  congr 2
  push_cast
  ring

/-- **The plane waves are orthonormal** (Bonneau-Faraut-Valent, eq. (15): `(φ_m, φ_n) = δ_mn`):
`⟪e^{ikx}, e^{i(k + 2πm)x}⟫ = 1` if `m = 0` and `0` otherwise. -/
theorem inner_planeWave (k : ℝ) (m : ℤ) :
    ⟪planeWave k, planeWave (k + 2 * Real.pi * m)⟫_ℂ = if m = 0 then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def, integral_Ioo_eq]
  have hcongr : ∫ x in (0 : ℝ)..1, ⟪(planeWave k : ℝ → ℂ) x, (planeWave (k + 2 * Real.pi * m) : ℝ → ℂ) x⟫_ℂ =
      ∫ x in (0 : ℝ)..1, Complex.exp ((2 * Real.pi * m * Complex.I) * x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo (planeWave_ae k) ⟨zero_le_one, le_rfl⟩,
      ae_uIoc_of_ae_Ioo (planeWave_ae (k + 2 * Real.pi * m)) ⟨zero_le_one, le_rfl⟩] with x h1 h2 hxI
    rw [h1 hxI, h2 hxI, RCLike.inner_apply, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hcongr]
  split_ifs with hm
  · subst hm
    simp
  · have hc : (2 * Real.pi * m * Complex.I : ℂ) ≠ 0 := by
      have : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) this) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * m * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]; exact ⟨m, by push_cast; ring⟩
    rw [h1]
    simp

/-- **The eigenfunctions are orthonormal**: `n ↦ e^{i(θ + 2πn)x}` is an orthonormal family. -/
theorem orthonormal_planeWave (θ : ℝ) : Orthonormal ℂ fun n : ℤ => planeWave (θ + 2 * Real.pi * n) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := inner_planeWave (θ + 2 * Real.pi * i) (j - i)
  rw [show θ + 2 * Real.pi * i + 2 * Real.pi * ((j - i : ℤ) : ℝ) = θ + 2 * Real.pi * j by push_cast; ring] at h
  rw [h]
  by_cases hij : i = j
  · subst hij; simp
  · have : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    simp [hij, this]

/-- A function continuous on `[0, 1]` as a vector of `L²(0, 1)`. -/
lemma memLp_of_continuousOn {Y : ℝ → ℂ} (hY : ContinuousOn Y (Icc 0 1)) :
    MemLp Y 2 ((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  refine MemLp.of_bound ((hY.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hC x (Ioo_subset_Icc_self hx)

/-- **The resolvent equation is solvable off the eigenvalues**: for `z ∉ θ + 2πℤ` and every `f ∈ L²(0, 1)` there is `y ∈ D_θ` with
`P_θ y - z y = f`. The solution is `y(x) = e^{izx} (C + i ∫₀ˣ e^{-izt} f(t) dt)`, with `C` fixed by `y(1) = e^{iθ} y(0)`, which is possible
since `e^{iz} ≠ e^{iθ}`. -/
theorem exists_momentumTheta_sub_eq {θ : ℝ} {z : ℂ} (hz : ∀ n : ℤ, z ≠ θ + 2 * Real.pi * n) (f : L2I) :
    ∃ y : (momentumTheta θ).domain, momentumTheta θ y - z • (y : L2I) = f := by
  have hfi : IntervalIntegrable (fun t => (f : ℝ → ℂ) t) volume 0 1 := intervalIntegrable_of_integrableOn (integrable_L2I f)
  set E : ℝ → ℂ := fun x => Complex.exp (Complex.I * z * x) with hE
  set Em : ℝ → ℂ := fun x => Complex.exp (-(Complex.I * z) * x) with hEm
  have hEc : Continuous E := Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hEmc : Continuous Em := Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hEd : ∀ x, HasDerivAt E (Complex.I * z * E x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Complex.I * z * (x : ℂ)) (Complex.I * z) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (Complex.I * z)
    convert h1.cexp using 1
    ring
  set k : ℝ → ℂ := fun t => Em t * (Complex.I * (f : ℝ → ℂ) t) with hk
  have hki : IntervalIntegrable k volume 0 1 :=
    (hfi.const_mul Complex.I).continuousOn_mul hEmc.continuousOn
  set F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, k t with hF
  have hEθ : Complex.exp (θ * Complex.I) - Complex.exp (Complex.I * z) ≠ 0 := by
    intro h
    have hexp : Complex.exp (Complex.I * z - θ * Complex.I) = 1 := by
      rw [Complex.exp_sub, ← sub_eq_zero.mp h, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    apply hz n
    have hI : Complex.I * (z - (θ + 2 * Real.pi * n)) = 0 := by linear_combination hn
    have := (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
    linear_combination this
  set C : ℂ := Complex.exp (Complex.I * z) * F 1 / (Complex.exp (θ * Complex.I) - Complex.exp (Complex.I * z)) with hC
  set Y : ℝ → ℂ := fun x => E x * (C + F x) with hY
  have hFc : ContinuousOn F (Icc 0 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hki (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
    rwa [uIcc_of_le zero_le_one] at h
  have hYc : ContinuousOn Y (Icc 0 1) := hEc.continuousOn.mul (continuousOn_const.add hFc)
  -- `Y` is absolutely continuous with `Y' = i z Y + i f` almost everywhere
  have hEac : AbsolutelyContinuousOnInterval E 0 1 :=
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp : ContDiff ℝ 1 E).contDiffOn.absolutelyContinuousOnInterval
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) 0 1 :=
    (contDiff_const (c := C)).contDiffOn.absolutelyContinuousOnInterval
  have hYac : AbsolutelyContinuousOnInterval Y 0 1 := hEac.smul (hconst.add (ac_primitive hki))
  have hYd : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      deriv Y t = Complex.I * z * Y t + Complex.I * (f : ℝ → ℂ) t := by
    have h := hki.ae_hasDerivAt_integral
    refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
    filter_upwards [h] with t ht htI
    have htI' : t ∈ uIcc (0 : ℝ) 1 := by rw [uIcc_of_le zero_le_one]; exact ⟨htI.1.le, htI.2.le⟩
    have hFd : HasDerivAt F (k t) t := ht htI' 0 left_mem_uIcc
    have hYd := (hEd t).mul (hFd.const_add C)
    rw [show deriv Y t = _ from hYd.deriv, hk]
    simp only [hEm, hY]
    have hinv : Complex.exp (Complex.I * z * t) * Complex.exp (-(Complex.I * z) * t) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    linear_combination (Complex.I * (f : ℝ → ℂ) t) * hinv
  obtain ⟨Yv, hYv⟩ : ∃ Yv : L2I, Yv = (memLp_of_continuousOn hYc).toLp Y := ⟨_, rfl⟩
  have hYv_ae : (Yv : ℝ → ℂ) =ᵐ[(volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)] Y := by
    rw [hYv]; exact MemLp.coeFn_toLp _
  obtain ⟨g, hg⟩ : ∃ g : L2I, g = Complex.I • (z • Yv + f) := ⟨_, rfl⟩
  have hg_ae : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), (g : ℝ → ℂ) t = deriv Y t := by
    rw [hg]
    filter_upwards [Lp.coeFn_smul Complex.I (z • Yv + f), Lp.coeFn_add (z • Yv) f, Lp.coeFn_smul z Yv, hYv_ae, hYd]
      with t h1 h2 h3 h4 h5
    rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, Pi.smul_apply, h4, h5, smul_eq_mul, smul_eq_mul]
    ring
  have hint : ∀ x ∈ Icc (0 : ℝ) 1, ∫ t in (0 : ℝ)..x, (g : ℝ → ℂ) t = ∫ t in (0 : ℝ)..x, deriv Y t := by
    intro x hx
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_uIoc_of_ae_Ioo hg_ae hx] with t ht htI
    exact ht htI
  have hprim : ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)), Yv x = Y 0 + ∫ t in (0 : ℝ)..x, (g : ℝ → ℂ) t := by
    filter_upwards [hYv_ae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [hx, hint x ⟨hxI.1.le, hxI.2.le⟩]
    exact ac_eq_primitive hYac ⟨hxI.1.le, hxI.2.le⟩
  obtain ⟨hD, hA⟩ := mem_adjoint_of_primitive Yv g (Y 0) hprim
  obtain ⟨b0, b1⟩ := bv_of_primitive Yv g (Y 0) hprim hD
  have hY0 : Y 0 = C := by simp [hY, hE, hF]
  have hY1 : Y 1 = Complex.exp (θ * Complex.I) * C := by
    simp only [hY, hE, Complex.ofReal_one, mul_one]
    have hCeq : C * (Complex.exp (θ * Complex.I) - Complex.exp (Complex.I * z)) = Complex.exp (Complex.I * z) * F 1 := by
      rw [hC]; exact div_mul_cancel₀ _ hEθ
    linear_combination -hCeq
  have hθ : Yv ∈ domTheta θ := by
    refine mem_domTheta.mpr ⟨hD, ?_⟩
    rw [b0, b1, hint 1 ⟨zero_le_one, le_rfl⟩, ← ac_eq_primitive hYac ⟨zero_le_one, le_rfl⟩, hY1, hY0]
  refine ⟨⟨Yv, by rw [momentumTheta_domain]; exact hθ⟩, ?_⟩
  rw [momentumTheta_apply]
  show momentumMin† ⟨Yv, hD⟩ - z • Yv = f
  rw [hA, hg, smul_smul]
  have : -Complex.I * Complex.I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
  rw [this, one_smul, add_sub_cancel_left]

/-- `(P_θ - z)` on its domain, the domain of `P_θ`. -/
lemma momentumTheta_sub_apply (θ : ℝ) (z : ℂ) (x : (momentumTheta θ - z • 1).domain) :
    (momentumTheta θ - z • 1).toFun x = momentumTheta θ ⟨x, (Submodule.mem_inf.mp x.2).1⟩ - z • (x : L2I) :=
  rfl

/-- At `z = θ + 2πn` the kernel of `P_θ - z` contains the plane wave `e^{i(θ + 2πn)x}`. -/
lemma ker_momentumTheta_ne_bot (θ : ℝ) (n : ℤ) :
    (momentumTheta θ - ((θ : ℂ) + 2 * Real.pi * n) • 1).toFun.ker ≠ ⊥ := by
  obtain ⟨h, hP⟩ := momentumTheta_planeWave θ n
  refine (Submodule.ne_bot_iff _).mpr ⟨⟨planeWave (θ + 2 * Real.pi * n),
    Submodule.mem_inf.mpr ⟨h, by simp [LinearPMap.smul_domain, LinearPMap.one_domain]⟩⟩, LinearMap.mem_ker.mpr ?_, ?_⟩
  · rw [momentumTheta_sub_apply, sub_eq_zero]
    convert hP using 2
    push_cast
    ring
  · intro h0
    exact planeWave_ne_zero _ (congrArg Subtype.val h0)

/-- **The spectrum of `P_θ` is `θ + 2πℤ`** (Bonneau-Faraut-Valent, Section 5.3, p. 8, eq. (15) and "the spectra are purely discrete", with
`ħ = 1`, `L = 1`), in Physlib's sense of the spectrum of a partial linear map: `z` is in the resolvent set iff `P_θ - z` is a bijection of
the domain onto `L²(0, 1)` (with continuous inverse, automatic since `P_θ` is closed). -/
theorem spectrum_momentumTheta (θ : ℝ) :
    LinearPMap.spectrum (momentumTheta θ) = {z : ℂ | ∃ n : ℤ, z = θ + 2 * Real.pi * n} := by
  have hcl : (momentumTheta θ).IsClosed := (momentumTheta_isSelfAdjoint θ).isClosed
  ext z
  rw [LinearPMap.spectrum_eq, hcl.resolventSet_eq]
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or]
  constructor
  · rintro (hker | hran)
    · obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
      have hx' : (momentumTheta θ - z • 1).toFun x = 0 := LinearMap.mem_ker.mp hx
      rw [momentumTheta_sub_apply, sub_eq_zero] at hx'
      refine eigenvalue_momentumTheta ⟨x, (Submodule.mem_inf.mp x.2).1⟩ ?_ hx'
      intro h0
      exact hx0 (Subtype.ext h0)
    · by_contra hz
      push Not at hz
      apply hran
      refine LinearMap.range_eq_top.mpr fun f => ?_
      obtain ⟨y, hy⟩ := exists_momentumTheta_sub_eq (fun n h => hz n h) f
      refine ⟨⟨y, Submodule.mem_inf.mpr ⟨y.2, by simp [LinearPMap.smul_domain, LinearPMap.one_domain]⟩⟩, ?_⟩
      rw [momentumTheta_sub_apply]
      exact hy
  · rintro ⟨n, rfl⟩
    left
    exact ker_momentumTheta_ne_bot θ n

/-- **The spectrum is the point spectrum** ("the spectra are purely discrete", Bonneau-Faraut-Valent, p. 8): every point of the spectrum of
`P_θ` is an eigenvalue, the eigenspaces are one-dimensional (`eigenvector_momentumTheta`), and the points are isolated. -/
theorem pointSpectrum_momentumTheta (θ : ℝ) :
    LinearPMap.pointSpectrum (momentumTheta θ) = LinearPMap.spectrum (momentumTheta θ) := by
  refine (LinearPMap.pointSpectrum_subset_spectrum _).antisymm fun z hz => ?_
  rw [spectrum_momentumTheta] at hz
  obtain ⟨n, rfl⟩ := hz
  exact ker_momentumTheta_ne_bot θ n

end Lightlike.OperatorAlgebras
