module

public import Lightlike.Lorentz.Levels

/-!
# Density of the level spaces in L²(ℂ)

**Theorem (`eq_zero_of_orthogonal_levels`).** For all `p₀, q₀ ∈ ℕ` and `ρ ∈ ℝ`, a vector
`h ∈ L²(ℂ)` orthogonal to every level space `levelSpace (ℓ + p₀) (ℓ + q₀) ρ`, `ℓ ∈ ℕ`, is zero.
So the union of these levels is dense.

Proof. Pairing `h` with the generators of the levels gives `∫ φ · E = 0` for every monomial
`φ = (z̄/(1+|z|²))^α (z/(1+|z|²))^β (1/(1+|z|²))^γ` and the integrable function
`E(z) = (1+|z|²)^{-(p₀+q₀)/2} z̄^{p₀} z^{q₀} \overline{(1+|z|²)^{iρ-1}} h(z)`.
The monomials span a star subalgebra of continuous functions on the Riemann sphere
`OnePoint ℂ` (`monAlg`) that separates points (`monAlg_separatesPoints`), so by the
Stone–Weierstrass theorem `∫ φ · E = 0` for every continuous `φ` on the sphere
(`integral_mul_eq_zero_of_mon`), in particular for every smooth compactly supported `φ` on `ℂ`.
Hence `E = 0` almost everywhere (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), and so is `h`.

References: the Stone–Weierstrass theorem is Mathlib's
`ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`; for the density of
the K-finite vectors of the principal series see A. W. Knapp, *Representation Theory of Semisimple
Groups* (Princeton, 1986), Chapter II.
-/

@[expose] public section

open Matrix Complex MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace Lightlike.Lorentz

/-! ## The generators on the Riemann sphere -/

/-- `z ↦ z / (1 + |z|²)`. -/
noncomputable def gU : C(ℂ, ℂ) where
  toFun z := z * (((1 + ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ)
  continuous_toFun := by
    refine continuous_id.mul (Complex.continuous_ofReal.comp ?_)
    exact (by fun_prop : Continuous fun z : ℂ => 1 + ‖z‖ ^ 2).inv₀ fun z => (one_add_pos z).ne'

/-- `z ↦ 1 / (1 + |z|²)`. -/
noncomputable def gV : C(ℂ, ℂ) where
  toFun z := (((1 + ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ)
  continuous_toFun := by
    refine Complex.continuous_ofReal.comp ?_
    exact (by fun_prop : Continuous fun z : ℂ => 1 + ‖z‖ ^ 2).inv₀ fun z => (one_add_pos z).ne'

lemma gU_apply (z : ℂ) : gU z = z * (((1 + ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) := rfl
lemma gV_apply (z : ℂ) : gV z = (((1 + ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) := rfl

lemma eventually_one_le_norm : ∀ᶠ z : ℂ in cocompact ℂ, 1 ≤ ‖z‖ :=
  tendsto_norm_cocompact_atTop.eventually_ge_atTop 1

lemma tendsto_inv_norm : Tendsto (fun z : ℂ => ‖z‖⁻¹) (cocompact ℂ) (𝓝 0) :=
  tendsto_norm_cocompact_atTop.inv_tendsto_atTop

lemma tendsto_gU : Tendsto gU (coclosedCompact ℂ) (𝓝 0) := by
  rw [coclosedCompact_eq_cocompact]
  refine squeeze_zero_norm' ?_ tendsto_inv_norm
  filter_upwards [eventually_one_le_norm] with z hz
  have hz0 : 0 < ‖z‖ := by linarith
  rw [gU_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr
    (one_add_pos z))]
  rw [mul_inv_le_iff₀ (one_add_pos z), inv_mul_eq_div, le_div_iff₀ hz0]
  nlinarith

lemma tendsto_gV : Tendsto gV (coclosedCompact ℂ) (𝓝 0) := by
  rw [coclosedCompact_eq_cocompact]
  refine squeeze_zero_norm' ?_ tendsto_inv_norm
  filter_upwards [eventually_one_le_norm] with z hz
  have hz0 : 0 < ‖z‖ := by linarith
  rw [gV_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (one_add_pos z))]
  exact inv_anti₀ hz0 (by nlinarith)

/-- `z / (1 + |z|²)` on the Riemann sphere (`0` at `∞`). -/
noncomputable def sU : C(OnePoint ℂ, ℂ) := OnePoint.continuousMapMk gU 0 tendsto_gU
/-- `1 / (1 + |z|²)` on the Riemann sphere (`0` at `∞`). -/
noncomputable def sV : C(OnePoint ℂ, ℂ) := OnePoint.continuousMapMk gV 0 tendsto_gV

@[simp] lemma sU_coe (z : ℂ) : sU z = gU z := rfl
@[simp] lemma sV_coe (z : ℂ) : sV z = gV z := rfl
@[simp] lemma sU_infty : sU (OnePoint.infty : OnePoint ℂ) = 0 := rfl
@[simp] lemma sV_infty : sV (OnePoint.infty : OnePoint ℂ) = 0 := rfl

lemma star_sV : star sV = sV := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp [sV_infty]
  | coe z => simp [gV_apply]

/-- **The monomials** `(star U)^α U^β V^γ` on the Riemann sphere. -/
noncomputable def mon (m : ℕ × ℕ × ℕ) : C(OnePoint ℂ, ℂ) :=
  star sU ^ m.1 * sU ^ m.2.1 * sV ^ m.2.2

lemma mon_coe (m : ℕ × ℕ × ℕ) (z : ℂ) :
    mon m z = conj z ^ m.1 * z ^ m.2.1 *
      ((((1 + ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ)) ^ (m.1 + m.2.1 + m.2.2) := by
  simp only [mon, ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.star_apply,
    sU_coe, sV_coe, gU_apply, gV_apply, star_def, map_mul, Complex.conj_ofReal]
  ring

lemma mon_mul (m m' : ℕ × ℕ × ℕ) :
    mon m * mon m' = mon (m.1 + m'.1, m.2.1 + m'.2.1, m.2.2 + m'.2.2) := by
  simp only [mon, pow_add]; ring

lemma star_mon (m : ℕ × ℕ × ℕ) : star (mon m) = mon (m.2.1, m.1, m.2.2) := by
  simp only [mon, star_mul, star_pow, star_star, star_sV]
  ring

/-- The span of the monomials. -/
noncomputable def monSpan : Submodule ℂ C(OnePoint ℂ, ℂ) := Submodule.span ℂ (Set.range mon)

lemma mon_mem (m : ℕ × ℕ × ℕ) : mon m ∈ monSpan := Submodule.subset_span ⟨m, rfl⟩

lemma monSpan_mul {f g : C(OnePoint ℂ, ℂ)} (hf : f ∈ monSpan) (hg : g ∈ monSpan) :
    f * g ∈ monSpan := by
  have h := Submodule.mul_mem_mul hf hg
  rw [monSpan, Submodule.span_mul_span] at h
  refine Submodule.span_le.mpr ?_ h
  rintro _ ⟨a, ⟨m, rfl⟩, b, ⟨m', rfl⟩, rfl⟩
  show mon m * mon m' ∈ monSpan
  rw [mon_mul]; exact mon_mem _

lemma monSpan_star {f : C(OnePoint ℂ, ℂ)} (hf : f ∈ monSpan) : star f ∈ monSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; rw [star_mon]; exact mon_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

/-- **The star algebra of monomials** on the Riemann sphere. -/
noncomputable def monAlg : StarSubalgebra ℂ C(OnePoint ℂ, ℂ) where
  carrier := monSpan
  mul_mem' := monSpan_mul
  add_mem' := add_mem
  algebraMap_mem' c := by
    have : algebraMap ℂ C(OnePoint ℂ, ℂ) c = c • mon (0, 0, 0) := by
      ext x; simp [mon, Algebra.algebraMap_eq_smul_one]
    rw [this]; exact Submodule.smul_mem _ _ (mon_mem _)
  star_mem' := monSpan_star

lemma mem_monAlg_iff (f : C(OnePoint ℂ, ℂ)) : f ∈ monAlg ↔ f ∈ monSpan := Iff.rfl

/-- **The monomials separate the points of the Riemann sphere.** -/
theorem monAlg_separatesPoints : monAlg.SeparatesPoints := by
  have hU : sU ∈ monAlg := by
    have : sU = mon (0, 1, 0) := by ext x; simp [mon]
    rw [this]; exact mon_mem _
  have hV : sV ∈ monAlg := by
    have : sV = mon (0, 0, 1) := by ext x; simp [mon]
    rw [this]; exact mon_mem _
  intro x y hxy
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => exact absurd rfl hxy
    | coe w =>
      refine ⟨sV, ⟨sV, hV, rfl⟩, ?_⟩
      simp only [sV_infty, sV_coe, gV_apply]
      exact (Complex.ofReal_ne_zero.mpr (inv_pos.mpr (one_add_pos w)).ne').symm
  | coe z =>
    induction y using OnePoint.rec with
    | infty =>
      refine ⟨sV, ⟨sV, hV, rfl⟩, ?_⟩
      simp only [sV_infty, sV_coe, gV_apply]
      exact Complex.ofReal_ne_zero.mpr (inv_pos.mpr (one_add_pos z)).ne'
    | coe w =>
      have hzw : z ≠ w := fun h => hxy (by rw [h])
      by_cases hv : gV z = gV w
      · refine ⟨sU, ⟨sU, hU, rfl⟩, ?_⟩
        simp only [sU_coe, gU_apply]
        intro h
        apply hzw
        have hv' : (((1 + ‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) = (((1 + ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) := hv
        rw [hv'] at h
        have hne : (((1 + ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (inv_pos.mpr (one_add_pos w)).ne'
        exact mul_right_cancel₀ hne h
      · exact ⟨sV, ⟨sV, hV, rfl⟩, by simpa using hv⟩

/-! ## The annihilator of the monomials -/

variable {E : ℂ → ℂ}

/-- `φ ↦ ∫ φ(z) E(z) dz` as a continuous linear functional on `C(OnePoint ℂ, ℂ)`. -/
noncomputable def pairing (hE : Integrable E volume) : C(OnePoint ℂ, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun φ => ∫ z : ℂ, φ (z : OnePoint ℂ) * E z
      map_add' := fun φ ψ => by
        simp only [ContinuousMap.add_apply, add_mul]
        refine integral_add ?_ ?_
        · exact hE.bdd_mul (φ.continuous.comp OnePoint.continuous_coe).aestronglyMeasurable
            (Eventually.of_forall fun z => φ.norm_coe_le_norm _)
        · exact hE.bdd_mul (ψ.continuous.comp OnePoint.continuous_coe).aestronglyMeasurable
            (Eventually.of_forall fun z => ψ.norm_coe_le_norm _)
      map_smul' := fun c φ => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
    (∫ z : ℂ, ‖E z‖) fun φ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ z : ℂ, φ (z : OnePoint ℂ) * E z‖ ≤ ∫ z : ℂ, ‖φ‖ * ‖E z‖ := by
            refine norm_integral_le_of_norm_le (hE.norm.const_mul _)
              (Eventually.of_forall fun z => ?_)
            rw [norm_mul]; gcongr; exact φ.norm_coe_le_norm _
        _ = (∫ z : ℂ, ‖E z‖) * ‖φ‖ := by rw [integral_const_mul, mul_comm]

lemma pairing_apply (hE : Integrable E volume) (φ : C(OnePoint ℂ, ℂ)) :
    pairing hE φ = ∫ z : ℂ, φ (z : OnePoint ℂ) * E z := rfl

/-- **Stone–Weierstrass step**: if `E` integrates to zero against every monomial, it integrates to
zero against every continuous function on the Riemann sphere. -/
theorem integral_mul_eq_zero_of_mon (hE : Integrable E volume)
    (h0 : ∀ m, ∫ z : ℂ, mon m (z : OnePoint ℂ) * E z = 0) (φ : C(OnePoint ℂ, ℂ)) :
    ∫ z : ℂ, φ (z : OnePoint ℂ) * E z = 0 := by
  have hker : (monAlg : Set C(OnePoint ℂ, ℂ)) ⊆ {φ | pairing hE φ = 0} := by
    intro f hf
    change f ∈ monSpan at hf
    induction hf using Submodule.span_induction with
    | mem x hx => obtain ⟨m, rfl⟩ := hx; exact h0 m
    | zero => exact map_zero _
    | add x y _ _ hx hy =>
      simp only [Set.mem_ofPred_eq] at hx hy ⊢; rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => simp only [Set.mem_ofPred_eq] at hx ⊢; rw [map_smul, hx, smul_zero]
  have hclosed : IsClosed {φ : C(OnePoint ℂ, ℂ) | pairing hE φ = 0} :=
    isClosed_eq (pairing hE).continuous continuous_const
  have hdense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints monAlg
    monAlg_separatesPoints
  have hφ : φ ∈ monAlg.topologicalClosure := by rw [hdense]; trivial
  have : φ ∈ closure (monAlg : Set C(OnePoint ℂ, ℂ)) := hφ
  exact closure_minimal hker hclosed this

/-- **An integrable function annihilating all monomials vanishes almost everywhere.** -/
theorem ae_eq_zero_of_mon (hE : Integrable E volume)
    (h0 : ∀ m, ∫ z : ℂ, mon m (z : OnePoint ℂ) * E z = 0) :
    E =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hE.locallyIntegrable fun g hg hgc => ?_
  let g' : C(ℂ, ℂ) := ⟨fun z => (g z : ℂ), Complex.continuous_ofReal.comp hg.continuous⟩
  have hg' : Tendsto g' (coclosedCompact ℂ) (𝓝 0) := by
    rw [coclosedCompact_eq_cocompact]
    have := (Complex.continuous_ofReal.tendsto 0).comp hgc.is_zero_at_infty
    rw [Complex.ofReal_zero] at this
    exact this
  have := integral_mul_eq_zero_of_mon hE h0 (OnePoint.continuousMapMk g' 0 hg')
  simp only [Complex.real_smul]
  exact this

/-! ## Orthogonality to all levels -/

/-- The integrable function `E` built from `h`. -/
noncomputable def efun (p₀ q₀ : ℕ) (ρ : ℝ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (((Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p₀ + q₀) : ℝ) : ℂ) * conj z ^ p₀ * z ^ q₀ *
    conj ((((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) ^ (I * ρ - 1)) * h z

lemma integrable_efun (p₀ q₀ : ℕ) (ρ : ℝ) (h : L2C) : Integrable (efun p₀ q₀ ρ h) volume := by
  have hm : MemLp (mono p₀ q₀ ρ p₀ q₀) 2 volume := memLp_mono le_rfl le_rfl ρ
  have hc : MemLp (fun z => conj (mono p₀ q₀ ρ p₀ q₀ z)) 2 volume := by
    refine memLp_of_bound ?_ 1 fun z => ?_
    · exact Complex.continuous_conj.comp (continuous_mono _ _ _ _ _)
    · rw [RCLike.norm_conj]; exact norm_mono_le le_rfl le_rfl ρ z
  have := hc.integrable_mul (Lp.memLp h)
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.mul_apply, mono, wgt, efun, map_mul, map_pow, Complex.conj_ofReal,
    Complex.conj_conj]
  push_cast
  ring

/-- The pairing of a level generator with `h` is a monomial integral against `efun`. -/
lemma inner_mono_eq (p₀ q₀ : ℕ) (ρ : ℝ) (h : L2C) (m : ℕ × ℕ × ℕ) :
    ⟪(memLp_mono (p := m.1 + m.2.1 + m.2.2 + p₀) (q := m.1 + m.2.1 + m.2.2 + q₀)
        (a := p₀ + m.1) (b := q₀ + m.2.1) (by omega) (by omega) ρ).toLp _, h⟫_ℂ =
      ∫ z : ℂ, mon m (z : OnePoint ℂ) * efun p₀ q₀ ρ h z := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_mono (p := m.1 + m.2.1 + m.2.2 + p₀)
    (q := m.1 + m.2.1 + m.2.2 + q₀) (a := p₀ + m.1) (b := q₀ + m.2.1) (by omega) (by omega) ρ)]
    with z hz
  rw [hz, RCLike.inner_apply, mon_coe, efun]
  set ℓ := m.1 + m.2.1 + m.2.2
  have hsq : Real.sqrt (1 + ‖z‖ ^ 2) ^ 2 = 1 + ‖z‖ ^ 2 := Real.sq_sqrt (one_add_pos z).le
  set s := Real.sqrt (1 + ‖z‖ ^ 2)
  have key : s⁻¹ ^ (ℓ + p₀ + (ℓ + q₀)) = s⁻¹ ^ (p₀ + q₀) * ((1 + ‖z‖ ^ 2)⁻¹) ^ ℓ := by
    rw [← hsq, show ℓ + p₀ + (ℓ + q₀) = (p₀ + q₀) + 2 * ℓ by ring, pow_add, pow_mul, inv_pow s 2]
  simp only [mono, wgt, map_mul, map_pow, Complex.conj_conj, Complex.conj_ofReal]
  rw [key]
  push_cast
  ring

/-- **Density of the levels**: a vector of `L²(ℂ)` orthogonal to every level
`levelSpace (ℓ + p₀) (ℓ + q₀) ρ` is zero. -/
theorem eq_zero_of_orthogonal_levels (p₀ q₀ : ℕ) (ρ : ℝ) (h : L2C)
    (hh : ∀ ℓ : ℕ, ∀ f ∈ levelSpace (ℓ + p₀) (ℓ + q₀) ρ, ⟪f, h⟫_ℂ = 0) : h = 0 := by
  have hE := integrable_efun p₀ q₀ ρ h
  have h0 : ∀ m, ∫ z : ℂ, mon m (z : OnePoint ℂ) * efun p₀ q₀ ρ h z = 0 := by
    intro m
    rw [← inner_mono_eq]
    exact hh _ _ (toLp_mono_mem (by omega) (by omega) ρ)
  have hae := ae_eq_zero_of_mon hE h0
  rw [Lp.ext_iff]
  have hnull : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton 0
  filter_upwards [hae, hnull, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz hz0 hzero
  rw [hzero]
  simp only [efun, Pi.zero_apply, mul_eq_zero] at hz
  have h1 : (((Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p₀ + q₀) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (1 + ‖z‖ ^ 2) := Real.sqrt_pos.mpr (one_add_pos z)
    exact_mod_cast (pow_pos (inv_pos.mpr this) _).ne'
  have h2 : conj z ^ p₀ ≠ 0 := pow_ne_zero _ (by simpa using hz0)
  have h3 : z ^ q₀ ≠ 0 := pow_ne_zero _ hz0
  have h4 : conj ((((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) ^ (I * ρ - 1)) ≠ 0 := by
    rw [map_ne_zero, Ne, Complex.cpow_eq_zero_iff, not_and]
    intro h; exact absurd h (by exact_mod_cast (one_add_pos z).ne')
  tauto

end Lightlike.Lorentz
