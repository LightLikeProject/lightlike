import Lightlike.Asymptotics.EPRL.HaarSphere
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Gnomonic chart of the 3-sphere: change of variables

The map `Φ(a, q) = (a, a q)` of `ℝ × ℝ³` is the polar parametrisation of the cone over a
hemisphere in gnomonic coordinates `q = u / a`. Its Jacobian is `a³`.
-/

open MeasureTheory Set Quaternion Metric Pointwise

namespace Lightlike.Asymptotics.EPRL

/-- `Φ(a, q) = (a, a q)` on `ℝ⁴ = Fin 4 → ℝ`. -/
def cone4 (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![y 0, y 0 * y 1, y 0 * y 2, y 0 * y 3]

/-- Its Jacobian matrix. -/
def cone4J (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; y 1, y 0, 0, 0; y 2, 0, y 0, 0; y 3, 0, 0, y 0]

lemma det_cone4J (y : Fin 4 → ℝ) : (cone4J y).det = y 0 ^ 3 := by
  simp [cone4J, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring

/-- Fréchet derivative of `cone4`. -/
noncomputable def cone4D (y : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (cone4J y))

lemma det_cone4D (y : Fin 4 → ℝ) : (cone4D y).det = y 0 ^ 3 := by
  have : (cone4D y).det = LinearMap.det (Matrix.toLin' (cone4J y)) := rfl
  rw [this, LinearMap.det_toLin', det_cone4J]

lemma hasFDerivAt_cone4 (y : Fin 4 → ℝ) : HasFDerivAt cone4 (cone4D y) y := by
  rw [hasFDerivAt_pi']
  intro i
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y
  have h3 := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y
  fin_cases i
  · show HasFDerivAt (fun x : Fin 4 → ℝ => x 0) _ y
    refine h0.congr_fderiv ?_
    ext z; simp [cone4D, cone4J, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · show HasFDerivAt (fun x : Fin 4 → ℝ => x 0 * x 1) _ y
    refine (h0.mul h1).congr_fderiv ?_
    ext z; simp [cone4D, cone4J, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · show HasFDerivAt (fun x : Fin 4 → ℝ => x 0 * x 2) _ y
    refine (h0.mul h2).congr_fderiv ?_
    ext z; simp [cone4D, cone4J, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · show HasFDerivAt (fun x : Fin 4 → ℝ => x 0 * x 3) _ y
    refine (h0.mul h3).congr_fderiv ?_
    ext z; simp [cone4D, cone4J, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

lemma injOn_cone4 : InjOn cone4 {y : Fin 4 → ℝ | 0 < y 0} := by
  intro y hy z hz h
  have hy0 : 0 < y 0 := hy
  have e0 : y 0 = z 0 := congrFun h 0
  have h1 : y 0 * y 1 = z 0 * z 1 := congrFun h 1
  have h2 : y 0 * y 2 = z 0 * z 2 := congrFun h 2
  have h3 : y 0 * y 3 = z 0 * z 3 := congrFun h 3
  rw [← e0] at h1 h2 h3
  funext i
  fin_cases i
  · exact e0
  · exact mul_left_cancel₀ hy0.ne' h1
  · exact mul_left_cancel₀ hy0.ne' h2
  · exact mul_left_cancel₀ hy0.ne' h3

/-- **Volume of the image under `cone4`**: `vol Φ(D) = ∫_D a³`. -/
theorem volume_cone4_image {D : Set (Fin 4 → ℝ)} (hD : MeasurableSet D) (hpos : D ⊆ {y | 0 < y 0}) :
    volume (cone4 '' D) = ∫⁻ y in D, ENNReal.ofReal (y 0 ^ 3) := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume hD
    (fun y _ => (hasFDerivAt_cone4 y).hasFDerivWithinAt) (injOn_cone4.mono hpos)]
  refine setLIntegral_congr_fun hD (fun y hy => ?_)
  rw [det_cone4D, abs_of_pos (pow_pos (hpos hy) 3)]

/-- `s(q) = 1 + |q|²` on `ℝ³`. -/
def gsq (q : Fin 3 → ℝ) : ℝ := 1 + q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2

lemma gsq_pos (q : Fin 3 → ℝ) : 0 < gsq q := by unfold gsq; positivity

/-- Radial bound `1/√(1+|q|²)`. -/
noncomputable def grad (q : Fin 3 → ℝ) : ℝ := (Real.sqrt (gsq q))⁻¹

lemma grad_pos (q : Fin 3 → ℝ) : 0 < grad q := inv_pos.mpr (Real.sqrt_pos.mpr (gsq_pos q))

lemma grad_pow_four (q : Fin 3 → ℝ) : grad q ^ 4 = 1 / gsq q ^ 2 := by
  unfold grad
  rw [inv_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (gsq_pos q).le]
  simp

/-- The cone region over `P ⊆ ℝ³` in the `(a, q)` coordinates. -/
def coneRegion (P : Set (Fin 3 → ℝ)) : Set (ℝ × (Fin 3 → ℝ)) :=
  {z | z.2 ∈ P ∧ 0 < z.1 ∧ z.1 < grad z.2}

lemma lintegral_a3 (r : ℝ) (hr : 0 < r) :
    ∫⁻ a in Ioo 0 r, ENNReal.ofReal (a ^ 3) = ENNReal.ofReal (r ^ 4 / 4) := by
  have hint : IntegrableOn (fun a : ℝ => a ^ 3) (Ioo 0 r) :=
    (continuous_pow 3).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioo (fun a ha => pow_nonneg ha.1.le 3))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
    integral_pow]
  norm_num

/-- Measurable measure-preserving splitting `ℝ⁴ ≃ ℝ × ℝ³`. -/
noncomputable def split4 : (Fin 4 → ℝ) ≃ᵐ ℝ × (Fin 3 → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0

lemma split4_apply (y : Fin 4 → ℝ) : split4 y = (y 0, fun i : Fin 3 => y i.succ) := by
  simp [split4, MeasurableEquiv.piFinSuccAbove_apply]
  rfl

lemma measurePreserving_split4 : MeasurePreserving split4 volume volume :=
  volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0

lemma measurableSet_coneRegion {P : Set (Fin 3 → ℝ)} (hP : MeasurableSet P) :
    MeasurableSet (coneRegion P) := by
  have hg : Measurable grad := by
    unfold grad gsq
    fun_prop
  refine (measurable_snd hP).inter ?_
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst (hg.comp measurable_snd))

/-- **Fubini over the cone**: `∫_{cone over P} a³ = ∫_P 1/(4 (1+|q|²)²) dq`. -/
theorem lintegral_cone_region {P : Set (Fin 3 → ℝ)} (hP : MeasurableSet P) :
    ∫⁻ y in split4 ⁻¹' coneRegion P, ENNReal.ofReal (y 0 ^ 3)
      = ∫⁻ q in P, ENNReal.ofReal (1 / (4 * gsq q ^ 2)) := by
  have hE := measurableSet_coneRegion hP
  have h1 : ∫⁻ y in split4 ⁻¹' coneRegion P, ENNReal.ofReal (y 0 ^ 3)
      = ∫⁻ z in coneRegion P, ENNReal.ofReal (z.1 ^ 3) := by
    have := measurePreserving_split4.setLIntegral_comp_preimage_emb split4.measurableEmbedding
      (fun z : ℝ × (Fin 3 → ℝ) => ENNReal.ofReal (z.1 ^ 3)) (coneRegion P)
    simpa [split4_apply] using this
  rw [h1, ← lintegral_indicator hE, Measure.volume_eq_prod, lintegral_prod_symm _ (by
    exact (Measurable.indicator (by fun_prop) hE).aemeasurable)]
  rw [← lintegral_indicator hP]
  refine lintegral_congr (fun q => ?_)
  by_cases hq : q ∈ P
  · simp only [indicator_of_mem hq]
    have : (fun a : ℝ => (coneRegion P).indicator (fun z : ℝ × (Fin 3 → ℝ) => ENNReal.ofReal (z.1 ^ 3)) (a, q))
        = (Ioo 0 (grad q)).indicator (fun a : ℝ => ENNReal.ofReal (a ^ 3)) := by
      funext a
      by_cases ha : a ∈ Ioo 0 (grad q)
      · simp [indicator_of_mem ha, indicator_of_mem (show (a, q) ∈ coneRegion P from ⟨hq, ha.1, ha.2⟩)]
      · simp [indicator_of_notMem ha,
          indicator_of_notMem (show (a, q) ∉ coneRegion P from fun h => ha ⟨h.2.1, h.2.2⟩)]
    rw [this, lintegral_indicator measurableSet_Ioo, lintegral_a3 _ (grad_pos q), grad_pow_four]
    congr 1
    field_simp
  · simp only [indicator_of_notMem hq]
    have : (fun a : ℝ => (coneRegion P).indicator (fun z : ℝ × (Fin 3 → ℝ) => ENNReal.ofReal (z.1 ^ 3)) (a, q))
        = fun _ => 0 := by
      funext a
      exact indicator_of_notMem (fun h => hq h.1) _
    rw [this]; simp

/-! ## Gnomonic parametrisation of the open hemisphere -/

/-- The Borel σ-algebra on the real quaternions. -/
noncomputable local instance : MeasurableSpace ℍ[ℝ] := borel ℍ[ℝ]
local instance : BorelSpace ℍ[ℝ] := ⟨rfl⟩

/-- The quaternion with coordinates `y`. -/
def toH (y : Fin 4 → ℝ) : ℍ[ℝ] := ⟨y 0, y 1, y 2, y 3⟩

/-- The quaternion `(1, q) / √(1 + |q|²)`, a unit quaternion with positive real part. -/
noncomputable def gammaH (q : Fin 3 → ℝ) : ℍ[ℝ] :=
  ⟨grad q, grad q * q 0, grad q * q 1, grad q * q 2⟩

lemma normSq_gammaH (q : Fin 3 → ℝ) : Quaternion.normSq (gammaH q) = 1 := by
  have h : grad q ^ 2 * gsq q = 1 := by
    unfold grad
    rw [inv_pow, Real.sq_sqrt (gsq_pos q).le]
    exact inv_mul_cancel₀ (gsq_pos q).ne'
  rw [Quaternion.normSq_def']
  simp only [gammaH]
  unfold gsq at h
  nlinarith [h]

lemma norm_gammaH (q : Fin 3 → ℝ) : ‖gammaH q‖ = 1 := by
  have := normSq_gammaH q
  rw [Quaternion.normSq_eq_norm_mul_self] at this
  nlinarith [norm_nonneg (gammaH q)]

/-- The gnomonic chart `ℝ³ → S³`. -/
noncomputable def gamma (q : Fin 3 → ℝ) : sphere (0 : ℍ[ℝ]) 1 :=
  ⟨gammaH q, by simpa using norm_gammaH q⟩

/-- Gnomonic coordinates `u / a` of a quaternion with positive real part. -/
noncomputable def tailH (x : ℍ[ℝ]) : Fin 3 → ℝ := ![x.imI / x.re, x.imJ / x.re, x.imK / x.re]

lemma tailH_zero (x : ℍ[ℝ]) : tailH x 0 = x.imI / x.re := rfl
lemma tailH_one (x : ℍ[ℝ]) : tailH x 1 = x.imJ / x.re := rfl
lemma tailH_two (x : ℍ[ℝ]) : tailH x 2 = x.imK / x.re := rfl

lemma grad_tailH {x : ℍ[ℝ]} (hn : Quaternion.normSq x = 1) (hre : 0 < x.re) :
    grad (tailH x) = x.re := by
  have hs : gsq (tailH x) = (x.re)⁻¹ ^ 2 := by
    rw [Quaternion.normSq_def'] at hn
    simp only [gsq, tailH_zero, tailH_one, tailH_two]
    field_simp
    nlinarith [hn]
  unfold grad
  rw [hs, Real.sqrt_sq (inv_nonneg.mpr hre.le), inv_inv]

lemma gammaH_tailH {x : ℍ[ℝ]} (hn : Quaternion.normSq x = 1) (hre : 0 < x.re) :
    gammaH (tailH x) = x := by
  have hg := grad_tailH hn hre
  ext
  · simp [gammaH, hg]
  · simp [gammaH, hg, tailH_zero]; field_simp
  · simp [gammaH, hg, tailH_one]; field_simp
  · simp [gammaH, hg, tailH_two]; field_simp

lemma tailH_gammaH (q : Fin 3 → ℝ) : tailH (gammaH q) = q := by
  have hg := grad_pos q
  funext i
  fin_cases i
  · simp [tailH_zero, gammaH]; field_simp
  · simp [tailH_one, gammaH]; field_simp
  · simp [tailH_two, gammaH]; field_simp

lemma re_gammaH (q : Fin 3 → ℝ) : (gammaH q).re = grad q := rfl

lemma gamma_coe (q : Fin 3 → ℝ) : ((gamma q : sphere (0 : ℍ[ℝ]) 1) : ℍ[ℝ]) = gammaH q := rfl

lemma tail_split (y : Fin 4 → ℝ) : (split4 y).2 = fun i : Fin 3 => y i.succ := by
  rw [split4_apply]

/-- **The cone over a region of the hemisphere** is the image of the gnomonic cone region. -/
theorem cone_eq (s : Set (sphere (0 : ℍ[ℝ]) 1)) (hs : ∀ x ∈ s, 0 < (x : ℍ[ℝ]).re) :
    Ioo (0 : ℝ) 1 • ((↑) '' s : Set ℍ[ℝ])
      = toH '' (cone4 '' (split4 ⁻¹' coneRegion (gamma ⁻¹' s))) := by
  ext z
  constructor
  · rintro ⟨c, hc, _, ⟨x, hx, rfl⟩, rfl⟩
    have hre := hs x hx
    have hn := normSq_of_mem_sphere x
    set y : Fin 4 → ℝ := ![c * (x : ℍ[ℝ]).re, (x : ℍ[ℝ]).imI / (x : ℍ[ℝ]).re,
      (x : ℍ[ℝ]).imJ / (x : ℍ[ℝ]).re, (x : ℍ[ℝ]).imK / (x : ℍ[ℝ]).re] with hy
    have htail : (fun i : Fin 3 => y i.succ) = tailH (x : ℍ[ℝ]) := by
      funext i; fin_cases i <;> rfl
    have hg := grad_tailH hn hre
    refine ⟨cone4 y, ⟨y, ?_, rfl⟩, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · rw [tail_split, htail]
        show gamma (tailH (x : ℍ[ℝ])) ∈ s
        have : gamma (tailH (x : ℍ[ℝ])) = x := Subtype.ext (gammaH_tailH hn hre)
        rwa [this]
      · show 0 < (split4 y).1
        rw [split4_apply]; exact mul_pos hc.1 hre
      · show (split4 y).1 < grad (split4 y).2
        rw [split4_apply]; simp only [htail, hg]
        show c * (x : ℍ[ℝ]).re < _
        nlinarith [hc.2]
    · ext <;> simp [toH, cone4, hy] <;> field_simp
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨hP, ha, hlt⟩ := hy
    set q : Fin 3 → ℝ := (split4 y).2 with hq
    set a : ℝ := (split4 y).1 with ha'
    have hgp := grad_pos q
    refine ⟨a / grad q, ⟨div_pos ha hgp, (div_lt_one hgp).mpr hlt⟩, _, ⟨gamma q, hP, rfl⟩, ?_⟩
    have hy0 : y 0 = a := by simp [ha', split4_apply]
    have hyi : ∀ i : Fin 3, y i.succ = q i := fun i => by simp [hq, split4_apply]
    have h1 : y 1 = q 0 := hyi 0
    have h2 : y 2 = q 1 := hyi 1
    have h3 : y 3 = q 2 := hyi 2
    rw [gamma_coe]
    ext <;> simp [toH, cone4, gammaH, hy0, h1, h2, h3] <;> field_simp

/-- The coordinate map `ℝ⁴ ≃ ℍ` as a measurable equivalence. -/
noncomputable def toHEquiv : (Fin 4 → ℝ) ≃ᵐ ℍ[ℝ] :=
  (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).trans
    (Quaternion.linearIsometryEquivTuple.symm.toHomeomorph.toMeasurableEquiv)

lemma toHEquiv_apply (y : Fin 4 → ℝ) : toHEquiv y = toH y := by
  ext <;> rfl

lemma measurePreserving_toHEquiv : MeasurePreserving toHEquiv volume volume :=
  (Quaternion.linearIsometryEquivTuple.symm.measurePreserving).comp
    (PiLp.volume_preserving_toLp (Fin 4))

lemma measurable_grad : Measurable grad := by unfold grad gsq; fun_prop

lemma measurable_gamma : Measurable gamma := by
  have hgrad := measurable_grad
  refine Measurable.subtype_mk ?_
  have : gammaH = fun q => toHEquiv ![grad q, grad q * q 0, grad q * q 1, grad q * q 2] := by
    funext q; rw [toHEquiv_apply]; rfl
  show Measurable gammaH
  rw [this]
  refine toHEquiv.measurable.comp (measurable_pi_iff.mpr fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

/-- **Surface measure in gnomonic coordinates**: for a measurable set `s` of the open hemisphere,
`σ(s) = ∫_{γ⁻¹ s} (1 + |q|²)⁻² dq`. -/
theorem toSphere_gamma (s : Set (sphere (0 : ℍ[ℝ]) 1)) (hs : MeasurableSet s)
    (hpos : ∀ x ∈ s, 0 < (x : ℍ[ℝ]).re) :
    (volume : Measure ℍ[ℝ]).toSphere s
      = ∫⁻ q in gamma ⁻¹' s, ENNReal.ofReal (1 / gsq q ^ 2) := by
  have hgm : Measurable gamma := measurable_gamma
  have hP : MeasurableSet (gamma ⁻¹' s) := hgm hs
  have hD : MeasurableSet (split4 ⁻¹' coneRegion (gamma ⁻¹' s)) :=
    split4.measurable (measurableSet_coneRegion hP)
  have hDpos : split4 ⁻¹' coneRegion (gamma ⁻¹' s) ⊆ {y | 0 < y 0} := by
    intro y hy
    have : 0 < (split4 y).1 := hy.2.1
    rwa [split4_apply] at this
  rw [Measure.toSphere_apply' _ hs, cone_eq s hpos]
  set X := cone4 '' (split4 ⁻¹' coneRegion (gamma ⁻¹' s)) with hX
  have h1 : volume (toH '' X) = volume X := by
    have e1 : toH '' X = toHEquiv.symm ⁻¹' X := by
      have : (toH : (Fin 4 → ℝ) → ℍ[ℝ]) = toHEquiv := by
        funext y; exact (toHEquiv_apply y).symm
      rw [this]
      exact toHEquiv.toEquiv.image_eq_preimage_symm X
    rw [e1]
    exact (measurePreserving_toHEquiv.symm toHEquiv).measure_preimage_equiv X
  rw [h1, hX, volume_cone4_image hD hDpos, lintegral_cone_region hP]
  have h4 : (Module.finrank ℝ ℍ[ℝ] : ENNReal) = ENNReal.ofReal 4 := by
    rw [Quaternion.finrank_eq_four]; simp
  rw [h4, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun q => ?_)
  rw [← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have := (gsq_pos q).ne'
  field_simp

/-! ## The Haar measure of SU(2) in the gnomonic chart -/

open Lightlike Lightlike.Spin4

/-- The gnomonic chart of SU(2): `q ↦ (1, q)/√(1+|q|²)` as a unit quaternion matrix. -/
noncomputable def gammaSU (q : Fin 3 → ℝ) : SU2 := sphereToSU2 (gamma q)

/-- The open hemisphere `Re g₀₀ > 0` of SU(2). -/
def hemiSU : Set SU2 := {g | 0 < ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re}

lemma re_sphereToSU2 (x : sphere (0 : ℍ[ℝ]) 1) :
    (((sphereToSU2 x : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re = (x : ℍ[ℝ]).re := by
  simp [sphereToSU2, toMat_apply, quatMat]

lemma gammaSU_mem_hemi (q : Fin 3 → ℝ) : gammaSU q ∈ hemiSU := by
  change 0 < (((sphereToSU2 (gamma q) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re
  rw [re_sphereToSU2]
  exact grad_pos q

lemma measurable_gammaSU : Measurable gammaSU :=
  continuous_sphereToSU2.measurable.comp measurable_gamma

/-- **Haar measure of SU(2) in the gnomonic chart** (set version): for a measurable subset `s` of
the hemisphere, `haar(s) = ∫_{γ⁻¹ s} dq / (2π² (1+|q|²)²)`. -/
theorem haarSU2_gnomonic {s : Set SU2} (hs : MeasurableSet s) (hsH : s ⊆ hemiSU) :
    haarSU2 s = ∫⁻ q in gammaSU ⁻¹' s, ENNReal.ofReal (1 / (2 * Real.pi ^ 2 * gsq q ^ 2)) := by
  have hm : Measurable sphereToSU2 := continuous_sphereToSU2.measurable
  have hpre : ∀ x ∈ sphereToSU2 ⁻¹' s, 0 < (x : ℍ[ℝ]).re := by
    intro x hx
    have := hsH hx
    change 0 < (((sphereToSU2 x : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re at this
    rwa [re_sphereToSU2] at this
  rw [haarSU2_eq_cone_div, Measure.smul_apply, smul_eq_mul]
  unfold coneSU2
  rw [Measure.map_apply hm hs, toSphere_gamma _ (hm hs) hpre]
  have hpos : 0 < 2 * Real.pi ^ 2 := by positivity
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (by simpa using hpos))]
  refine lintegral_congr (fun q => ?_)
  rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have := (gsq_pos q).ne'
  field_simp

/-- The Haar density in the gnomonic chart, `1 / (2π² (1+|q|²)²)`. -/
noncomputable def haarDensity (q : Fin 3 → ℝ) : ℝ := 1 / (2 * Real.pi ^ 2 * gsq q ^ 2)

lemma haarDensity_pos (q : Fin 3 → ℝ) : 0 < haarDensity q := by
  unfold haarDensity; have := gsq_pos q; positivity

lemma measurable_haarDensity : Measurable haarDensity := by
  unfold haarDensity gsq; fun_prop

/-- **Known value**: at the identity the density is `1/(2π²)`, the reciprocal of the volume of `S³`. -/
lemma haarDensity_zero : haarDensity 0 = 1 / (2 * Real.pi ^ 2) := by
  simp [haarDensity, gsq]

/-- **Wrong-model check**: a density with exponent 1 instead of 2 differs from `haarDensity`
away from the identity (at `q = (1,0,0)`). -/
lemma haarDensity_ne_wrong :
    haarDensity ![1, 0, 0] ≠ 1 / (2 * Real.pi ^ 2 * gsq ![1, 0, 0]) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have h2 : gsq ![1, 0, 0] = 2 := by norm_num [gsq]
  rw [haarDensity, h2]
  intro h
  have := congrArg (fun x => x * (2 * Real.pi ^ 2)) h
  field_simp at this
  norm_num at this

/-- The restriction of the Haar measure to the hemisphere is the push-forward of the density. -/
theorem haarSU2_restrict_hemi :
    haarSU2.restrict hemiSU
      = Measure.map gammaSU (volume.withDensity (fun q => ENNReal.ofReal (haarDensity q))) := by
  have hH : MeasurableSet hemiSU :=
    measurableSet_lt measurable_const
      (Complex.measurable_re.comp ((measurable_pi_apply 0).comp (measurable_pi_apply 0 |>.comp
        measurable_subtype_coe)))
  ext s hs
  rw [Measure.restrict_apply hs, Measure.map_apply measurable_gammaSU hs,
    withDensity_apply _ (measurable_gammaSU hs)]
  rw [haarSU2_gnomonic (hs.inter hH) inter_subset_right]
  have : gammaSU ⁻¹' (s ∩ hemiSU) = gammaSU ⁻¹' s := by
    ext q; simp [gammaSU_mem_hemi q]
  rw [this]; rfl

/-- **Integration against Haar measure in the gnomonic chart.** For a continuous function
supported in the open hemisphere, `∫ f dg = ∫ f(γ q) / (2π² (1+|q|²)²) dq`. -/
theorem integral_haar_gnomonic (f : SU2 → ℂ) (hf : Continuous f)
    (hsupp : ∀ g, f g ≠ 0 → g ∈ hemiSU) :
    ∫ g, f g ∂haarSU2 = ∫ q, haarDensity q • f (gammaSU q) := by
  have hH : MeasurableSet hemiSU :=
    measurableSet_lt measurable_const
      (Complex.measurable_re.comp ((measurable_pi_apply 0).comp (measurable_pi_apply 0 |>.comp
        measurable_subtype_coe)))
  have h1 : ∫ g, f g ∂haarSU2 = ∫ g in hemiSU, f g ∂haarSU2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun g hg => by
      by_contra h; exact hg (hsupp g h))).symm
  rw [h1, haarSU2_restrict_hemi, integral_map measurable_gammaSU.aemeasurable
    hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (by
      exact (measurable_haarDensity.ennreal_ofReal)) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  refine integral_congr_ae (ae_of_all _ (fun q => ?_))
  simp [ENNReal.toReal_ofReal (haarDensity_pos q).le]

end Lightlike.Asymptotics.EPRL
