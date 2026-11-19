import Lightlike.GR.ConformalMinkowski
import Lightlike.GR.AdSInversion
import Lightlike.Lorentz.Signature

/-!
# The Poincaré group acts conformally on the compactified Minkowski space

The conformally compactified Minkowski metric of `ConformalMinkowski.lean` (the region `|T ± R| < π/2` of the
Einstein static universe), read in Cartesian coordinates `x = (t, x₁, x₂, x₃)`, is `Ω²(x) η` with
`Ω²(x) = 1/((1 + t² + |x⃗|²)² − 4 t² |x⃗|²)` (`compactCart`): its pullback by the spherical chart `sph` is the
pullback of `compactMetric` by `compactify` (`pullback_compactCart_sph`). A Poincaré transformation
`x ↦ Λ x + a` with `Λᵀ η Λ = η` (`poincareMap`) is an isometry of `η` (`poincare_isometry`), hence a conformal
transformation of the compactified metric, with conformal factor `Ω²(Λ x + a)/Ω²(x)` (`poincare_conformal`).
The condition `Λᵀ η Λ = η` holds for every element of Physlib's `LorentzGroup 3` reindexed to `Fin 4`
(`lorentzGroup_reindex_isLorentz`).

The time translation in the compactified null coordinates `ũ± = arctan(t ± r)` is `ũ ↦ arctan(tan ũ + a)`
(`timeShift`, `compactify_timeShift`); it extends to null infinity `ũ₊ = π/2` and fixes it
(`tendsto_timeShift_scri`), and its generator is `cos² ũ ∂_ũ` (`hasDerivAt_timeShift`), which vanishes on
null infinity.

Gap row GE7 (the conformal action of the isometry group of Minkowski space on its compactification). Source read
(pdftotext): O. Aharony, S. Gubser, J. Maldacena, H. Ooguri, Y. Oz, *Large N field theories, string theory and
gravity*, arXiv:hep-th/9905111, section 2.2, "Conformal Structure of Flat Space", eqs. (2.10)–(2.19), printed
pp. 36–40: the compactification `u± = tan ũ±`, `ũ± = (τ ± θ)/2` (2.14) mapping `R^{1,p}` into `R × S^p`, the
statement that the conformal group `SO(2, p+1)` of `R^{1,p}` acts there, the translation `P₀ : ½(∂_{u₊} + ∂_{u₋})`
(2.19) and `∂_ũ = (1 + u²) ∂_u` (2.12), (2.17). The source states the Poincaré group as part of the conformal
group; that each Poincaré transformation rescales the compactified metric by the explicit factor
`Ω²(Λ x + a)/Ω²(x)` is our computation, not a sentence of the source.
-/

open Matrix Real Filter Topology

noncomputable section

namespace Lightlike

/-! ## Minkowski space in Cartesian coordinates and its Poincaré transformations -/

/-- The Minkowski metric `η` in Cartesian coordinates `(t, x₁, x₂, x₃)`. -/
def minkCart (_ : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := eta 4

/-- The Poincaré transformation `x ↦ Λ x + a`. -/
def poincareMap (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a : Fin 4 → ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  Λ *ᵥ x + a

lemma pd_poincareMap (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a y : Fin 4 → ℝ) (μ k : Fin 4) :
    pd k (fun z => poincareMap Λ a z μ) y = Λ μ k := by
  set L : (Fin 4 → ℝ) →L[ℝ] ℝ :=
    ∑ j : Fin 4, Λ μ j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j with hL
  have hf : (fun z => poincareMap Λ a z μ) = fun z => L z + a μ := by
    funext z
    simp [poincareMap, hL, Matrix.mulVec, dotProduct, _root_.sum_apply]
  have hd : HasFDerivAt (fun z => L z + a μ) L y := L.hasFDerivAt.add_const _
  unfold pd
  rw [hf, hd.fderiv]
  simp [hL, _root_.sum_apply, Pi.single_apply]

lemma jac_poincareMap (Λ : Matrix (Fin 4) (Fin 4) ℝ) (a y : Fin 4 → ℝ) :
    jac (poincareMap Λ a) y = Λ := by
  ext μ k
  exact pd_poincareMap Λ a y μ k

/-- **Poincaré transformations are isometries of Minkowski space.** -/
theorem poincare_isometry {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4) (a y : Fin 4 → ℝ) :
    pullback minkCart (poincareMap Λ a) y = minkCart y := by
  rw [pullback_eq_mul, jac_poincareMap]
  simpa [minkCart] using hΛ

/-- **Physlib's Lorentz group gives Lorentz transformations in the project's convention**: for
`Λ ∈ LorentzGroup 3`, the matrix reindexed along `Fin 1 ⊕ Fin 3 ≃ Fin 4` satisfies `Λᵀ η Λ = η`. -/
theorem lorentzGroup_reindex_isLorentz {Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ}
    (hΛ : Λ ∈ LorentzGroup 3) :
    (reindex finSumFinEquiv finSumFinEquiv Λ : Matrix (Fin 4) (Fin 4) ℝ)ᵀ * eta 4 *
      reindex finSumFinEquiv finSumFinEquiv Λ = eta 4 := by
  have h := congrArg (fun M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ =>
      (reindex finSumFinEquiv finSumFinEquiv M : Matrix (Fin 4) (Fin 4) ℝ))
    ((LorentzGroup.mem_iff_transpose_mul_minkowskiMatrix_mul_self Λ).1 hΛ)
  simp only [Lorentz.reindex_fin_mul, Lorentz.reindex_minkowskiMatrix] at h
  simpa [Matrix.mul_neg, Matrix.neg_mul, Matrix.transpose_reindex] using h

/-! ## The compactified metric in Cartesian coordinates -/

/-- The library's `spatialSq` (`Lightlike/Spacetime/Minkowski.lean`) in four dimensions. -/
lemma spatialSq_four (x : Fin 4 → ℝ) : spatialSq x = x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  simp [spatialSq, Fin.sum_univ_three]

/-- The conformal factor `Ω²(x) = 1/((1 + t² + |x⃗|²)² − 4 t² |x⃗|²) = 1/((1 + (t+r)²)(1 + (t−r)²))`. -/
def cfC (x : Fin 4 → ℝ) : ℝ :=
  1 / ((1 + x 0 ^ 2 + spatialSq x) ^ 2 - 4 * x 0 ^ 2 * spatialSq x)

lemma cfC_denom_eq (x : Fin 4 → ℝ) :
    (1 + x 0 ^ 2 + spatialSq x) ^ 2 - 4 * x 0 ^ 2 * spatialSq x =
      (1 + (x 0 + √(spatialSq x)) ^ 2) * (1 + (x 0 - √(spatialSq x)) ^ 2) := by
  have hs : 0 ≤ spatialSq x := by rw [spatialSq_four]; positivity
  have h := Real.sq_sqrt hs
  set r := √(spatialSq x)
  rw [← h]
  ring

lemma cfC_pos (x : Fin 4 → ℝ) : 0 < cfC x := by
  unfold cfC
  rw [cfC_denom_eq]
  positivity

/-- The compactified metric `Ω² η` in Cartesian coordinates. -/
def compactCart (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := cfC x • minkCart x

/-- **Poincaré transformations act conformally on the compactified Minkowski space**: the pullback of the
compactified metric by `x ↦ Λ x + a` is the compactified metric times `Ω²(Λ x + a)/Ω²(x)`. -/
theorem poincare_conformal {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : Λᵀ * eta 4 * Λ = eta 4)
    (a y : Fin 4 → ℝ) :
    pullback compactCart (poincareMap Λ a) y =
      (cfC (poincareMap Λ a y) / cfC y) • compactCart y := by
  have e : compactCart = fun x => cfC x • minkCart x := rfl
  rw [e, pullback_smul_field cfC minkCart, poincare_isometry hΛ, smul_smul,
    div_mul_cancel₀ _ (cfC_pos y).ne']

/-! ## The link with `compactify`: spherical coordinates -/

/-- The spherical chart `(t, r, θ, φ) ↦ (t, r sin θ cos φ, r sin θ sin φ, r cos θ)`. -/
def sph (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![y 0, y 1 * sin (y 2) * cos (y 3), y 1 * sin (y 2) * sin (y 3), y 1 * cos (y 2)]

lemma spatialSq_sph (y : Fin 4 → ℝ) : spatialSq (sph y) = y 1 ^ 2 := by
  have h1 := sin_sq_add_cos_sq (y 2)
  have h2 := sin_sq_add_cos_sq (y 3)
  rw [spatialSq_four]
  simp [sph]
  linear_combination y 1 ^ 2 * sin (y 2) ^ 2 * h2 + y 1 ^ 2 * h1

/-- The conformal factor in spherical coordinates is `conformalFactor`. -/
theorem cfC_sph (y : Fin 4 → ℝ) : cfC (sph y) = conformalFactor y := by
  unfold cfC conformalFactor
  rw [spatialSq_sph]
  have : sph y 0 = y 0 := rfl
  rw [this]
  congr 1
  ring

lemma jac_sph (y : Fin 4 → ℝ) :
    jac sph y =
      !![1, 0, 0, 0;
         0, sin (y 2) * cos (y 3), y 1 * cos (y 2) * cos (y 3), -(y 1 * sin (y 2) * sin (y 3));
         0, sin (y 2) * sin (y 3), y 1 * cos (y 2) * sin (y 3), y 1 * sin (y 2) * cos (y 3);
         0, cos (y 2), -(y 1 * sin (y 2)), 0] := by
  have dA : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => z 1) y := by fun_prop
  have dS : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => sin (z 2)) y := by fun_prop
  have dC : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => cos (z 3)) y := by fun_prop
  have dS' : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => sin (z 3)) y := by fun_prop
  have pA : ∀ k : Fin 4, pd k (fun z => z 1) y = if k = 1 then 1 else 0 := fun k =>
    pd_coord (n := 4) 1 k (hasDerivAt_id' (y 1))
  have pT : ∀ k : Fin 4, pd k (fun z => z 0) y = if k = 0 then 1 else 0 := fun k =>
    pd_coord (n := 4) 0 k (hasDerivAt_id' (y 0))
  have pS : ∀ k : Fin 4, pd k (fun z => sin (z 2)) y = if k = 2 then cos (y 2) else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_sin (y 2))
  have pC : ∀ k : Fin 4, pd k (fun z => cos (z 3)) y = if k = 3 then -sin (y 3) else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_cos (y 3))
  have pS' : ∀ k : Fin 4, pd k (fun z => sin (z 3)) y = if k = 3 then cos (y 3) else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_sin (y 3))
  have p1 : ∀ k, pd k (fun z => z 1 * sin (z 2) * cos (z 3)) y = _ := fun k => pd_triple dA dS dC k
  have p2 : ∀ k, pd k (fun z => z 1 * sin (z 2) * sin (z 3)) y = _ := fun k => pd_triple dA dS dS' k
  have p3 : ∀ k : Fin 4, pd k (fun z => z 1 * cos (z 2)) y =
      (if k = 1 then 1 else 0) * cos (y 2) + y 1 * (if k = 2 then -sin (y 2) else 0) := fun k =>
    pd_coord_mul (n := 4) (f := fun t => t) (g := cos) 1 2 k (hasDerivAt_id' (y 1)) (hasDerivAt_cos (y 2))
  ext μ k
  fin_cases μ <;> fin_cases k <;> simp only [jac, sph] <;>
    simp [pT, p1, p2, p3, pA, pS, pC, pS']

/-- **The spherical chart pulls the Cartesian Minkowski metric back to `minkSph`.** -/
theorem pullback_minkCart_sph (y : Fin 4 → ℝ) : pullback minkCart sph y = minkSph y := by
  rw [pullback_eq_mul, jac_sph]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, minkCart, eta, etaDiag, minkSph, Matrix.diagonal_apply] <;>
    ring_nf <;> simp only [Real.cos_sq'] <;> ring_nf

/-- **The compactified metric in Cartesian coordinates is the compactified Minkowski metric**: pulled back by
the spherical chart, `Ω² η` is the pullback of the Einstein-static-universe metric `compactMetric` by
`compactify` (`pullback_compact`). -/
theorem pullback_compactCart_sph (y : Fin 4 → ℝ) :
    pullback compactCart sph y = pullback compactMetric compactify y := by
  have e : compactCart = fun x => cfC x • minkCart x := rfl
  rw [e, pullback_smul_field cfC minkCart, pullback_minkCart_sph, cfC_sph, pullback_compact]

/-! ## The time translation on null infinity -/

/-- The time translation `t ↦ t + a` in a compactified null coordinate `ũ = arctan u`: `ũ ↦ arctan(tan ũ + a)`. -/
def timeShift (a u : ℝ) : ℝ := arctan (tan u + a)

/-- **The time translation in compactified coordinates.** Translating `t` by `a` moves `ũ± = T ± R` by
`timeShift a`. -/
theorem compactify_timeShift (a : ℝ) (y : Fin 4 → ℝ) :
    compactify (y + Pi.single 0 a) 0 + compactify (y + Pi.single 0 a) 1 =
        timeShift a (compactify y 0 + compactify y 1) ∧
      compactify (y + Pi.single 0 a) 0 - compactify (y + Pi.single 0 a) 1 =
        timeShift a (compactify y 0 - compactify y 1) := by
  have hp : ∀ z : Fin 4 → ℝ, compactify z 0 + compactify z 1 = arctan (z 0 + z 1) := fun z => by
    simp [compactify]; ring
  have hm : ∀ z : Fin 4 → ℝ, compactify z 0 - compactify z 1 = arctan (z 0 - z 1) := fun z => by
    simp [compactify]; ring
  refine ⟨?_, ?_⟩
  · rw [hp, hp, timeShift, Real.tan_arctan]
    simp; ring_nf
  · rw [hm, hm, timeShift, Real.tan_arctan]
    simp; ring_nf

/-- **The time translation extends to future null infinity and fixes it**: `timeShift a ũ → π/2` as
`ũ → π/2` from below (future null infinity `I⁺` is `ũ₊ = π/2`). -/
theorem tendsto_timeShift_scri (a : ℝ) :
    Tendsto (timeShift a) (𝓝[<] (π / 2)) (𝓝 (π / 2)) := by
  have h1 : Tendsto (fun u => tan u + a) (𝓝[<] (π / 2)) atTop :=
    tendsto_atTop_add_const_right _ a Real.tendsto_tan_pi_div_two
  exact (Real.tendsto_arctan_atTop.comp h1).mono_right nhdsWithin_le_nhds

/-- **The generator of the time translation is `cos² ũ ∂_ũ`** (`= ∂_u`, since `∂_ũ = (1 + u²) ∂_u`,
AGMOO (2.12)); it vanishes on null infinity `ũ = ±π/2`. -/
theorem hasDerivAt_timeShift {u : ℝ} (hu : cos u ≠ 0) :
    HasDerivAt (fun a => timeShift a u) (cos u ^ 2) 0 := by
  have h := (Real.hasDerivAt_arctan (tan u + 0)).comp (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).const_add (tan u))
  unfold timeShift
  refine h.congr_deriv ?_
  rw [add_zero, Real.tan_eq_sin_div_cos]
  have hc := sin_sq_add_cos_sq u
  field_simp
  linarith

end Lightlike
