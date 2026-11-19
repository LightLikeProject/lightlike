import Lightlike.Poincare.CommutantCone

/-!
# The massless one-particle representations are irreducible

On `L²(ν)` of the forward light cone, for every `SL(2,ℂ)`-invariant σ-finite measure `ν` and every helicity `n/2`,
every bounded operator commuting with the translations and with the induced action `U(A)` is a scalar
(`commutant_eq_scalar_cone`), and every closed subspace invariant under both is `0` or everything
(`irreducible_massless`). Steps: the operator is the multiplication by a measurable function `m`
(`exists_mulField_of_commute_transl_cone`); the helicity factor is unimodular, so covariance gives `m(A⁻¹ P) = m(P)`
almost everywhere for each `A` (`mulField_invariant`); `A ↦ m(A • K)` is then almost everywhere invariant under
every left translation of `SL(2,ℂ)`, hence almost everywhere constant (ergodicity of the left regular action), and `ν`
has the null sets of the image of the Haar measure (`absolutelyContinuous_coneHaar`).

## References

* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §6, Theorem 6.2, page 149.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology
open scoped InnerProductSpace

namespace Lightlike.Poincare

noncomputable section

variable {ν : Measure LightCone}

/-- **Covariance**: if `B` commutes with every `U(A)` and is the multiplication by `m`, then `m(P) = m(A⁻¹ P)`
almost everywhere. -/
lemma mulField_invariant [SigmaFinite ν] (n : ℤ)
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (M : LightCone → ℂ) (hM : ∀ f : Lp ℂ 2 ν, (B f : LightCone → ℂ) =ᵐ[ν] fun Q => M Q * f Q)
    (hU : ∀ A f, B (helL2 n hν A f) = helL2 n hν A (B f)) (A : SL2C) :
    ∀ᵐ Q ∂ν, M Q = M (A⁻¹ • Q) := by
  obtain ⟨w, hwpos, hwm, hwL⟩ := exists_posWeight_cone (ν := ν)
  set W : Lp ℂ 2 ν := hwL.toLp _
  have hW : (W : LightCone → ℂ) =ᵐ[ν] fun Q => (w Q : ℂ) := hwL.coeFn_toLp
  have h1 := hM (helL2 n hν A W)
  have h3 := coeFn_helL2 n hν A W
  have h4 := coeFn_helL2 n hν A (B W)
  have h5 := (hν A⁻¹).quasiMeasurePreserving.ae_eq_comp (hM W)
  have h6 := (hν A⁻¹).quasiMeasurePreserving.ae_eq_comp hW
  filter_upwards [h1, h3, h4, h5, h6] with Q e1 e3 e4 e5 e6
  rw [hU, e4, e3] at e1
  simp only [Function.comp_apply] at e5 e6
  rw [e5, e6] at e1
  have hh : helMult n A Q ≠ 0 := by
    intro h
    have := norm_helMult n A Q
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hw : ((w (A⁻¹ • Q) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hwpos _).ne'
  have h0 : (M Q - M (A⁻¹ • Q)) * (helMult n A Q * (w (A⁻¹ • Q) : ℂ)) = 0 := by linear_combination -e1
  rcases mul_eq_zero.1 h0 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (mul_ne_zero hh hw)

/-- **Irreducibility of the massless one-particle representations (Schur form)**: on `L²` of the light cone for an
invariant σ-finite measure, every bounded operator commuting with the translations and with the induced action
`U(A)` of helicity `n/2` is a scalar. -/
theorem commutant_eq_scalar_cone [SigmaFinite ν] (n : ℤ)
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν) (B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hT : ∀ a f, B (translCone a f) = translCone a (B f))
    (hU : ∀ A f, B (helL2 n hν A f) = helL2 n hν A (B f)) :
    ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ _ := by
  by_cases hν0 : ν = 0
  · subst hν0
    refine ⟨0, ?_⟩
    ext f : 1
    apply Lp.ext
    rw [EventuallyEq, ae_zero]
    exact Filter.eventually_bot
  obtain ⟨M, hMm, hM⟩ := exists_mulField_of_commute_transl_cone B hT
  have hinv : ∀ A : SL2C, ∀ᵐ P ∂ν, M (A • P) = M P := by
    intro A
    have h := (hν A).quasiMeasurePreserving.ae (mulField_invariant n hν B M hM hU A)
    filter_upwards [h] with P hP
    rw [hP, inv_smul_smul]
  have hinv' : ∀ A : SL2C, ∀ᵐ P ∂coneHaar, M (A • P) = M P := fun A =>
    (coneHaar_absolutelyContinuous hν hν0).ae_le (hinv A)
  have hφm : Measurable fun A : SL2C => M (coneOrbit A) := hMm.comp continuous_coneOrbit.measurable
  obtain ⟨c, hc⟩ := ae_eq_const_of_forall_ae_eq_mul_left (ν := SL2C.haar) hφm fun A' => by
    have h := ae_of_ae_map continuous_coneOrbit.aemeasurable (hinv' A')
    filter_upwards [h] with A hA
    change M ((A' * A) • coneBase) = M (A • coneBase)
    rw [mul_smul]
    exact hA
  have hset : MeasurableSet {P : LightCone | M P = c} := hMm (measurableSet_singleton c)
  have hMc : ∀ᵐ P ∂ν, M P = c := (absolutelyContinuous_coneHaar hν).ae_le
    ((ae_map_iff continuous_coneOrbit.aemeasurable hset).2 hc)
  refine ⟨c, ?_⟩
  ext f : 1
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply]
  apply Lp.ext
  filter_upwards [hM f, hMc, Lp.coeFn_smul c f] with Q h1 h2 h3
  rw [h1, h2, h3, Pi.smul_apply, smul_eq_mul]

/-- **The massless one-particle representations are irreducible**: on `L²` of the light cone for an invariant
σ-finite measure, a closed subspace invariant under every translation and every `U(A)` of helicity `n/2` is `0` or
everything. -/
theorem irreducible_massless [SigmaFinite ν] (n : ℤ)
    (hν : ∀ A : SL2C, MeasurePreserving (fun Q : LightCone => A • Q) ν ν)
    (K : Submodule ℂ (Lp ℂ 2 ν)) (hK : IsClosed (K : Set (Lp ℂ 2 ν)))
    (hT : ∀ a, ∀ f ∈ K, translCone a f ∈ K) (hU : ∀ A, ∀ f ∈ K, helL2 n hν A f ∈ K) : K = ⊥ ∨ K = ⊤ := by
  haveI : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨c, hc⟩ := commutant_eq_scalar_cone n hν K.starProjection
    (fun a f => starProjection_map_eq K (translCone a) (translCone (-a))
      (fun x => by rw [← translCone_add, neg_add_cancel, translCone_zero]) (hT a) (hT (-a)) f)
    (fun A f => starProjection_map_eq K (helL2 n hν A) (helL2 n hν A⁻¹)
      (fun x => by rw [← helL2_mul, inv_mul_cancel, helL2_one]) (hU A) (hU A⁻¹) f)
  by_cases hc0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro k hk
    have h := K.starProjection_eq_self_iff.2 hk
    rw [hc, hc0] at h
    simpa using h.symm
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have hx := K.starProjection_apply_mem (c⁻¹ • x)
    rw [hc] at hx
    simpa [smul_smul, inv_mul_cancel₀ hc0] using hx

end

end Lightlike.Poincare
