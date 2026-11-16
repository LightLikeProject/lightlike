import Lightlike.Lorentz.EPRL
import Lightlike.Lorentz.SU2Decomposition
import Lightlike.Asymptotics.Lorentzian.Amplitude

/-!
# The coherent Lorentzian vertex and the principal-series vertex

First steps of the identification of `lorVertex` (BDFHP coherent form) with `eprlVertex`
(`Lightlike.Lorentz.EPRL`, after Engle and Pereira 2009): the contraction `Λ` of the lowest SU(2)
level of the principal series on a coherent state is a power of a linear form.
-/

open Matrix Complex
open scoped ComplexConjugate
open Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz

namespace Lightlike.Asymptotics.Lorentzian

/-- With no antilinear factors, every linear form is `ζ`. -/
theorem lform_zero (p : ℕ) (i : Fin (p + 0)) (ζ : Fin 2 → ℂ) : lform p 0 i ζ = ζ := by
  induction i using Fin.addCases with
  | left j =>
    unfold lform
    exact Fin.addCases_left (motive := fun _ => Fin 2 → ℂ) j
  | right j => exact j.elim0

/-- The column of `emb n` at the lowest level is the indicator of the zero string. -/
theorem emb_mulVec_single_zero (n : ℕ) :
    emb n *ᵥ (Pi.single 0 1 : Fin (n + 1) → ℂ) = Pi.single (fun _ => 0) 1 := by
  have hdowns : ∀ s : Str n, downs s = 0 ↔ s = fun _ => 0 := by
    intro s
    unfold downs
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro h; funext i; have := h (Finset.mem_univ i); omega
    · intro h i _; rw [h]; simp
  have hnrm : nrm n 0 = 1 := by
    unfold nrm clsCard cls
    have : (Finset.univ.filter fun s : Str n => downs s = 0) = {fun _ => 0} := by
      ext s; simp [hdowns]
    rw [this]; simp
  funext s
  rw [mulVec_single_one]
  show emb n s 0 = _
  rw [emb_apply]
  by_cases hs : s = fun _ => 0
  · subst hs; simp [hnrm, hdowns]
  · have : ¬ downs s = 0 := fun h => hs ((hdowns s).mp h)
    simp [this, hs, Pi.single_apply]

/-- **The lowest level on a coherent state**: `Λ(emb (g^{⊗n} e₀))(ζ) = (g₀₀ ζ₀ + g₁₀ ζ₁)^n`, the
`n`-th power of the pairing of `ζ` with the first column of `g`. -/
theorem lam_emb_cohState (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) (ζ : Fin 2 → ℂ) :
    lam n 0 (emb (n + 0) *ᵥ cohState n g) ζ = (g 0 0 * ζ 0 + g 1 0 * ζ 1) ^ n := by
  have h : emb n *ᵥ cohState n g = kron n g *ᵥ Pi.single (fun _ => 0) 1 := by
    rw [cohState, mulVec_mulVec, ← kron_mul_emb, ← mulVec_mulVec, emb_mulVec_single_zero]
  change lam n 0 (emb n *ᵥ cohState n g) ζ = _
  rw [h]
  have hk : ∀ t : Str n, (kron n g *ᵥ (Pi.single (fun _ => 0) 1 : Str n → ℂ)) t =
      ∏ i, g (t i) 0 := fun t => by
    rw [mulVec_single_one]; rfl
  have h3 : lam n 0 (kron n g *ᵥ (Pi.single (fun _ => 0) 1 : Str n → ℂ)) ζ =
      ∑ t : Str n, ∏ i, (g (t i) 0 * ζ (t i)) := by
    unfold lam
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [lform_zero]
    rw [hk t, Finset.prod_mul_distrib]
    rfl
  have h4 := (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 2)))
    (fun (_ : Fin n) (a : Fin 2) => g a 0 * ζ a)).symm
  rw [Fintype.piFinset_univ] at h4
  rw [h3, h4]
  simp [Fin.sum_univ_two]

/-- **`suV` as a function on the chart**: the isometry of the SU(2) decomposition is, almost
everywhere on the chart `z ↦ (z, 1)`, the constant `(‖A e₀‖)⁻¹` times the weight and the contraction
`Λ`, where `A = tlin` is the explicit intertwiner of `Lightlike.Lorentz.SpinVectors`. -/
theorem suV_ae (n : ℤ) (ρ : ℝ) (ℓ : ℕ) (x : Espace (dsp n ℓ)) :
    (suV n ρ ℓ x : ℂ → ℂ) =ᵐ[MeasureTheory.volume] fun z =>
      ((nrmA (tlin (ℓ + p0 n) (ℓ + q0 n) ρ))⁻¹ : ℂ) *
        (wgt (ℓ + p0 n) (ℓ + q0 n) ρ z *
          lam (ℓ + p0 n) (ℓ + q0 n) (emb ((ℓ + p0 n) + (ℓ + q0 n)) *ᵥ x.ofLp) ![z, 1]) := by
  unfold suV
  rw [normalize_apply]
  have h1 : (tlin (ℓ + p0 n) (ℓ + q0 n) ρ x.ofLp : ℂ → ℂ) =ᵐ[MeasureTheory.volume]
      tfun (ℓ + p0 n) (ℓ + q0 n) ρ x.ofLp :=
    MeasureTheory.MemLp.coeFn_toLp (memLp_tfun (ℓ + p0 n) (ℓ + q0 n) ρ x.ofLp)
  filter_upwards [MeasureTheory.Lp.coeFn_smul (((nrmA (tlin (ℓ + p0 n) (ℓ + q0 n) ρ))⁻¹ : ℂ))
    (tlin (ℓ + p0 n) (ℓ + q0 n) ρ x.ofLp), h1] with z hz1 hz2
  rw [hz1, Pi.smul_apply, hz2, smul_eq_mul]
  unfold tfun
  rw [chart_hvec]

/-- **The pairing of two boosted functions as an integral over the chart**: for homogeneous `F`,
`G` of the same degree with `L²` charts,
`⟪π(a) [F], π(b) [G]⟫ = ∫ conj(F(aᵀ(z, 1))) G(bᵀ(z, 1)) dz`. -/
theorem inner_principalSeries_eq_integral (n : ℤ) (ρ : ℝ) (a b : SL2C) {F G : C2 → ℂ}
    (hF : IsHomog n ρ F) (hG : IsHomog n ρ G)
    (hFm : MeasureTheory.MemLp (chart F) 2 MeasureTheory.volume)
    (hGm : MeasureTheory.MemLp (chart G) 2 MeasureTheory.volume) :
    inner ℂ (principalSeries n ρ a (hFm.toLp (chart F))) (principalSeries n ρ b (hGm.toLp (chart G))) =
      ∫ z : ℂ, conj (F ((a : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ![z, 1])) *
        G ((b : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ![z, 1]) := by
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  have h1 := coeFn_principalSeries n ρ a (hFm.toLp (chart F))
  have h2 := coeFn_principalSeries n ρ b (hGm.toLp (chart G))
  have h3 := ae_eq_comp_mob a (MeasureTheory.MemLp.coeFn_toLp hFm)
  have h4 := ae_eq_comp_mob b (MeasureTheory.MemLp.coeFn_toLp hGm)
  filter_upwards [h1, h2, h3, h4, ae_den_ne_zero a, ae_den_ne_zero b] with z z1 z2 z3 z4 da db
  simp only [Function.comp_apply] at z3 z4
  have ea := chart_actH hF a da
  have eb := chart_actH hG b db
  simp only [chart, actH] at ea eb
  rw [RCLike.inner_apply, z1, z2, z3, z4]
  simp only [act, chart] at ea eb ⊢
  rw [← ea, ← eb]
  ring

end Lightlike.Asymptotics.Lorentzian
