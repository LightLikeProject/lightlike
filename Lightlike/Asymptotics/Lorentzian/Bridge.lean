import Lightlike.Lorentz.EPRL
import Lightlike.Lorentz.SU2Decomposition
import Lightlike.Asymptotics.Lorentzian.Amplitude
import Lightlike.SpinFoam.Tetrahedron

/-!
# The coherent Lorentzian vertex and the principal-series vertex

Steps towards the identification of `lorVertex` (BDFHP, arXiv:0907.2440, §3.2–3.3 and §4, eq. (17))
with `Lightlike.Lorentz.eprlVertex` (after Engle and Pereira, arXiv:0805.4696, eqs. (22), (23)),
which is finite for every spin (`integrable_eprlIntegrand`):

* `lam_emb_cohState`: the contraction `Λ` of the lowest SU(2) level of the principal series on a
  coherent state is the `n`-th power of a linear form, `(g₀₀ ζ₀ + g₁₀ ζ₁)^n`;
* `suV_ae`: the isometry `suV` of the SU(2) decomposition is, on the chart `z ↦ (z, 1)` and almost
  everywhere, the constant `(‖A e₀‖)⁻¹` times the weight and `Λ`;
* `hvec_cohState`: the explicit homogeneous function of a coherent state of the lowest level;
* `inner_principalSeries_eq_integral`: the pairing of two boosted homogeneous functions is an
  integral over the chart;
* `exp_triAction_nat`: for `2k = n`, `e^S` of the power-form action is the product of
  `(⟨Z,ξ⟩⟨Jξ',Z'⟩)^n`, `(‖Z‖²‖Z'‖²)^{-n/2}` and `(‖Z'‖²/‖Z‖²)^{iρ}`.

**Not here:** the identity `eprlVertex = lorVertex` itself. It needs the pointwise identity of the
two integrands (with `X = conj a`, the source spinor `firstCol (conj g)` and the target spinor
`firstCol (wM g)`), the sum over the magnetic configurations, and Fubini over `SL(2,ℂ)^4 × ℂ^10`;
the normalisation constants of `suV` stay abstract (`nrmA`).
-/

open Matrix Complex
open scoped ComplexConjugate
open Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz Lightlike.SpinFoam

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

/-- **The coherent function of the lowest level**: `hvec n 0 ρ (|n/2, g⟩)` is
`N^{iρ-1} N^{-n/2} (g₀₀ ζ₀ + g₁₀ ζ₁)^n` with `N = ‖ζ‖²`. -/
theorem hvec_cohState (n : ℕ) (ρ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) (ζ : C2) :
    hvec n 0 ρ (cohState n g) ζ =
      ((nsq ζ : ℝ) : ℂ) ^ (I * ρ - 1) * (((Real.sqrt (nsq ζ))⁻¹ ^ n : ℝ) : ℂ) *
        (g 0 0 * ζ 0 + g 1 0 * ζ 1) ^ n := by
  unfold hvec
  rw [← lam_emb_cohState n g ζ]
  rfl

/-- **The exponential of the one-triangle action for `2k = n`** (BDFHP (17), power form): where
the overlaps and spinors are nonzero,
`e^S = (⟨Z,ξ⟩⟨Jξ',Z'⟩)^n · ((‖Z‖²‖Z'‖²)^{-n/2}) · (‖Z'‖²/‖Z‖²)^{iρ}`. -/
theorem exp_triAction_nat {n : ℕ} {p : ℝ} {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0) (hZ' : Z' ≠ 0)
    (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    Complex.exp (triAction ((n : ℝ) / 2) p Z ξ Z' ξ') =
      (inner ℂ Z ξ * inner ℂ (jMap ξ') Z') ^ n *
        ((((‖Z‖ ^ 2 * ‖Z'‖ ^ 2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ)) : ℂ) *
        ((((‖Z'‖ ^ 2 / ‖Z‖ ^ 2 : ℝ) : ℝ) : ℂ) ^ (I * p)) := by
  have hz : 0 < ‖Z‖ := norm_pos_iff.mpr hZ
  have hz' : 0 < ‖Z'‖ := norm_pos_iff.mpr hZ'
  have hab : inner ℂ Z ξ * inner ℂ (jMap ξ') Z' ≠ 0 := mul_ne_zero h1 h2
  have hr : 0 < ‖Z‖ ^ 2 * ‖Z'‖ ^ 2 := by positivity
  have hq : 0 < ‖Z'‖ ^ 2 / ‖Z‖ ^ 2 := by positivity
  have e1 : Complex.exp (((2 * ((n : ℝ) / 2) : ℝ) : ℂ) *
      Complex.log (inner ℂ Z ξ * inner ℂ (jMap ξ') Z')) =
      (inner ℂ Z ξ * inner ℂ (jMap ξ') Z') ^ n := by
    have : ((2 * ((n : ℝ) / 2) : ℝ) : ℂ) = (n : ℂ) := by push_cast; ring
    rw [this, Complex.exp_nat_mul, Complex.exp_log hab]
  have e2 : Complex.exp (-(((n : ℝ) / 2 : ℝ) : ℂ) *
      Complex.log (((‖Z‖ ^ 2 : ℝ) : ℂ) * ((‖Z'‖ ^ 2 : ℝ) : ℂ))) =
      (((‖Z‖ ^ 2 * ‖Z'‖ ^ 2 : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
    have h : ((‖Z‖ ^ 2 : ℝ) : ℂ) * ((‖Z'‖ ^ 2 : ℝ) : ℂ) = (((‖Z‖ ^ 2 * ‖Z'‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast; rfl
    rw [h, ← Complex.ofReal_log hr.le, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp, Real.rpow_def_of_pos hr]
    congr 2
    ring
  have e3 : Complex.exp (I * (p : ℂ) * Complex.log (((‖Z'‖ ^ 2 : ℝ) : ℂ) / ((‖Z‖ ^ 2 : ℝ) : ℂ))) =
      (((‖Z'‖ ^ 2 / ‖Z‖ ^ 2 : ℝ) : ℝ) : ℂ) ^ (I * p) := by
    have h : ((‖Z'‖ ^ 2 : ℝ) : ℂ) / ((‖Z‖ ^ 2 : ℝ) : ℂ) = (((‖Z'‖ ^ 2 / ‖Z‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast; rfl
    rw [h, Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne')]
    congr 1; ring
  unfold triAction
  have : ∀ A B C : ℂ, Complex.exp (A - B + C) = Complex.exp A * Complex.exp (-B) * Complex.exp C := by
    intro A B C; rw [Complex.exp_add, Complex.exp_sub, div_eq_mul_inv, ← Complex.exp_neg]
  rw [this, e1, ← e2, ← e3]
  congr 3
  ring

/-- `‖aᵀ ζ‖²` of a transposed action on the chart is `nsq`, and `spinAct` is `mulVec`. -/
theorem spinAct_lorSpinor_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) (i : Fin 2) :
    spinAct M (lorSpinor w) i = (M *ᵥ ![w, 1]) i := by
  fin_cases i <;> simp [spinAct, lorSpinor, mulVec, dotProduct, Fin.sum_univ_two]

theorem norm_sq_spinAct_lorSpinor (M : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) :
    ‖spinAct M (lorSpinor w)‖ ^ 2 = nsq (M *ᵥ ![w, 1]) := by
  rw [EuclideanSpace.norm_sq_eq, nsq]
  simp [Fin.sum_univ_two, spinAct_lorSpinor_apply]

/-- The conjugate of a positive real to a complex power. -/
theorem conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    conj (((x : ℝ) : ℂ) ^ s) = ((x : ℝ) : ℂ) ^ (conj s) := by
  have h : (((x : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm
  have := Complex.cpow_conj (((x : ℝ) : ℂ)) s h
  rw [this, Complex.conj_ofReal]

/-- The real prefactor `(√N⁻¹)^n` is `N^{-n/2}`. -/
theorem sqrt_inv_pow_eq_rpow {N : ℝ} (hN : 0 < N) (n : ℕ) :
    (Real.sqrt N)⁻¹ ^ n = N ^ (-(n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hN.le, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1; ring

/-- **The weights of the two ends of a link**: for `Na, Nb > 0`,
`conj(Na^{iρ-1}) Nb^{iρ-1} = (Nb/Na)^{iρ} (Na Nb)⁻¹`. -/
theorem weight_pair {Na Nb : ℝ} (ha : 0 < Na) (hb : 0 < Nb) (ρ : ℝ) :
    conj (((Na : ℝ) : ℂ) ^ (I * ρ - 1)) * (((Nb : ℝ) : ℂ) ^ (I * ρ - 1)) =
      ((((Nb / Na : ℝ)) : ℂ) ^ (I * ρ)) * (((Na * Nb)⁻¹ : ℝ) : ℂ) := by
  rw [conj_ofReal_cpow ha]
  have hc : conj (I * (ρ : ℂ) - 1) = -(I * ρ) - 1 := by
    simp [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [hc, Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hb.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (div_pos hb ha).ne'),
    ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le, ← Complex.ofReal_log (div_pos hb ha).le,
    Real.log_div hb.ne' ha.ne']
  have hinv : (((Na * Nb)⁻¹ : ℝ) : ℂ) =
      Complex.exp (-(Real.log Na : ℂ) - (Real.log Nb : ℂ)) := by
    have : (Na * Nb)⁻¹ = Real.exp (-Real.log Na - Real.log Nb) := by
      rw [show -Real.log Na - Real.log Nb = -(Real.log Na + Real.log Nb) by ring,
        Real.exp_neg, ← Real.log_mul ha.ne' hb.ne', Real.exp_log (mul_pos ha hb)]
    rw [this, Complex.ofReal_exp]; push_cast; rfl
  rw [hinv, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The integrand of one link, pointwise**: for the transported chart vectors
`ζ_a = A (w, 1)`, `ζ_b = B (w, 1)` with `N_a = ‖ζ_a‖² > 0`, `N_b = ‖ζ_b‖² > 0`,
`conj F_{g₁}(ζ_a) · F_{g₂}(ζ_b) = (conj P_a · P_b)^n (N_a N_b)^{-n/2} (N_b/N_a)^{iρ} (N_a N_b)⁻¹`,
with `F_g = hvec n 0 ρ (|n/2, g⟩)` and `P_a = g₁₀₀ ζ_{a0} + g₁₁₀ ζ_{a1}`, and likewise for `P_b`. -/
theorem link_pointwise (n : ℕ) (ρ : ℝ) (g1 g2 : Matrix (Fin 2) (Fin 2) ℂ) (ζa ζb : C2)
    (ha : 0 < nsq ζa) (hb : 0 < nsq ζb) :
    conj (hvec n 0 ρ (cohState n g1) ζa) * hvec n 0 ρ (cohState n g2) ζb =
      (conj (g1 0 0 * ζa 0 + g1 1 0 * ζa 1) * (g2 0 0 * ζb 0 + g2 1 0 * ζb 1)) ^ n *
        ((((nsq ζa * nsq ζb) ^ (-(n : ℝ) / 2) : ℝ)) : ℂ) *
        (((((nsq ζb / nsq ζa : ℝ)) : ℂ) ^ (I * ρ)) * (((nsq ζa * nsq ζb)⁻¹ : ℝ) : ℂ)) := by
  rw [hvec_cohState, hvec_cohState, map_mul, map_mul, map_pow]
  have hr1 : (conj ((((Real.sqrt (nsq ζa))⁻¹ ^ n : ℝ)) : ℂ)) = (((Real.sqrt (nsq ζa))⁻¹ ^ n : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [hr1, sqrt_inv_pow_eq_rpow ha, sqrt_inv_pow_eq_rpow hb]
  have hw := weight_pair ha hb ρ
  have hrp : (nsq ζa * nsq ζb) ^ (-(n : ℝ) / 2) =
      nsq ζa ^ (-(n : ℝ) / 2) * nsq ζb ^ (-(n : ℝ) / 2) :=
    Real.mul_rpow ha.le hb.le
  rw [hrp, Complex.ofReal_mul, mul_pow]
  linear_combination (conj (g1 0 0 * ζa 0 + g1 1 0 * ζa 1) ^ n * (g2 0 0 * ζb 0 + g2 1 0 * ζb 1) ^ n *
    ((nsq ζa ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * ((nsq ζb ^ (-(n : ℝ) / 2) : ℝ) : ℂ)) * hw

/-- The overlap `⟨Z, ξ⟩` with the source spinor `ξ = first column of ḡ` is the conjugate of the
pairing `P = g₀₀ Z₀ + g₁₀ Z₁`. -/
theorem inner_firstCol_map_star (Z : Spinor) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    inner ℂ Z (firstCol (g.map star)) = conj (g 0 0 * Z 0 + g 1 0 * Z 1) := by
  simp [firstCol, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The overlap `⟨J ξ', Z'⟩` with the target spinor `ξ' = first column of w g` is the pairing
`P' = g₀₀ Z'₀ + g₁₀ Z'₁`. -/
theorem inner_jMap_firstCol_wM (Z : Spinor) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    inner ℂ (jMap (firstCol (wM * g))) Z = g 0 0 * Z 0 + g 1 0 * Z 1 := by
  simp [firstCol, jMap, wM, PiLp.inner_apply, Fin.sum_univ_two, mul_comm, Matrix.mul_apply]

end Lightlike.Asymptotics.Lorentzian
