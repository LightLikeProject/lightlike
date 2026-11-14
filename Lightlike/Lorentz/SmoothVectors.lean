module

public import Lightlike.Lorentz.SpinVectors

/-!
# The Casimirs on the SU(2)-finite vectors

The vectors `hvec p q ρ x` of `SpinVectors.lean` are smooth on `ℂ² ∖ 0` (`contDiffAt_hvec`):
`N^{iρ-1}` and `N^{-(p+q)/2}` are smooth where `N = |ζ₀|² + |ζ₁|² > 0`, and the contraction `Λ`
is a polynomial in the real coordinates. So the Casimir theorems of `Homogeneous.lean` apply to
them: **on every SU(2)-finite vector of the unitary principal series `(k, ρ)`, `ρ ∈ ℝ`,
`C₁ = k² - ρ² - 1` and `C₂ = kρ`** (`casimir1_hvec`, `casimir2_hvec`). By
`SU2Decomposition.lean` these vectors span a dense subspace of `L²(ℂ)`.

Reference: J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, F. Hellmann, R. Pereira, *Lorentzian
spin foam amplitudes: graphical calculus and asymptotics*, Class. Quantum Grav. 27 (2010) 165009.
-/

@[expose] public section

open Matrix Complex Filter Topology
open scoped ComplexConjugate

namespace Lightlike.Lorentz

open Lightlike.SU2

lemma contDiff_coord (c : Fin 2) : ContDiff ℝ 2 fun ζ : C2 => ζ c :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) c).contDiff

lemma contDiff_nsq : ContDiff ℝ 2 nsq := by
  unfold nsq
  exact ((contDiff_norm_sq ℝ).comp (contDiff_coord 0)).add
    ((contDiff_norm_sq ℝ).comp (contDiff_coord 1))

lemma nsq_pos {ζ : C2} (hζ : ζ ≠ 0) : 0 < nsq ζ := by
  refine lt_of_le_of_ne (nsq_nonneg ζ) fun h0 => hζ ?_
  have h0' : ‖ζ 0‖ ^ 2 + ‖ζ 1‖ ^ 2 = 0 := h0.symm
  have a : ‖ζ 0‖ = 0 := by nlinarith [sq_nonneg ‖ζ 0‖, sq_nonneg ‖ζ 1‖, norm_nonneg (ζ 0)]
  have b : ‖ζ 1‖ = 0 := by nlinarith [sq_nonneg ‖ζ 0‖, sq_nonneg ‖ζ 1‖, norm_nonneg (ζ 1)]
  ext i; fin_cases i
  · exact norm_eq_zero.mp a
  · exact norm_eq_zero.mp b

lemma eventually_nsq_pos {ζ : C2} (hζ : ζ ≠ 0) : ∀ᶠ ζ' in 𝓝 ζ, 0 < nsq ζ' :=
  (contDiff_nsq.continuous.tendsto ζ).eventually (lt_mem_nhds (nsq_pos hζ))

lemma contDiffAt_cpow_nsq (c : ℂ) {ζ : C2} (hζ : ζ ≠ 0) :
    ContDiffAt ℝ 2 (fun ζ => ((nsq ζ : ℝ) : ℂ) ^ c) ζ := by
  have heq : (fun ζ => ((nsq ζ : ℝ) : ℂ) ^ c) =ᶠ[𝓝 ζ]
      fun ζ => cexp (((Real.log (nsq ζ) : ℝ) : ℂ) * c) := by
    filter_upwards [eventually_nsq_pos hζ] with ζ' h'
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast h'.ne'), ← Complex.ofReal_log h'.le]
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  refine ContDiffAt.cexp (ContDiffAt.mul ?_ contDiffAt_const)
  have hlog : ContDiffAt ℝ 2 (fun ζ => Real.log (nsq ζ)) ζ :=
    (Real.contDiffAt_log.mpr (nsq_pos hζ).ne').comp ζ contDiff_nsq.contDiffAt
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp ζ hlog

lemma contDiffAt_sqrt_inv_pow (m : ℕ) {ζ : C2} (hζ : ζ ≠ 0) :
    ContDiffAt ℝ 2 (fun ζ => (((Real.sqrt (nsq ζ))⁻¹ ^ m : ℝ) : ℂ)) ζ := by
  have hs : ContDiffAt ℝ 2 (fun ζ => Real.sqrt (nsq ζ)) ζ :=
    (Real.contDiffAt_sqrt (nsq_pos hζ).ne').comp ζ contDiff_nsq.contDiffAt
  have hi : ContDiffAt ℝ 2 (fun ζ => (Real.sqrt (nsq ζ))⁻¹) ζ :=
    (contDiffAt_inv ℝ (Real.sqrt_pos.mpr (nsq_pos hζ)).ne').comp ζ hs
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (hi.pow m)

lemma contDiff_lform_apply (p q : ℕ) (i : Fin (p + q)) (c : Fin 2) :
    ContDiff ℝ 2 fun ζ : C2 => lform p q i ζ c := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [lform] using contDiff_coord c
  · simp only [lform, Fin.addCases_right]
    have hc : ∀ d : Fin 2, ContDiff ℝ 2 fun ζ : C2 => conj (ζ d) := fun d =>
      Complex.conjCLE.contDiff.comp (contDiff_coord d)
    fin_cases c
    · simpa [epsConj] using hc 1
    · simpa [epsConj] using (hc 0).neg

lemma contDiff_lam (p q : ℕ) (v : Str (p + q) → ℂ) : ContDiff ℝ 2 (lam p q v) := by
  unfold lam
  exact ContDiff.sum fun t _ =>
    contDiff_const.mul (contDiff_prod fun i _ => contDiff_lform_apply p q i (t i))

/-- **The SU(2)-finite vectors are smooth** on `ℂ² ∖ 0`. -/
theorem contDiffAt_hvec (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) {ζ : C2} (hζ : ζ ≠ 0) :
    ContDiffAt ℝ 2 (hvec p q ρ x) ζ :=
  ((contDiffAt_cpow_nsq _ hζ).mul (contDiffAt_sqrt_inv_pow _ hζ)).mul
    (contDiff_lam p q _).contDiffAt

/-- **First Casimir on the SU(2)-finite vectors** of the unitary principal series:
`C₁ = k² - ρ² - 1`. -/
theorem casimir1_hvec {n : ℤ} {p q : ℕ} (hpq : (p : ℤ) - q = n) (ρ : ℝ)
    (x : Fin (p + q + 1) → ℂ) {ζ : C2} (hζ : ζ ≠ 0) :
    casimir1 (hvec p q ρ x) ζ = ((n / 2 : ℂ) ^ 2 - (ρ : ℂ) ^ 2 - 1) * hvec p q ρ x ζ :=
  casimir1_eq (isHomog_hvec hpq ρ x) hζ (contDiffAt_hvec p q ρ x hζ)

/-- **Second Casimir on the SU(2)-finite vectors** of the unitary principal series: `C₂ = kρ`. -/
theorem casimir2_hvec {n : ℤ} {p q : ℕ} (hpq : (p : ℤ) - q = n) (ρ : ℝ)
    (x : Fin (p + q + 1) → ℂ) {ζ : C2} (hζ : ζ ≠ 0) :
    casimir2 (hvec p q ρ x) ζ = ((n / 2 : ℂ) * ρ) * hvec p q ρ x ζ :=
  casimir2_eq (isHomog_hvec hpq ρ x) hζ (contDiffAt_hvec p q ρ x hζ)

end Lightlike.Lorentz
