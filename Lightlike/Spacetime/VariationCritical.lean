import Lightlike.Spacetime.VariationIntegral

/-!
# Critical points of the Einstein-Hilbert action (GE15, stage S4)

`IsEHCritical g Λ`: the first variation of `∫ √|g| (R - 2Λ)` vanishes for every smooth symmetric perturbation of compact support
(over any compact region containing its support). `isEHCritical_iff`: this holds iff `E^{αβ} + E^{βα} = 0` with
`E^{αβ} = R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` (`einsteinUp`), that is, iff `g` satisfies the vacuum Einstein equations with the
cosmological constant `Λ` (`E` is symmetric). The proof is `eh_first_variation` and the fundamental lemma of the calculus of
variations (Mathlib's `ae_eq_zero_of_integral_contDiff_smul_eq_zero`) with the perturbations `φ(x) S`, `S` a symmetric constant matrix.

**Limits.** Coordinates on `ℝⁿ`, a smooth metric of any signature with `det g ≠ 0` everywhere; "critical" means for compactly
supported perturbations (fixed data outside a compact set); the manifold statement and the trust checks are later stages.
-/

open Matrix Filter Topology MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

section
variable (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hdet : ∀ x, (g x).det ≠ 0)
include hg hdet

theorem contDiff_inv_entry (a b : Fin n) : ContDiff ℝ ∞ (fun y => (g y)⁻¹ a b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_inv_entry hg (hdet x) a b

theorem contDiff_christoffel (i j k : Fin n) : ContDiff ℝ ∞ (fun y => christoffel g i j k y) := by
  unfold christoffel
  refine contDiff_const.mul (ContDiff.sum fun l _ => (contDiff_inv_entry g hg hdet i l).mul ?_)
  exact ((contDiff_pd (hg l k) j).add (contDiff_pd (hg l j) k)).sub (contDiff_pd (hg j k) l)

theorem contDiff_riemann (ρ σ μ ν : Fin n) : ContDiff ℝ ∞ (fun y => riemann g ρ σ μ ν y) := by
  unfold riemann
  refine ((contDiff_pd (contDiff_christoffel g hg hdet ρ ν σ) μ).sub (contDiff_pd (contDiff_christoffel g hg hdet ρ μ σ) ν)).add
    (ContDiff.sum fun l _ => ?_)
  exact ((contDiff_christoffel g hg hdet ρ μ l).mul (contDiff_christoffel g hg hdet l ν σ)).sub
    ((contDiff_christoffel g hg hdet ρ ν l).mul (contDiff_christoffel g hg hdet l μ σ))

theorem contDiff_ricci (σ ν : Fin n) : ContDiff ℝ ∞ (fun y => ricci g σ ν y) := by
  unfold ricci
  exact ContDiff.sum fun ρ _ => contDiff_riemann g hg hdet ρ σ ρ ν

theorem contDiff_scalarCurvature : ContDiff ℝ ∞ (fun y => scalarCurvature g y) := by
  unfold scalarCurvature
  exact ContDiff.sum fun σ _ => ContDiff.sum fun ν _ => (contDiff_inv_entry g hg hdet σ ν).mul (contDiff_ricci g hg hdet σ ν)

theorem contDiff_ricciUp (α β : Fin n) : ContDiff ℝ ∞ (fun y => ricciUp g y α β) := by
  unfold ricciUp
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    ((contDiff_inv_entry g hg hdet α a).mul (contDiff_ricci g hg hdet a b)).mul (contDiff_inv_entry g hg hdet b β)


/-- The Einstein tensor with a cosmological term, indices up: `E^{αβ} = R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}`. -/
def einsteinUp (Λ : ℝ) (x : Fin n → ℝ) (α β : Fin n) : ℝ :=
  ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β

/-- **The metric is a critical point of the Einstein-Hilbert action**: the first variation vanishes for every smooth symmetric
perturbation of compact support. -/
def IsEHCritical (Λ : ℝ) : Prop :=
  ∀ (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ), (∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) →
    (∀ y a b, h y a b = h y b a) → ∀ {T : Set (Fin n → ℝ)}, IsCompact T → (∀ a b, tsupport (fun y => h y a b) ⊆ T) →
      HasDerivAt (fun t : ℝ => ∫ x in T, lagDensity g h Λ t x) 0 0

variable (hgs : ∀ y a b, g y a b = g y b a)
include hgs

theorem contDiff_einsteinUp (Λ : ℝ) (α β : Fin n) : ContDiff ℝ ∞ (fun y => einsteinUp g Λ y α β) := by
  unfold einsteinUp
  exact ((contDiff_ricciUp g hg hdet α β).sub (((contDiff_scalarCurvature g hg hdet).const_smul (1 / 2 : ℝ)).mul
    (contDiff_inv_entry g hg hdet α β))).add (contDiff_const.mul (contDiff_inv_entry g hg hdet α β))

/-- **Critical points of the Einstein-Hilbert action are the vacuum Einstein equations**: `g` is critical iff
`R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` is antisymmetric in `α, β` (it is symmetric, so this says it vanishes). -/
theorem isEHCritical_iff (Λ : ℝ) :
    IsEHCritical g Λ ↔ ∀ x α β, einsteinUp g Λ x α β + einsteinUp g Λ x β α = 0 := by
  constructor
  · intro hcrit x a b
    set c : (Fin n → ℝ) → ℝ := fun y => einsteinUp g Λ y a b + einsteinUp g Λ y b a with hc
    set f : (Fin n → ℝ) → ℝ := fun y => √|(g y).det| * c y with hf
    have hcc : Continuous c := ((contDiff_einsteinUp g hg hdet hgs Λ a b).add (contDiff_einsteinUp g hg hdet hgs Λ b a)).continuous
    have hsq : Continuous (fun y => √|(g y).det|) :=
      (contDiff_iff_contDiffAt.2 fun x => contDiffAt_sqrt_abs ((contDiff_det_of (f := g) (m := ⊤) hg).contDiffAt) (hdet x)).continuous
    have hfc : Continuous f := hsq.mul hcc
    have hzero : ∀ φ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ x, φ x • f x = 0 := by
      intro φ hφ hφc
      set S : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0) with hS
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
      have hderiv := hcrit h hhd hhs hφc hsup
      have hv := eh_first_variation g h hg hhd hgs hhs hdet hφc hsup Λ
      have hu := hv.unique hderiv
      have hint : ∫ x in tsupport φ, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) = 0 := by
        linarith
      have hform : ∀ x, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) = φ x * f x := by
        intro x
        have hE : ∀ α β, (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) =
            einsteinUp g Λ x α β := fun α β => rfl
        have hsum : ∑ α, ∑ β, h x α β * (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) =
            φ x * c x := by
          simp only [hE, hh, hS, hc, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
          simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq']
        rw [hsum, hf]; ring
      simp only [hform] at hint
      have hsupp : ∀ x, x ∉ tsupport φ → φ x • f x = 0 := by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
      simpa using hint
    have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hfc.locallyIntegrable) hzero
    have hfz : ∀ x, f x = 0 := fun x => congrFun ((hfc.ae_eq_iff_eq volume continuous_const).1 hae) x
    have := hfz x
    simp only [hf, hc] at this
    have hpos : 0 < √|(g x).det| := Real.sqrt_pos.2 (abs_pos.2 (hdet x))
    exact (mul_eq_zero.1 this).resolve_left hpos.ne'
  · intro hE h hh hhs T hT hsupp
    have hv := eh_first_variation g h hg hh hgs hhs hdet hT hsupp Λ
    have : (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
        (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β)) = 0 := by
      have h0 : ∀ x, (∑ α, ∑ β, h x α β *
        (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β)) = 0 := by
        intro x
        have e : ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β = ∑ α, ∑ β, h x α β * einsteinUp g Λ x β α := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
          rw [hhs x α β]
        have h2 : ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β = 0 := by
          have : (∑ α, ∑ β, h x α β * einsteinUp g Λ x α β) + ∑ α, ∑ β, h x α β * einsteinUp g Λ x α β = 0 := by
            nth_rewrite 2 [e]
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_eq_zero fun α _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_eq_zero fun β _ => ?_
            rw [← mul_add, hE x α β, mul_zero]
          linarith
        simpa [einsteinUp] using h2
      have hfun : (fun x => √|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β)) = fun _ => (0 : ℝ) := by
        funext x; rw [h0 x, mul_zero]
      rw [hfun]
      simp
    rw [this] at hv
    exact hv

end

end Lightlike
