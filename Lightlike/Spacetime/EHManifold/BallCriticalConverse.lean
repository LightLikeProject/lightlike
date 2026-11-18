import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Lightlike.Spacetime.EHManifold.BallCritical

/-!
# Critical metrics on a ball satisfy the vacuum Einstein equations

`einsteinUp_symm_eq_zero_of_critical_ball`: for a coordinate metric `g` that is smooth, symmetric and
nondegenerate on a ball, if the first variation of the Einstein–Hilbert action vanishes for every smooth
symmetric perturbation supported in a compact subset of the smaller concentric ball, then the symmetric part
of `R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` vanishes on the smaller ball.

`isEHCriticalOnBall_iff` combines it with `eh_first_variation_ball_eq_zero`.

The proof is the one of `isEHCritical_iff` (perturbations `ψ • (E_ab + E_ba)` and the fundamental lemma of
the calculus of variations), with test functions supported in the ball.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.66) and
  (4.67), p. 116.
-/

open Filter Topology Metric MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {c : Fin n → ℝ}

/-- **The metric on a ball is a critical point of the Einstein–Hilbert action**: the first variation
vanishes for every smooth symmetric perturbation supported in a compact subset of the smaller ball. -/
def IsEHCriticalOnBall (φ : ContDiffBump c) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (Λ : ℝ) : Prop :=
  ∀ (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ), (∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) →
    (∀ y a b, h y a b = h y b a) → ∀ {T : Set (Fin n → ℝ)}, IsCompact T → T ⊆ ball c φ.rIn →
      (∀ a b, tsupport (fun y => h y a b) ⊆ T) →
      HasDerivAt (fun t : ℝ => ∫ x in T, lagDensity g h Λ t x) 0 0

/-- **Critical metrics on a ball satisfy the vacuum Einstein equations** on the smaller ball. -/
theorem einsteinUp_symm_eq_zero_of_critical_ball (φ : ContDiffBump c)
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun y => g y a b) (ball c φ.rOut))
    (hgs : ∀ y ∈ ball c φ.rOut, ∀ a b, g y a b = g y b a)
    (hdet : ∀ y ∈ ball c φ.rOut, (g y).det ≠ 0) (Λ : ℝ) (hcrit : IsEHCriticalOnBall φ g Λ)
    {x : Fin n → ℝ} (hx : x ∈ ball c φ.rIn) (a b : Fin n) :
    einsteinUp g Λ x a b + einsteinUp g Λ x b a = 0 := by
  obtain ⟨gt, hgt⟩ : ∃ gt : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ,
      gt = fun y => g (ballRetract φ y) := ⟨_, rfl⟩
  have hsm : ∀ a b, ContDiff ℝ ∞ (fun y => gt y a b) := by
    intro a b
    rw [hgt]
    exact contDiff_comp_ballRetract φ hg a b
  have hsym : ∀ y a b, gt y a b = gt y b a := by
    intro y a b
    rw [hgt]
    exact hgs _ (ballRetract_mem φ y) a b
  have hdt : ∀ y, (gt y).det ≠ 0 := by
    intro y
    rw [hgt]
    exact hdet _ (ballRetract_mem φ y)
  have hev : ∀ y ∈ ball c φ.rIn, gt =ᶠ[𝓝 y] g := by
    intro y hy
    rw [hgt]
    exact eventuallyEq_comp_ballRetract φ g hy
  have hEin : ∀ y ∈ ball c φ.rIn, ∀ α β, einsteinUp gt Λ y α β = einsteinUp g Λ y α β := by
    intro y hy α β
    have hy0 : gt y = g y := (hev y hy).eq_of_nhds
    have hric : ∀ i j, ricci gt i j y = ricci g i j y := fun i j => ricci_congr (hev y hy) i j
    simp only [einsteinUp, ricciUp, hy0, hric, scalarCurvature_congr (hev y hy)]
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → ℝ) → ℝ,
      f = fun y => √|(gt y).det| * (einsteinUp gt Λ y a b + einsteinUp gt Λ y b a) := ⟨_, rfl⟩
  have hgtc : Continuous gt := continuous_matrix fun i j => (hsm i j).continuous
  have hfc : Continuous f := by
    rw [hf]
    exact (Real.continuous_sqrt.comp (continuous_abs.comp hgtc.matrix_det)).mul
      ((contDiff_einsteinUp gt hsm hdt hsym Λ a b).continuous.add
        (contDiff_einsteinUp gt hsm hdt hsym Λ b a).continuous)
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin n) ℝ, S = Matrix.of fun i j =>
      (if i = a ∧ j = b then (1 : ℝ) else 0) + (if i = b ∧ j = a then 1 else 0) := ⟨_, rfl⟩
  have hzero : ∀ ψ : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c φ.rIn → ∫ y, ψ y • f y = 0 := by
    intro ψ hψ hψc hψs
    have hhd : ∀ i j, ContDiff ℝ ∞ (fun y => (ψ y • S) i j) := by
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact hψ.mul contDiff_const
    have hhs : ∀ y i j, (ψ y • S) i j = (ψ y • S) j i := by
      intro y i j
      simp only [hS, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      congr 1
      rw [add_comm]
      simp only [and_comm]
    have hsup : ∀ i j, tsupport (fun y => (ψ y • S) i j) ⊆ tsupport ψ := by
      intro i j
      exact tsupport_smul_subset_left (fun y => ψ y) (fun _ => S i j)
    have hderiv := hcrit (fun y => ψ y • S) hhd hhs hψc hψs hsup
    have hv := eh_first_variation_ball φ g (fun y => ψ y • S) hg hhd hgs hhs hdet hψc hψs hsup Λ
    have hu := hv.unique hderiv
    have hint : ∫ y in tsupport ψ, √|(g y).det| * ∑ α, ∑ β, (ψ y • S) α β *
        (ricciUp g y α β - (1 / 2) * scalarCurvature g y * (g y)⁻¹ α β + Λ * (g y)⁻¹ α β) = 0 :=
      neg_eq_zero.1 hu
    have hsuppz : ∀ y, y ∉ tsupport ψ → ψ y • f y = 0 := by
      intro y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsuppz, ← hint]
    refine setIntegral_congr_fun (isClosed_tsupport ψ).measurableSet fun y hy => ?_
    have hyb := hψs hy
    have hsum : ∑ α, ∑ β, (ψ y • S) α β * einsteinUp g Λ y α β =
        ψ y * (einsteinUp g Λ y a b + einsteinUp g Λ y b a) := by
      simp only [hS, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      simp [mul_add, add_mul, Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq']
    show ψ y • f y = √|(g y).det| * ∑ α, ∑ β, (ψ y • S) α β * einsteinUp g Λ y α β
    rw [hsum, hf, smul_eq_mul]
    show ψ y * (√|(gt y).det| * (einsteinUp gt Λ y a b + einsteinUp gt Λ y b a)) = _
    rw [hEin y hyb a b, hEin y hyb b a, (hev y hyb).eq_of_nhds]
    ring
  have hae := (isOpen_ball (x := c) (ε := φ.rIn)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) (hfc.locallyIntegrable.locallyIntegrableOn _) hzero
  have hopen : IsOpen (ball c φ.rIn ∩ {y | f y ≠ 0}) :=
    isOpen_ball.inter (isOpen_ne_fun hfc continuous_const)
  have hnull : volume (ball c φ.rIn ∩ {y | f y ≠ 0}) = 0 :=
    measure_mono_null (fun y hy himp => hy.2 (himp hy.1)) (ae_iff.1 hae)
  have hempty : ball c φ.rIn ∩ {y | f y ≠ 0} = ∅ := (hopen.measure_eq_zero_iff volume).1 hnull
  have hfx : f x = 0 := by
    by_contra hne
    have hmem : x ∈ ball c φ.rIn ∩ {y | f y ≠ 0} := ⟨hx, hne⟩
    rw [hempty] at hmem
    exact hmem
  rw [hf] at hfx
  have hpos : 0 < √|(gt x).det| := Real.sqrt_pos.2 (abs_pos.2 (hdt x))
  have hc0 : einsteinUp gt Λ x a b + einsteinUp gt Λ x b a = 0 :=
    (mul_eq_zero.1 hfx).resolve_left hpos.ne'
  rw [hEin x hx a b, hEin x hx b a] at hc0
  exact hc0

/-- **Critical points of the Einstein–Hilbert action on a ball are the vacuum Einstein equations** on the
smaller ball. -/
theorem isEHCriticalOnBall_iff (φ : ContDiffBump c) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun y => g y a b) (ball c φ.rOut))
    (hgs : ∀ y ∈ ball c φ.rOut, ∀ a b, g y a b = g y b a)
    (hdet : ∀ y ∈ ball c φ.rOut, (g y).det ≠ 0) (Λ : ℝ) :
    IsEHCriticalOnBall φ g Λ ↔
      ∀ x ∈ ball c φ.rIn, ∀ α β, einsteinUp g Λ x α β + einsteinUp g Λ x β α = 0 := by
  constructor
  · intro hcrit x hx α β
    exact einsteinUp_symm_eq_zero_of_critical_ball φ g hg hgs hdet Λ hcrit hx α β
  · intro hE h hh hhs T hT hTball hsupp
    exact eh_first_variation_ball_eq_zero φ g h hg hh hgs hhs hdet hT hTball hsupp Λ
      fun x hx => hE x (hTball hx)

end Lightlike
