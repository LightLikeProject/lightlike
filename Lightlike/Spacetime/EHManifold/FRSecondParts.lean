import Lightlike.Spacetime.EHManifold.FRParts
import Lightlike.Spacetime.EHManifold.WSplit

/-!
# The second integration by parts for the `f(R)` variation

For a `C²` function `φ` (in the application, `φ = f'(R)`) and a smooth symmetric perturbation `h` supported
in a compact set `T`,

`∫_T √|g| W^ρ ∂_ρ φ = ∫_T (√|g| W₀^ρ ∂_ρ φ - ∂_μ (c^{μαβ}) h_{αβ})`,

with `c^{μαβ} = √|g| (g^{ρα} g^{μβ} - g^{ρμ} g^{αβ}) ∂_ρ φ` (`hessCoeff`) and `W₀` the part of the Palatini
vector without derivatives of `h` (`integral_flux_mul_pd`). The right side contains `h` without
derivatives: it is the integral of `h_{αβ}` against a tensor built from `g` and the first two derivatives
of `φ`. Its identification with `-√|g| (∇^α ∇^β φ - g^{αβ} □φ)` is not proved here.

Supporting lemma for the `f(R)` field equations; no catalogue entry.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The coefficient `c^{μαβ} = √|g| (g^{ρα} g^{μβ} - g^{ρμ} g^{αβ}) ∂_ρ φ` of `∂_μ h_{αβ}` in
`√|g| W^ρ ∂_ρ φ`. -/
def hessCoeff (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → ℝ) (μ α β : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  √|(g x).det| * ∑ ρ, ((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x

/-- The partial derivatives of a `C²` function are `C¹`. -/
lemma contDiff_pd_one {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (ρ : Fin n) :
    ContDiff ℝ 1 (fun x => pd ρ φ x) := by
  unfold pd
  exact (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0)

include hg hdet in
/-- The coefficients `c^{μαβ}` are `C¹`. -/
lemma contDiff_hessCoeff {φ : (Fin n → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (μ α β : Fin n) :
    ContDiff ℝ 1 (hessCoeff g φ μ α β) := by
  have hinv : ∀ a b, ContDiff ℝ 1 (fun y => (g y)⁻¹ a b) := fun a b =>
    (contDiff_inv_entry g hg hdet a b).of_le (by simp)
  have hsq : ContDiff ℝ 1 (fun y => √|(g y).det|) :=
    (contDiff_iff_contDiffAt.2 fun x => contDiffAt_sqrt_abs
      ((contDiff_det_of (f := g) (m := ⊤) hg).contDiffAt) (hdet x)).of_le (by simp)
  unfold hessCoeff
  exact hsq.mul (ContDiff.sum fun ρ _ =>
    (((hinv ρ α).mul (hinv μ β)).sub ((hinv ρ μ).mul (hinv α β))).mul (contDiff_pd_one hφ ρ))

include hgs hhs in
/-- **The flux against a gradient, pointwise**: the part without derivatives of `h` plus
`c^{μαβ} ∂_μ h_{αβ}`. -/
lemma flux_mul_pd_eq (φ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x =
      (∑ ρ, (√|(g x).det| * Wvec0 g h ρ x) * pd ρ φ x) +
        ∑ μ, ∑ α, ∑ β, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x := by
  have hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a := by
    intro a b
    have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
      have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
      rw [Matrix.transpose_nonsing_inv, this]
    have := congrFun (congrFun hT a) b
    rw [Matrix.transpose_apply] at this
    exact this.symm
  have hterm : ∀ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x =
      (√|(g x).det| * Wvec0 g h ρ x) * pd ρ φ x +
        ∑ μ, ∑ α, ∑ β, √|(g x).det| *
          (((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x) *
            pd μ (fun z => h z α β) x := by
    intro ρ
    rw [Wvec_split g h x hinv hhs ρ, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  simp only [hterm, Finset.sum_add_distrib]
  congr 1
  have hc : ∀ μ α β, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x =
      ∑ ρ, √|(g x).det| *
        (((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x) *
          pd μ (fun z => h z α β) x := by
    intro μ α β
    unfold hessCoeff
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [hc]
  calc ∑ ρ, ∑ μ, ∑ α, ∑ β, √|(g x).det| *
          (((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x) *
            pd μ (fun z => h z α β) x
      = ∑ μ, ∑ ρ, ∑ α, ∑ β, √|(g x).det| *
          (((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x) *
            pd μ (fun z => h z α β) x := Finset.sum_comm
    _ = ∑ μ, ∑ α, ∑ ρ, ∑ β, √|(g x).det| *
          (((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x) *
            pd μ (fun z => h z α β) x := Finset.sum_congr rfl fun μ _ => Finset.sum_comm
    _ = ∑ μ, ∑ α, ∑ β, ∑ ρ, √|(g x).det| *
          (((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) * pd ρ φ x) *
            pd μ (fun z => h z α β) x :=
        Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ => Finset.sum_comm

include hg hh hgs hhs hdet in
/-- **The second integration by parts**: the integral of the flux against a gradient, as an integral of
`h` without derivatives. -/
theorem integral_flux_mul_pd (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ 2 φ) {T : Set (Fin n → ℝ)}
    (hT : IsCompact T) (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T) :
    ∫ x in T, ∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x =
      ∫ x in T, ((∑ ρ, (√|(g x).det| * Wvec0 g h ρ x) * pd ρ φ x) -
        ∑ μ, ∑ α, ∑ β, pd μ (hessCoeff g φ μ α β) x * h x α β) := by
  have hmeasT : MeasurableSet T := hT.isClosed.measurableSet
  have hcC : ∀ μ α β, ContDiff ℝ 1 (hessCoeff g φ μ α β) := fun μ α β =>
    contDiff_hessCoeff g hg hdet hφ μ α β
  have hh1 : ∀ α β, ContDiff ℝ 1 (fun y => h y α β) := fun α β => (hh α β).of_le (by simp)
  have hhc : ∀ α β, HasCompactSupport (fun y => h y α β) := fun α β =>
    hT.of_isClosed_subset (isClosed_tsupport _) (hsupp α β)
  have hpdh : ∀ μ α β, Continuous (fun x => pd μ (fun z => h z α β) x) := fun μ α β =>
    (contDiff_pd (hh α β) μ).continuous
  have hpdc : ∀ μ α β, Continuous (fun x => pd μ (hessCoeff g φ μ α β) x) := fun μ α β => by
    unfold pd
    exact ((hcC μ α β).continuous_fderiv (by simp)).clm_apply continuous_const
  have hpdφ : ∀ ρ, Continuous (fun x => pd ρ φ x) := fun ρ => (contDiff_pd_one hφ ρ).continuous
  -- the three integrands are continuous
  have hA : Continuous (fun x => ∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x) :=
    continuous_finsetSum _ fun ρ _ => (contDiff_flux g h hg hh hdet ρ).continuous.mul (hpdφ ρ)
  have hB : Continuous (fun x => ∑ μ, ∑ α, ∑ β,
      hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x) :=
    continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun α _ => continuous_finsetSum _
      fun β _ => (hcC μ α β).continuous.mul (hpdh μ α β)
  have hC : Continuous (fun x => ∑ μ, ∑ α, ∑ β, pd μ (hessCoeff g φ μ α β) x * h x α β) :=
    continuous_finsetSum _ fun μ _ => continuous_finsetSum _ fun α _ => continuous_finsetSum _
      fun β _ => (hpdc μ α β).mul (hh α β).continuous
  have iA : IntegrableOn (fun x => ∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x) T volume :=
    hA.continuousOn.integrableOn_compact hT
  have iB : IntegrableOn (fun x => ∑ μ, ∑ α, ∑ β,
      hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x) T volume :=
    hB.continuousOn.integrableOn_compact hT
  have iC : IntegrableOn (fun x => ∑ μ, ∑ α, ∑ β, pd μ (hessCoeff g φ μ α β) x * h x α β) T volume :=
    hC.continuousOn.integrableOn_compact hT
  -- integration by parts of each term of `B`
  have hparts : ∀ μ α β, ∫ x in T, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x =
      -∫ x in T, pd μ (hessCoeff g φ μ α β) x * h x α β := by
    intro μ α β
    have h1 := integral_mul_pd_eq_neg (hessCoeff g φ μ α β) (fun y => h y α β) (hcC μ α β) (hh1 α β)
      (hhc α β) μ
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, setIntegral_eq_integral_of_forall_compl_eq_zero,
      h1]
    · intro x hx
      have h0 : h x α β = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => h y α β) fun hmem => hx (hsupp α β hmem)
      rw [h0, mul_zero]
    · intro x hx
      have hev : (fun z => h z α β) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        notMem_tsupport_iff_eventuallyEq.1 fun hmem => hx (hsupp α β hmem)
      have hpd0 : pd μ (fun z => h z α β) x = 0 := by
        unfold pd
        rw [hev.fderiv_eq]
        simp
      rw [hpd0, mul_zero]
  have hBC : ∫ x in T, ∑ μ, ∑ α, ∑ β, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x =
      -∫ x in T, ∑ μ, ∑ α, ∑ β, pd μ (hessCoeff g φ μ α β) x * h x α β := by
    have i3 : ∀ μ α β, IntegrableOn (fun x => hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x) T
        volume := fun μ α β =>
      ((hcC μ α β).continuous.mul (hpdh μ α β)).continuousOn.integrableOn_compact hT
    have i4 : ∀ μ α β, IntegrableOn (fun x => pd μ (hessCoeff g φ μ α β) x * h x α β) T volume :=
      fun μ α β => ((hpdc μ α β).mul (hh α β).continuous).continuousOn.integrableOn_compact hT
    have i3' : ∀ μ α, IntegrableOn (fun x => ∑ β, hessCoeff g φ μ α β x *
        pd μ (fun z => h z α β) x) T volume := fun μ α => integrable_finsetSum _ fun β _ => i3 μ α β
    have i3'' : ∀ μ, IntegrableOn (fun x => ∑ α, ∑ β, hessCoeff g φ μ α β x *
        pd μ (fun z => h z α β) x) T volume := fun μ => integrable_finsetSum _ fun α _ => i3' μ α
    have i4' : ∀ μ α, IntegrableOn (fun x => ∑ β, pd μ (hessCoeff g φ μ α β) x * h x α β) T volume :=
      fun μ α => integrable_finsetSum _ fun β _ => i4 μ α β
    have i4'' : ∀ μ, IntegrableOn (fun x => ∑ α, ∑ β, pd μ (hessCoeff g φ μ α β) x * h x α β) T
        volume := fun μ => integrable_finsetSum _ fun α _ => i4' μ α
    rw [integral_finsetSum _ fun μ _ => i3'' μ, integral_finsetSum _ fun μ _ => i4'' μ,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [integral_finsetSum _ fun α _ => i3' μ α, integral_finsetSum _ fun α _ => i4' μ α,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun β _ => i3 μ α β, integral_finsetSum _ fun β _ => i4 μ α β,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun β _ => hparts μ α β
  -- assemble
  have iAB : IntegrableOn (fun x => (∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x) -
      ∑ μ, ∑ α, ∑ β, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x) T volume := iA.sub iB
  have hsplit : ∫ x in T, ∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x =
      (∫ x in T, ((∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x) -
          ∑ μ, ∑ α, ∑ β, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x)) +
        ∫ x in T, ∑ μ, ∑ α, ∑ β, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x := by
    rw [← integral_add iAB iB]
    refine setIntegral_congr_fun hmeasT fun x _ => ?_
    show _ = (_ - _) + _
    ring
  have hW0 : ∀ x, (∑ ρ, (√|(g x).det| * Wvec g h ρ x) * pd ρ φ x) -
        ∑ μ, ∑ α, ∑ β, hessCoeff g φ μ α β x * pd μ (fun z => h z α β) x =
      ∑ ρ, (√|(g x).det| * Wvec0 g h ρ x) * pd ρ φ x := by
    intro x
    rw [flux_mul_pd_eq g h hgs hhs φ x]
    ring
  have iW0 : IntegrableOn (fun x => ∑ ρ, (√|(g x).det| * Wvec0 g h ρ x) * pd ρ φ x) T volume :=
    iAB.congr_fun (fun x _ => hW0 x) hmeasT
  rw [hsplit, hBC, integral_sub iW0 iC, sub_eq_add_neg]
  congr 1
  exact setIntegral_congr_fun hmeasT fun x _ => hW0 x

end Lightlike
