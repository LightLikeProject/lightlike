import Lightlike.Spacetime.KaluzaKlein.KKDiv

/-!
# The Ricci tensor of the Kaluza-Klein metric: the `55` component (G1-044)

At a point over `U` where `A = 0`, `R̂_{55} = -φ □φ - ¼ φ⁴ F_a{}ᶜ F_c{}ᵃ` (`ricci_kk_55`), the dilaton equation.
The proof applies `ricci_of_christoffel_add_cov` to the product metric `kkRef g` and the difference tensor `kkDiff`.

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix Filter
open scoped ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} {x : Fin (n + 1) → ℝ}

/-- The inverse of a symmetric matrix is symmetric. -/
theorem inv_symm_of (hgs : ∀ y a b, g y a b = g y b a) (p : Fin n → ℝ) (c d : Fin n) :
    (g p)⁻¹ c d = (g p)⁻¹ d c := by
  have hT : ((g p)⁻¹)ᵀ = (g p)⁻¹ := by
    have : (g p)ᵀ = g p := by ext i j; exact hgs p j i
    rw [Matrix.transpose_nonsing_inv, this]
  simpa [Matrix.transpose_apply] using (congrFun (congrFun hT c) d).symm

/-- **Trace of the difference tensor on a base index**: `Σ_ρ (Γ̂^ρ_{ρa} - Γ̃^ρ_{ρa}) = φ⁻¹ ∂_a φ`. -/
theorem sum_kkDiff_trace_a (hgs : ∀ y a b, g y a b = g y b a) (h : KKReg g A φ (proj x)) (a : Fin n) :
    ∑ l, kkDiff g A φ l l a.castSucc x = (φ (proj x))⁻¹ * pd a φ (proj x) := by
  rw [Fin.sum_univ_castSucc, kkDiff_symm hgs (Fin.last n) (Fin.last n) a.castSucc, kkDiff_5a5 h a]
  simp only [kkDiff_cab h]
  exact trace_a (inv_symm_of hgs _) a

/-- **Trace of the difference tensor on the fifth index**: `Σ_ρ (Γ̂^ρ_{ρ5} - Γ̃^ρ_{ρ5}) = 0`. -/
theorem sum_kkDiff_trace_five (hgs : ∀ y a b, g y a b = g y b a) (h : KKReg g A φ (proj x)) :
    ∑ l, kkDiff g A φ l l (Fin.last n) x = 0 := by
  rw [Fin.sum_univ_castSucc, kkDiff_555 h]
  simp only [kkDiff_ca5 h]
  exact trace_five (inv_symm_of hgs _)

section Values

variable (hgs : ∀ y a b, g y a b = g y b a) (h : KKReg g A φ (proj x)) (hA0 : ∀ a, A (proj x) a = 0)
include hgs h hA0

/-- Values of the difference tensor at a point where `A = 0`. -/
theorem kd_cab0 (c a b : Fin n) : kkDiff g A φ c.castSucc a.castSucc b.castSucc x = 0 := by
  rw [kkDiff_cab h]; simp [hA0]

theorem kd_ca5 (c a : Fin n) :
    kkDiff g A φ c.castSucc a.castSucc (Fin.last n) x = (1 / 2) * φ (proj x) ^ 2 * FU g A a c (proj x) := by
  rw [kkDiff_ca5 h]; simp [hA0]

theorem kd_c5a (c a : Fin n) :
    kkDiff g A φ c.castSucc (Fin.last n) a.castSucc x = (1 / 2) * φ (proj x) ^ 2 * FU g A a c (proj x) := by
  rw [kkDiff_symm hgs, kd_ca5 hgs h hA0]

theorem kd_c55 (c : Fin n) :
    kkDiff g A φ c.castSucc (Fin.last n) (Fin.last n) x = -(φ (proj x) * gradU g φ c (proj x)) :=
  kkDiff_c55 h c

theorem kd_5a5 (a : Fin n) :
    kkDiff g A φ (Fin.last n) a.castSucc (Fin.last n) x = (φ (proj x))⁻¹ * pd a φ (proj x) := by
  rw [kkDiff_5a5 h]; simp [hA0, AU]

theorem kd_55a (a : Fin n) :
    kkDiff g A φ (Fin.last n) (Fin.last n) a.castSucc x = (φ (proj x))⁻¹ * pd a φ (proj x) := by
  rw [kkDiff_symm hgs, kd_5a5 hgs h hA0]

theorem kd_555 : kkDiff g A φ (Fin.last n) (Fin.last n) (Fin.last n) x = 0 := by
  rw [kkDiff_555 h]; simp [hA0, AU]

end Values

section Main

variable (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hA : ∀ a, ContDiffOn ℝ ∞ (fun y => A y a) U)
  (hφ : ContDiffOn ℝ ∞ φ U) (hφne : ∀ y ∈ U, φ y ≠ 0) (hx : proj x ∈ U) (hA0 : ∀ a, A (proj x) a = 0)
include hg hgs hA hφ hφne hx hA0

/-- **The `55` component of the Ricci tensor of the Kaluza-Klein metric** at a point where `A = 0`. -/
theorem ricci_kk_55 :
    ricci (kkMetric g A φ) (Fin.last n) (Fin.last n) x =
      -(φ (proj x) * boxC g φ (proj x)) -
        (1 / 4) * φ (proj x) ^ 4 * ∑ a, ∑ c, FU g A a c (proj x) * FU g A c a (proj x) := by
  have h := kkReg_of_contDiffOn hg hA hφ hφne hx
  have hΓd : ∀ a b c, DifferentiableAt ℝ (christoffel (kkRef g) a b c) x := fun a b c =>
    differentiableAt_of_contDiffOn ((isCoordMetric_kkRef hg).contDiffOn_christoffel a b c)
      (isCoordMetric_kkRef hg).isOpen hx
  rw [ricci_of_christoffel_add_cov (g := kkRef g) (g' := kkMetric g A φ)
    (fun y a b => kkMetric_symm (A := fun _ _ => 0) (φ := fun _ => 1) hgs y a b) (kkDiff g A φ)
    (Filter.Eventually.of_forall fun y a b c => by simp [kkDiff]) hΓd
    (differentiableAt_kkDiff hg hA hφ hφne hx), ricci_kkRef_last hg hgs hx _ _ (Or.inl rfl)]
  simp only [covC, christoffel_kkRef_eq hg hgs hx, Fin.sum_univ_castSucc, cref_cab,
    cref_mid_last, cref_right_last, pd_last_kkDiff, kd_cab0 hgs h hA0, kd_ca5 hgs h hA0,
    kd_c5a hgs h hA0, kd_c55 hgs h hA0, kd_5a5 hgs h hA0, kd_55a hgs h hA0, kd_555 hgs h hA0,
    pd_kkDiff_c55 hg hA hφ hφne hx, zero_mul, mul_zero, add_zero, zero_add, sub_zero, Finset.sum_const_zero,
    sub_self]
  have hdG : ∀ c, DifferentiableAt ℝ (gradU g φ c) (proj x) := fun c =>
    differentiableAt_of_contDiffOn (contDiffOn_gradU hg hA hφ c) hg.isOpen hx
  have hpd : ∀ c, pd c (Ec55 g φ c) (proj x) =
      -(pd c φ (proj x) * gradU g φ c (proj x) + φ (proj x) * pd c (gradU g φ c) (proj x)) := fun c => by
    have e : Ec55 g φ c = fun y => (-1 : ℝ) * (φ y * gradU g φ c y) := by funext y; simp [Ec55]
    rw [e, pd_const_mul (-1) (f := fun y => φ y * gradU g φ c y) (h.dφ.mul (hdG c)) c, pd_mul h.dφ (hdG c) c]
    ring
  have hdiv := div_gradU hg hgs hφ hx (p := proj x)
  have e1 : ∀ c, pd c (Ec55 g φ c) (proj x) +
      ∑ l, christoffel g c c l (proj x) * -(φ (proj x) * gradU g φ l (proj x)) =
      -(pd c φ (proj x) * gradU g φ c (proj x)) - φ (proj x) * (pd c (gradU g φ c) (proj x) +
        ∑ l, christoffel g c c l (proj x) * gradU g φ l (proj x)) := fun c => by
    have hs : ∑ l, christoffel g c c l (proj x) * -(φ (proj x) * gradU g φ l (proj x)) =
        -(φ (proj x) * ∑ l, christoffel g c c l (proj x) * gradU g φ l (proj x)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hpd c, hs]
    ring
  have e2 : ∀ c, 0 - (φ (proj x))⁻¹ * pd c φ (proj x) * -(φ (proj x) * gradU g φ c (proj x)) =
      pd c φ (proj x) * gradU g φ c (proj x) := fun c => by
    have := hφne _ hx
    field_simp
    ring
  have e3 : ∑ c, ∑ a, (0 - 1 / 2 * φ (proj x) ^ 2 * FU g A a c (proj x) *
      (1 / 2 * φ (proj x) ^ 2 * FU g A c a (proj x))) =
      -((1 / 4) * φ (proj x) ^ 4 * ∑ a, ∑ c, FU g A a c (proj x) * FU g A c a (proj x)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  simp only [e1, e2]
  rw [e3, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, hdiv]
  unfold boxC
  ring

end Main

end KK

end Lightlike
