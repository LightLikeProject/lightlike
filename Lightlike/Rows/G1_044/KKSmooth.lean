import Lightlike.Rows.G1_044.KKDiff

/-!
# Regularity of the Kaluza-Klein metric (G1-044)

If `(g, A, φ)` are smooth on an open set `U ⊆ ℝⁿ`, `g` is a coordinate metric on `U` and `φ ≠ 0` on `U`, then
`kkMetric g A φ` is a coordinate metric on the cylinder `proj ⁻¹' U ⊆ ℝⁿ⁺¹` (`isCoordMetric_kk`), and so is the
product metric `kkRef g` (`isCoordMetric_kkRef`); the regularity bundle `KKReg` holds at every point of `U`
(`kkReg_of_contDiffOn`).

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)}

/-- A smooth function on `U`, pulled back along the projection, is smooth on the cylinder `proj ⁻¹' U`. -/
theorem contDiffOn_comp_proj {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun y : Fin (n + 1) → ℝ => f (proj y)) (proj ⁻¹' U) :=
  hf.comp (projL n).contDiff.contDiffOn (fun _ hy => hy)

theorem isOpen_preimage_proj (hU : IsOpen U) : IsOpen (proj ⁻¹' U : Set (Fin (n + 1) → ℝ)) :=
  hU.preimage (projL n).continuous

/-- The Kaluza-Klein metric is a coordinate metric on the cylinder over `U`. -/
theorem isCoordMetric_kk (hg : IsCoordMetric g U) (hA : ∀ a, ContDiffOn ℝ ∞ (fun y => A y a) U)
    (hφ : ContDiffOn ℝ ∞ φ U) (hφne : ∀ y ∈ U, φ y ≠ 0) :
    IsCoordMetric (kkMetric g A φ) (proj ⁻¹' U) where
  isOpen := isOpen_preimage_proj hg.isOpen
  symm y hy := by
    have hs : ∀ a b, g (proj y) a b = g (proj y) b a := fun a b =>
      (congrFun (congrFun (hg.symm _ hy) a) b).symm
    ext i j
    show kkMetric g A φ y j i = kkMetric g A φ y i j
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    · rfl
    · simp
    · simp
    · simp only [kkMetric_cc, hs a b]
      ring
  isUnit_det y hy :=
    Matrix.isUnit_det_of_right_inverse
      (kkMetric_mul_kkInv g A φ y (Matrix.mul_nonsing_inv _ (hg.isUnit_det _ hy)) (hφne _ hy))
  smooth i j := by
    refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
    · simp only [kkMetric_55]
      exact contDiffOn_comp_proj (f := fun z => φ z ^ 2) (hφ.pow 2)
    · simp only [kkMetric_5c]
      exact contDiffOn_comp_proj (f := fun z => φ z ^ 2 * A z b) ((hφ.pow 2).mul (hA b))
    · simp only [kkMetric_c5]
      exact contDiffOn_comp_proj (f := fun z => φ z ^ 2 * A z a) ((hφ.pow 2).mul (hA a))
    · simp only [kkMetric_cc]
      exact contDiffOn_comp_proj (f := fun z => g z a b + φ z ^ 2 * A z a * A z b)
        ((hg.smooth a b).add (((hφ.pow 2).mul (hA a)).mul (hA b)))

/-- The product metric `g ⊕ 1` is a coordinate metric on the cylinder over `U`. -/
theorem isCoordMetric_kkRef (hg : IsCoordMetric g U) : IsCoordMetric (kkRef g) (proj ⁻¹' U) :=
  isCoordMetric_kk hg (fun _ => contDiffOn_const) contDiffOn_const (fun _ _ => one_ne_zero)

/-- The regularity bundle `KKReg` holds at every point of `U`. -/
theorem kkReg_of_contDiffOn (hg : IsCoordMetric g U) (hA : ∀ a, ContDiffOn ℝ ∞ (fun y => A y a) U)
    (hφ : ContDiffOn ℝ ∞ φ U) (hφne : ∀ y ∈ U, φ y ≠ 0) {p : Fin n → ℝ} (hp : p ∈ U) :
    KKReg g A φ p where
  inv := Matrix.mul_nonsing_inv _ (hg.isUnit_det _ hp)
  φne := hφne _ hp
  dg a b := differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hp
  dA a := differentiableAt_of_contDiffOn (hA a) hg.isOpen hp
  dφ := differentiableAt_of_contDiffOn hφ hg.isOpen hp

end KK

end Lightlike
