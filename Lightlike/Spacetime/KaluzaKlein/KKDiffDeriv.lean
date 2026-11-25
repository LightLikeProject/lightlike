import Lightlike.Spacetime.KaluzaKlein.KKTrans
import Lightlike.Spacetime.KaluzaKlein.KKSmooth

/-!
# Derivatives of the difference tensor (G1-044)

On the cylinder over `U`, the components `Γ̂ - Γ̃` of the difference tensor with an explicit formula
(`kkDiff_c55`, `kkDiff_ca5`, `kkDiff_cab`, `kkDiff_5a5`, `kkDiff_555`) are pull-backs `E ∘ proj` of smooth functions
on `U` (`Ec55`, `Eca5`, `Ecab`, `E5a5`, `E555`); the partial derivatives `∂_k` (`k < n`) of the components are then
`∂_k E` (`pd_kkDiff_*`), and `∂_n` vanishes (`pd_last_kkDiff`).  All components are differentiable
(`differentiableAt_kkDiff`).

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

/-- All components of the difference tensor are differentiable over `U`. -/
theorem differentiableAt_kkDiff (hg : IsCoordMetric g U) (hA : ∀ a, ContDiffOn ℝ ∞ (fun y => A y a) U)
    (hφ : ContDiffOn ℝ ∞ φ U) (hφne : ∀ y ∈ U, φ y ≠ 0) (hx : proj x ∈ U) (i j k : Fin (n + 1)) :
    DifferentiableAt ℝ (kkDiff g A φ i j k) x := by
  have h1 := isCoordMetric_kk hg hA hφ hφne
  have h2 := isCoordMetric_kkRef hg
  exact (differentiableAt_of_contDiffOn (h1.contDiffOn_christoffel i j k) h1.isOpen hx).sub
    (differentiableAt_of_contDiffOn (h2.contDiffOn_christoffel i j k) h2.isOpen hx)

/-- The derivative `∂_k` (`k < n`) of a function which is eventually a pull-back along `proj`. -/
theorem pd_cast_of_eventuallyEq {F : (Fin (n + 1) → ℝ) → ℝ} {E : (Fin n → ℝ) → ℝ}
    (hev : F =ᶠ[𝓝 x] fun y => E (proj y)) (hE : DifferentiableAt ℝ E (proj x)) (k : Fin n) :
    pd k.castSucc F x = pd k E (proj x) := by
  have : pd k.castSucc F x = pd k.castSucc (fun y => E (proj y)) x := by
    unfold pd
    rw [hev.fderiv_eq]
  rw [this, pd_comp_proj E x hE k]

section Smooth

variable (hg : IsCoordMetric g U) (hA : ∀ a, ContDiffOn ℝ ∞ (fun y => A y a) U) (hφ : ContDiffOn ℝ ∞ φ U)

include hg hA hφ

theorem contDiffOn_FU (a c : Fin n) : ContDiffOn ℝ ∞ (FU g A a c) U := by
  unfold FU
  exact ContDiffOn.sum fun d _ => (hg.contDiffOn_inv c d).mul
    ((contDiffOn_pd (hA d) hg.isOpen a).sub (contDiffOn_pd (hA a) hg.isOpen d))

theorem contDiffOn_gradU (c : Fin n) : ContDiffOn ℝ ∞ (gradU g φ c) U := by
  unfold gradU
  exact ContDiffOn.sum fun d _ => (hg.contDiffOn_inv c d).mul (contDiffOn_pd hφ hg.isOpen d)

theorem contDiffOn_AU (d : Fin n) : ContDiffOn ℝ ∞ (AU g A d) U := by
  unfold AU
  exact ContDiffOn.sum fun e _ => (hA e).mul (hg.contDiffOn_inv e d)

end Smooth

/-- `Γ̂^c_{ab} - Γ̃^c_{ab}` as a function on `ℝⁿ` (general `A`). -/
def Ecab (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ)
    (c a b : Fin n) (p : Fin n → ℝ) : ℝ :=
  (1 / 2) * φ p ^ 2 * (A p b * FU g A a c p + A p a * FU g A b c p) - φ p * A p a * A p b * gradU g φ c p

/-- `Γ̂^c_{a5} - Γ̃^c_{a5}` as a function on `ℝⁿ`. -/
def Eca5 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ)
    (c a : Fin n) (p : Fin n → ℝ) : ℝ :=
  (1 / 2) * φ p ^ 2 * FU g A a c p - φ p * A p a * gradU g φ c p

/-- `Γ̂^c_{55}` as a function on `ℝⁿ`. -/
def Ec55 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → ℝ) (c : Fin n) (p : Fin n → ℝ) : ℝ :=
  -(φ p * gradU g φ c p)

/-- `Γ̂^5_{a5}` as a function on `ℝⁿ`. -/
def E5a5 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ)
    (a : Fin n) (p : Fin n → ℝ) : ℝ :=
  (φ p)⁻¹ * pd a φ p -
    (1 / 2) * φ p ^ 2 * ∑ d, AU g A d p * (pd a (fun y => A y d) p - pd d (fun y => A y a) p) +
    φ p * A p a * ∑ d, AU g A d p * pd d φ p

/-- `Γ̂^5_{55}` as a function on `ℝⁿ`. -/
def E555 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ)
    (p : Fin n → ℝ) : ℝ :=
  φ p * ∑ d, AU g A d p * pd d φ p

section Pull

variable (hg : IsCoordMetric g U) (hA : ∀ a, ContDiffOn ℝ ∞ (fun y => A y a) U) (hφ : ContDiffOn ℝ ∞ φ U)
  (hφne : ∀ y ∈ U, φ y ≠ 0)

include hg hA hφ hφne

theorem kkDiff_cab_eventually (hx : proj x ∈ U) (c a b : Fin n) :
    kkDiff g A φ c.castSucc a.castSucc b.castSucc =ᶠ[𝓝 x] fun y => Ecab g A φ c a b (proj y) := by
  filter_upwards [(isOpen_preimage_proj hg.isOpen).mem_nhds hx] with y hy
  exact kkDiff_cab (kkReg_of_contDiffOn hg hA hφ hφne hy) c a b

theorem kkDiff_ca5_eventually (hx : proj x ∈ U) (c a : Fin n) :
    kkDiff g A φ c.castSucc a.castSucc (Fin.last n) =ᶠ[𝓝 x] fun y => Eca5 g A φ c a (proj y) := by
  filter_upwards [(isOpen_preimage_proj hg.isOpen).mem_nhds hx] with y hy
  exact kkDiff_ca5 (kkReg_of_contDiffOn hg hA hφ hφne hy) c a

theorem kkDiff_c55_eventually (hx : proj x ∈ U) (c : Fin n) :
    kkDiff g A φ c.castSucc (Fin.last n) (Fin.last n) =ᶠ[𝓝 x] fun y => Ec55 g φ c (proj y) := by
  filter_upwards [(isOpen_preimage_proj hg.isOpen).mem_nhds hx] with y hy
  exact kkDiff_c55 (kkReg_of_contDiffOn hg hA hφ hφne hy) c

theorem kkDiff_5a5_eventually (hx : proj x ∈ U) (a : Fin n) :
    kkDiff g A φ (Fin.last n) a.castSucc (Fin.last n) =ᶠ[𝓝 x] fun y => E5a5 g A φ a (proj y) := by
  filter_upwards [(isOpen_preimage_proj hg.isOpen).mem_nhds hx] with y hy
  exact kkDiff_5a5 (kkReg_of_contDiffOn hg hA hφ hφne hy) a

theorem kkDiff_555_eventually (hx : proj x ∈ U) :
    kkDiff g A φ (Fin.last n) (Fin.last n) (Fin.last n) =ᶠ[𝓝 x] fun y => E555 g A φ (proj y) := by
  filter_upwards [(isOpen_preimage_proj hg.isOpen).mem_nhds hx] with y hy
  exact kkDiff_555 (kkReg_of_contDiffOn hg hA hφ hφne hy)

end Pull

section Smooth2

variable (hg : IsCoordMetric g U) (hA : ∀ a, ContDiffOn ℝ ∞ (fun y => A y a) U) (hφ : ContDiffOn ℝ ∞ φ U)
  (hφne : ∀ y ∈ U, φ y ≠ 0)

include hg hA hφ hφne

theorem contDiffOn_Ecab (c a b : Fin n) : ContDiffOn ℝ ∞ (Ecab g A φ c a b) U := by
  unfold Ecab
  exact ((contDiffOn_const.mul (hφ.pow 2)).mul (((hA b).mul (contDiffOn_FU hg hA hφ a c)).add
    ((hA a).mul (contDiffOn_FU hg hA hφ b c)))).sub
    ((((hφ.mul (hA a)).mul (hA b))).mul (contDiffOn_gradU hg hA hφ c))

theorem contDiffOn_Eca5 (c a : Fin n) : ContDiffOn ℝ ∞ (Eca5 g A φ c a) U := by
  unfold Eca5
  exact ((contDiffOn_const.mul (hφ.pow 2)).mul (contDiffOn_FU hg hA hφ a c)).sub
    ((hφ.mul (hA a)).mul (contDiffOn_gradU hg hA hφ c))

theorem contDiffOn_Ec55 (c : Fin n) : ContDiffOn ℝ ∞ (Ec55 g φ c) U := by
  unfold Ec55
  exact (hφ.mul (contDiffOn_gradU hg hA hφ c)).neg

theorem contDiffOn_E5a5 (a : Fin n) : ContDiffOn ℝ ∞ (E5a5 g A φ a) U := by
  unfold E5a5
  refine ((hφ.inv hφne).mul (contDiffOn_pd hφ hg.isOpen a)).sub ?_ |>.add ?_
  · exact (contDiffOn_const.mul (hφ.pow 2)).mul (ContDiffOn.sum fun d _ => (contDiffOn_AU hg hA hφ d).mul
      ((contDiffOn_pd (hA d) hg.isOpen a).sub (contDiffOn_pd (hA a) hg.isOpen d)))
  · exact (hφ.mul (hA a)).mul (ContDiffOn.sum fun d _ => (contDiffOn_AU hg hA hφ d).mul
      (contDiffOn_pd hφ hg.isOpen d))

theorem contDiffOn_E555 : ContDiffOn ℝ ∞ (E555 g A φ) U := by
  unfold E555
  exact hφ.mul (ContDiffOn.sum fun d _ => (contDiffOn_AU hg hA hφ d).mul (contDiffOn_pd hφ hg.isOpen d))

variable (hx : proj x ∈ U)

include hx

theorem pd_kkDiff_cab (c a b k : Fin n) :
    pd k.castSucc (kkDiff g A φ c.castSucc a.castSucc b.castSucc) x = pd k (Ecab g A φ c a b) (proj x) :=
  pd_cast_of_eventuallyEq (kkDiff_cab_eventually hg hA hφ hφne hx c a b)
    (differentiableAt_of_contDiffOn (contDiffOn_Ecab hg hA hφ hφne c a b) hg.isOpen hx) k

theorem pd_kkDiff_ca5 (c a k : Fin n) :
    pd k.castSucc (kkDiff g A φ c.castSucc a.castSucc (Fin.last n)) x = pd k (Eca5 g A φ c a) (proj x) :=
  pd_cast_of_eventuallyEq (kkDiff_ca5_eventually hg hA hφ hφne hx c a)
    (differentiableAt_of_contDiffOn (contDiffOn_Eca5 hg hA hφ hφne c a) hg.isOpen hx) k

theorem pd_kkDiff_c55 (c k : Fin n) :
    pd k.castSucc (kkDiff g A φ c.castSucc (Fin.last n) (Fin.last n)) x = pd k (Ec55 g φ c) (proj x) :=
  pd_cast_of_eventuallyEq (kkDiff_c55_eventually hg hA hφ hφne hx c)
    (differentiableAt_of_contDiffOn (contDiffOn_Ec55 hg hA hφ hφne c) hg.isOpen hx) k

theorem pd_kkDiff_5a5 (a k : Fin n) :
    pd k.castSucc (kkDiff g A φ (Fin.last n) a.castSucc (Fin.last n)) x = pd k (E5a5 g A φ a) (proj x) :=
  pd_cast_of_eventuallyEq (kkDiff_5a5_eventually hg hA hφ hφne hx a)
    (differentiableAt_of_contDiffOn (contDiffOn_E5a5 hg hA hφ hφne a) hg.isOpen hx) k

theorem pd_kkDiff_555 (k : Fin n) :
    pd k.castSucc (kkDiff g A φ (Fin.last n) (Fin.last n) (Fin.last n)) x = pd k (E555 g A φ) (proj x) :=
  pd_cast_of_eventuallyEq (kkDiff_555_eventually hg hA hφ hφne hx)
    (differentiableAt_of_contDiffOn (contDiffOn_E555 hg hA hφ hφne) hg.isOpen hx) k

end Smooth2

end KK

end Lightlike
