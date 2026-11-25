import Lightlike.Spacetime.KaluzaKlein.KKCalculus
import Lightlike.Spacetime.RiemannSymmetry

/-!
# Christoffel symbols of the Kaluza-Klein metric (G1-044)

Regularity bundle `KKReg`, derivatives of the entries of `kkMetric`, and the Christoffel symbols
`Γ̂ⁱ_{jk}` of `kkMetric g A φ` expressed through the four-dimensional data.

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ}

/-- Regularity of the four-dimensional data `(g, A, φ)` at a point `p`: `g p` invertible, `φ p ≠ 0`, and all the
components differentiable at `p`. -/
structure KKReg (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
    (φ : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) : Prop where
  inv : g p * (g p)⁻¹ = 1
  φne : φ p ≠ 0
  dg : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) p
  dA : ∀ a, DifferentiableAt ℝ (fun y => A y a) p
  dφ : DifferentiableAt ℝ φ p

section Derivs

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}

theorem kk_fun_cc (a b : Fin n) : (fun y => kkMetric g A φ y a.castSucc b.castSucc) =
    fun y => (fun z => g z a b + φ z ^ 2 * A z a * A z b) (proj y) := by
  funext y; simp

theorem kk_fun_c5 (a : Fin n) : (fun y => kkMetric g A φ y a.castSucc (Fin.last n)) =
    fun y => (fun z => φ z ^ 2 * A z a) (proj y) := by
  funext y; simp

theorem kk_fun_5c (a : Fin n) : (fun y => kkMetric g A φ y (Fin.last n) a.castSucc) =
    fun y => (fun z => φ z ^ 2 * A z a) (proj y) := by
  funext y; simp

theorem kk_fun_55 : (fun y => kkMetric g A φ y (Fin.last n) (Fin.last n)) =
    fun y => (fun z => φ z ^ 2) (proj y) := by
  funext y; simp

theorem pd_last_kk (h : KKReg g A φ (proj x)) (i j : Fin (n + 1)) :
    pd (Fin.last n) (fun y => kkMetric g A φ y i j) x = 0 := by
  have h1 := h.dg
  have h2 := h.dA
  have h3 := h.dφ
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · rw [kk_fun_55]; exact pd_last_comp_proj (fun z => φ z ^ 2) x (by fun_prop)
  · rw [kk_fun_5c]; exact pd_last_comp_proj (fun z => φ z ^ 2 * A z b) x (by have := h2 b; fun_prop)
  · rw [kk_fun_c5]; exact pd_last_comp_proj (fun z => φ z ^ 2 * A z a) x (by have := h2 a; fun_prop)
  · rw [kk_fun_cc]
    exact pd_last_comp_proj (fun z => g z a b + φ z ^ 2 * A z a * A z b) x
      (by have := h2 a; have := h2 b; have := h1 a b; fun_prop)

theorem pd_kk_cc (h : KKReg g A φ (proj x)) (j a b : Fin n) :
    pd j.castSucc (fun y => kkMetric g A φ y a.castSucc b.castSucc) x =
      pd j (fun y => g y a b) (proj x) + 2 * φ (proj x) * pd j φ (proj x) * A (proj x) a * A (proj x) b +
        φ (proj x) ^ 2 * (pd j (fun y => A y a) (proj x) * A (proj x) b +
          A (proj x) a * pd j (fun y => A y b) (proj x)) := by
  have h1 := h.dg a b
  have h2 := h.dA a
  have h3 := h.dA b
  have h4 := h.dφ
  rw [kk_fun_cc, pd_comp_proj (fun z => g z a b + φ z ^ 2 * A z a * A z b) x (by fun_prop) j]
  simp (disch := fun_prop) only [pd_add, pd_mul, pd_sq]
  ring

theorem pd_kk_c5 (h : KKReg g A φ (proj x)) (j a : Fin n) :
    pd j.castSucc (fun y => kkMetric g A φ y a.castSucc (Fin.last n)) x =
      2 * φ (proj x) * pd j φ (proj x) * A (proj x) a + φ (proj x) ^ 2 * pd j (fun y => A y a) (proj x) := by
  have h2 := h.dA a
  have h4 := h.dφ
  rw [kk_fun_c5, pd_comp_proj (fun z => φ z ^ 2 * A z a) x (by fun_prop) j]
  simp (disch := fun_prop) only [pd_add, pd_mul, pd_sq]

theorem pd_kk_5c (h : KKReg g A φ (proj x)) (j a : Fin n) :
    pd j.castSucc (fun y => kkMetric g A φ y (Fin.last n) a.castSucc) x =
      2 * φ (proj x) * pd j φ (proj x) * A (proj x) a + φ (proj x) ^ 2 * pd j (fun y => A y a) (proj x) := by
  rw [kk_fun_5c]
  have := pd_kk_c5 h j a
  rwa [kk_fun_c5] at this

theorem pd_kk_55 (h : KKReg g A φ (proj x)) (j : Fin n) :
    pd j.castSucc (fun y => kkMetric g A φ y (Fin.last n) (Fin.last n)) x =
      2 * φ (proj x) * pd j φ (proj x) := by
  have h4 := h.dφ
  rw [kk_fun_55, pd_comp_proj (fun z => φ z ^ 2) x (by fun_prop) j]
  simp (disch := fun_prop) only [pd_sq]

end Derivs

section Gamma

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}

/-- The Christoffel symbols of the Kaluza-Klein metric with the explicit inverse `kkInv`. -/
theorem christoffel_kk (h : KKReg g A φ (proj x)) (i j k : Fin (n + 1)) :
    christoffel (kkMetric g A φ) i j k x = (1 / 2) * ∑ l, kkInv g A φ x i l *
      (pd j (fun y => kkMetric g A φ y l k) x + pd k (fun y => kkMetric g A φ y l j) x -
        pd l (fun y => kkMetric g A φ y j k) x) := by
  unfold christoffel
  rw [kkMetric_inv g A φ x h.inv h.φne]

/-- `Γ̂ᶜ₅₅ = -φ ∂ᶜφ`. -/
theorem christoffel_kk_c55 (h : KKReg g A φ (proj x)) (c : Fin n) :
    christoffel (kkMetric g A φ) c.castSucc (Fin.last n) (Fin.last n) x =
      -(φ (proj x) * ∑ d, (g (proj x))⁻¹ c d * pd d φ (proj x)) := by
  rw [christoffel_kk h]
  simp only [Fin.sum_univ_castSucc, pd_last_kk h, pd_kk_55 h, kkInv_cc, kkInv_c5]
  simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- `Γ̂ᶜ_{a5} = ½ φ² F_a{}ᶜ - φ A_a ∂ᶜφ`, with `F_a{}ᶜ = gᶜᵈ (∂_a A_d - ∂_d A_a)`. -/
theorem christoffel_kk_ca5 (h : KKReg g A φ (proj x)) (c a : Fin n) :
    christoffel (kkMetric g A φ) c.castSucc a.castSucc (Fin.last n) x =
      (1 / 2) * φ (proj x) ^ 2 * ∑ d, (g (proj x))⁻¹ c d *
          (pd a (fun y => A y d) (proj x) - pd d (fun y => A y a) (proj x)) -
        φ (proj x) * A (proj x) a * ∑ d, (g (proj x))⁻¹ c d * pd d φ (proj x) := by
  rw [christoffel_kk h]
  simp only [Fin.sum_univ_castSucc, pd_last_kk h, pd_kk_55 h, pd_kk_c5 h, pd_kk_5c h, kkInv_cc, kkInv_c5]
  simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- `Γ̂ᶜ_{ab} = Γᶜ_{ab} + ½ φ² (A_b F_a{}ᶜ + A_a F_b{}ᶜ) - φ A_a A_b ∂ᶜφ`. -/
theorem christoffel_kk_cab (h : KKReg g A φ (proj x)) (c a b : Fin n) :
    christoffel (kkMetric g A φ) c.castSucc a.castSucc b.castSucc x =
      christoffel g c a b (proj x) +
        (1 / 2) * φ (proj x) ^ 2 * (A (proj x) b * ∑ d, (g (proj x))⁻¹ c d *
            (pd a (fun y => A y d) (proj x) - pd d (fun y => A y a) (proj x)) +
          A (proj x) a * ∑ d, (g (proj x))⁻¹ c d *
            (pd b (fun y => A y d) (proj x) - pd d (fun y => A y b) (proj x))) -
        φ (proj x) * A (proj x) a * A (proj x) b * ∑ d, (g (proj x))⁻¹ c d * pd d φ (proj x) := by
  rw [christoffel_kk h]
  unfold christoffel
  simp only [Fin.sum_univ_castSucc, pd_last_kk h, pd_kk_cc h, pd_kk_c5 h, pd_kk_5c h, kkInv_cc, kkInv_c5]
  simp only [neg_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

section Alg

/-- Algebra for `Γ̂⁵₅₅`. -/
theorem alg_555 (φ : ℝ) (A : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → ℝ) (K : ℝ) :
    1 / 2 * (∑ x, (-∑ d, A d * G d x) * (0 + 0 - 2 * φ * f x) + K * (0 + 0 - 0)) =
      φ * ∑ d, (∑ e, A e * G e d) * f d := by
  have e : ∑ x, (-∑ d, A d * G d x) * (0 + 0 - 2 * φ * f x) = 2 * φ * ∑ d, (∑ e, A e * G e d) * f d := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [e]
  ring

/-- Algebra for `Γ̂⁵_{a5}`. -/
theorem christoffel_kk_555 (h : KKReg g A φ (proj x)) :
    christoffel (kkMetric g A φ) (Fin.last n) (Fin.last n) (Fin.last n) x =
      φ (proj x) * ∑ d, (∑ e, A (proj x) e * (g (proj x))⁻¹ e d) * pd d φ (proj x) := by
  rw [christoffel_kk h]
  simp only [Fin.sum_univ_castSucc, pd_last_kk h, pd_kk_55 h, kkInv_5c, kkInv_55]
  exact alg_555 (φ (proj x)) (fun d => A (proj x) d) (g (proj x))⁻¹ (fun d => pd d φ (proj x)) _

/-- `Γ̂⁵_{a5} = φ⁻¹ ∂_a φ - ½ φ² A^d F_{ad} + φ A_a A^d ∂_d φ`. -/
theorem alg_5a5 (φ fa Aa : ℝ) (hφ : φ ≠ 0) (A : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (f a1 a2 : Fin n → ℝ) :
    1 / 2 * (∑ x, (-∑ d, A d * G d x) * (2 * φ * fa * A x + φ ^ 2 * a1 x + 0 -
        (2 * φ * f x * Aa + φ ^ 2 * a2 x)) +
      (φ⁻¹ ^ 2 + ∑ c, ∑ d, A c * G c d * A d) * (2 * φ * fa + 0 - 0)) =
    φ⁻¹ * fa - 1 / 2 * φ ^ 2 * ∑ d, (∑ e, A e * G e d) * (a1 d - a2 d) +
      φ * Aa * ∑ d, (∑ e, A e * G e d) * f d := by
  have hQ : ∑ c, ∑ d, A c * G c d * A d = ∑ x, (∑ e, A e * G e x) * A x := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have e1 : ∑ x, (-∑ d, A d * G d x) * (2 * φ * fa * A x + φ ^ 2 * a1 x + 0 -
        (2 * φ * f x * Aa + φ ^ 2 * a2 x)) + ∑ x, (∑ e, A e * G e x) * A x * (2 * φ * fa + 0 - 0) =
      -(φ ^ 2 * ∑ d, (∑ e, A e * G e d) * (a1 d - a2 d)) + 2 * φ * Aa * ∑ d, (∑ e, A e * G e d) * f d := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hQ, add_mul, Finset.sum_mul]
  have hφ' : φ * φ⁻¹ = 1 := mul_inv_cancel₀ hφ
  linear_combination (1 / 2) * e1 + (φ⁻¹ * fa) * hφ'

end Alg

/-- `Γ̂⁵_{a5} = φ⁻¹ ∂_a φ - ½ φ² A^d F_{ad} + φ A_a A^d ∂_d φ`. -/
theorem christoffel_kk_5a5 (h : KKReg g A φ (proj x)) (a : Fin n) :
    christoffel (kkMetric g A φ) (Fin.last n) a.castSucc (Fin.last n) x =
      (φ (proj x))⁻¹ * pd a φ (proj x) -
        (1 / 2) * φ (proj x) ^ 2 * ∑ d, (∑ e, A (proj x) e * (g (proj x))⁻¹ e d) *
          (pd a (fun y => A y d) (proj x) - pd d (fun y => A y a) (proj x)) +
        φ (proj x) * A (proj x) a * ∑ d, (∑ e, A (proj x) e * (g (proj x))⁻¹ e d) * pd d φ (proj x) := by
  rw [christoffel_kk h]
  simp only [Fin.sum_univ_castSucc, pd_last_kk h, pd_kk_55 h, pd_kk_c5 h, pd_kk_5c h, kkInv_5c, kkInv_55]
  exact alg_5a5 (φ (proj x)) (pd a φ (proj x)) (A (proj x) a) h.φne (fun d => A (proj x) d) (g (proj x))⁻¹
    (fun d => pd d φ (proj x)) (fun d => pd a (fun y => A y d) (proj x))
    (fun d => pd d (fun y => A y a) (proj x))

end Gamma

end KK

end Lightlike
