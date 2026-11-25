import Lightlike.Spacetime.KaluzaKlein.KKChristoffel

/-!
# The difference tensor between the Kaluza-Klein and the product connection (G1-044)

`kkRef g = kkMetric g 0 1` is the product metric `g ⊕ 1` on `ℝⁿ⁺¹`; its Christoffel symbols are those of `g` (for the
indices `< n`) and `0` otherwise.  The difference `kkDiff g A φ = Γ̂ - Γ̃` of the Christoffel symbols of
`kkMetric g A φ` and of `kkRef g` is a tensor, computed here (`kkDiff_c55`, `kkDiff_ca5`, `kkDiff_cab`, `kkDiff_5a5`,
`kkDiff_555`, `kkDiff_5ab_zero`); it feeds `ricci_of_christoffel_add_cov` in the computation of the five-dimensional
Ricci tensor.

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ}

/-- The product metric `g ⊕ 1`: the Kaluza-Klein metric with `A = 0`, `φ = 1`. -/
def kkRef (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  kkMetric g (fun _ _ => 0) (fun _ => 1)

/-- The difference `Γ̂ - Γ̃` of the Christoffel symbols of the Kaluza-Klein metric and of the product metric. -/
def kkDiff (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin n → ℝ) → ℝ)
    (i j k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) : ℝ :=
  christoffel (kkMetric g A φ) i j k y - christoffel (kkRef g) i j k y

/-- `F_a{}ᶜ = gᶜᵈ (∂_a A_d - ∂_d A_a)`. -/
def FU (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ) (a c : Fin n)
    (p : Fin n → ℝ) : ℝ :=
  ∑ d, (g p)⁻¹ c d * (pd a (fun y => A y d) p - pd d (fun y => A y a) p)

/-- `∂ᶜφ = gᶜᵈ ∂_d φ`. -/
def gradU (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → ℝ) (c : Fin n) (p : Fin n → ℝ) : ℝ :=
  ∑ d, (g p)⁻¹ c d * pd d φ p

/-- `Aᵈ = A_e gᵉᵈ`. -/
def AU (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ) (d : Fin n)
    (p : Fin n → ℝ) : ℝ :=
  ∑ e, A p e * (g p)⁻¹ e d

section Ref

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}

theorem KKReg.ref (h : KKReg g A φ (proj x)) : KKReg g (fun _ _ => 0) (fun _ => 1) (proj x) :=
  ⟨h.inv, one_ne_zero, h.dg, fun _ => differentiableAt_const _, differentiableAt_const _⟩

theorem kkMetric_symm (hgs : ∀ y a b, g y a b = g y b a) (y : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    kkMetric g A φ y i j = kkMetric g A φ y j i := by
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · rfl
  · simp
  · simp
  · simp only [kkMetric_cc, hgs (proj y) a b]
    ring

theorem kkRef_c55 (h : KKReg g A φ (proj x)) (c : Fin n) :
    christoffel (kkRef g) c.castSucc (Fin.last n) (Fin.last n) x = 0 := by
  have := christoffel_kk_c55 h.ref c
  simpa [kkRef, pd_const] using this

theorem kkRef_ca5 (h : KKReg g A φ (proj x)) (c a : Fin n) :
    christoffel (kkRef g) c.castSucc a.castSucc (Fin.last n) x = 0 := by
  have := christoffel_kk_ca5 h.ref c a
  simpa [kkRef, pd_const] using this

theorem kkRef_cab (h : KKReg g A φ (proj x)) (c a b : Fin n) :
    christoffel (kkRef g) c.castSucc a.castSucc b.castSucc x = christoffel g c a b (proj x) := by
  have := christoffel_kk_cab h.ref c a b
  simpa [kkRef, pd_const] using this

theorem kkRef_5a5 (h : KKReg g A φ (proj x)) (a : Fin n) :
    christoffel (kkRef g) (Fin.last n) a.castSucc (Fin.last n) x = 0 := by
  have := christoffel_kk_5a5 h.ref a
  simpa [kkRef, pd_const] using this

theorem kkRef_555 (h : KKReg g A φ (proj x)) :
    christoffel (kkRef g) (Fin.last n) (Fin.last n) (Fin.last n) x = 0 := by
  have := christoffel_kk_555 h.ref
  simpa [kkRef, pd_const] using this

/-- `Γ̂⁵_{ab} = ½ (∂_a A_b + ∂_b A_a)` at a point where `A = 0`. -/
theorem christoffel_kk_5ab_zero (h : KKReg g A φ (proj x)) (hA : ∀ a, A (proj x) a = 0) (a b : Fin n) :
    christoffel (kkMetric g A φ) (Fin.last n) a.castSucc b.castSucc x =
      (1 / 2) * (pd a (fun y => A y b) (proj x) + pd b (fun y => A y a) (proj x)) := by
  have hφ := h.φne
  rw [christoffel_kk h]
  simp only [Fin.sum_univ_castSucc, pd_last_kk h, pd_kk_5c h, pd_kk_cc h, kkInv_5c, kkInv_55, hA]
  simp
  field_simp

theorem kkRef_5ab (h : KKReg g A φ (proj x)) (a b : Fin n) :
    christoffel (kkRef g) (Fin.last n) a.castSucc b.castSucc x = 0 := by
  have := christoffel_kk_5ab_zero h.ref (fun _ => rfl) a b
  simpa [kkRef, pd_const] using this

end Ref

section Diff

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {x : Fin (n + 1) → ℝ}

theorem kkDiff_c55 (h : KKReg g A φ (proj x)) (c : Fin n) :
    kkDiff g A φ c.castSucc (Fin.last n) (Fin.last n) x = -(φ (proj x) * gradU g φ c (proj x)) := by
  rw [kkDiff, kkRef_c55 h, sub_zero]
  exact christoffel_kk_c55 h c

theorem kkDiff_ca5 (h : KKReg g A φ (proj x)) (c a : Fin n) :
    kkDiff g A φ c.castSucc a.castSucc (Fin.last n) x =
      (1 / 2) * φ (proj x) ^ 2 * FU g A a c (proj x) - φ (proj x) * A (proj x) a * gradU g φ c (proj x) := by
  rw [kkDiff, kkRef_ca5 h, sub_zero]
  exact christoffel_kk_ca5 h c a

theorem kkDiff_cab (h : KKReg g A φ (proj x)) (c a b : Fin n) :
    kkDiff g A φ c.castSucc a.castSucc b.castSucc x =
      (1 / 2) * φ (proj x) ^ 2 * (A (proj x) b * FU g A a c (proj x) + A (proj x) a * FU g A b c (proj x)) -
        φ (proj x) * A (proj x) a * A (proj x) b * gradU g φ c (proj x) := by
  rw [kkDiff, kkRef_cab h]
  have := christoffel_kk_cab h c a b
  unfold FU gradU
  linarith

theorem kkDiff_5a5 (h : KKReg g A φ (proj x)) (a : Fin n) :
    kkDiff g A φ (Fin.last n) a.castSucc (Fin.last n) x =
      (φ (proj x))⁻¹ * pd a φ (proj x) -
        (1 / 2) * φ (proj x) ^ 2 * ∑ d, AU g A d (proj x) *
          (pd a (fun y => A y d) (proj x) - pd d (fun y => A y a) (proj x)) +
        φ (proj x) * A (proj x) a * ∑ d, AU g A d (proj x) * pd d φ (proj x) := by
  rw [kkDiff, kkRef_5a5 h, sub_zero]
  exact christoffel_kk_5a5 h a

theorem kkDiff_555 (h : KKReg g A φ (proj x)) :
    kkDiff g A φ (Fin.last n) (Fin.last n) (Fin.last n) x =
      φ (proj x) * ∑ d, AU g A d (proj x) * pd d φ (proj x) := by
  rw [kkDiff, kkRef_555 h, sub_zero]
  exact christoffel_kk_555 h

theorem kkDiff_5ab_zero (h : KKReg g A φ (proj x)) (hA : ∀ a, A (proj x) a = 0) (a b : Fin n) :
    kkDiff g A φ (Fin.last n) a.castSucc b.castSucc x =
      (1 / 2) * (pd a (fun y => A y b) (proj x) + pd b (fun y => A y a) (proj x)) := by
  rw [kkDiff, kkRef_5ab h, sub_zero]
  exact christoffel_kk_5ab_zero h hA a b

/-- The difference tensor is symmetric in its lower indices. -/
theorem kkDiff_symm (hgs : ∀ y a b, g y a b = g y b a) (i j k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    kkDiff g A φ i j k y = kkDiff g A φ i k j y := by
  unfold kkDiff
  rw [christoffel_symm (kkMetric g A φ) (kkMetric_symm hgs) i j k y,
    christoffel_symm (kkRef g) (kkMetric_symm hgs) i j k y]

end Diff

end KK

end Lightlike
