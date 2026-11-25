import Lightlike.Spacetime.KaluzaKlein.KKDiffDeriv

/-!
# Traces of the difference tensor (G1-044)

For a symmetric inverse metric, the traces of the difference tensor are
`Γ̂^ρ_{ρ5} - Γ̃^ρ_{ρ5} = 0` (`trace_five`) and `Γ̂^ρ_{ρa} - Γ̃^ρ_{ρa} = φ⁻¹ ∂_a φ` (`trace_a`), as identities between the
explicit component functions `Ecab`, `Eca5`, `E5a5`, `E555` (they say `det Ĝ = φ² det g`).

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {p : Fin n → ℝ}

/-- The trace of `F_a{}ᶜ` vanishes for a symmetric inverse metric. -/
theorem sum_FU_diag (hS : ∀ c d, (g p)⁻¹ c d = (g p)⁻¹ d c) : ∑ c, FU g A c c p = 0 := by
  unfold FU
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by rw [hS c d]

theorem sum_A_FU (a : Fin n) :
    ∑ c, A p c * FU g A a c p = ∑ d, AU g A d p * (pd a (fun y => A y d) p - pd d (fun y => A y a) p) := by
  unfold FU AU
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_A_gradU : ∑ c, A p c * gradU g φ c p = ∑ d, AU g A d p * pd d φ p := by
  unfold gradU AU
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Trace of the difference tensor on the fifth index**: `Γ̂^ρ_{ρ5} = Γ̃^ρ_{ρ5}`. -/
theorem trace_five (hS : ∀ c d, (g p)⁻¹ c d = (g p)⁻¹ d c) :
    ∑ c, Eca5 g A φ c c p + E555 g A φ p = 0 := by
  unfold Eca5 E555
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_FU_diag hS]
  have e : ∀ c, φ p * A p c * gradU g φ c p = φ p * (A p c * gradU g φ c p) := fun c => by ring
  simp only [e, ← Finset.mul_sum, sum_A_gradU]
  ring

/-- **Trace of the difference tensor on a base index**: `Γ̂^ρ_{ρa} - Γ̃^ρ_{ρa} = φ⁻¹ ∂_a φ`. -/
theorem trace_a (hS : ∀ c d, (g p)⁻¹ c d = (g p)⁻¹ d c) (a : Fin n) :
    ∑ c, Ecab g A φ c c a p + E5a5 g A φ a p = (φ p)⁻¹ * pd a φ p := by
  have e : ∀ c, Ecab g A φ c c a p = ((1 / 2) * φ p ^ 2 * A p a) * FU g A c c p +
      ((1 / 2) * φ p ^ 2) * (A p c * FU g A a c p) - (φ p * A p a) * (A p c * gradU g φ c p) := fun c => by
    unfold Ecab
    ring
  rw [Finset.sum_congr rfl fun c _ => e c]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_FU_diag hS, sum_A_FU,
    sum_A_gradU]
  unfold E5a5
  ring

end KK

end Lightlike
