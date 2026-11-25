module

public import Lightlike.Cosmology.ScalarFieldFLRW.ScalarFLRW

/-!
# The scalar field in FLRW: trust checks (row G1-027, milestone CO29)

Three sanity checks on the homogeneous scalar field with `ρ = φ̇²/2 + V(φ)`, `p = φ̇²/2 − V(φ)`:
* `φ̇ = 0` gives the equation of state `w = p/ρ = −1`;
* a wrong-sign (phantom) kinetic term gives `w < −1`;
* a constant potential gives de Sitter space.

Source: Baumann, *TASI lectures on inflation* (`baumann-2009`), eq. (A.140).
-/

@[expose] public section

noncomputable section

namespace Lightlike

namespace Cosmology

/-- `ρ + p = φ̇²` for the scalar field. -/
theorem scalarRho_add_scalarP (φ V : ℝ → ℝ) (t : ℝ) :
    scalarRho φ V t + scalarP φ V t = deriv φ t ^ 2 := by
  unfold scalarRho scalarP; ring

/-- Trust check: at an instant with `φ̇ = 0` the field has `p = −ρ`. -/
theorem scalarP_eq_neg_scalarRho {φ V : ℝ → ℝ} {t : ℝ} (h : deriv φ t = 0) :
    scalarP φ V t = -scalarRho φ V t := by
  unfold scalarP scalarRho; rw [h]; ring

/-- Trust check: at an instant with `φ̇ = 0` and `ρ ≠ 0`, the equation of state is `w = p/ρ = −1`. -/
theorem scalar_w_eq_neg_one {φ V : ℝ → ℝ} {t : ℝ} (h : deriv φ t = 0)
    (hρ : scalarRho φ V t ≠ 0) : scalarP φ V t / scalarRho φ V t = -1 := by
  rw [scalarP_eq_neg_scalarRho h]; field_simp

/-- The energy density `−φ̇²/2 + V(φ)` of a field with wrong-sign (phantom) kinetic term. -/
def phantomRho (φ V : ℝ → ℝ) (t : ℝ) : ℝ := -(deriv φ t ^ 2 / 2) + V (φ t)

/-- The pressure `−φ̇²/2 − V(φ)` of a field with wrong-sign (phantom) kinetic term. -/
def phantomP (φ V : ℝ → ℝ) (t : ℝ) : ℝ := -(deriv φ t ^ 2 / 2) - V (φ t)

/-- Trust check: for a wrong-sign kinetic term and `φ̇ ≠ 0` with `ρ > 0` the equation of state
satisfies `w = p/ρ < −1`. -/
theorem phantom_w_lt_neg_one {φ V : ℝ → ℝ} {t : ℝ} (h : deriv φ t ≠ 0)
    (hρ : 0 < phantomRho φ V t) : phantomP φ V t / phantomRho φ V t < -1 := by
  rw [div_lt_iff₀ hρ]
  have : 0 < deriv φ t ^ 2 := by positivity
  unfold phantomP phantomRho at *
  linarith

/-- Trust check: for the normal kinetic term, `w ≥ −1` when `ρ > 0`. -/
theorem scalar_w_ge_neg_one {φ V : ℝ → ℝ} {t : ℝ} (hρ : 0 < scalarRho φ V t) :
    -1 ≤ scalarP φ V t / scalarRho φ V t := by
  rw [le_div_iff₀ hρ]
  have := scalarRho_add_scalarP φ V t
  nlinarith [sq_nonneg (deriv φ t)]

/-- A constant field in a constant potential has `ρ = Λ₀` at all times. -/
theorem scalarRho_const (c Λ₀ : ℝ) :
    scalarRho (fun _ => c) (fun _ => Λ₀) = fun _ => Λ₀ := by
  funext t; simp [scalarRho]

/-- A constant field in a constant potential has `p = −Λ₀` at all times. -/
theorem scalarP_const (c Λ₀ : ℝ) :
    scalarP (fun _ => c) (fun _ => Λ₀) = fun _ => -Λ₀ := by
  funext t; simp [scalarP]

/-- Trust check: de Sitter. For a constant potential `V ≡ Λ₀` and the constant field, the
Klein–Gordon equation holds on `a = e^{Ht}`, and both Friedmann equations (`k = Λ = 0`) hold at
every time iff `H² = 8πGΛ₀/3`. -/
theorem scalar_deSitter (H c Λ₀ Gn : ℝ) :
    (∀ t, IsKG (fun t => Real.exp (H * t)) (fun _ => c) (fun _ => Λ₀) t) ∧
    ((∀ t, FirstFriedmann (fun t => Real.exp (H * t)) (scalarRho (fun _ => c) (fun _ => Λ₀)) 0 0 Gn t ∧
      SecondFriedmann (fun t => Real.exp (H * t)) (scalarRho (fun _ => c) (fun _ => Λ₀))
        (scalarP (fun _ => c) (fun _ => Λ₀)) 0 Gn t) ↔
      H ^ 2 = 8 * Real.pi * Gn * Λ₀ / 3) := by
  refine ⟨fun t => ?_, ?_⟩
  · simp [IsKG]
  · rw [scalarRho_const, scalarP_const]
    exact deSitter_friedmann_iff H Λ₀ Gn

end Cosmology

end Lightlike
