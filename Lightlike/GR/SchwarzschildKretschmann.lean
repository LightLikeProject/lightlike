import Lightlike.GR.Schwarzschild
import Lightlike.Spacetime.Kretschmann

/-!
# The Riemann tensor and the Kretschmann scalar of the Schwarzschild metric

In the coordinates `(t, r, θ, φ)` the Riemann tensor of the Schwarzschild metric has, up to the symmetries, only
the components `R^a_{bab} = κ_{ab} g_{bb}` with `κ_{tr} = κ_{θφ} = 2M/r³` and `κ = -M/r³` for the four other pairs
(`riemann_sch`). Hence (`kretschmann_sch`)

`R_{abcd} R^{abcd} = 48 M² / r⁶`.

**Difference from the source (kind: the source is in error).** S. M. Carroll, *Lecture Notes on General
Relativity*, arXiv:gr-qc/9712019v1 (3 December 1997), eq. (7.30) (printed page 172, read) prints
`R^{μνρσ} R_{μνρσ} = 12 G²M²/r⁶`, with `G` and `M` (not `2GM` or a Schwarzschild radius; `12 (2GM)²/r⁶` would be
correct). The computation here gives `48 M²/r⁶` (`G = 1`): the six index pairs contribute
`4 (2M/r³)² · 2 + 4 (M/r³)² · 4 = 48 M²/r⁶`; `12 M²/r⁶` is the sum `Σ_{a<b} κ_{ab}²` without the factor `4` from the
symmetries of the Riemann tensor. The conclusion drawn in the source, that the invariant diverges as `r → 0`, is
unaffected.
-/

open Matrix Real

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- The sectional numbers `κ_{ab}` of the Schwarzschild metric: `2M/r³` for the pairs `{t, r}` and `{θ, φ}`,
`-M/r³` for the others. -/
def schKappa (a b : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) then 2 * M / y 1 ^ 3
  else -(M / y 1 ^ 3)

/-- The expected components `R^a_{bcd}` of the Riemann tensor of the Schwarzschild metric. -/
def schRiem (a b c d : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if a = b then 0
  else if a = c ∧ b = d then schKappa M a b y * schD M y b
  else if a = d ∧ b = c then -(schKappa M a b y * schD M y b)
  else 0

set_option maxHeartbeats 4000000 in
/-- **The Riemann tensor of the Schwarzschild metric** (wherever the chart is valid). -/
theorem riemann_sch {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (a b c d : Fin 4) :
    riemann (schMetric M) a b c d x = schRiem M a b c d x := by
  have hx' := hx
  obtain ⟨h1, h2, h3⟩ := hx'
  have h1' : x 1 ≠ 0 := h1.ne'
  have hc : cos (x 2) ^ 2 = 1 - sin (x 2) ^ 2 := cos_sq' _
  have h2b : 2 * M - x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2d : x 1 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have h2e : -(M * 2) + x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2f : x 1 + -(M * 2) ≠ 0 := fun h => h2 (by linarith)
  have h2g : -(2 * M) + x 1 ≠ 0 := fun h => h2 (by linarith)
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [riemann, Fin.sum_univ_four, pd_christoffel_sch M hx, christoffel_sch M hx,
      schΓ, schDΓ, schRiem, schKappa, schD] <;> field_simp <;> (try simp only [hc]) <;> ring

/-- **The Kretschmann scalar of the Schwarzschild metric is `48 M²/r⁶`.** -/
theorem kretschmann_sch {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) :
    kretschmann (schMetric M) x = 48 * M ^ 2 / x 1 ^ 6 := by
  obtain ⟨h1, h2, h3⟩ := hx
  have h1' : x 1 ≠ 0 := h1.ne'
  have hf : 1 - 2 * M / x 1 ≠ 0 := by
    rw [one_sub_div h1']; exact div_ne_zero h2 h1'
  have hne : ∀ i, schD M x i ≠ 0 := by
    intro i
    fin_cases i
    · show -(1 - 2 * M / x 1) ≠ 0
      exact neg_ne_zero.2 hf
    · show (1 - 2 * M / x 1)⁻¹ ≠ 0
      exact inv_ne_zero hf
    · show x 1 ^ 2 ≠ 0
      exact pow_ne_zero 2 h1'
    · show x 1 ^ 2 * sin (x 2) ^ 2 ≠ 0
      exact mul_ne_zero (pow_ne_zero 2 h1') (pow_ne_zero 2 h3)
  have hD : schMetric M x = diagonal (schD M x) := rfl
  have hDi : (schMetric M x)⁻¹ = diagonal fun i => (schD M x i)⁻¹ := by
    rw [hD]; exact inv_diagonal_of_ne hne
  have h2b : 2 * M - x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2d : x 1 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have h2e : -(M * 2) + x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2f : x 1 + -(M * 2) ≠ 0 := fun h => h2 (by linarith)
  have h2g : -(2 * M) + x 1 ≠ 0 := fun h => h2 (by linarith)
  rw [kretschmann_diagonal _ _ hD hDi]
  simp only [riemann_sch M ⟨h1, h2, h3⟩]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four, schRiem, schKappa, schD]
  field_simp
  ring

end Lightlike
