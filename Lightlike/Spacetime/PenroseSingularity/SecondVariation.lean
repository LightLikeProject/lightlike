import Lightlike.Spacetime.PenroseSingularity.JacobiIdentity
import Lightlike.Spacetime.PenroseSingularity.JacobiCompat
import Lightlike.Spacetime.PenroseSingularity.JacobiGeom
import Lightlike.Spacetime.ConjugatePoints.JacobiVariation

/-!
# The commutator of covariant derivatives in a chart (G1-012, step D4)

For a two-parameter family `α (s, t)` and a field `X` along it, in a chart the commutator of the covariant
derivatives is the curvature: `D_t D_s X - D_s D_t X = R (∂_t α, ∂_s α) X`. This file proves the algebraic
identity between the jets (`riemS` is the Riemann tensor from the symbols).
-/

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ}

/-- `D_t D_s X` in terms of the jets: `A = α_s`, `B = α_t`, `C = α_{st}`, `X1 = X_s`, `X2 = X_t`, `X12 = X_{st}`. -/
def covDtDs (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (A B C X X1 X2 X12 : Fin n → ℝ) (a : Fin n) : ℝ :=
  (X12 a + ∑ d, ∑ b, ∑ c, dG d a b c * B d * A b * X c + ∑ b, ∑ c, G a b c * C b * X c +
      ∑ b, ∑ c, G a b c * A b * X2 c) +
    ∑ b, ∑ c, G a b c * B b * (X1 c + ∑ d, ∑ e, G c d e * A d * X e)

/-- `D_s D_t X` in terms of the same jets. -/
def covDsDt (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (A B C X X1 X2 X12 : Fin n → ℝ) (a : Fin n) : ℝ :=
  (X12 a + ∑ d, ∑ b, ∑ c, dG d a b c * A d * B b * X c + ∑ b, ∑ c, G a b c * C b * X c +
      ∑ b, ∑ c, G a b c * B b * X1 c) +
    ∑ b, ∑ c, G a b c * A b * (X2 c + ∑ d, ∑ e, G c d e * B d * X e)

/-- **The commutator of covariant derivatives is the curvature.** -/
theorem covDtDs_sub_covDsDt (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (A B C X X1 X2 X12 : Fin n → ℝ) (a : Fin n) :
    covDtDs G dG A B C X X1 X2 X12 a - covDsDt G dG A B C X X1 X2 X12 a =
      ∑ σ, ∑ μ, ∑ ν, riemS G dG a σ μ ν * X σ * B μ * A ν := by
  unfold covDtDs covDsDt riemS
  -- the derivative terms
  have r1 : ∑ σ, ∑ μ, ∑ ν, dG μ a ν σ * X σ * B μ * A ν =
      ∑ d, ∑ b, ∑ c, dG d a b c * B d * A b * X c := by
    rw [sum3_rot]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  have r2 : ∑ σ, ∑ μ, ∑ ν, dG ν a μ σ * X σ * B μ * A ν =
      ∑ d, ∑ b, ∑ c, dG d a b c * A d * B b * X c := by
    rw [sum3_swap23, sum3_swap12, sum3_swap23]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  -- the quadratic terms
  have r3 : ∑ σ, ∑ μ, ∑ ν, (∑ l, G a μ l * G l ν σ) * X σ * B μ * A ν =
      ∑ b, ∑ c, G a b c * B b * ∑ d, ∑ e, G c d e * A d * X e := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [sum3_swap23, sum3_swap12, sum3_swap23]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  have r4 : ∑ σ, ∑ μ, ∑ ν, (∑ l, G a ν l * G l μ σ) * X σ * B μ * A ν =
      ∑ b, ∑ c, G a b c * A b * ∑ d, ∑ e, G c d e * B d * X e := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum3_swap23, sum3_swap12, sum3_swap23]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [sum3_rot, sum3_rot]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  have e : ∀ σ μ ν, (dG μ a ν σ - dG ν a μ σ + ∑ l, (G a μ l * G l ν σ - G a ν l * G l μ σ)) * X σ * B μ * A ν =
      dG μ a ν σ * X σ * B μ * A ν - dG ν a μ σ * X σ * B μ * A ν +
        ((∑ l, G a μ l * G l ν σ) * X σ * B μ * A ν - (∑ l, G a ν l * G l μ σ) * X σ * B μ * A ν) := by
    intro σ μ ν
    rw [Finset.sum_sub_distrib]; ring
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => e σ μ ν]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [r1, r2, r3, r4]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

section Jets

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- `covDAlong` is the derivative plus the Christoffel term. -/
theorem covDAlong_eq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x v W W' : Fin n → ℝ) :
    (fun a => covDAlong g x v W W' a) = W' + Lightlike.Geodesic.gammaApply g x v W := by
  funext a
  simp [covDAlong, Lightlike.Geodesic.gammaApply]

/-- The covariant derivative `D_s Y = Y' + Γ(c, c', Y)` of a field along a curve. -/
def covK (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c c1 Y Y1 : ℝ → Fin n → ℝ) (s : ℝ) : Fin n → ℝ :=
  Y1 s + Lightlike.Geodesic.gammaApply g (c s) (c1 s) (Y s)

/-- The derivative of `covK`. -/
def covK' (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c c1 c2 Y Y1 Y2 : ℝ → Fin n → ℝ) (s : ℝ) :
    Fin n → ℝ :=
  Y2 s + (Lightlike.Geodesic.gammaDeriv g (c s) (c1 s) (c1 s) (Y s) +
    Lightlike.Geodesic.gammaApply g (c s) (c2 s) (Y s) + Lightlike.Geodesic.gammaApply g (c s) (c1 s) (Y1 s))

/-- **First derivative** of `s ↦ g(c)(Y, Y)`. -/
theorem hasDerivAt_normK (hg : Lightlike.IsCoordMetric g U) {c c1 Y Y1 : ℝ → Fin n → ℝ} {s : ℝ}
    (hc : HasDerivAt c (c1 s) s) (hY : HasDerivAt Y (Y1 s) s) (hs : c s ∈ U) :
    HasDerivAt (fun r => gpairAt g (c r) (Y r) (Y r)) (2 * gpairAt g (c s) (covK g c c1 Y Y1 s) (Y s)) s := by
  have h := hasDerivAt_gpair hg hc hs hY hY
  refine h.congr_deriv ?_
  rw [gpairAt_symm hg hs (Y s)]
  have e : (fun a => covDAlong g (c s) (c1 s) (Y s) (Y1 s) a) = covK g c c1 Y Y1 s := by
    rw [covDAlong_eq]; rfl
  rw [e]; ring

/-- The derivative of `covK`. -/
theorem hasDerivAt_covK (hg : Lightlike.IsCoordMetric g U) {c c1 c2 Y Y1 Y2 : ℝ → Fin n → ℝ} {s : ℝ}
    (hc : HasDerivAt c (c1 s) s) (hc1 : HasDerivAt c1 (c2 s) s) (hY : HasDerivAt Y (Y1 s) s)
    (hY1 : HasDerivAt Y1 (Y2 s) s) (hs : c s ∈ U) :
    HasDerivAt (covK g c c1 Y Y1) (covK' g c c1 c2 Y Y1 Y2 s) s := by
  have hch : ∀ i j k, DifferentiableAt ℝ (Lightlike.christoffel g i j k) (c s) := fun i j k =>
    ((hg.contDiffOn_christoffel i j k).contDiffAt (hg.isOpen.mem_nhds hs)).differentiableAt (by simp)
  have hG := Lightlike.Geodesic.hasDerivAt_gammaApply (g := g) hch hc hc1 hY
  have := hY1.fun_add hG
  refine this.congr_deriv ?_
  unfold covK'
  abel

/-- **Second derivative** of `s ↦ g(c)(Y, Y)`: `f''/2 = g(K' + Γ(c', K), Y) + g(K, K)`. -/
theorem hasDerivAt_normK_second (hg : Lightlike.IsCoordMetric g U) {c c1 c2 Y Y1 Y2 : ℝ → Fin n → ℝ} {s : ℝ}
    (hc : HasDerivAt c (c1 s) s) (hc1 : HasDerivAt c1 (c2 s) s) (hY : HasDerivAt Y (Y1 s) s)
    (hY1 : HasDerivAt Y1 (Y2 s) s) (hs : c s ∈ U) :
    HasDerivAt (fun r => 2 * gpairAt g (c r) (covK g c c1 Y Y1 r) (Y r))
      (2 * (gpairAt g (c s) (covK' g c c1 c2 Y Y1 Y2 s +
            Lightlike.Geodesic.gammaApply g (c s) (c1 s) (covK g c c1 Y Y1 s)) (Y s) +
        gpairAt g (c s) (covK g c c1 Y Y1 s) (covK g c c1 Y Y1 s))) s := by
  have h := hasDerivAt_gpair hg hc hs (hasDerivAt_covK hg hc hc1 hY hY1 hs) hY
  refine (h.const_mul 2).congr_deriv ?_
  have e1 : (fun a => covDAlong g (c s) (c1 s) (covK g c c1 Y Y1 s) (covK' g c c1 c2 Y Y1 Y2 s) a) =
      covK' g c c1 c2 Y Y1 Y2 s + Lightlike.Geodesic.gammaApply g (c s) (c1 s) (covK g c c1 Y Y1 s) :=
    covDAlong_eq g _ _ _ _
  have e2 : (fun a => covDAlong g (c s) (c1 s) (Y s) (Y1 s) a) = covK g c c1 Y Y1 s := by
    rw [covDAlong_eq]; rfl
  rw [e1, e2]

end Jets

end Lightlike.Penrose
