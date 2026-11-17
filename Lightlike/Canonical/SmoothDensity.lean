import Mathlib
import Lightlike.Canonical.MatrixSmooth
import Lightlike.Canonical.CurvatureJet
import Lightlike.Canonical.DensityDeriv

/-!
# Smoothness of the curvature and kinetic terms as functions of the jets

`Rjet` (the scalar curvature as a function of the 2-jet), `Kfun` (the kinetic term) and `√det` are `C^∞` where the
metric is invertible. This is what makes the Hamiltonian density jointly smooth in the parameter of a variation
`h + t k` and the point, so that the derivative of the smeared constraint can be taken under the integral sign.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- **The scalar curvature is `C^∞` on the space of jets** at every jet whose metric is invertible. -/
theorem contDiffAt_Rjet {J : Jet d} (hdet : (Matrix.of J.1).det ≠ 0) : ContDiffAt ℝ ∞ Rjet J := by
  have hHi : ∀ a b, ContDiffAt ℝ ∞ (fun J : Jet d => ((Matrix.of J.1)⁻¹) a b) J := fun a b =>
    contDiffAt_inv_entry (fun J : Jet d => Matrix.of J.1)
      (fun i j => by simp only [Matrix.of_apply]; fun_prop) hdet a b
  have h1 : ∀ a b c, ContDiffAt ℝ ∞ (fun J : Jet d => J.2.1 a b c) J := fun a b c => by fun_prop
  have h2 : ∀ a b c e, ContDiffAt ℝ ∞ (fun J : Jet d => J.2.2 a b c e) J := fun a b c e => by fun_prop
  have dgam : ∀ i j k, ContDiffAt ℝ ∞ (fun J : Jet d => gamJ (Matrix.of J.1)⁻¹ J.2.1 i j k) J := by
    intro i j k
    unfold gamJ
    exact contDiffAt_const.mul (ContDiffAt.sum fun l _ => (hHi i l).mul (((h1 j l k).add (h1 k l j)).sub (h1 l j k)))
  have ddHi : ∀ μ i l, ContDiffAt ℝ ∞ (fun J : Jet d => dHiJ (Matrix.of J.1)⁻¹ J.2.1 μ i l) J := by
    intro μ i l
    unfold dHiJ
    exact (ContDiffAt.sum fun b _ => ContDiffAt.sum fun c _ => ((hHi i c).mul (h1 μ c b)).mul (hHi b l)).neg
  have ddgam : ∀ μ i j k, ContDiffAt ℝ ∞ (fun J : Jet d => dgamJ (Matrix.of J.1)⁻¹ J.2.1 J.2.2 μ i j k) J := by
    intro μ i j k
    unfold dgamJ
    exact contDiffAt_const.mul (ContDiffAt.sum fun l _ => ((ddHi μ i l).mul (((h1 j l k).add (h1 k l j)).sub
      (h1 l j k))).add ((hHi i l).mul (((h2 μ j l k).add (h2 μ k l j)).sub (h2 μ l j k))))
  have driem : ∀ ρ σ μ ν, ContDiffAt ℝ ∞
      (fun J : Jet d => riemJ (Matrix.of J.1)⁻¹ J.2.1 J.2.2 ρ σ μ ν) J := by
    intro ρ σ μ ν
    unfold riemJ
    exact ((ddgam μ ρ ν σ).sub (ddgam ν ρ μ σ)).add (ContDiffAt.sum fun l _ =>
      (((dgam ρ μ l).mul (dgam l ν σ)).sub ((dgam ρ ν l).mul (dgam l μ σ))))
  unfold Rjet scalJ
  exact ContDiffAt.sum fun σ _ => ContDiffAt.sum fun ν _ =>
    (hHi σ ν).mul (ContDiffAt.sum fun ρ _ => driem ρ σ ρ ν)

lemma dm_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F G : E → Matrix (Fin d) (Fin d) ℝ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ ∞ (fun z => F z i j) x) (hG : ∀ i j, ContDiffAt ℝ ∞ (fun z => G z i j) x)
    (i j : Fin d) : ContDiffAt ℝ ∞ (fun z => (F z * G z) i j) x := by
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun k _ => (hF i k).mul (hG k j)

lemma dm_trace' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Matrix (Fin d) (Fin d) ℝ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ ∞ (fun z => F z i j) x) :
    ContDiffAt ℝ ∞ (fun z => (F z).trace) x := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact ContDiffAt.sum fun i _ => hF i i

/-- The kinetic term is `C^∞` where `det H > 0`. -/
lemma contDiffAt_Kfun (c : ℝ) {Z : Arr d} (hZ : 0 < (Matrix.of Z.1).det) : ContDiffAt ℝ ∞ (Kfun c) Z := by
  have h1 : ∀ i j, ContDiffAt ℝ ∞ (fun Z : Arr d => (Matrix.of Z.1) i j) Z := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have h2 : ∀ i j, ContDiffAt ℝ ∞ (fun Z : Arr d => (Matrix.of Z.2) i j) Z := fun i j => by
    simp only [Matrix.of_apply]; fun_prop
  have hHP := dm_mul' h1 h2
  have hHPHP := dm_mul' (dm_mul' hHP h1) h2
  have hnum : ContDiffAt ℝ ∞ (fun Z : Arr d => ((Matrix.of Z.1) * (Matrix.of Z.2) * (Matrix.of Z.1) *
      (Matrix.of Z.2)).trace - c * ((Matrix.of Z.1) * (Matrix.of Z.2)).trace ^ 2) Z :=
    (dm_trace' hHPHP).sub (contDiffAt_const.mul ((dm_trace' hHP).pow 2))
  have hdet : ContDiffAt ℝ ∞ (fun Z : Arr d => (Matrix.of Z.1).det) Z := contDiffAt_det (fun Z : Arr d => Matrix.of Z.1) h1
  have hs : ContDiffAt ℝ ∞ (fun Z : Arr d => Real.sqrt (Matrix.of Z.1).det) Z := hdet.sqrt hZ.ne'
  have hne : Real.sqrt (Matrix.of Z.1).det ≠ 0 := (Real.sqrt_pos.mpr hZ).ne'
  unfold Kfun kinJ
  simp only [div_eq_mul_inv]
  exact hnum.mul (hs.inv hne)

end Lightlike.Canonical

end
