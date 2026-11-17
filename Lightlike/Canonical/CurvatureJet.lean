import Mathlib
import Lightlike.Canonical.LieDeriv
import Lightlike.Canonical.MatrixInverseAt
import Lightlike.Spacetime.Curvature

/-!
# The curvature of a metric as a function of its 2-jet

`Lightlike.christoffel`, `riemann`, `ricci` and `scalarCurvature` at a point `x` depend only on the 2-jet
`(g x, ∂g x, ∂²g x)` of the metric there: with `Hi = (g x)⁻¹`, `Γ = ½ Hi (∂g + ∂g - ∂g)` and
`∂Γ = ½ (∂Hi)(∂g + ∂g - ∂g) + ½ Hi (∂²g + ∂²g - ∂²g)` with `∂ Hi = - Hi (∂g) Hi`. The explicit functions of
the jet are `gamJ`, `dgamJ`, `riemJ`, `scalJ`; `scalarCurvature_eq_scalJ` identifies them with the library
definitions for a smooth metric, nondegenerate at `x`. No curvature is defined here.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The Christoffel symbols from the inverse metric and the first jet. -/
def gamJ (Hi : Matrix (Fin d) (Fin d) ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (i j k : Fin d) : ℝ :=
  (1 / 2) * ∑ l, Hi i l * (h1 j l k + h1 k l j - h1 l j k)

/-- The derivative `∂_μ (g⁻¹)_{il} = - (g⁻¹ ∂_μ g g⁻¹)_{il}` from the first jet. -/
def dHiJ (Hi : Matrix (Fin d) (Fin d) ℝ) (h1 : Fin d → Fin d → Fin d → ℝ) (μ i l : Fin d) : ℝ :=
  -∑ b, ∑ c, Hi i c * h1 μ c b * Hi b l

/-- The derivative `∂_μ Γ^i_{jk}` from the 2-jet. -/
def dgamJ (Hi : Matrix (Fin d) (Fin d) ℝ) (h1 : Fin d → Fin d → Fin d → ℝ)
    (h2 : Fin d → Fin d → Fin d → Fin d → ℝ) (μ i j k : Fin d) : ℝ :=
  (1 / 2) * ∑ l, (dHiJ Hi h1 μ i l * (h1 j l k + h1 k l j - h1 l j k) +
    Hi i l * (h2 μ j l k + h2 μ k l j - h2 μ l j k))

/-- The Riemann tensor `R^ρ_{σμν}` from the 2-jet. -/
def riemJ (Hi : Matrix (Fin d) (Fin d) ℝ) (h1 : Fin d → Fin d → Fin d → ℝ)
    (h2 : Fin d → Fin d → Fin d → Fin d → ℝ) (ρ σ μ ν : Fin d) : ℝ :=
  dgamJ Hi h1 h2 μ ρ ν σ - dgamJ Hi h1 h2 ν ρ μ σ +
    ∑ l, (gamJ Hi h1 ρ μ l * gamJ Hi h1 l ν σ - gamJ Hi h1 ρ ν l * gamJ Hi h1 l μ σ)

/-- The scalar curvature `g^{σν} R^ρ_{σρν}` from the 2-jet. -/
def scalJ (Hi : Matrix (Fin d) (Fin d) ℝ) (h1 : Fin d → Fin d → Fin d → ℝ)
    (h2 : Fin d → Fin d → Fin d → Fin d → ℝ) : ℝ :=
  ∑ σ, ∑ ν, Hi σ ν * ∑ ρ, riemJ Hi h1 h2 ρ σ ρ ν

lemma christoffel_eq_gamJ (g : TensorField d) (i j k : Fin d) (y : Fin d → ℝ) :
    Lightlike.christoffel g i j k y = gamJ (g y)⁻¹ (jet1 g y) i j k := rfl

/-- The partial derivative of the Christoffel symbols is `dgamJ` of the 2-jet. -/
lemma pd_christoffel {g : TensorField d} (hg : SmoothTensor g) {x : Fin d → ℝ} (hdet : (g x).det ≠ 0)
    (μ i j k : Fin d) :
    Lightlike.pd μ (fun y => Lightlike.christoffel g i j k y) x =
      dgamJ (g x)⁻¹ (jet1 g x) (jet2 g x) μ i j k := by
  have dg : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b => diff_of_smooth (hg a b) x
  have dHi : ∀ i l, DifferentiableAt ℝ (fun y => (g y)⁻¹ i l) x := fun i l =>
    Gauge.differentiableAt_inv_entry g dg hdet i l
  have dT : ∀ l, DifferentiableAt ℝ (fun y => Lightlike.pd j (fun y => g y l k) y +
      Lightlike.pd k (fun y => g y l j) y - Lightlike.pd l (fun y => g y j k) y) x := fun l =>
    diff_of_smooth (((smooth_pd (hg l k) j).add (smooth_pd (hg l j) k)).sub (smooth_pd (hg j k) l)) x
  have e1 : (fun y => Lightlike.christoffel g i j k y) = fun y => (1 / 2 : ℝ) * ∑ l, (g y)⁻¹ i l *
      (Lightlike.pd j (fun y => g y l k) y + Lightlike.pd k (fun y => g y l j) y -
        Lightlike.pd l (fun y => g y j k) y) := rfl
  have hF : DifferentiableAt ℝ (fun y => ∑ l, (g y)⁻¹ i l *
      (Lightlike.pd j (fun y => g y l k) y + Lightlike.pd k (fun y => g y l j) y -
        Lightlike.pd l (fun y => g y j k) y)) x :=
    DifferentiableAt.fun_sum fun l _ => (dHi i l).mul (dT l)
  rw [e1, Lightlike.pd_const_mul (1 / 2 : ℝ)
    (f := fun y => ∑ l, (g y)⁻¹ i l * (Lightlike.pd j (fun y => g y l k) y +
      Lightlike.pd k (fun y => g y l j) y - Lightlike.pd l (fun y => g y j k) y)) hF μ]
  rw [Lightlike.pd_sum Finset.univ (f := fun l y => (g y)⁻¹ i l * (Lightlike.pd j (fun y => g y l k) y +
      Lightlike.pd k (fun y => g y l j) y - Lightlike.pd l (fun y => g y j k) y))
    (fun l _ => (dHi i l).mul (dT l))]
  unfold dgamJ
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Lightlike.pd_mul (dHi i l) (dT l)]
  have hs : ∀ a b : Fin d, Lightlike.pd μ (fun y => g y a b) x = jet1 g x μ a b := fun a b => rfl
  rw [Lightlike.pd_sub (f₁ := fun y => Lightlike.pd j (fun y => g y l k) y + Lightlike.pd k (fun y => g y l j) y)
      (f₂ := fun y => Lightlike.pd l (fun y => g y j k) y)
      ((diff_of_smooth (smooth_pd (hg l k) j) x).add (diff_of_smooth (smooth_pd (hg l j) k) x))
      (diff_of_smooth (smooth_pd (hg j k) l) x),
    Lightlike.pd_add (f₁ := fun y => Lightlike.pd j (fun y => g y l k) y)
      (f₂ := fun y => Lightlike.pd k (fun y => g y l j) y)
      (diff_of_smooth (smooth_pd (hg l k) j) x) (diff_of_smooth (smooth_pd (hg l j) k) x)]
  have hinv : Lightlike.pd μ (fun y => (g y)⁻¹ i l) x = dHiJ (g x)⁻¹ (jet1 g x) μ i l := by
    unfold dHiJ Lightlike.pd
    rw [Gauge.fderiv_inv_entry_at g (fun a b => (hg a b).differentiable (by simp)) _ _ hdet]
    rfl
  rw [hinv]
  rfl

/-- The Riemann tensor at `x` is `riemJ` of the 2-jet. -/
lemma riemann_eq_riemJ {g : TensorField d} (hg : SmoothTensor g) {x : Fin d → ℝ} (hdet : (g x).det ≠ 0)
    (ρ σ μ ν : Fin d) :
    Lightlike.riemann g ρ σ μ ν x = riemJ (g x)⁻¹ (jet1 g x) (jet2 g x) ρ σ μ ν := by
  unfold Lightlike.riemann riemJ
  rw [pd_christoffel hg hdet, pd_christoffel hg hdet]
  rfl

/-- **The scalar curvature at `x` is `scalJ` of the 2-jet** of a smooth metric that is nondegenerate at `x`. -/
theorem scalarCurvature_eq_scalJ {g : TensorField d} (hg : SmoothTensor g) {x : Fin d → ℝ}
    (hdet : (g x).det ≠ 0) :
    Lightlike.scalarCurvature g x = scalJ (g x)⁻¹ (jet1 g x) (jet2 g x) := by
  unfold Lightlike.scalarCurvature Lightlike.ricci scalJ
  simp only [riemann_eq_riemJ hg hdet]

/-- The space of 2-jets of a metric at a point: `(h, ∂h, ∂²h)` as arrays of numbers. -/
abbrev Jet (d : ℕ) :=
  (Fin d → Fin d → ℝ) × (Fin d → Fin d → Fin d → ℝ) × (Fin d → Fin d → Fin d → Fin d → ℝ)

/-- The 2-jet of a tensor field at a point. -/
def jetAt (g : TensorField d) (x : Fin d → ℝ) : Jet d :=
  (fun a b => g x a b, jet1 g x, jet2 g x)

/-- The scalar curvature as a function on the space of jets. -/
def Rjet (J : Jet d) : ℝ := scalJ (Matrix.of J.1)⁻¹ J.2.1 J.2.2

lemma scalarCurvature_eq_Rjet {g : TensorField d} (hg : SmoothTensor g) {x : Fin d → ℝ}
    (hdet : (g x).det ≠ 0) : Lightlike.scalarCurvature g x = Rjet (jetAt g x) :=
  scalarCurvature_eq_scalJ hg hdet

/-- **The scalar curvature is differentiable on the space of jets** at every jet whose metric is invertible. -/
theorem differentiableAt_Rjet {J : Jet d} (hdet : (Matrix.of J.1).det ≠ 0) : DifferentiableAt ℝ Rjet J := by
  have hHi : ∀ a b, DifferentiableAt ℝ (fun J : Jet d => ((Matrix.of J.1)⁻¹) a b) J := fun a b =>
    Gauge.differentiableAt_inv_entry (fun J : Jet d => Matrix.of J.1)
      (fun i j => by
        simp only [Matrix.of_apply]
        exact ((differentiableAt_pi.mp (differentiableAt_pi.mp differentiableAt_fst i)) j)) hdet a b
  have h1 : ∀ a b c, DifferentiableAt ℝ (fun J : Jet d => J.2.1 a b c) J := fun a b c => by fun_prop
  have h2 : ∀ a b c e, DifferentiableAt ℝ (fun J : Jet d => J.2.2 a b c e) J := fun a b c e => by fun_prop
  have dgam : ∀ i j k, DifferentiableAt ℝ (fun J : Jet d => gamJ (Matrix.of J.1)⁻¹ J.2.1 i j k) J := by
    intro i j k
    unfold gamJ
    exact (DifferentiableAt.fun_sum fun l _ => (hHi i l).mul (((h1 j l k).add (h1 k l j)).sub (h1 l j k))).const_mul _
  have ddHi : ∀ μ i l, DifferentiableAt ℝ (fun J : Jet d => dHiJ (Matrix.of J.1)⁻¹ J.2.1 μ i l) J := by
    intro μ i l
    unfold dHiJ
    exact (DifferentiableAt.fun_sum fun b _ => DifferentiableAt.fun_sum fun c _ =>
      ((hHi i c).mul (h1 μ c b)).mul (hHi b l)).neg
  have ddgam : ∀ μ i j k, DifferentiableAt ℝ (fun J : Jet d => dgamJ (Matrix.of J.1)⁻¹ J.2.1 J.2.2 μ i j k) J := by
    intro μ i j k
    unfold dgamJ
    exact (DifferentiableAt.fun_sum fun l _ => ((ddHi μ i l).mul (((h1 j l k).add (h1 k l j)).sub (h1 l j k))).add
      ((hHi i l).mul (((h2 μ j l k).add (h2 μ k l j)).sub (h2 μ l j k)))).const_mul _
  have driem : ∀ ρ σ μ ν, DifferentiableAt ℝ
      (fun J : Jet d => riemJ (Matrix.of J.1)⁻¹ J.2.1 J.2.2 ρ σ μ ν) J := by
    intro ρ σ μ ν
    unfold riemJ
    exact ((ddgam μ ρ ν σ).sub (ddgam ν ρ μ σ)).add (DifferentiableAt.fun_sum fun l _ =>
      (((dgam ρ μ l).mul (dgam l ν σ)).sub ((dgam ρ ν l).mul (dgam l μ σ))))
  unfold Rjet scalJ
  exact DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.fun_sum fun ν _ =>
    (hHi σ ν).mul (DifferentiableAt.fun_sum fun ρ _ => driem ρ σ ρ ν)

end Lightlike.Canonical
