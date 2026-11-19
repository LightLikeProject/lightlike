import Lightlike.Spacetime.KillingRigidityCoord
import Lightlike.Spacetime.ConformalCoord

/-!
# Killing algebras in coordinates (G1-024)

The bridge between the two coordinate forms of Killing's equation used in the library:

* `lowerVec`: the covector `θ_b = g_{bc} Yᶜ` of a vector field;
* `covCo_lowerVec`: `∇_a θ_b = g_{bl} (∂_a Yˡ + Γˡ_{ac} Yᶜ)`, the lowered covariant derivative of `Y`;
* `covCo_lowerVec_add`: `∇_a θ_b + ∇_b θ_a = Yᶜ ∂_c g_{ab} + ∂_a Yˡ g_{lb} + g_{al} ∂_b Yˡ`, the Lie derivative
  `(L_Y g)_{ab}` in coordinates (the form of the Killing hypotheses of `isometric_spaceForm` and
  `flrw_of_killing_algebra` on coordinate vectors), so the rigidity of `KillingRigidityCoord.lean` applies to those fields.
-/

open Matrix Filter Set
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The covector `θ_b = g_{bc} Yᶜ` of a vector field in coordinates. -/
def lowerVec (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (Y : (Fin n → ℝ) → Fin n → ℝ) (z : Fin n → ℝ)
    (b : Fin n) : ℝ :=
  ∑ c, g z b c * Y z c

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Y : (Fin n → ℝ) → Fin n → ℝ} {y : Fin n → ℝ}

/-- **The covariant derivative of the lowered field** is the lowered covariant derivative:
`∇_a θ_b = g_{bl} (∂_a Yˡ + Γˡ_{ac} Yᶜ)`. -/
theorem covCo_lowerVec (hgs : ∀ z a b, g z a b = g z b a) (hdet : (g y).det ≠ 0)
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (hY : ∀ c, DifferentiableAt ℝ (fun z => Y z c) y)
    (a b : Fin n) :
    covCo g (lowerVec g Y) a b y =
      ∑ l, g y b l * (pd a (fun z => Y z l) y + ∑ c, christoffel g l a c y * Y y c) := by
  unfold covCo lowerVec
  rw [pd_sum Finset.univ (f := fun c z => g z b c * Y z c) (fun c _ => (hgd b c).mul (hY c)) a]
  simp only [fun c => pd_mul (hgd b c) (hY c) a, pd_metric_eq_christoffel hgs hdet a b]
  simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  have e1 : ∑ c, ∑ l, g y l c * christoffel g l a b y * Y y c = ∑ c, ∑ l, christoffel g c a b y * (g y c l * Y y l) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [hgs y]; ring
  have e2 : ∑ c, ∑ l, g y b l * christoffel g l a c y * Y y c = ∑ l, ∑ c, g y b l * (christoffel g l a c y * Y y c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]
  ring

/-- **Killing's equation for the lowered field is the Lie-derivative form in coordinates**:
`∇_a θ_b + ∇_b θ_a = Yᶜ ∂_c g_{ab} + ∂_a Yˡ g_{lb} + g_{al} ∂_b Yˡ`. -/
theorem covCo_lowerVec_add (hgs : ∀ z a b, g z a b = g z b a) (hdet : (g y).det ≠ 0)
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (hY : ∀ c, DifferentiableAt ℝ (fun z => Y z c) y)
    (a b : Fin n) :
    covCo g (lowerVec g Y) a b y + covCo g (lowerVec g Y) b a y =
      ∑ c, Y y c * pd c (fun z => g z a b) y +
        ∑ l, (pd a (fun z => Y z l) y * g y l b + g y a l * pd b (fun z => Y z l) y) := by
  rw [covCo_lowerVec hgs hdet hgd hY, covCo_lowerVec hgs hdet hgd hY]
  simp only [pd_metric_eq_christoffel hgs hdet _ a b]
  have hΓ : ∀ l i j, christoffel g l i j y = christoffel g l j i y := fun l i j => christoffel_symm g hgs l i j y
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∑ l, ∑ c, g y b l * (christoffel g l a c y * Y y c) =
      ∑ c, ∑ l, Y y c * (g y l b * christoffel g l c a y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by rw [hgs y b l, hΓ l a c]; ring
  have e2 : ∑ l, ∑ c, g y a l * (christoffel g l b c y * Y y c) =
      ∑ c, ∑ l, Y y c * (g y a l * christoffel g l c b y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by rw [hΓ l b c]; ring
  rw [e1, e2]
  have e3 : ∀ l, g y b l * pd a (fun z => Y z l) y = pd a (fun z => Y z l) y * g y l b := fun l => by
    rw [hgs y b l]; ring
  simp only [e3]
  ring

end

end Lightlike
