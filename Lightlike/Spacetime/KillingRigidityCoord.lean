import Lightlike.Spacetime.PalatiniCoord
import Lightlike.Spacetime.RicciContinuous
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.EHManifold.DomainDivergence

/-!
# Killing rigidity in coordinates (G1-024)

For a coordinate metric and a smooth covector field `θ` in coordinates:

* `covCo`, `covCo2`: the covariant derivatives `∇_a θ_b` and `∇_a ∇_b θ_c`;
* `covCo2_sub_covCo2`: the Ricci identity `∇_a ∇_b θ_c - ∇_b ∇_a θ_c = -Rᵈ_{cab} θ_d`;
* `covCo2_antisymm`: if `θ` satisfies Killing's equation `∇_a θ_b + ∇_b θ_a = 0` near a point, `∇_a ∇_b θ_c` is
  antisymmetric in `b, c` there;
* `covCo2_killing`: for such `θ`, `∇_a ∇_b θ_c = Rᵈ_{abc} θ_d` (from the Ricci identity at three orderings of the
  indices and the first Bianchi identity): the second derivatives of a Killing field are determined by its value.

## References

* M. Blau, *Lecture Notes on General Relativity* (version of 15 November 2026,
  http://www.blau.itp.unibe.ch/newlecturesGR.pdf), section 13.2, eqs. (13.5)–(13.8), p. 322, and section 14.1,
  eq. (14.2) and the statement after it, p. 337: `∇_α ∇_β K_γ = Rᵟ_{αβγ} K_δ`, so that "a Killing vector field is
  completely and uniquely determined everywhere by the values of `K_μ(x₀)` and `∇_μ K_ν(x₀)` at a single point".
-/

open Matrix Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The covariant derivative `∇_a θ_b = ∂_a θ_b - Γᶜ_{ab} θ_c` of a covector field in coordinates. -/
def covCo (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (θ : (Fin n → ℝ) → Fin n → ℝ) (a b : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  pd a (fun z => θ z b) y - ∑ c, christoffel g c a b y * θ y c

/-- The second covariant derivative `∇_a ∇_b θ_c = ∂_a (∇_b θ_c) - Γᵈ_{ab} ∇_d θ_c - Γᵈ_{ac} ∇_b θ_d`. -/
def covCo2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (θ : (Fin n → ℝ) → Fin n → ℝ) (a b c : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  pd a (fun z => covCo g θ b c z) y - ∑ d, christoffel g d a b y * covCo g θ d c y -
    ∑ d, christoffel g d a c y * covCo g θ b d y

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {θ : (Fin n → ℝ) → Fin n → ℝ}
  {y : Fin n → ℝ}

variable (hg : IsCoordMetric g U) (hgs : ∀ z a b, g z a b = g z b a) (hθ : ∀ c, ContDiffOn ℝ ∞ (fun z => θ z c) U)
  (hy : y ∈ U)
include hg hgs hθ hy

/-- **The Ricci identity for a covector field** in coordinates: `∇_a ∇_b θ_c - ∇_b ∇_a θ_c = -Rᵈ_{cab} θ_d`. -/
theorem covCo2_sub_covCo2 (a b c : Fin n) :
    covCo2 g θ a b c y - covCo2 g θ b a c y = -∑ d, riemann g d c a b y * θ y d := by
  have hdθ : ∀ c, DifferentiableAt ℝ (fun z => θ z c) y := fun c =>
    differentiableAt_of_contDiffOn (hθ c) hg.isOpen hy
  have hdpθ : ∀ k c, DifferentiableAt ℝ (fun z => pd k (fun w => θ w c) z) y := fun k c =>
    differentiableAt_of_contDiffOn (contDiffOn_pd (hθ c) hg.isOpen k) hg.isOpen hy
  have hdΓ : ∀ i j k, DifferentiableAt ℝ (christoffel g i j k) y := fun i j k =>
    differentiableAt_of_contDiffOn (contDiffOn_christoffel hg i j k) hg.isOpen hy
  have hΓ : ∀ l i j, christoffel g l i j y = christoffel g l j i y := fun l i j => christoffel_symm g hgs l i j y
  have hpd : ∀ k b c, pd k (fun z => covCo g θ b c z) y =
      pd k (fun z => pd b (fun w => θ w c) z) y -
        ∑ e, (pd k (christoffel g e b c) y * θ y e + christoffel g e b c y * pd k (fun z => θ z e) y) := by
    intro k b c
    unfold covCo
    rw [pd_sub (f₁ := fun z => pd b (fun w => θ w c) z) (f₂ := fun z => ∑ e, christoffel g e b c z * θ z e)
      (hdpθ b c) (DifferentiableAt.fun_sum fun e _ => (hdΓ e b c).mul (hdθ e)) k,
      pd_sum Finset.univ (f := fun e z => christoffel g e b c z * θ z e) (fun e _ => (hdΓ e b c).mul (hdθ e)) k]
    congr 1
    exact Finset.sum_congr rfl fun e _ => pd_mul (hdΓ e b c) (hdθ e) k
  have hcomm : pd a (fun z => pd b (fun w => θ w c) z) y = pd b (fun z => pd a (fun w => θ w c) z) y :=
    pd_pd_comm (hθ c) hg.isOpen hy a b
  unfold covCo2
  rw [hpd a b c, hpd b a c, hcomm]
  unfold covCo riemann
  simp only [hΓ _ b a, Finset.mul_sum, Finset.sum_mul, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, add_mul]
  have h1 : ∑ x, ∑ i, christoffel g x a c y * (christoffel g i b x y * θ y i) =
      ∑ x, ∑ i, christoffel g x b i y * christoffel g i a c y * θ y x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ x, ∑ i, christoffel g x b c y * (christoffel g i a x y * θ y i) =
      ∑ x, ∑ i, christoffel g x a i y * christoffel g i b c y * θ y x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [h1, h2]
  ring

omit hgs in
/-- A covector field satisfying Killing's equation near `y` has a second covariant derivative antisymmetric in its last
two indices at `y`. -/
theorem covCo2_antisymm (hK : ∀ᶠ z in 𝓝 y, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) (a b c : Fin n) :
    covCo2 g θ a b c y + covCo2 g θ a c b y = 0 := by
  have hdθ : ∀ c, DifferentiableAt ℝ (fun z => θ z c) y := fun c =>
    differentiableAt_of_contDiffOn (hθ c) hg.isOpen hy
  have hdpθ : ∀ k c, DifferentiableAt ℝ (fun z => pd k (fun w => θ w c) z) y := fun k c =>
    differentiableAt_of_contDiffOn (contDiffOn_pd (hθ c) hg.isOpen k) hg.isOpen hy
  have hdΓ : ∀ i j k, DifferentiableAt ℝ (christoffel g i j k) y := fun i j k =>
    differentiableAt_of_contDiffOn (contDiffOn_christoffel hg i j k) hg.isOpen hy
  have hdcov : ∀ b c, DifferentiableAt ℝ (fun z => covCo g θ b c z) y := fun b c =>
    (hdpθ b c).sub (DifferentiableAt.fun_sum fun e _ => (hdΓ e b c).mul (hdθ e))
  have hK0 := hK.self_of_nhds
  have hpd : pd a (fun z => covCo g θ b c z) y + pd a (fun z => covCo g θ c b z) y = 0 := by
    rw [← pd_add (hdcov b c) (hdcov c b)]
    exact pd_eq_zero_of_eventually_eq_zero (hK.mono fun z hz => hz b c) a
  have e1 : ∑ d, christoffel g d a b y * covCo g θ d c y + ∑ d, christoffel g d a b y * covCo g θ c d y = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun d _ => by rw [← mul_add, hK0 d c, mul_zero]
  have e2 : ∑ d, christoffel g d a c y * covCo g θ b d y + ∑ d, christoffel g d a c y * covCo g θ d b y = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun d _ => by rw [← mul_add, hK0 b d, mul_zero]
  unfold covCo2
  linarith

/-- **The second covariant derivative of a Killing covector** (Blau (13.8)): if `∇_a θ_b + ∇_b θ_a = 0` near `y`, then
`∇_a ∇_b θ_c = Rᵈ_{abc} θ_d` at `y`. -/
theorem covCo2_killing (hK : ∀ᶠ z in 𝓝 y, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) (a b c : Fin n) :
    covCo2 g θ a b c y = ∑ d, riemann g d a b c y * θ y d := by
  have r1 := covCo2_sub_covCo2 hg hgs hθ hy a b c
  have r2 := covCo2_sub_covCo2 hg hgs hθ hy b c a
  have r3 := covCo2_sub_covCo2 hg hgs hθ hy c a b
  have i1 := covCo2_antisymm hg hθ hy hK a b c
  have i2 := covCo2_antisymm hg hθ hy hK b c a
  have i3 := covCo2_antisymm hg hθ hy hK c a b
  have hb : ∑ d, riemann g d c a b y * θ y d + ∑ d, riemann g d a b c y * θ y d +
      ∑ d, riemann g d b c a y * θ y d = 0 := by
    simp only [← Finset.sum_add_distrib, ← add_mul]
    exact Finset.sum_eq_zero fun d _ => by rw [hg.bianchi_first hy d c a b, zero_mul]
  linarith

end

end Lightlike
