import Lightlike.Spacetime.ChartChange
import Lightlike.Regge.Geodesic.Equation

/-!
# Geodesics are chart-independent

Let `φ` be a chart change from `V` into `U` and `g` a coordinate metric on `U`. If `(c, u)` is a geodesic of the
pulled-back metric `pullback g φ` staying in `V`, then `(φ ∘ c, J u)` with `J = ∂φ` is a geodesic of `g`
(`Lightlike.Geodesic.IsGeodesicOn.map_chartChange`). The proof is the transformation law of the Christoffel
symbols (`christoffel_pullback`): the inhomogeneous term `∂²φ` cancels the derivative of the Jacobian along the
curve.
-/

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U V : Set (Fin n → ℝ)}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}

/-- Reordering a fourfold sum. -/
lemma sum4_comm (F : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ∑ b, ∑ c, ∑ ν, ∑ l, F b c ν l = ∑ ν, ∑ l, ∑ b, ∑ c, F b c ν l := by
  calc ∑ b, ∑ c, ∑ ν, ∑ l, F b c ν l = ∑ b, ∑ ν, ∑ c, ∑ l, F b c ν l :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ ν, ∑ b, ∑ c, ∑ l, F b c ν l := Finset.sum_comm
    _ = ∑ ν, ∑ b, ∑ l, ∑ c, F b c ν l :=
        Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ ν, ∑ l, ∑ b, ∑ c, F b c ν l := Finset.sum_congr rfl fun ν _ => Finset.sum_comm

/-- The algebra of the transformation: with the Christoffel law
`Σ_a J_a Γ'^a_{bc} = Σ_{νl} Γ_{νl} J^ν_b J^l_c + H_{bc}`. -/
lemma accel_transform (J : Fin n → ℝ) (Jm : Fin n → Fin n → ℝ) (Γ' : Fin n → Fin n → Fin n → ℝ)
    (Γ H : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hlaw : ∀ b c, ∑ a, J a * Γ' a b c = ∑ ν, ∑ l, Γ ν l * Jm ν b * Jm l c + H b c) :
    ∑ a, ((∑ k, u k * H k a) * u a + J a * (-∑ b, ∑ c, Γ' a b c * u b * u c)) =
      -∑ ν, ∑ l, Γ ν l * (∑ b, Jm ν b * u b) * (∑ c, Jm l c * u c) := by
  have h1 : ∑ a, J a * (-∑ b, ∑ c, Γ' a b c * u b * u c) =
      -∑ b, ∑ c, (∑ a, J a * Γ' a b c) * u b * u c := by
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∑ a, (∑ k, u k * H k a) * u a = ∑ b, ∑ c, H b c * u b * u c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have h3 : ∑ ν, ∑ l, Γ ν l * (∑ b, Jm ν b * u b) * (∑ c, Jm l c * u c) =
      ∑ b, ∑ c, (∑ ν, ∑ l, Γ ν l * Jm ν b * Jm l c) * u b * u c := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum4_comm fun b c ν l => Γ ν l * Jm ν b * Jm l c * u b * u c]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_add_distrib, h1, h2, h3]
  simp only [hlaw, add_mul, Finset.sum_add_distrib]
  ring

/-- **Geodesics are chart-independent**: the image of a geodesic of the pulled-back metric under a chart
change is a geodesic, with velocity `J u`. -/
theorem IsGeodesicOn.map_chartChange (hg : Lightlike.IsCoordMetric g U)
    (hφ : Lightlike.IsChartChange φ V U) {c u : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hgeo : IsGeodesicOn (Lightlike.pullback g φ) c u I) (hc : ∀ t ∈ I, c t ∈ V) :
    IsGeodesicOn g (fun t => φ (c t)) (fun t => Lightlike.jac φ (c t) *ᵥ u t) I where
  pos := fun t ht => by
    rw [hasDerivAt_pi]
    intro μ
    have hd : DifferentiableAt ℝ (fun z => φ z μ) (c t) :=
      ((hφ.smooth μ).contDiffAt (hφ.isOpen.mem_nhds (hc t ht))).differentiableAt (by simp)
    refine (hasDerivAt_comp_pd hd (hgeo.pos t ht)).congr_deriv ?_
    show ∑ k, u t k * Lightlike.pd k (fun z => φ z μ) (c t) = ∑ k, Lightlike.jac φ (c t) μ k * u t k
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  vel := fun t ht => by
    rw [hasDerivAt_pi]
    intro μ
    have hV := hc t ht
    -- the derivative of the Jacobian along the curve
    have hJ : ∀ a, HasDerivAt (fun s => Lightlike.jac φ (c s) μ a)
        (∑ k, u t k * Lightlike.hess φ μ k a (c t)) t := fun a => by
      have hd : DifferentiableAt ℝ (fun z => Lightlike.jac φ z μ a) (c t) :=
        ((hφ.contDiffOn_jac μ a).contDiffAt (hφ.isOpen.mem_nhds hV)).differentiableAt (by simp)
      exact hasDerivAt_comp_pd hd (hgeo.pos t ht)
    have hu : ∀ a, HasDerivAt (fun s => u s a) (accel (Lightlike.pullback g φ) (c t) (u t) a) t :=
      fun a => hasDerivAt_pi.1 (hgeo.vel t ht) a
    have hsum : HasDerivAt (fun s => ∑ a, Lightlike.jac φ (c s) μ a * u s a)
        (∑ a, ((∑ k, u t k * Lightlike.hess φ μ k a (c t)) * u t a +
          Lightlike.jac φ (c t) μ a * accel (Lightlike.pullback g φ) (c t) (u t) a)) t :=
      HasDerivAt.fun_sum fun a _ => (hJ a).mul (hu a)
    refine hsum.congr_deriv ?_
    have hlaw : ∀ b d, ∑ a, Lightlike.jac φ (c t) μ a *
        Lightlike.christoffel (Lightlike.pullback g φ) a b d (c t) =
        ∑ ν, ∑ l, Lightlike.christoffel g μ ν l (φ (c t)) * Lightlike.jac φ (c t) ν b *
          Lightlike.jac φ (c t) l d + Lightlike.hess φ μ b d (c t) := fun b d =>
      Lightlike.christoffel_pullback hg hφ hV μ b d
    exact accel_transform (fun a => Lightlike.jac φ (c t) μ a) (fun ν b => Lightlike.jac φ (c t) ν b)
      (fun a b d => Lightlike.christoffel (Lightlike.pullback g φ) a b d (c t))
      (fun ν l => Lightlike.christoffel g μ ν l (φ (c t))) (fun b d => Lightlike.hess φ μ b d (c t))
      (u t) hlaw

end Lightlike.Geodesic
