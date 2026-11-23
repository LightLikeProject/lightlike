import Lightlike.Regge.Geodesic.Equation
import Lightlike.Spacetime.Curvature

/-!
# Jacobi fields along a geodesic, in a chart (row G1-006, GE3)

The geodesic deviation (Jacobi) equation `D²J = -R(J, γ')γ'` for a coordinate metric `g`, the
analytic input to conjugate points and to the singularity theorems.

## Main definitions

* `Lightlike.Geodesic.gammaApply g x v u`: the vector `Γ(x)(v, u)^i = Σ Γ^i_{jk}(x) v^j u^k`.
* `Lightlike.Geodesic.riemannApply g x w J`: the vector `R^i_{σμν}(x) w^σ J^μ w^ν`.
* `Lightlike.Geodesic.IsJacobiOn g γ w J P I`: on `I`, `γ` is a geodesic with velocity `w`, `J` is
  a field along it and `P = D_t J` its covariant derivative (`J' = P - Γ(w, J)`), with
  `P' = -Γ(w, P) - R(J, w) w`, i.e. `D_t D_t J = -R(J, w) w` in the sign convention of
  `Lightlike.riemann` (`R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - …`, as in Carroll (3.67)).

## Trust checks

For a constant metric (flat chart) `J'' = 0`: `J t = a + t b` is a Jacobi field along a line
(`isJacobiOn_const_metric_line`), and `J t = t² e` with `e ≠ 0` is not
(`not_isJacobiOn_const_metric_quadratic`).
-/

open Set Filter Topology Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}

/-- The vector `Γ(x)(v, u)^i = Σ_{j,k} Γ^i_{jk}(x) v^j u^k` (the connection term of the covariant
derivative along a curve with velocity `v`). -/
noncomputable def gammaApply (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x v u : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, ∑ k, Lightlike.christoffel g i j k x * v j * u k

/-- The vector `R(J, w) w` with components `R^i_{σμν}(x) w^σ J^μ w^ν`. -/
noncomputable def riemannApply (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w J : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ σ, ∑ μ, ∑ ν, Lightlike.riemann g i σ μ ν x * w σ * J μ * w ν

/-- `J` is a **Jacobi field** along the geodesic `γ` (velocity `w`) on `I`, with `P = D_t J`:
`J' = P - Γ(w, J)` and `P' = -Γ(w, P) - R(J, w) w`, so that `D_t D_t J + R(J, w) w = 0`. -/
structure IsJacobiOn (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ w J P : ℝ → Fin n → ℝ)
    (I : Set ℝ) : Prop where
  /-- `γ` is a geodesic with velocity `w`. -/
  geodesic : IsGeodesicOn g γ w I
  /-- `P` is the covariant derivative of `J` along `γ`. -/
  deriv_field : ∀ t ∈ I, HasDerivAt J (P t - gammaApply g (γ t) (w t) (J t)) t
  /-- The Jacobi equation `D_t P = -R(J, w) w`. -/
  deriv_cov : ∀ t ∈ I,
    HasDerivAt P (-gammaApply g (γ t) (w t) (P t) - riemannApply g (γ t) (w t) (J t)) t

/-- For a constant metric all Christoffel symbols vanish. -/
theorem christoffel_const (G : Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) (x : Fin n → ℝ) :
    Lightlike.christoffel (fun _ => G) i j k x = 0 := by
  simp [Lightlike.christoffel, Lightlike.pd]

/-- For a constant metric the Riemann tensor vanishes. -/
theorem riemann_const (G : Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n) (x : Fin n → ℝ) :
    Lightlike.riemann (fun _ => G) ρ σ μ ν x = 0 := by
  have h : ∀ a b c, Lightlike.christoffel (fun _ => G) a b c = fun _ => 0 :=
    fun a b c => funext (christoffel_const G a b c)
  simp [Lightlike.riemann, h, Lightlike.pd]

/-- **Trust check, flat chart**: along a straight line `γ t = x + t v` of a constant metric,
`J t = a + t b` (with `P = b`) is a Jacobi field. -/
theorem isJacobiOn_const_metric_line (G : Matrix (Fin n) (Fin n) ℝ) (x v a b : Fin n → ℝ) :
    IsJacobiOn (fun _ => G) (fun t => x + t • v) (fun _ => v) (fun t => a + t • b) (fun _ => b)
      univ where
  geodesic := by
    refine ⟨fun t _ => ?_, fun t _ => ?_⟩
    · simpa using ((hasDerivAt_id t).smul_const v).const_add x
    · have : accel (fun _ => G) (x + t • v) v = 0 := by
        funext i
        simp [accel, christoffel_const]
      rw [this]
      exact hasDerivAt_const t v
  deriv_field := fun t _ => by
    have : gammaApply (fun _ => G) (x + t • v) v (a + t • b) = 0 := by
      funext i
      simp [gammaApply, christoffel_const]
    rw [this, sub_zero]
    simpa using ((hasDerivAt_id t).smul_const b).const_add a
  deriv_cov := fun t _ => by
    have h1 : gammaApply (fun _ => G) (x + t • v) v b = 0 := by
      funext i
      simp [gammaApply, christoffel_const]
    have h2 : riemannApply (fun _ => G) (x + t • v) v (a + t • b) = 0 := by
      funext i
      simp [riemannApply, riemann_const]
    rw [h1, h2]
    simpa using hasDerivAt_const t b

/-- **Trust check, wrong field**: in a flat chart, `J t = t² e` with `e ≠ 0` is not a Jacobi field
along a line with velocity `v`, for any choice of `P`. -/
theorem not_isJacobiOn_const_metric_quadratic (G : Matrix (Fin n) (Fin n) ℝ) (x v e : Fin n → ℝ)
    (he : e ≠ 0) (P : ℝ → Fin n → ℝ) :
    ¬ IsJacobiOn (fun _ => G) (fun t : ℝ => x + t • v) (fun _ => v) (fun t : ℝ => t ^ 2 • e) P
      univ := by
  intro h
  have g1 : ∀ (t : ℝ) u, gammaApply (fun _ => G) (x + t • v) v u = 0 := by
    intro t u; funext i
    simp [gammaApply, christoffel_const]
  have g2 : ∀ (t : ℝ) u, riemannApply (fun _ => G) (x + t • v) v u = 0 := by
    intro t u; funext i
    simp [riemannApply, riemann_const]
  have hPeq : P = fun t : ℝ => (2 * t) • e := by
    funext t
    have h1 := h.deriv_field t (mem_univ _)
    rw [g1, sub_zero] at h1
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 • e) ((2 * t) • e) t := by
      simpa [two_mul, pow_two] using ((hasDerivAt_pow 2 t).smul_const e)
    exact h1.unique h2
  have h3 := h.deriv_cov 0 (mem_univ _)
  rw [g1, g2, hPeq] at h3
  have h4 : HasDerivAt (fun t : ℝ => (2 * t) • e) ((2 : ℝ) • e) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).smul_const e
  have h5 := h3.unique h4
  apply he
  simpa using h5.symm

end Lightlike.Geodesic
