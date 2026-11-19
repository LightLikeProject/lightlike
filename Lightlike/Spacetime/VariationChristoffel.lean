import Lightlike.Spacetime.VariationDet
import Lightlike.Spacetime.Curvature

/-!
# The variation of the Christoffel symbols (GE15, stage S1)

For a metric `g` and a symmetric perturbation `h` (smooth near `x`), `g_t = g + t h`: the Christoffel symbols of `g_t` at `x`
are differentiable in `t` and
`d/dt Γ^i_{jk}(g_t) |_{t=0} = ½ gⁱˡ (∂_j h_{lk} + ∂_k h_{lj} − ∂_l h_{jk}) − ½ (g⁻¹ h g⁻¹)ⁱˡ (∂_j g_{lk} + ∂_k g_{lj} − ∂_l g_{jk})`
(`hasDerivAt_christoffel_add_smul`).
-/

open Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

theorem pd_add_smul (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (j l k : Fin n) (x : Fin n → ℝ)
    (hg : DifferentiableAt ℝ (fun y => g y l k) x) (hh : DifferentiableAt ℝ (fun y => h y l k) x) :
    pd j (fun y => (g y + t • h y) l k) x = pd j (fun y => g y l k) x + t * pd j (fun y => h y l k) x := by
  unfold pd
  have : (fun y => (g y + t • h y) l k) = fun y => g y l k + t * h y l k := by
    funext y; simp
  have hd : HasFDerivAt (fun y => g y l k + t * h y l k)
      (fderiv ℝ (fun y => g y l k) x + t • fderiv ℝ (fun y => h y l k) x) x :=
    hg.hasFDerivAt.add (hh.hasFDerivAt.const_mul t)
  rw [this, hd.fderiv]
  simp


/-- **The variation of the Christoffel symbols**. -/
theorem hasDerivAt_christoffel_add_smul (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hgd : ∀ l k, DifferentiableAt ℝ (fun y => g y l k) x) (hhd : ∀ l k, DifferentiableAt ℝ (fun y => h y l k) x)
    (hG : (g x).det ≠ 0) (i j k : Fin n) :
    HasDerivAt (fun t : ℝ => christoffel (fun y => g y + t • h y) i j k x)
      ((1 / 2) * ∑ l, (-((g x)⁻¹ * h x * (g x)⁻¹) i l *
          (pd j (fun y => g y l k) x + pd k (fun y => g y l j) x - pd l (fun y => g y j k) x) +
        (g x)⁻¹ i l * (pd j (fun y => h y l k) x + pd k (fun y => h y l j) x - pd l (fun y => h y j k) x))) 0 := by
  have hform : ∀ t : ℝ, christoffel (fun y => g y + t • h y) i j k x =
      (1 / 2) * ∑ l, ((g x + t • h x)⁻¹ i l *
        ((pd j (fun y => g y l k) x + pd k (fun y => g y l j) x - pd l (fun y => g y j k) x) +
          t * (pd j (fun y => h y l k) x + pd k (fun y => h y l j) x - pd l (fun y => h y j k) x))) := by
    intro t
    unfold christoffel
    simp only [pd_add_smul g h t _ _ _ x (hgd _ _) (hhd _ _)]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  simp_rw [hform]
  refine HasDerivAt.const_mul _ ?_
  refine HasDerivAt.fun_sum (u := Finset.univ) fun l _ => ?_
  have hinv := hasDerivAt_inv_add_smul (g x) (h x) hG i l
  have hlin : HasDerivAt (fun t : ℝ => (pd j (fun y => g y l k) x + pd k (fun y => g y l j) x - pd l (fun y => g y j k) x) +
      t * (pd j (fun y => h y l k) x + pd k (fun y => h y l j) x - pd l (fun y => h y j k) x))
      (pd j (fun y => h y l k) x + pd k (fun y => h y l j) x - pd l (fun y => h y j k) x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (pd j (fun y => h y l k) x + pd k (fun y => h y l j) x - pd l (fun y => h y j k) x)).const_add
      (pd j (fun y => g y l k) x + pd k (fun y => g y l j) x - pd l (fun y => g y j k) x)
  have := hinv.mul hlin
  convert this using 1
  simp only [zero_smul, add_zero, zero_mul]

end Lightlike
