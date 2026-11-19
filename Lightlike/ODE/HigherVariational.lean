import Lightlike.ODE.FlowContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The higher order variational equations

The last sentence of Teschl's Theorem 2.10: for `f` of class `C^k`, every partial derivative
`D_k φ` of order `k` of the solution `φ (t, s, x)` of `ẋ = f (t, x)` satisfies

`∂/∂t D_k φ = D_k ∂/∂t φ = D_k f (t, φ)`     (2.51),

the higher order variational equation, and the derivatives commute. Here all partial derivatives
of order `j` at once are the iterated Fréchet derivative `iteratedFDeriv ℝ j` in `(t, s, x)`, and
(2.51) reads `D (D^j φ) (1, 0, 0) = D^j (f (t, φ))`
(`Lightlike.ODE.exists_solution_contDiffOn_variational`).

The commutation of a directional derivative with the iterated derivative
(`Lightlike.ODE.fderiv_iteratedFDeriv_apply_comm`) is proved by induction on the order from the
symmetry of the second derivative; the pinned Mathlib has no symmetry statement for iterated
derivatives of higher order.

## References

* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Theorem 2.10
  and equation (2.51), page 46 of the author's version.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.ODE

/-- **A directional derivative commutes with the iterated derivative**: for `g` of class
`C^{j+1}` on an open set `S` and a direction `e`, the derivative of `D^j g` in the direction `e`
is `D^j` of the directional derivative `y ↦ Dg(y) e`, on `S`. -/
theorem fderiv_iteratedFDeriv_apply_comm.{u} {G : Type u} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (j : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : G → F} {S : Set G},
      IsOpen S → ContDiffOn ℝ ((j : ℕ∞ω) + 1) g S → ∀ (e : G) {q : G}, q ∈ S →
      fderiv ℝ (iteratedFDeriv ℝ j g) q e = iteratedFDeriv ℝ j (fun y => fderiv ℝ g y e) q := by
  induction j with
  | zero =>
    intro F _ _ g S _ _ e q _
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.comp_fderiv]
    rfl
  | succ j ih =>
    intro F _ _ g S hS hg e q hq
    have hcast : ((j + 1 : ℕ) : ℕ∞ω) = (j : ℕ∞ω) + 1 := by push_cast; rfl
    rw [hcast] at hg
    have hg' : ContDiffOn ℝ ((j : ℕ∞ω) + 1) (fderiv ℝ g) S :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hS).1 hg).2.2
    have hL : iteratedFDeriv ℝ (j + 1) g =
        (continuousMultilinearCurryRightEquiv' ℝ j G F).symm ∘
          iteratedFDeriv ℝ j (fun y => fderiv ℝ g y) :=
      funext fun x => iteratedFDeriv_succ_eq_comp_right
    have hev : (fun y => fderiv ℝ (fderiv ℝ g) y e) =ᶠ[𝓝 q]
        fun y => fderiv ℝ (fun y => fderiv ℝ g y e) y := by
      filter_upwards [hS.mem_nhds hq] with y hy
      have hgy : ContDiffAt ℝ ((j : ℕ∞ω) + 1 + 1) g y := hg.contDiffAt (hS.mem_nhds hy)
      have hd : DifferentiableAt ℝ (fderiv ℝ g) y :=
        (hg'.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp)
      have h2 : (2 : ℕ∞ω) ≤ (j : ℕ∞ω) + 1 + 1 := by
        rw [add_assoc, one_add_one_eq_two]; exact le_add_self
      have hs := hgy.isSymmSndFDerivAt (by simpa using h2)
      refine ContinuousLinearMap.ext fun w => ?_
      rw [fderiv_clm_apply hd (differentiableAt_const e)]
      simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply]
      exact hs.eq e w
    have hc := LinearIsometryEquiv.comp_fderiv (continuousMultilinearCurryRightEquiv' ℝ j G F).symm
      (f := iteratedFDeriv ℝ j fun y => fderiv ℝ g y) (x := q)
    rw [hL, hc, iteratedFDeriv_succ_eq_comp_right]
    simp only [ContinuousLinearMap.comp_apply, Function.comp_apply]
    rw [ih hS hg' e hq, (hev.iteratedFDeriv ℝ j).self_of_nhds]
    rfl

/-- **The higher order variational equation** (Teschl, (2.51)). Let `φ` be `C^{k+1}` on an open
set `S` of `(t, s, x)`, with time derivative `∂φ/∂t = f (t, φ)` there. Then for `j ≤ k` the
time derivative of `D^j φ` is `D^j` of `f (t, φ)`, on `S`. -/
theorem fderiv_iteratedFDeriv_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {f : ℝ × E → E} {φ : ℝ × ℝ × E → E} {S : Set (ℝ × ℝ × E)} (hS : IsOpen S)
    (hφ : ContDiffOn ℝ ((k : ℕ∞ω) + 1) φ S)
    (ht : ∀ q ∈ S, fderiv ℝ φ q ((1 : ℝ), (0 : ℝ), (0 : E)) = f (q.1, φ q))
    {j : ℕ} (hj : j ≤ k) {q : ℝ × ℝ × E} (hq : q ∈ S) :
    fderiv ℝ (iteratedFDeriv ℝ j φ) q ((1 : ℝ), (0 : ℝ), (0 : E)) =
      iteratedFDeriv ℝ j (fun q : ℝ × ℝ × E => f (q.1, φ q)) q := by
  have hle : (j : ℕ∞ω) + 1 ≤ (k : ℕ∞ω) + 1 := by
    have : (j : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hj
    gcongr
  rw [fderiv_iteratedFDeriv_apply_comm j hS (hφ.of_le hle) _ hq]
  have hev : (fun y => fderiv ℝ φ y ((1 : ℝ), (0 : ℝ), (0 : E))) =ᶠ[𝓝 q]
      fun q : ℝ × ℝ × E => f (q.1, φ q) := by
    filter_upwards [hS.mem_nhds hq] with y hy using ht y hy
  exact (hev.iteratedFDeriv ℝ j).self_of_nhds

/-- **Teschl's Theorem 2.10, with the higher order variational equations.** Let `f : ℝ × E → E`
be `C^{k+1}` at `(t₀, x₀)`. Then there are `δ > 0` and a map `φ` such that, with
`I = (t₀ - δ, t₀ + δ)` and `B` the ball of radius `δ` about `x₀`: for `s ∈ I` and `x ∈ B`,
`φ s s x = x` and `t ↦ φ t s x` solves `ẋ = f (t, x)` on `I`; `(t, s, x) ↦ φ t s x` and its time
derivative `(t, s, x) ↦ f (t, φ t s x)` are `C^{k+1}` on `I × I × B`; and for every `j ≤ k` the
derivative `D^j φ` of order `j` in `(t, s, x)` satisfies the higher order variational equation
`∂/∂t D^j φ = D^j (f (t, φ))` on `I × I × B` (equation (2.51)). -/
theorem exists_solution_contDiffOn_variational {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (k : ℕ) {f : ℝ × E → E} {t₀ : ℝ} {x₀ : E}
    (hf : ContDiffAt ℝ ((k : ℕ∞ω) + 1) f (t₀, x₀)) :
    ∃ (δ : ℝ) (φ : ℝ → ℝ → E → E), 0 < δ ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ), ∀ x ∈ ball x₀ δ, φ s s x = x ∧
        ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), HasDerivAt (fun t => φ t s x) (f (t, φ t s x)) t) ∧
      ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun q : ℝ × ℝ × E => φ q.1 q.2.1 q.2.2)
        (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) ∧
      ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun q : ℝ × ℝ × E => f (q.1, φ q.1 q.2.1 q.2.2))
        (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) ∧
      ∀ j ≤ k, ∀ q ∈ Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ,
        fderiv ℝ (iteratedFDeriv ℝ j (fun q : ℝ × ℝ × E => φ q.1 q.2.1 q.2.2)) q
            ((1 : ℝ), (0 : ℝ), (0 : E)) =
          iteratedFDeriv ℝ j (fun q : ℝ × ℝ × E => f (q.1, φ q.1 q.2.1 q.2.2)) q := by
  obtain ⟨δ, φ, hδ, h1, h2, h3⟩ := exists_solution_contDiffOn k hf
  refine ⟨δ, φ, hδ, h1, h2, h3, fun j hj q hq => ?_⟩
  have hS : IsOpen (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo (t₀ - δ) (t₀ + δ) ×ˢ ball x₀ δ) :=
    isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_ball)
  refine fderiv_iteratedFDeriv_solution (φ := fun q : ℝ × ℝ × E => φ q.1 q.2.1 q.2.2) hS h2
    (fun y hy => ?_) hj hq
  obtain ⟨t, s, x⟩ := y
  obtain ⟨ht, hs, hx⟩ := hy
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ × E => φ q.1 q.2.1 q.2.2) (t, s, x) :=
    (h2.contDiffAt (hS.mem_nhds ⟨ht, hs, hx⟩)).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun u : ℝ => ((u, s, x) : ℝ × ℝ × E)) ((1 : ℝ), (0 : ℝ), (0 : E)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t ((s, x) : ℝ × E))
  have h4 : HasDerivAt (fun u : ℝ => φ u s x)
      (fderiv ℝ (fun q : ℝ × ℝ × E => φ q.1 q.2.1 q.2.2) (t, s, x) ((1 : ℝ), (0 : ℝ), (0 : E)))
      t :=
    HasFDerivAt.comp_hasDerivAt (l := fun q : ℝ × ℝ × E => φ q.1 q.2.1 q.2.2) t hd.hasFDerivAt hcurve
  exact h4.unique ((h1 s hs x hx).2 t ht)

end Lightlike.ODE
