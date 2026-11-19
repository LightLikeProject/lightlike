import Lightlike.Geodesic.Gauss

/-!
# The first variation identity for a family of geodesics

For a one-parameter family `F t s` of geodesics `t ↦ F t s` with velocities `a t s`, the pairing
of the velocity with the variation field `b t = ∂F/∂s (t, 0)` has derivative

`d/dt g (a, b) = ½ d/ds|₀ g (a, a)`

(`Lightlike.Geodesic.hasDerivAt_pairing_variation`). The right-hand side does not depend on `t`,
because geodesics have constant speed. This is the computation in the proof of the Gauss lemma,
stated without the exponential map; it applies to geodesic variations along a geodesic of any
length.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), proof of Theorem 2.1.21, pages
  43–44.
-/

open Set Metric Filter Topology Matrix
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The first variation identity.** Let `F t s` be a family of curves with `t`-velocity
`a t s`, such that at the time `t` the curve `τ ↦ F τ 0` satisfies the geodesic equation, with
variation field `b τ = ∂F/∂s (τ, 0)` whose `t`-derivative `c` is also the `s`-derivative of the
velocity at `(t, 0)` (the mixed partial derivatives agree). If the squared speed
`g (a t s, a t s)` equals `N s` for `s` near `0` and `N` has derivative `N'` at `0`, then
`τ ↦ g (F τ 0) (a τ 0, b τ)` has derivative `N' / 2` at `t`. -/
theorem hasDerivAt_pairing_variation (hg : Lightlike.IsCoordMetric g U)
    {F a : ℝ → ℝ → Fin n → ℝ} {b : ℝ → Fin n → ℝ} {c : Fin n → ℝ} {N : ℝ → ℝ} {N' t : ℝ}
    (hU : F t 0 ∈ U)
    (hFt : HasDerivAt (fun τ => F τ 0) (a t 0) t)
    (hat : HasDerivAt (fun τ => a τ 0) (accel g (F t 0) (a t 0)) t)
    (hFs : HasDerivAt (fun s => F t s) (b t) 0)
    (hbt : HasDerivAt b c t)
    (has : HasDerivAt (fun s => a t s) c 0)
    (hN : ∀ᶠ s in 𝓝 (0 : ℝ), normSq g (F t s) (a t s) = N s)
    (hN' : HasDerivAt N N' 0) :
    HasDerivAt (fun τ => pairing g (F τ 0) (a τ 0) (b τ)) (N' / 2) t := by
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) (F t 0) := fun i j =>
    ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hU)).differentiableAt (by simp)
  set y : Fin n → ℝ := F t 0 with hy
  set av : Fin n → ℝ := a t 0 with hav
  have hψd := hasDerivAt_pairing (g := g) (γ := fun τ => F τ 0) (a := fun τ => a τ 0)
    (b := b) hdiff hFt hat hbt
  have hNd := hasDerivAt_pairing (g := g) (γ := fun s => F t s) (a := fun s => a t s)
    (b := fun s => a t s) (s := 0) hdiff hFs has has
  have hevN : N =ᶠ[𝓝 (0 : ℝ)] fun s => ∑ i, ∑ j, a t s i * (g (F t s) i j * a t s j) := by
    filter_upwards [hN] with s hs
    rw [← hs, ← pairing_self]
    rfl
  have hNeq := (hNd.congr_of_eventuallyEq hevN).unique hN'
  have hGsym : ∀ i j, g y i j = g y j i := fun i j => by
    have := congrFun (congrFun (hg.symm y hU) j) i
    simpa [Matrix.transpose_apply] using this
  have halg := gauss_algebra (fun i j => g y i j)
    (fun k i j => Lightlike.pd k (fun z => g z i j) y) (accel g y av) av (b t) c hGsym
    (fun j => lowered_accel_add hg hU av j)
  refine hψd.congr_deriv ?_
  rw [halg, hNeq]
  ring

/-- The derivative of the squared speed along a line of velocities:
`d/ds|₀ g x (v + s w, v + s w) = 2 g x (v, w)`. -/
theorem hasDerivAt_normSq_line (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (v w : Fin n → ℝ) :
    HasDerivAt (fun s : ℝ => normSq g x (v + s • w)) (2 * pairing g x v w) 0 := by
  have hdiffx : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x := fun i j =>
    ((hg.smooth i j).contDiffAt (hg.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have h3 : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    have h0 := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
    rw [one_smul] at h0
    exact h0
  have hNx := hasDerivAt_pairing (g := g) (γ := fun _ : ℝ => x) (a := fun s : ℝ => v + s • w)
    (b := fun s : ℝ => v + s • w) (s := 0) hdiffx (hasDerivAt_const (0 : ℝ) x) h3 h3
  have hfun : (fun s : ℝ => normSq g x (v + s • w)) =
      fun s => ∑ i, ∑ j, (v + s • w) i * (g x i j * (v + s • w) j) := by
    funext s
    rw [← pairing_self]; rfl
  rw [hfun]
  refine hNx.congr_deriv ?_
  have h7 : ∀ i j, w i * (g x i j * (v + (0 : ℝ) • w) j) +
      (v + (0 : ℝ) • w) i * ((∑ k, (0 : Fin n → ℝ) k *
        Lightlike.pd k (fun y => g y i j) x) * (v + (0 : ℝ) • w) j + g x i j * w j) =
      w i * (g x i j * v j) + v i * (g x i j * w j) := fun i j => by
    simp
  simp only [h7, Finset.sum_add_distrib]
  have h8 : ∑ i, ∑ j, w i * (g x i j * v j) = pairing g x w v := rfl
  have h9 : ∑ i, ∑ j, v i * (g x i j * w j) = pairing g x v w := rfl
  rw [h8, h9, pairing_comm hg hx w v]
  ring

/-- The first component of the derivative of the geodesic vector field is the velocity
component: `(D geodField (p) X).1 = X.2`. -/
theorem fderiv_geodField_fst (hg : Lightlike.IsCoordMetric g U)
    {p : (Fin n → ℝ) × (Fin n → ℝ)} (hp : p.1 ∈ U) (X : (Fin n → ℝ) × (Fin n → ℝ)) :
    (fderiv ℝ (geodField g) p X).1 = X.2 := by
  have hG : DifferentiableAt ℝ (geodField g) p :=
    ((contDiffOn_geodField hg).contDiffAt ((hg.isOpen.prod isOpen_univ).mem_nhds
      (mk_mem_prod hp (mem_univ _)))).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (geodField g q).1)
      ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp (fderiv ℝ (geodField g) p)) p :=
    hasFDerivAt_fst.comp p hG.hasFDerivAt
  have h2 : HasFDerivAt (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (geodField g q).1)
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)) p := hasFDerivAt_snd
  have h3 := congrArg (fun L : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => L X)
    (h1.unique h2)
  simpa using h3

end Lightlike.Geodesic
