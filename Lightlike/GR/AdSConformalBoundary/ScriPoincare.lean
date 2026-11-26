import Lightlike.GR.AdSConformalBoundary.ScriDilation

/-!
# The Poincaré group acts conformally on future null infinity of Minkowski space

The main statement of GE7 m1, collecting the layers `NullDirection`, `ScriAction`, `SphereConformal`, `ScriLimit` and
`ScriDilation`: an orthochronous Poincaré transformation `x ↦ Λ x + a` acts on the points `(u, n)` of future null
infinity (retarded time `u`, direction `n` on the unit sphere) by `scriAct Λ a`, and

* the action maps null infinity to itself (the image direction is a unit vector);
* it is the limit of the action on the bulk (along outgoing null rays, `tendsto_scriCoord_ray`);
* it is conformal on the sphere of directions, lengths being divided by `K = nullDirFactor Λ n`
  (`sum_sq_nullDirDeriv`: the differential of the direction map has `|dn'(v)|² = |v|² / K²`);
* the retarded time is divided by `K` and shifted by `a₀ - n' · a⃗`: the degenerate metric `0 du² + dΩ²` of null
  infinity is preserved up to the factor `K⁻²`, the conformal factor of the compactification.

The group law is `scriAct_comp`; the dilation is `scriDil_scriAct`.
-/

open Filter Topology Matrix

noncomputable section

namespace Lightlike

/-- **The Poincaré group acts conformally on future null infinity**: for an orthochronous `Λ`, a translation `a`,
a retarded time `u` and a unit direction `n`, with `(u', n') = scriAct Λ a (u, n)` and `K = nullDirFactor Λ n > 0`:
the direction `n'` is a unit vector; the retarded time and direction of the image of the outgoing ray converge to
`(u', n')`; and the map `n ↦ n'` is conformal on the unit sphere, with `|dn'(v)|² = |v|² / K²` for every tangent
vector `v`. -/
theorem poincare_act_scriPlus {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : IsOrthochronous Λ) (a : Fin 4 → ℝ)
    (u : ℝ) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    0 < nullDirFactor Λ n ∧ ∑ i, (scriAct Λ a (u, n)).2 i ^ 2 = 1 ∧
      Tendsto (fun s : ℝ => scriCoord (Λ *ᵥ scriRay u n s + a)) atTop (𝓝 (scriAct Λ a (u, n))) ∧
      ∀ v : Fin 3 → ℝ, ∑ i, n i * v i = 0 →
        ∑ i, nullDirDeriv Λ n v i ^ 2 = (∑ i, v i ^ 2) / nullDirFactor Λ n ^ 2 :=
  ⟨nullDirFactor_pos hΛ.lorentz hΛ.pos hn, sum_sq_nullDirMap hΛ.lorentz hΛ.pos hn,
    tendsto_scriCoord_ray hΛ a u hn, fun _ hv => sum_sq_nullDirDeriv hΛ.lorentz hΛ.pos hn hv⟩

end Lightlike
