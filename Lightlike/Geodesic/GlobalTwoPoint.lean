import Lightlike.Geodesic.ExpMap
import Lightlike.Geodesic.TwoPoint

/-!
# The map `(p, v) ↦ (p, exp_p v)` near the zero section

For a coordinate metric `g` on `U`, the map `E (p, v) = (p, exp_p v)` is a diffeomorphism from an
open neighbourhood of the zero section `U × {0}` onto an open neighbourhood of the diagonal of
`U × U` (`Lightlike.Geodesic.exists_twoPoint_diffeo_global`).

The local statement is `exists_twoPoint_diffeo`. The neighbourhood is the union of products of
balls `B(x, a_x) × B(0, a_x)` on which the local statement holds; `E` is injective on the union
because the balls of velocities are centred at `0`: two points with the same base point lie in
the larger of the two products.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Theorem 2.2.6 (properties of `E`),
  pages 47–49: "The mapping `E` is a diffeomorphism from a neighbourhood of the zero section
  `TM_0` of `TM` to a neighbourhood of the diagonal `△M ⊆ M × M`." Difference: a coordinate
  metric on an open subset of `ℝⁿ`; the source's auxiliary Riemannian metric is replaced by the
  norm of `ℝⁿ`.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The map `E (p, v) = (p, exp_p v)`. -/
def twoPointMap (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (q : (Fin n → ℝ) × (Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (q.1, expMap g U q)

/-- The local statement in terms of `expMap`: near `(x, 0)` the map `twoPointMap` is an open
partial homeomorphism, smooth with smooth inverse, on a product of balls. -/
theorem exists_local_twoPointMap (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) :
    ∃ (a : ℝ) (Θ : OpenPartialHomeomorph ((Fin n → ℝ) × (Fin n → ℝ))
        ((Fin n → ℝ) × (Fin n → ℝ))), 0 < a ∧
      ball ((x, (0 : Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ)) a ⊆ Θ.source ∧
      Θ.source ⊆ expDomain g U ∧ (∀ q ∈ Θ.source, Θ q = twoPointMap g U q) ∧
      ContDiffOn ℝ ∞ Θ Θ.source ∧ ContDiffOn ℝ ∞ Θ.symm Θ.target := by
  obtain ⟨ρ, E, Θ, hρ, hE0, hEs, hEU, hEg, hxΘ, hΘsub, hΘeq, hΘs, hΘi⟩ :=
    exists_twoPoint_diffeo hg hx
  have hexp : ∀ q ∈ Θ.source, q ∈ expDomain g U ∧ expMap g U q = E q := by
    rintro ⟨p, v⟩ hq
    obtain ⟨hp, hv⟩ := hΘsub hq
    obtain ⟨γ, w, hγ0, hw0, hgeo, hγE⟩ := hEg p hp v hv
    have h01 : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsm : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ ball (0 : Fin n → ℝ) ρ := by
      intro t ht
      have hv' := mem_ball_zero_iff.1 hv
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      nlinarith [norm_nonneg v, ht.2, ht.1]
    have hUγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := fun t ht => by
      rw [hγE t ⟨by linarith [ht.1], ht.2⟩]
      exact hEU p hp _ (hsm t ht)
    have h1 := mem_expDomain_of_geodesic isOpen_Ioo h01 hgeo hUγ
    have h2 := expMap_eq hg isOpen_Ioo h01 hgeo hUγ
    rw [hγ0, hw0] at h1 h2
    refine ⟨h1, ?_⟩
    rw [h2, hγE 1 ⟨by norm_num, le_rfl⟩, one_smul]
  obtain ⟨a, ha, hasub⟩ := Metric.isOpen_iff.1 Θ.open_source _ hxΘ
  refine ⟨a, Θ, ha, hasub, fun q hq => (hexp q hq).1, fun q hq => ?_, hΘs, hΘi⟩
  rw [hΘeq q hq, twoPointMap, (hexp q hq).2]

/-- **`E (p, v) = (p, exp_p v)` is a diffeomorphism from a neighbourhood of the zero section onto
a neighbourhood of the diagonal** (Kunzinger–Steinbauer, Theorem 2.2.6, for a coordinate metric
of any signature).

There is an open set `W` with `U × {0} ⊆ W ⊆ expDomain g U` on which `twoPointMap g U` is
smooth and injective, with open image containing the diagonal `{(p, p) | p ∈ U}`, and with a
smooth inverse `G` on the image. -/
theorem exists_twoPoint_diffeo_global (hg : Lightlike.IsCoordMetric g U) :
    ∃ (W : Set ((Fin n → ℝ) × (Fin n → ℝ))) (G : (Fin n → ℝ) × (Fin n → ℝ) →
        (Fin n → ℝ) × (Fin n → ℝ)),
      IsOpen W ∧ (∀ p ∈ U, ((p, 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ W) ∧ W ⊆ expDomain g U ∧
      InjOn (twoPointMap g U) W ∧ ContDiffOn ℝ ∞ (twoPointMap g U) W ∧
      IsOpen (twoPointMap g U '' W) ∧
      (∀ p ∈ U, ((p, p) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ twoPointMap g U '' W) ∧
      (∀ q ∈ W, G (twoPointMap g U q) = q) ∧ ContDiffOn ℝ ∞ G (twoPointMap g U '' W) := by
  classical
  choose a Θ ha hasub hΘdom hΘeq hΘs hΘi using fun x : U => exists_local_twoPointMap hg x.2
  set Wx : U → Set ((Fin n → ℝ) × (Fin n → ℝ)) := fun x =>
    ball (((x : Fin n → ℝ), (0 : Fin n → ℝ)) : (Fin n → ℝ) × (Fin n → ℝ)) (a x) with hWx
  set W : Set ((Fin n → ℝ) × (Fin n → ℝ)) := ⋃ x : U, Wx x with hW
  set f := twoPointMap g U with hf
  have hWopen : IsOpen W := isOpen_iUnion fun _ => isOpen_ball
  have hfx : ∀ (x : U), ∀ q ∈ Wx x, f q = Θ x q := fun x q hq => (hΘeq x q (hasub x hq)).symm
  have hmemWx : ∀ (x : U) (q : (Fin n → ℝ) × (Fin n → ℝ)),
      q ∈ Wx x ↔ Dist.dist q.1 (x : Fin n → ℝ) < a x ∧ ‖q.2‖ < a x := by
    intro x q
    simp only [hWx, mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · intro h
      exact ⟨h.1, by simpa [dist_zero_right] using h.2⟩
    · intro h
      exact ⟨h.1, by simpa [dist_zero_right] using h.2⟩
  -- injectivity
  have hinj : InjOn f W := by
    have key : ∀ (x₁ x₂ : U) (q₁ q₂ : (Fin n → ℝ) × (Fin n → ℝ)), a x₁ ≤ a x₂ →
        q₁ ∈ Wx x₁ → q₂ ∈ Wx x₂ → f q₁ = f q₂ → q₁ = q₂ := by
      intro x₁ x₂ q₁ q₂ hle h1 h2 hfq
      have hbase : q₁.1 = q₂.1 := by
        have h0 : (f q₁).1 = (f q₂).1 := by rw [hfq]
        exact h0
      have h1' : q₁ ∈ Wx x₂ := by
        rw [hmemWx] at h1 h2 ⊢
        exact ⟨by rw [hbase]; exact h2.1, lt_of_lt_of_le h1.2 hle⟩
      have h3 : Θ x₂ q₁ = Θ x₂ q₂ := by rw [← hfx x₂ q₁ h1', ← hfx x₂ q₂ h2, hfq]
      exact (Θ x₂).injOn (hasub x₂ h1') (hasub x₂ h2) h3
    intro q₁ hq₁ q₂ hq₂ hfq
    obtain ⟨x₁, h1⟩ := mem_iUnion.1 hq₁
    obtain ⟨x₂, h2⟩ := mem_iUnion.1 hq₂
    rcases le_total (a x₁) (a x₂) with hle | hle
    · exact key x₁ x₂ q₁ q₂ hle h1 h2 hfq
    · exact (key x₂ x₁ q₂ q₁ hle h2 h1 hfq.symm).symm
  have himgx : ∀ x : U, f '' Wx x = Θ x '' Wx x := fun x =>
    image_congr fun q hq => hfx x q hq
  have hopenx : ∀ x : U, IsOpen (f '' Wx x) := fun x => by
    rw [himgx x]
    exact ((Θ x).isOpen_image_iff_of_subset_source (hasub x)).2 isOpen_ball
  have himg : f '' W = ⋃ x : U, f '' Wx x := image_iUnion
  set G := Function.invFunOn f W with hG
  have hGleft : ∀ q ∈ W, G (f q) = q := fun q hq => hinj.leftInvOn_invFunOn hq
  refine ⟨W, G, hWopen, fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, mem_ball_self (ha ⟨p, hp⟩)⟩,
    fun q hq => ?_, hinj, fun q hq => ?_, ?_, fun p hp => ?_, hGleft, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := mem_iUnion.1 hq
    exact hΘdom x (hasub x hx)
  · obtain ⟨x, hx⟩ := mem_iUnion.1 hq
    have hat : ContDiffAt ℝ ∞ (Θ x) q :=
      (hΘs x).contDiffAt ((Θ x).open_source.mem_nhds (hasub x hx))
    have hev : f =ᶠ[𝓝 q] Θ x := by
      filter_upwards [isOpen_ball.mem_nhds hx] with q' hq' using hfx x q' hq'
    exact (hat.congr_of_eventuallyEq hev).contDiffWithinAt
  · rw [himg]
    exact isOpen_iUnion hopenx
  · refine ⟨(p, 0), mem_iUnion.2 ⟨⟨p, hp⟩, mem_ball_self (ha ⟨p, hp⟩)⟩, ?_⟩
    show (p, expMap g U (p, 0)) = (p, p)
    rw [expMap_zero hg hp]
  · -- the inverse is smooth
    obtain ⟨q, hq, rfl⟩ := hy
    obtain ⟨x, hx⟩ := mem_iUnion.1 hq
    refine ContDiffAt.contDiffWithinAt ?_
    have hmemT : f q ∈ (Θ x).target := by
      rw [hfx x q hx]; exact (Θ x).map_source (hasub x hx)
    have hat : ContDiffAt ℝ ∞ (Θ x).symm (f q) :=
      (hΘi x).contDiffAt ((Θ x).open_target.mem_nhds hmemT)
    have hev : G =ᶠ[𝓝 (f q)] (Θ x).symm := by
      filter_upwards [(hopenx x).mem_nhds (mem_image_of_mem f hx)] with y hy
      obtain ⟨q', hq', rfl⟩ := hy
      rw [hGleft q' (mem_iUnion.2 ⟨x, hq'⟩), hfx x q' hq', (Θ x).left_inv (hasub x hq')]
    exact hat.congr_of_eventuallyEq hev

end Lightlike.Geodesic
