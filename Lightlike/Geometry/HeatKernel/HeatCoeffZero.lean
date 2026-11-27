import Mathlib
import Lightlike.Geodesic.SquaredDistance
import Lightlike.Geometry.HeatKernel.NormalTransport
import Lightlike.Geometry.HeatKernel.ParamLaplacian
import Lightlike.Asymptotics.SmoothExtension

/-!
# The first heat-kernel coefficient near the diagonal

For a coordinate metric `g` on an open `U ⊆ ℝⁿ` (any signature) and `x ∈ U` there are an open `Ω ∋ (x, x)` and
functions `σ, u₀` on `Ω`, jointly smooth in `(p, y)`, such that for every base point `p` (`exists_heatCoeff_zero`):

* `σ(p, ·)` is the world function of `p` (`g_p(V, V)` with `V(p, y)` the initial velocity of the short geodesic from
  `p` to `y`), it satisfies the eikonal equation `g⁻¹(dσ, dσ) = 4σ` and vanishes on the diagonal;
* `u₀(p, p) = 1`;
* the **transport equation of order `0`** holds: `g⁻¹(dσ, du₀)/2 − (Δσ/4 + n/2) u₀ = 0`.

The construction: the transport coefficient `h = Δσ/4 + n/2` is jointly smooth
(`IsCoordMetric.contDiffOn_coordLaplacian_param`), so is `H(p, v) = h(p, E(p, v))` in normal coordinates (`E` the
joint inverse of `V` from `Lightlike.Geodesic.exists_sqDist_eikonal`), and `H(p, 0) = h(p, p) = 0`
(`IsCoordMetric.transportCoeff_diag`). Extended to a smooth function on all of `ℝⁿ × ℝⁿ` near a closed ball
(`exists_contDiff_eqOn_nhds`), its Euler primitive `K(p, v)` is jointly smooth (`contDiff_eulerPrimitive_param`), and
`u₀(p, y) = e^{K(p, V(p, y))}` solves the transport equation (`IsCoordMetric.transport_zero_of_euler`).
-/

open Set Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- A coordinate metric on `U` is one on every open subset of `U`. -/
theorem IsCoordMetric.mono (hg : IsCoordMetric g U) {U' : Set (Fin n → ℝ)} (hU' : IsOpen U') (h : U' ⊆ U) :
    IsCoordMetric g U' :=
  ⟨hU', fun y hy => hg.symm y (h hy), fun y hy => hg.isUnit_det y (h hy), fun i j => (hg.smooth i j).mono h⟩

/-- **The first heat-kernel coefficient**: near `(x, x)` there are a jointly smooth world function `σ` (with the
eikonal equation, vanishing on the diagonal) and a jointly smooth `u₀` with `u₀(p, p) = 1` solving the transport
equation of order `0`, `g⁻¹(dσ, du₀)/2 − (Δσ/4 + n/2) u₀ = 0`, in the second variable for every base point. -/
theorem exists_heatCoeff_zero (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))) (σ u₀ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ),
      IsOpen Ω ∧ (x, x) ∈ Ω ∧ (∀ q ∈ Ω, q.2 ∈ U) ∧ ContDiffOn ℝ ∞ σ Ω ∧ ContDiffOn ℝ ∞ u₀ Ω ∧
      (∀ q ∈ Ω, coordGradPair g (fun y => σ (q.1, y)) (fun y => σ (q.1, y)) q.2 = 4 * σ q) ∧
      (∀ p, (p, p) ∈ Ω → σ (p, p) = 0 ∧ u₀ (p, p) = 1) ∧
      ∀ q ∈ Ω, coordGradPair g (fun y => σ (q.1, y)) (fun y => u₀ (q.1, y)) q.2 / 2 -
        (coordLaplacian g (fun y => σ (q.1, y)) q.2 / 4 + n / 2) * u₀ q = 0 := by
  obtain ⟨W, V, hWo, hxW, hVs, ⟨S, Ex, hSo, hExs, hfwd, hbwd⟩, hWU, hV0, hDV, -, hσs, hgr⟩ :=
    Geodesic.exists_sqDist_eikonal hg hx
  set σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => Geodesic.pairing g q.1 (V q) (V q) with hσdef
  -- the transport coefficient, jointly smooth
  set h : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => coordLaplacian g (fun y => σ (q.1, y)) q.2 / 4 + n / 2
    with hhdef
  have hhs : ContDiffOn ℝ ∞ h W :=
    ((hg.contDiffOn_coordLaplacian_param hWo (fun q hq => (hWU q hq).2) hσs).div_const 4).add contDiffOn_const
  -- in normal coordinates
  set H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun s => h (s.1, Ex s) with hHdef
  have hHs : ContDiffOn ℝ ∞ H S :=
    hhs.comp (contDiffOn_fst.prodMk hExs) fun s hs => (hbwd s hs).1
  have hx0S : (x, (0 : Fin n → ℝ)) ∈ S := by
    have := (hfwd _ hxW).1
    rwa [hV0 x hxW] at this
  obtain ⟨r, hr, hrS⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hSo.mem_nhds hx0S)
  obtain ⟨Ht, hHt, W', hW'o, hKW', hHtW'⟩ :=
    exists_contDiff_eqOn_nhds hSo hHs (isCompact_closedBall _ _) hrS
  -- the Euler primitive and `u₀`
  set K₀ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => eulerPrimitive (fun v => Ht (q.1, v)) q.2 with hK₀def
  have hK₀ : ContDiff ℝ ∞ K₀ := contDiff_eulerPrimitive_param hHt
  set u₀ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => Real.exp (K₀ (q.1, V q)) with hu₀def
  -- the domain
  have hVc : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (q.1, V q)) W :=
    continuousOn_fst.prodMk hVs.continuousOn
  set Ω := (W ∩ (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (q.1, V q)) ⁻¹' W') ∩
    ({q : (Fin n → ℝ) × (Fin n → ℝ) | (q.1, (0 : Fin n → ℝ)) ∈ W'} ∩ {q | (q.1, q.1) ∈ W}) with hΩdef
  have hΩo : IsOpen Ω := by
    refine (hVc.isOpen_inter_preimage hWo hW'o).inter (IsOpen.inter ?_ ?_)
    · exact hW'o.preimage (continuous_fst.prodMk continuous_const)
    · exact hWo.preimage (continuous_fst.prodMk continuous_fst)
  have hΩW : ∀ q ∈ Ω, q ∈ W := fun q hq => hq.1.1
  have hxW' : (x, (0 : Fin n → ℝ)) ∈ W' := hKW' (mem_closedBall_self hr.le)
  have hxΩ : (x, x) ∈ Ω := by
    refine ⟨⟨hxW, ?_⟩, hxW', hxW⟩
    show (x, V (x, x)) ∈ W'
    rw [hV0 x hxW]; exact hxW'
  -- the coefficient vanishes on the diagonal
  have hdiag : ∀ p, (p, p) ∈ W → h (p, p) = 0 := by
    intro p hp
    set U' := {y | (p, y) ∈ W} with hU'
    have hU'o : IsOpen U' := isOpen_slice hWo p
    have hg' : IsCoordMetric g U' := hg.mono hU'o fun y hy => (hWU _ hy).2
    have hVs' : ∀ a, ContDiffOn ℝ ∞ (fun y => V (p, y) a) U' := fun a =>
      contDiffOn_pi.1 (hVs.comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy => hy) a
    have := hg'.transportCoeff_diag (p := p) hp hVs' (hV0 p hp) (hDV p hp)
    exact this
  have hEx0 : ∀ p, (p, p) ∈ W → Ex (p, 0) = p := by
    intro p hp
    have := (hfwd _ hp).2
    rwa [hV0 p hp] at this
  refine ⟨Ω, σ, u₀, hΩo, hxΩ, fun q hq => (hWU q (hΩW q hq)).2, hσs.mono hΩW, ?_, ?_, ?_, ?_⟩
  · exact (Real.contDiff_exp.comp_contDiffOn (hK₀.comp_contDiffOn (contDiffOn_fst.prodMk hVs))).mono hΩW
  · -- the eikonal equation, in the form of the pairing
    intro q hq
    have he := (hgr q (hΩW q hq)).2
    rw [← he]
    unfold coordGradPair
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold Geodesic.pd₂ pd
    ring
  · intro p hp
    have hpW : (p, p) ∈ W := hp.2.2
    refine ⟨?_, ?_⟩
    · simp [hσdef, Geodesic.pairing, hV0 p hpW]
    · simp only [hu₀def, hK₀def, hV0 p hpW, eulerPrimitive_zero, Real.exp_zero]
  · -- the transport equation of order `0`
    intro q hq
    have hqW := hΩW q hq
    obtain ⟨⟨-, hqW'⟩, hq0W', hqqW⟩ := hq
    obtain ⟨⟨T, hVT, hgrad⟩, -⟩ := hgr q hqW
    have hVd : DifferentiableAt ℝ (fun y => V (q.1, y)) q.2 :=
      ((hVs.contDiffAt (hWo.mem_nhds hqW)).differentiableAt (by simp)).comp q.2
        ((differentiableAt_const q.1).prodMk differentiableAt_id)
    have hHt0 : Ht (q.1, 0) = 0 := by
      rw [hHtW' _ hq0W']
      show h (q.1, Ex (q.1, 0)) = 0
      rw [hEx0 q.1 hqqW]
      exact hdiag q.1 hqqW
    have hHtp : ContDiff ℝ ∞ (fun v => Ht (q.1, v)) := hHt.comp (contDiff_const.prodMk contDiff_id)
    have htr := hg.transport_zero_of_euler (hWU q hqW).2 (σ := fun y => σ (q.1, y))
      (V := fun y => V (q.1, y)) (T := T) (fun i => hgrad i) hVd hVT hHtp hHt0
    -- `Ht(p, V(p, y)) = h(p, y)`
    have hHq : Ht (q.1, V (q.1, q.2)) = h q := by
      rw [hHtW' _ hqW']
      show h (q.1, Ex (q.1, V q)) = h q
      rw [(hfwd q hqW).2]
    have hu : (fun y => u₀ (q.1, y)) = fun z => Real.exp (eulerPrimitive (fun v => Ht (q.1, v)) (V (q.1, z))) := rfl
    rw [hu, htr, hHq]
    show h q * u₀ q - h q * u₀ q = 0
    ring

end Lightlike
