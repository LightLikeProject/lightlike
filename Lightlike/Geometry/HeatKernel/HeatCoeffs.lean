import Mathlib
import Lightlike.Geometry.HeatKernel.HeatCoeffZero
import Lightlike.Geometry.HeatKernel.TransportEquations

/-!
# All heat-kernel coefficients near the diagonal

For a coordinate metric `g` on an open `U ⊆ ℝⁿ` (any signature) and `x ∈ U` there are an open `Ω ∋ (x, x)`, a jointly
smooth world function `σ` and a sequence of jointly smooth coefficients `u_k(p, y)` on `Ω` such that, for every base
point `p`, `u₀(p, p) = 1` and the **transport equations** of every order hold in the second variable
(`exists_heatCoeffs`):

`g⁻¹(dσ, du_k)/2 + (k − Δσ/4 − n/2) u_k = −Δu_{k−1}`   (`Lightlike.IsTransport`, every `N`).

The construction is recursive in normal coordinates `v = V(p, y)`, with one cutoff `χ` (`exists_cutoff_of_isOpen`), equal to
`1` near a closed ball around `(x, 0)` and supported where the joint inverse `E` of `V` is defined: `U₀ = e^K`,
`K` the Euler primitive of `χ·h(p, E(p, v))`, and `U_{k+1} = U₀ · W_{k+1}(χ F_{k+1}/U₀)` with
`F_{k+1}(p, v) = −Δ_y (U_k(p, V(p, ·)))(E(p, v))` and `W` the radial average. Every `U_k` is smooth on all of
`ℝⁿ × ℝⁿ` (`contDiff_mul_of_tsupport_subset`, `contDiff_eulerPrimitive_param`, `contDiff_radialAverage_param`), so the
same domain serves every order. On `Ω` the cutoff is `1` and `IsCoordMetric.transport_zero_of_euler`,
`IsCoordMetric.transport_succ_of_euler` give the transport equations.

## References

* `rosenberg-1997`: S. Rosenberg, *The Laplacian on a Riemannian Manifold* (1997), §3.2, the recursive solution of the
  transport equations. Comparison pending (not read at that location).
-/

open Set Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

section Cutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A smooth cutoff**: for `K` compact in an open `U` there is a smooth `χ` with values in `[0, 1]` and support in
`U`, equal to `1` on an open neighbourhood of `K`. -/
theorem exists_cutoff_of_isOpen {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧ ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, χ x = 1) ∧
      ∀ x, χ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨δ, hδ, hcU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hd : Disjoint (thickening (δ / 2) K)ᶜ (cthickening (δ / 4) K) := by
    rw [Set.disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' (by linarith) (by linarith) K
  obtain ⟨χ, hχ, hχr, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (isOpen_thickening.isClosed_compl) isClosed_cthickening hd
  have hsupp : tsupport χ ⊆ U := by
    have h1 : Function.support χ ⊆ thickening (δ / 2) K := by
      intro x hx
      by_contra hxs
      exact hx ((hχ0 x).1 hxs)
    have h2 : tsupport χ ⊆ cthickening (δ / 2) K :=
      closure_minimal (h1.trans (thickening_subset_cthickening _ _)) isClosed_cthickening
    exact h2.trans ((cthickening_mono (by linarith) K).trans hcU)
  exact ⟨χ, hχ.of_le (by exact_mod_cast le_top), hsupp, thickening (δ / 4) K, isOpen_thickening,
    self_subset_thickening (by linarith) K, fun x hx => (hχ1 x).1 (thickening_subset_cthickening _ _ hx),
    fun x => hχr (Set.mem_range_self x)⟩

/-- **A cutoff times a function smooth on a neighbourhood of its support is smooth.** -/
theorem contDiff_mul_of_tsupport_subset {χ f : E → ℝ} {U : Set E} (hU : IsOpen U) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiffOn ℝ ∞ f U) (hs : tsupport χ ⊆ U) : ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
  · have hz : ∀ᶠ y in 𝓝 x, χ y = 0 := notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hs h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hz] with y hy
    simp [hy]

end Cutoff

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **All heat-kernel coefficients near the diagonal**: near `(x, x)` there are a jointly smooth world function `σ`
(eikonal equation, `σ(p, p) = 0`, `σ = g_p(V, V)` with `V(p, p) = 0` and `D_y V(p, p) = id`) and jointly smooth `u_k(p, y)` with `u₀(p, p) = 1` satisfying, for every base point
`p` and every order `N`, the transport equations `IsTransport` in the second variable. -/
theorem exists_heatCoeffs (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))) (σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
      (u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ),
      IsOpen Ω ∧ (x, x) ∈ Ω ∧ (∀ q ∈ Ω, q.2 ∈ U) ∧ ContDiffOn ℝ ∞ σ Ω ∧ (∀ k, ContDiffOn ℝ ∞ (u k) Ω) ∧
      (∀ q ∈ Ω, coordGradPair g (fun y => σ (q.1, y)) (fun y => σ (q.1, y)) q.2 = 4 * σ q) ∧
      (∃ V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ), ContDiffOn ℝ ∞ V Ω ∧
        (∀ p, (p, p) ∈ Ω → V (p, p) = 0 ∧
          HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) ∧
        ∀ q ∈ Ω, σ q = Geodesic.pairing g q.1 (V q) (V q)) ∧
      (∀ p, (p, p) ∈ Ω → σ (p, p) = 0 ∧ u 0 (p, p) = 1) ∧
      ∀ p N, IsTransport g {y | (p, y) ∈ Ω} (fun y => σ (p, y)) (fun k y => u k (p, y)) N := by
  obtain ⟨W, V, hWo, hxW, hVs, ⟨S, Ex, hSo, hExs, hfwd, hbwd⟩, hWU, hV0, hDV, -, hσs, hgr⟩ :=
    Geodesic.exists_sqDist_eikonal hg hx
  set σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => Geodesic.pairing g q.1 (V q) (V q) with hσdef
  set h : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun q => coordLaplacian g (fun y => σ (q.1, y)) q.2 / 4 + n / 2
    with hhdef
  have hhs : ContDiffOn ℝ ∞ h W :=
    ((hg.contDiffOn_coordLaplacian_param hWo (fun q hq => (hWU q hq).2) hσs).div_const 4).add contDiffOn_const
  have hEW : ∀ s ∈ S, (s.1, Ex s) ∈ W := fun s hs => (hbwd s hs).1
  have hFE : ContDiffOn ℝ ∞ (fun s : (Fin n → ℝ) × (Fin n → ℝ) => (s.1, Ex s)) S :=
    contDiffOn_fst.prodMk hExs
  have hVW : ContDiffOn ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (q.1, V q)) W := contDiffOn_fst.prodMk hVs
  -- the cutoff
  have hx0S : (x, (0 : Fin n → ℝ)) ∈ S := by
    have := (hfwd _ hxW).1
    rwa [hV0 x hxW] at this
  obtain ⟨r, hr, hrS⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hSo.mem_nhds hx0S)
  obtain ⟨χ, hχ, hχS, W₁, hW₁o, hKW₁, hχ1, -⟩ := exists_cutoff_of_isOpen hSo (isCompact_closedBall _ _) hrS
  -- the order-0 data in normal coordinates
  set Ht : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun s => χ s * h (s.1, Ex s) with hHtdef
  have hHt : ContDiff ℝ ∞ Ht := contDiff_mul_of_tsupport_subset hSo hχ (hhs.comp hFE hEW) hχS
  set U0 : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun s => Real.exp (eulerPrimitive (fun v => Ht (s.1, v)) s.2)
    with hU0def
  have hU0 : ContDiff ℝ ∞ U0 := Real.contDiff_exp.comp (contDiff_eulerPrimitive_param hHt)
  have hU0pos : ∀ s, U0 s ≠ 0 := fun s => (Real.exp_pos _).ne'
  -- the source of the next order, from a coefficient in normal coordinates
  set Fop : ((Fin n → ℝ) × (Fin n → ℝ) → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    fun Φ s => -coordLaplacian g (fun y => Φ (s.1, V (s.1, y))) (Ex s) with hFopdef
  have hFop : ∀ Φ, ContDiff ℝ ∞ Φ → ContDiff ℝ ∞ (fun s => χ s * Fop Φ s) := by
    intro Φ hΦ
    have hL : ContDiffOn ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        coordLaplacian g (fun y => Φ (q.1, V (q.1, y))) q.2) W :=
      hg.contDiffOn_coordLaplacian_param hWo (fun q hq => (hWU q hq).2)
        (F := fun q => Φ (q.1, V q)) (hΦ.comp_contDiffOn hVW)
    exact contDiff_mul_of_tsupport_subset hSo hχ (hL.comp hFE hEW).neg hχS
  -- the coefficients in normal coordinates, by recursion
  let Useq : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun k => Nat.rec U0
    (fun j Φ s => U0 s * radialAverage (j + 1) (fun v => χ (s.1, v) * Fop Φ (s.1, v) / U0 (s.1, v)) s.2) k
  have hUseq0 : Useq 0 = U0 := rfl
  have hUseqS : ∀ j, Useq (j + 1) = fun s => U0 s *
      radialAverage (j + 1) (fun v => χ (s.1, v) * Fop (Useq j) (s.1, v) / U0 (s.1, v)) s.2 := fun j => rfl
  have hUseq : ∀ k, ContDiff ℝ ∞ (Useq k) := by
    intro k
    induction k with
    | zero => exact hU0
    | succ j ih =>
      rw [hUseqS j]
      have hG : ContDiff ℝ ∞ (fun s => χ s * Fop (Useq j) s / U0 s) := (hFop _ ih).div hU0 hU0pos
      exact hU0.mul (contDiff_radialAverage_param (j + 1) hG)
  -- the domain
  set Ω := (W ∩ (fun q : (Fin n → ℝ) × (Fin n → ℝ) => (q.1, V q)) ⁻¹' W₁) ∩
    ({q : (Fin n → ℝ) × (Fin n → ℝ) | (q.1, (0 : Fin n → ℝ)) ∈ W₁} ∩ {q | (q.1, q.1) ∈ W}) with hΩdef
  have hΩo : IsOpen Ω := by
    refine (hVW.continuousOn.isOpen_inter_preimage hWo hW₁o).inter (IsOpen.inter ?_ ?_)
    · exact hW₁o.preimage (continuous_fst.prodMk continuous_const)
    · exact hWo.preimage (continuous_fst.prodMk continuous_fst)
  have hΩW : ∀ q ∈ Ω, q ∈ W := fun q hq => hq.1.1
  have hxW₁ : (x, (0 : Fin n → ℝ)) ∈ W₁ := hKW₁ (mem_closedBall_self hr.le)
  have hxΩ : (x, x) ∈ Ω := by
    refine ⟨⟨hxW, ?_⟩, hxW₁, hxW⟩
    show (x, V (x, x)) ∈ W₁
    rw [hV0 x hxW]; exact hxW₁
  have hdiag : ∀ p, (p, p) ∈ W → h (p, p) = 0 := by
    intro p hp
    set U' := {y | (p, y) ∈ W} with hU'
    have hU'o : IsOpen U' := isOpen_slice hWo p
    have hg' : IsCoordMetric g U' := hg.mono hU'o fun y hy => (hWU _ hy).2
    have hVs' : ∀ a, ContDiffOn ℝ ∞ (fun y => V (p, y) a) U' := fun a =>
      contDiffOn_pi.1 (hVs.comp (contDiffOn_const.prodMk contDiffOn_id) fun y hy => hy) a
    exact hg'.transportCoeff_diag (p := p) hp hVs' (hV0 p hp) (hDV p hp)
  have hEx0 : ∀ p, (p, p) ∈ W → Ex (p, 0) = p := by
    intro p hp
    have := (hfwd _ hp).2
    rwa [hV0 p hp] at this
  set u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun k q => Useq k (q.1, V q) with hudef
  refine ⟨Ω, σ, u, hΩo, hxΩ, fun q hq => (hWU q (hΩW q hq)).2, hσs.mono hΩW,
    fun k => ((hUseq k).comp_contDiffOn hVW).mono hΩW, ?_,
    ⟨V, hVs.mono hΩW, fun p hp => ⟨hV0 p (hΩW _ hp), hDV p (hΩW _ hp)⟩, fun q _ => rfl⟩, ?_, ?_⟩
  · intro q hq
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
    · show U0 (p, V (p, p)) = 1
      simp only [hU0def, hV0 p hpW, eulerPrimitive_zero, Real.exp_zero]
  · -- the transport equations
    intro p N k _ y hy
    set q : (Fin n → ℝ) × (Fin n → ℝ) := (p, y) with hqdef
    have hq : q ∈ Ω := hy
    have hqW := hΩW q hq
    obtain ⟨⟨-, hqW₁⟩, hq0W₁, hqqW⟩ := hq
    obtain ⟨⟨T, hVT, hgrad⟩, -⟩ := hgr q hqW
    have hVd : DifferentiableAt ℝ (fun y => V (p, y)) y :=
      ((hVs.contDiffAt (hWo.mem_nhds hqW)).differentiableAt (by simp)).comp y
        ((differentiableAt_const p).prodMk differentiableAt_id)
    have hHt0 : Ht (p, 0) = 0 := by
      show χ (p, 0) * h (p, Ex (p, 0)) = 0
      rw [hEx0 p hqqW, hdiag p hqqW, mul_zero]
    have hHtp : ContDiff ℝ ∞ (fun v => Ht (p, v)) := hHt.comp (contDiff_const.prodMk contDiff_id)
    have hχq : χ (p, V q) = 1 := hχ1 _ hqW₁
    have hHq : Ht (p, V q) = h q := by
      show χ (p, V q) * h (p, Ex (p, V q)) = h q
      rw [hχq, one_mul, (hfwd q hqW).2]
    rcases k with _ | j
    · -- order `0`
      have htr := hg.transport_zero_of_euler (hWU q hqW).2 (σ := fun y => σ (p, y))
        (V := fun y => V (p, y)) (T := T) (fun i => hgrad i) hVd hVT hHtp hHt0
      have hu : (fun y => u 0 (p, y)) =
          fun z => Real.exp (eulerPrimitive (fun v => Ht (p, v)) (V (p, z))) := rfl
      beta_reduce
      rw [hu, htr]
      show Ht (p, V q) * U0 (p, V q) + ((0 : ℕ) - (coordLaplacian g (fun y => σ (p, y)) y / 4 + n / 2)) *
        U0 (p, V q) = -(if (0 : ℕ) = 0 then 0 else _)
      rw [hHq]
      simp only [Nat.cast_zero, if_true, neg_zero]
      show h q * U0 (p, V q) + (0 - h q) * U0 (p, V q) = 0
      ring
    · -- order `j + 1`
      have hFj : ContDiff ℝ ∞ (fun v => χ (p, v) * Fop (Useq j) (p, v)) :=
        (hFop _ (hUseq j)).comp (contDiff_const.prodMk contDiff_id)
      have htr := hg.transport_succ_of_euler (hWU q hqW).2 (σ := fun y => σ (p, y))
        (V := fun y => V (p, y)) (T := T) (fun i => hgrad i) hVd hVT (j + 1) (by omega) hHtp hHt0 hFj
      have hu : (fun y => u (j + 1) (p, y)) = fun z => Real.exp (eulerPrimitive (fun v => Ht (p, v)) (V (p, z))) *
          radialAverage (j + 1) (fun w => χ (p, w) * Fop (Useq j) (p, w) /
            Real.exp (eulerPrimitive (fun v => Ht (p, v)) w)) (V (p, z)) := rfl
      have hu' : u (j + 1) (p, y) = Real.exp (eulerPrimitive (fun v => Ht (p, v)) (V (p, y))) *
          radialAverage (j + 1) (fun w => χ (p, w) * Fop (Useq j) (p, w) /
            Real.exp (eulerPrimitive (fun v => Ht (p, v)) w)) (V (p, y)) := rfl
      simp only
      rw [hu, hu']
      rw [hHq] at htr
      rw [show h q = coordLaplacian g (fun y => σ (p, y)) y / 4 + n / 2 from rfl] at htr
      rw [htr]
      -- the source: `χ = 1` at `(p, V q)` and `E(p, V(p, y)) = y`
      rw [hχq, one_mul]
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, if_false, hFopdef]
      rw [(hfwd q hqW).2]

end Lightlike
