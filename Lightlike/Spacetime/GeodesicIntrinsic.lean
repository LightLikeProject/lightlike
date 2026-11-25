import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.PenroseSingularity.Defs

/-!
# Geodesics of a connection on a manifold, defined intrinsically (G1-005, GE3)

A curve `γ : ℝ → M` is a **geodesic of the connection `cov`** (`IsGeodesicCov`) if near each `t ∈ J` its velocity is
the restriction of a smooth vector field `X` (`γ' = X ∘ γ`, as `HasMFDerivAt`) with `∇_X X = 0` along `γ`:
`cov X (γ s) (X (γ s)) = 0`. (A connection acts on vector fields, so the covariant derivative of `γ'` along `γ` is
written through a local extension; `∇_{γ'} X` only depends on `X` along `γ`.)

* `hv_eq_mfderiv`: the components of a tangent vector in the trivialization at `p` are its image under the derivative
  of the chart at `p`;
* `hasDerivAt_chart_curve`, `hasDerivAt_hat_curve`: chain rules along a curve with velocity `X ∘ γ`;
* `isGeodesicCurveOn_of_isGeodesicCov`: for the Levi-Civita connection of a Lorentzian metric an intrinsic geodesic is
  a chart-wise geodesic (`IsGeodesicCurveOn`, the definition used by the Penrose rows), via `hat_cov` and `gamHat_coord`.

**Limits.** Only this direction is proved: the converse needs a smooth extension of `γ'` to a vector field near `γ t`,
which exists when `γ' (t) ≠ 0` but is not constructed here. Levi-Civita connections only (the Christoffel symbols of the
coordinate metric enter through `gamHat_coord`). Not in Mathlib: there is no covariant derivative along a curve for
`CovariantDerivative` (checked in `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative`).

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, ch. 3, the geodesic equation (3.46)–(3.51)
  (`∇_{dx/dλ} (dx^μ/dλ) = 0`); comparison with the page pending (not read).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- The components of a tangent vector in the trivialization at `p` are its image under the derivative of the chart. -/
theorem hv_eq_mfderiv (p : M) {z : M} (hz : z ∈ (tTriv (E := Fin n → ℝ) p).baseSet)
    (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) z) :
    hv (E := Fin n → ℝ) p z u = mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) z u := by
  have hs : z ∈ (chartAt (Fin n → ℝ) p).source := by
    simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hz
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hs]
  exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ (tTriv (E := Fin n → ℝ) p) hz u).symm


/-- **A geodesic of the connection `cov`, intrinsically** (`∇_{γ'} γ' = 0`): near each `t ∈ J` the velocity of `γ` is
`X ∘ γ` for a smooth vector field `X` (`HasMFDerivAt` of `γ` with derivative `1 ↦ X (γ s)`) and `∇_X X = 0` at `γ s`. -/
def IsGeodesicCov (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ X : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y,
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧
    ∀ᶠ s in 𝓝 t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ s))) ∧
      cov X (γ s) (X (γ s)) = 0

/-- A `HasFDerivAt` of a curve in `Fin n → ℝ` is a `HasDerivAt`. -/
theorem hasDerivAt_of_hasFDerivAt' {c : ℝ → Fin n → ℝ} {L : ℝ →L[ℝ] (Fin n → ℝ)} {s : ℝ}
    (h : HasFDerivAt c L s) : HasDerivAt c (L 1) s :=
  hasFDerivAt_iff_hasDerivAt.1 h

/-- Chain rule in the chart at `p`: a curve with velocity `v` at `s` has chart expression with derivative `dφ v`. -/
theorem hasDerivAt_chart_curve (p : M) {γ : ℝ → M} {s : ℝ} {v : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s)}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hs : γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source) :
    HasDerivAt (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) p (γ r))
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) (γ s) v) s := by
  have h1 : HasMFDerivAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) (γ s)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) (γ s)) :=
    (mdifferentiableAt_extChartAt (by simpa [extChartAt_source] using hs)).hasMFDerivAt
  have h2 := h1.comp s hγ
  have h3 : HasFDerivAt (fun r => extChartAt 𝓘(ℝ, Fin n → ℝ) p (γ r))
      ((mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) (γ s)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight v)) s := hasMFDerivAt_iff_hasFDerivAt.1 h2
  have h4 := hasDerivAt_of_hasFDerivAt' h3
  have e : ((mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) (γ s)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)) 1 =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) (γ s) v := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  exact h4.congr_deriv e

/-- Chain rule for the components of a smooth vector field along a curve with velocity `X ∘ γ`. -/
theorem hasDerivAt_hat_curve (p : M) {X : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y} {γ : ℝ → M} {s : ℝ}
    (hX : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (γ s))
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ s))))
    (hb : γ s ∈ (tTriv (E := Fin n → ℝ) p).baseSet) :
    HasDerivAt (fun r => hat (E := Fin n → ℝ) p X (γ r))
      (mvfderiv 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) p X) (γ s) (X (γ s))) s := by
  have h0 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) p X) (γ s) :=
    (mdiffAt_hat_iff p X hb).1 hX
  have h1 := h0.hasMFDerivAt
  have h2 := h1.comp s hγ
  have h3 : HasFDerivAt (fun r => hat (E := Fin n → ℝ) p X (γ r))
      ((mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) p X) (γ s)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ s)))) s := hasMFDerivAt_iff_hasFDerivAt.1 h2
  have h4 := hasDerivAt_of_hasFDerivAt' h3
  have e : ((mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) p X) (γ s)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ s)))) 1 =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) p X) (γ s) (X (γ s)) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
  exact h4.congr_deriv e

/-- The `i`-th component of `B w w` for a bilinear map `B`: `∑ a, ∑ b, w a * w b * (B e_a e_b) i`. -/
theorem bil_apply_comp (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (w : Fin n → ℝ) (i : Fin n) :
    B w w i = ∑ a, ∑ b, w a * w b * B (Pi.single a 1) (Pi.single b 1) i := by
  have hw : w = ∑ a, w a • (Pi.single a 1 : Fin n → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, Finset.sum_apply, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring


/-- **An intrinsic geodesic of the Levi-Civita connection is a chart-wise geodesic.** If `∇_{γ'} γ' = 0`
(`IsGeodesicCov`) for a connection `cov` that is the Levi-Civita connection of the Lorentzian metric `g`, then `γ` is a
geodesic of the coordinate metric in the chart at each `γ t` (`IsGeodesicCurveOn`, the definition of the Penrose rows). -/
theorem isGeodesicCurveOn_of_isGeodesicCov (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita g.toNondegMetric) {γ : ℝ → M} {J : Set ℝ} (hg : IsGeodesicCov cov γ J) :
    Penrose.IsGeodesicCurveOn g γ J := by
  intro t ht
  obtain ⟨X, hX, hev⟩ := hg t ht
  set p := γ t with hp
  have hbase : (tTriv (E := Fin n → ℝ) p).baseSet = (chartAt (Fin n → ℝ) p).source := by
    simp [tTriv, TangentBundle.trivializationAt_baseSet]
  have hγt : γ t ∈ (tTriv (E := Fin n → ℝ) p).baseSet := mem_baseSet_trivializationAt _ _ _
  have hcont : ContinuousAt γ t := (hev.self_of_nhds.1).continuousAt
  have hO : ∀ᶠ s in 𝓝 t, γ s ∈ (tTriv (E := Fin n → ℝ) p).baseSet :=
    hcont.eventually ((tTriv (E := Fin n → ℝ) p).open_baseSet.mem_nhds hγt)
  have hall := hO.and hev
  refine ⟨fun s => hv (E := Fin n → ℝ) p (γ s) (X (γ s)), {s | γ s ∈ (tTriv (E := Fin n → ℝ) p).baseSet ∧
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ s))) ∧
      cov X (γ s) (X (γ s)) = 0}, hall, ?_, ?_, ?_⟩
  · intro s hs
    rw [extChartAt_source, ← hbase]
    exact hs.1
  · intro s hs
    obtain ⟨hb, hγs, -⟩ := hs
    have hsrc : γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).source := by
      rw [extChartAt_source, ← hbase]; exact hb
    have := hasDerivAt_chart_curve p hγs hsrc
    rwa [← hv_eq_mfderiv p hb] at this
  · intro s hs
    obtain ⟨hb, hγs, hcov⟩ := hs
    have hXmd : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
        (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (γ s) :=
      (hX.contMDiffAt).mdifferentiableAt (by simp)
    have hd := hasDerivAt_hat_curve p hXmd hγs hb
    have hc := hat_cov cov p hb (σ := X) hXmd (X (γ s))
    rw [hcov] at hc
    have h0 : hv (E := Fin n → ℝ) p (γ s) (0 : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s)) = 0 :=
      ((tTriv (E := Fin n → ℝ) p).linear ℝ hb).map_zero
    rw [h0] at hc
    refine hd.congr_deriv ?_
    have hmv : mvfderiv 𝓘(ℝ, Fin n → ℝ) (hat (E := Fin n → ℝ) p X) (γ s) (X (γ s)) =
        -(gamHat cov p (γ s) (hv (E := Fin n → ℝ) p (γ s) (X (γ s))) (hv (E := Fin n → ℝ) p (γ s) (X (γ s)))) :=
      eq_neg_of_add_eq_zero_left hc.symm
    have hG : ∀ a b i : Fin n, (gamHat cov p (γ s) (Pi.single a 1) (Pi.single b 1)) i =
        christoffel (g.coordMetric p) i b a (extChartAt 𝓘(ℝ, Fin n → ℝ) p (γ s)) := by
      intro a b i
      rw [gamHat_coord cov p g.toNondegMetric h hb b a]
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hmv]
    funext i
    simp only [Pi.neg_apply, Lightlike.Geodesic.accel]
    rw [bil_apply_comp, neg_inj, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hG]; ring

/-- Non-vacuity: a constant curve is an intrinsic geodesic of every connection (take `X = 0`, so `∇_X X = 0`). This
only shows that the hypotheses of `isGeodesicCurveOn_of_isGeodesicCov` are satisfiable; a curve with non-zero velocity
needs a concrete connection. -/
example (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (q : M) (J : Set ℝ) : IsGeodesicCov cov (fun _ => q) J := by
  intro t _
  refine ⟨fun _ => 0, ?_, Filter.Eventually.of_forall fun s => ⟨?_, by simp⟩⟩
  · exact contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)
  · have h : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) (fun _ : ℝ => q) s 0 := hasMFDerivAt_const q s
    have e : (1 : ℝ →L[ℝ] ℝ).smulRight ((fun _ : M => (0 : TangentSpace 𝓘(ℝ, Fin n → ℝ) q)) ((fun _ : ℝ => q) s)) =
        (0 : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) q) := by
      ext; simp only [ContinuousLinearMap.smulRight_apply, smul_zero]; rfl
    simpa [e] using h

end Lightlike
