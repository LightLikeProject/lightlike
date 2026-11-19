import Lightlike.Spacetime.LeviCivita
import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.Corners.Coordinates
import Lightlike.Spacetime.CurvatureWithin
import Lightlike.Spacetime.LieDerivation
import Lightlike.Spacetime.Corners.LieDerivation
import Lightlike.Spacetime.FlatConnection
import Lightlike.Spacetime.ChartConnection
import Lightlike.Spacetime.Corners.Curvature

/-!
# The Levi-Civita connection in a chart

For a Lorentzian metric `g` on a manifold `M` modelled on `ℝⁿ` and a chart at `x₀`, the coordinate vector
fields `∂ᵢ` (`coordFieldW`) commute (`mlieBracket_coordFieldW`) and the Levi-Civita connection of `g` is given
by the Christoffel symbols of the coordinate components: `∇_{∂ᵢ} ∂ⱼ = Γᵏᵢⱼ ∂ₖ`
(`leviCivita_coordFieldW`), where `Γ` is `christoffel (g.coordMetricW x₀)` of `Curvature.lean`.

Proof: in the chart the coordinate fields are constants (`chartField_coordFieldW`), so their bracket vanishes
(through Mathlib's `mpullback_mlieBracket`) and the Koszul expression of `LeviCivita.lean` reduces to
`½ (∂ᵢ g_{jl} + ∂ⱼ g_{li} - ∂_l g_{ij})` (`mvfderiv_gpair_coordFieldW`, from `LieDerivation.lean`), which is
`Γᵏᵢⱼ g_{kl}` by `g⁻¹ g = 1`.

**Limits.** The Christoffel form only. The agreement of the curvature of a connection (extension-based
`curvatureAt`) with the coordinate Riemann tensor needs the independence of the curvature from the
extensions (`T-GE1-P2`), which is open.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/ChartConnection.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The coordinate vector field `∂ᵢ` of the chart at `x₀`: the local frame of the tangent trivialization
(equal to `(extChartAt x₀).symm` pushforward of `eᵢ` on the chart domain). -/
def coordFieldW (x₀ : M) (i : Fin n) : Π p : M, TangentSpace I p :=
  (chartTrivW (I := I) n x₀).localFrame (Pi.basisFun ℝ (Fin n)) i

/-- On the chart target the coordinate field is the coordinate basis vector. -/
theorem coordField_applyW (x₀ : M) (i : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    coordFieldW x₀ i ((extChartAt I x₀).symm y) =
      coordBasisW x₀ (symm_mem_chartTriv_baseSetW x₀ hy) i := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  unfold coordFieldW
  rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTrivW (I := I) n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := i) hp]
  rfl

/-- The coordinate vector fields are differentiable on the chart domain. -/
theorem mdiffAt_coordFieldW (x₀ : M) (i : Fin n) {p : M} (hp : p ∈ (chartTrivW (I := I) n x₀).baseSet) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, coordFieldW x₀ i q⟩ : TangentBundle I M)) p := by
  have h : ContMDiffOn I (I.prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, coordFieldW x₀ i q⟩ : TangentBundle I M))
      (chartTrivW (I := I) n x₀).baseSet :=
    (chartTrivW (I := I) n x₀).contMDiffOn_localFrame_baseSet ∞ (Pi.basisFun ℝ (Fin n)) i
  exact ((h.contMDiffAt ((chartTrivW (I := I) n x₀).open_baseSet.mem_nhds hp))).mdifferentiableAt (by simp)


/-- In the chart, the coordinate field `∂ᵢ` is the constant `eᵢ`. -/
theorem chartField_coordFieldW (x₀ : M) (i : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    chartFieldW (I := I) x₀ (coordFieldW x₀ i) y = Pi.single i 1 := by
  have hz : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  have h1 := mpullback_chartW (coordFieldW x₀ i) x₀ _ hz
  rw [(extChartAt I x₀).right_inv hy] at h1
  have h2 : chartFieldW (I := I) x₀ (coordFieldW x₀ i) y =
      mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀)
        ((extChartAt I x₀).symm y) (coordFieldW x₀ i ((extChartAt I x₀).symm y)) := h1
  rw [h2, coordField_applyW x₀ i hy, coordBasis_applyW]
  have h3 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀) hy
  have h4 := mfderiv_extChartAt_symm_eqW x₀ hy
  rw [h4] at h3
  exact congrArg (fun L => L (Pi.single i 1)) h3

/-- The derivative of the chart maps `∂ᵢ` to `eᵢ`. -/
theorem mfderiv_chart_coordFieldW (x₀ : M) (i : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀)
        ((extChartAt I x₀).symm y)
        (coordFieldW x₀ i ((extChartAt I x₀).symm y)) = Pi.single i 1 := by
  have hz : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  have h1 := mpullback_chartW (coordFieldW x₀ i) x₀ _ hz
  rw [(extChartAt I x₀).right_inv hy] at h1
  exact h1.symm.trans (chartField_coordFieldW x₀ i hy)

/-- The `k`-th chart coordinate function is smooth on the chart domain. -/
theorem contMDiffAt_chartCoord (x₀ : M) (k : Fin n) {p : M} (hp : p ∈ (extChartAt I x₀).source) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (extChartAt I x₀ q) k) p := by
  have h1 : ContMDiffAt I 𝓘(ℝ, Fin n → ℝ) ∞ (extChartAt I x₀) p :=
    contMDiffAt_extChartAt' (by simpa using hp)
  have h2 : ContDiff ℝ ∞ (fun v : Fin n → ℝ => v k) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).contDiff
  exact h2.contMDiff.contMDiffAt.comp p h1

/-- The derivative of the `k`-th chart coordinate function is the `k`-th component of the chart derivative. -/
theorem mfderiv_chartCoord (x₀ : M) (k : Fin n) {p : M} (hp : p ∈ (extChartAt I x₀).source)
    (v : TangentSpace I p) :
    mfderiv I 𝓘(ℝ, ℝ) (fun q : M => (extChartAt I x₀ q) k) p v =
      (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) p v) k := by
  have h1 : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) p :=
    mdifferentiableAt_extChartAt (by simpa using hp)
  have h2 : ContDiff ℝ ∞ (fun v : Fin n → ℝ => v k) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).contDiff
  have hc : mfderiv I 𝓘(ℝ, ℝ) ((fun v : Fin n → ℝ => v k) ∘ (extChartAt I x₀)) p =
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (fun v : Fin n → ℝ => v k) (extChartAt I x₀ p)).comp
        (mfderiv I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) p) :=
    mfderiv_comp p (h2.contMDiff.mdifferentiableAt (by simp)) h1
  have hd : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (fun v : Fin n → ℝ => v k) (extChartAt I x₀ p) =
      ContinuousLinearMap.proj k := by
    rw [mfderiv_eq_fderiv]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).fderiv
  show mfderiv I 𝓘(ℝ, ℝ) ((fun v : Fin n → ℝ => v k) ∘ (extChartAt I x₀)) p v = _
  rw [hc, hd]
  rfl

/-- The coordinate vector fields commute. -/
theorem mlieBracket_coordFieldW (x₀ : M) (i j : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    mlieBracket I (coordFieldW x₀ i) (coordFieldW x₀ j)
      ((extChartAt I x₀).symm y) = 0 := by
  haveI : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  set φ := extChartAt I x₀ with hφ
  set z := φ.symm y with hz'
  have hz : z ∈ φ.source := φ.map_target hy
  have hp : z ∈ (chartTrivW (I := I) n x₀).baseSet := symm_mem_chartTriv_baseSetW x₀ hy
  have hsrc : ∀ᶠ q in nhds z, q ∈ φ.source := (isOpen_extChartAt_source (I := I) x₀).mem_nhds hz
  -- derivative of the chart applied to the bracket vanishes componentwise
  have hcomp : ∀ k : Fin n, mfderiv I 𝓘(ℝ, Fin n → ℝ) φ z
      (mlieBracket I (coordFieldW x₀ i) (coordFieldW x₀ j) z) k = 0 := by
    intro k
    have hdir : ∀ l : Fin n, ∀ᶠ q in nhds z,
        dirDerivW (I := I) (fun q : M => (φ q) k) (coordFieldW x₀ l) q = (Pi.single l 1 : Fin n → ℝ) k := by
      intro l
      filter_upwards [hsrc] with q hq
      show mfderiv I 𝓘(ℝ, ℝ) (fun q : M => (φ q) k) q (coordFieldW x₀ l q) = _
      rw [mfderiv_chartCoord x₀ k hq]
      have := mfderiv_chart_coordFieldW (I := I) x₀ l (y := φ q) (φ.map_source hq)
      rw [φ.left_inv hq] at this
      rw [this]
    have hX := mdiffAt_coordFieldW x₀ i hp
    have hY := mdiffAt_coordFieldW x₀ j hp
    have hg : ∀ᶠ q in nhds z, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun q : M => (φ q) k) q := by
      filter_upwards [hsrc] with q hq using contMDiffAt_chartCoord x₀ k hq
    have hb := mfderiv_mlieBracketW (fun q : M => (φ q) k) (coordFieldW x₀ i) (coordFieldW x₀ j) z hg hX hY
    have hconst : ∀ l : Fin n, ∀ v : TangentSpace I z,
        (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (dirDerivW (I := I) (fun q : M => (φ q) k) (coordFieldW x₀ l)) z v) = 0 := by
      intro l v
      have hc : (dirDerivW (I := I) (fun q : M => (φ q) k) (coordFieldW x₀ l)) =ᶠ[nhds z]
          fun _ => (Pi.single l 1 : Fin n → ℝ) k := hdir l
      rw [hc.mfderiv_eq]
      simp; rfl
    refine (mfderiv_chartCoord x₀ k hz _).symm.trans ?_
    refine hb.trans ?_
    rw [hconst j, hconst i]
    simp
  have h0 : mfderiv I 𝓘(ℝ, Fin n → ℝ) φ z (mlieBracket I (coordFieldW x₀ i) (coordFieldW x₀ j) z) = 0 :=
    funext hcomp
  have hA : (mfderiv I 𝓘(ℝ, Fin n → ℝ) φ z).IsInvertible := isInvertible_mfderiv_extChartAt (I := I) hz
  obtain ⟨B, hB⟩ := hA
  have h1 : B (mlieBracket I (coordFieldW x₀ i) (coordFieldW x₀ j) z) = 0 := by
    rw [← h0, ← hB]; rfl
  exact (B.map_eq_zero_iff).1 h1

/-- `g(∂ₐ, ∂_b)` is the coordinate component. -/
theorem g_coordFieldW (g : NondegMetric I M) (x₀ : M) (a b : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    g.g ((extChartAt I x₀).symm y) (coordFieldW x₀ a ((extChartAt I x₀).symm y))
      (coordFieldW x₀ b ((extChartAt I x₀).symm y)) = g.coordMetricW x₀ y a b := by
  rw [coordField_applyW x₀ a hy, coordField_applyW x₀ b hy, g.coordMetric_eqW x₀ hy]

/-- The derivative of the pairing of coordinate fields is the partial derivative of the coordinate metric. -/
theorem mvfderiv_gpair_coordFieldW [IsManifold I 2 M]
    (g : NondegMetric I M) (x₀ : M) (a b c : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    mvfderiv I (gpair g (coordFieldW x₀ a) (coordFieldW x₀ b))
        ((extChartAt I x₀).symm y)
        (coordFieldW x₀ c ((extChartAt I x₀).symm y)) =
      pdW (range I) c (fun y' => g.coordMetricW x₀ y' a b) y := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  have hg := mdiffAt_gpair g (mdiffAt_coordFieldW x₀ a hp) (mdiffAt_coordFieldW x₀ b hp)
  have hz : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  have h1 := mfderiv_eq_chartW (gpair g (coordFieldW x₀ a) (coordFieldW x₀ b)) x₀ _ hz hg
    (coordFieldW x₀ c ((extChartAt I x₀).symm y))
  rw [mfderiv_chart_coordFieldW x₀ c hy, (extChartAt I x₀).right_inv hy] at h1
  have hev' : (gpair g (coordFieldW x₀ a) (coordFieldW x₀ b) ∘ (extChartAt I x₀).symm) =ᶠ[nhdsWithin y (range I)]
      (fun y' => g.coordMetricW x₀ y' a b) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy] with z hz
    exact g_coordFieldW g x₀ a b hz
  rw [hev'.fderivWithin_eq (g_coordFieldW g x₀ a b hy)] at h1
  exact h1

/-- A tangent vector over the chart domain is determined by its pairings with the coordinate fields. -/
theorem eq_of_g_coordFieldW (g : NondegMetric I M) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target)
    {v w : TangentSpace I ((extChartAt I x₀).symm y)}
    (h : ∀ l, g.g _ v (coordFieldW x₀ l ((extChartAt I x₀).symm y)) =
      g.g _ w (coordFieldW x₀ l ((extChartAt I x₀).symm y))) : v = w := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  refine eq_of_g_eq g _ fun u => ?_
  rw [← (coordBasisW x₀ hp).sum_repr u]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := h l
  rw [coordField_applyW x₀ l hy] at this
  simp
  exact Or.inl this

/-- **The Christoffel form of the Levi-Civita connection in a chart**: `∇_{∂ᵢ} ∂ⱼ = Γᵏᵢⱼ ∂ₖ`. -/
theorem leviCivita_coordFieldW [IsManifold I 2 M]
    (g : NondegMetric I M) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) (i j : Fin n) :
    leviCivita g (coordFieldW x₀ j) ((extChartAt I x₀).symm y)
        (coordFieldW x₀ i ((extChartAt I x₀).symm y)) =
      ∑ k, christoffelW (range I) (g.coordMetricW x₀) k i j y •
        coordFieldW x₀ k ((extChartAt I x₀).symm y) := by
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  refine eq_of_g_coordFieldW g x₀ hy fun l => ?_
  rw [g_leviCivita g (mdiffAt_coordFieldW x₀ i hp) (mdiffAt_coordFieldW x₀ j hp) (mdiffAt_coordFieldW x₀ l hp)]
  unfold koszul
  rw [mlieBracket_coordFieldW x₀ i l hy, mlieBracket_coordFieldW x₀ j i hy, mlieBracket_coordFieldW x₀ l j hy,
    mvfderiv_gpair_coordFieldW g x₀ j l i hy, mvfderiv_gpair_coordFieldW g x₀ l i j hy,
    mvfderiv_gpair_coordFieldW g x₀ i j l hy]
  simp only [map_zero, sub_zero, add_zero]
  rw [map_sum, sum_apply]
  simp only [map_smul, smul_apply, smul_eq_mul, g_coordFieldW g x₀ _ l hy]
  have hsym := g.coordMetric_transposeW x₀ y
  have hdet := g.coordMetric_isUnit_detW x₀ hy
  have hinv : ∀ m l : Fin n, ∑ k, (g.coordMetricW x₀ y)⁻¹ k m * g.coordMetricW x₀ y k l = if m = l then 1 else 0 := by
    intro m l
    have h1 : ((g.coordMetricW x₀ y)⁻¹).transpose = (g.coordMetricW x₀ y)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hsym]
    have h2 := congrFun (congrFun (Matrix.nonsing_inv_mul _ hdet) m) l
    simp only [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    have h1' : ∀ k m : Fin n, (g.coordMetricW x₀ y)⁻¹ k m = (g.coordMetricW x₀ y)⁻¹ m k := fun k m => by
      have := congrFun (congrFun h1 m) k
      simpa using this
    exact Finset.sum_congr rfl fun k _ => by rw [h1' k m]
  unfold christoffelW
  set T : Fin n → ℝ := fun m => pdW (range I) i (fun y => g.coordMetricW x₀ y m j) y +
    pdW (range I) j (fun y => g.coordMetricW x₀ y m i) y - pdW (range I) m (fun y => g.coordMetricW x₀ y i j) y with hT
  have hsw : ∀ a b : Fin n, g.coordMetricW x₀ y a b = g.coordMetricW x₀ y b a := fun a b => by
    have := congrFun (congrFun hsym b) a
    simpa using this
  have hfun : (fun y' => g.coordMetricW x₀ y' j l) = fun y' => g.coordMetricW x₀ y' l j := by
    funext y'
    have := g.coordMetric_transposeW x₀ y'
    simpa using congrFun (congrFun this l) j
  have hsum : ∑ x, (1 / 2 * ∑ m, (g.coordMetricW x₀ y)⁻¹ x m * T m) * g.coordMetricW x₀ y x l =
      ∑ m, (1 / 2 * T m) * ∑ x, (g.coordMetricW x₀ y)⁻¹ x m * g.coordMetricW x₀ y x l := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => by ring
  show _ = ∑ x, (1 / 2 * ∑ m, (g.coordMetricW x₀ y)⁻¹ x m * T m) * g.coordMetricW x₀ y x l
  rw [hsum]
  simp only [hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hfun]
  simp only [hT]
  ring
end Lightlike
