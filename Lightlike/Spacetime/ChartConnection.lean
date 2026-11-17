import Lightlike.Spacetime.LeviCivita
import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.LieDerivation
import Lightlike.Spacetime.FlatConnection

/-!
# The Levi-Civita connection in a chart

For a Lorentzian metric `g` on a manifold `M` modelled on `ℝⁿ` and a chart at `x₀`, the coordinate vector
fields `∂ᵢ` (`coordField`) commute (`mlieBracket_coordField`) and the Levi-Civita connection of `g` is given
by the Christoffel symbols of the coordinate components: `∇_{∂ᵢ} ∂ⱼ = Γᵏᵢⱼ ∂ₖ`
(`leviCivita_coordField`), where `Γ` is `christoffel (g.coordMetric x₀)` of `Curvature.lean`.

Proof: in the chart the coordinate fields are constants (`chartField_coordField`), so their bracket vanishes
(through Mathlib's `mpullback_mlieBracket`) and the Koszul expression of `LeviCivita.lean` reduces to
`½ (∂ᵢ g_{jl} + ∂ⱼ g_{li} - ∂_l g_{ij})` (`mvfderiv_gpair_coordField`, from `LieDerivation.lean`), which is
`Γᵏᵢⱼ g_{kl}` by `g⁻¹ g = 1`.

**Limits.** The Christoffel form only. The agreement of the curvature of a connection (extension-based
`curvatureAt`) with the coordinate Riemann tensor needs the independence of the curvature from the
extensions (`T-GE1-P2`), which is open.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The coordinate vector field `∂ᵢ` of the chart at `x₀`: the local frame of the tangent trivialization
(equal to `(extChartAt x₀).symm` pushforward of `eᵢ` on the chart domain). -/
def coordField (x₀ : M) (i : Fin n) : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p :=
  (chartTriv n x₀).localFrame (Pi.basisFun ℝ (Fin n)) i

/-- On the chart target the coordinate field is the coordinate basis vector. -/
theorem coordField_apply (x₀ : M) (i : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    coordField x₀ i ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      coordBasis x₀ (symm_mem_chartTriv_baseSet x₀ hy) i := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  unfold coordField
  rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTriv n x₀) (b := Pi.basisFun ℝ (Fin n)) (i := i) hp]
  rfl

/-- The coordinate vector fields are differentiable on the chart domain. -/
theorem mdiffAt_coordField (x₀ : M) (i : Fin n) {p : M} (hp : p ∈ (chartTriv n x₀).baseSet) :
    MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, coordField x₀ i q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) p := by
  have h : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, coordField x₀ i q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))
      (chartTriv n x₀).baseSet :=
    (chartTriv n x₀).contMDiffOn_localFrame_baseSet ∞ (Pi.basisFun ℝ (Fin n)) i
  exact ((h.contMDiffAt ((chartTriv n x₀).open_baseSet.mem_nhds hp))).mdifferentiableAt (by simp)


/-- In the chart, the coordinate field `∂ᵢ` is the constant `eᵢ`. -/
theorem chartField_coordField (x₀ : M) (i : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    chartField x₀ (coordField x₀ i) y = Pi.single i 1 := by
  have hz : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_target hy
  have h1 := mpullback_chart (coordField x₀ i) x₀ _ hz
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy] at h1
  have h2 : chartField x₀ (coordField x₀ i) y =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀)
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (coordField x₀ i ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) := h1
  rw [h2, coordField_apply x₀ i hy, coordBasis_apply]
  have h3 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀) hy
  have h4 := mfderiv_extChartAt_symm_eq x₀ hy
  have h5 : mfderivWithin 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
      (range 𝓘(ℝ, Fin n → ℝ)) y = (chartTriv n x₀).symmL ℝ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
    rw [← h4]
    simp [mfderivWithin_univ]
    rfl
  rw [h5] at h3
  exact congrArg (fun L => L (Pi.single i 1)) h3

/-- The derivative of the chart maps `∂ᵢ` to `eᵢ`. -/
theorem mfderiv_chart_coordField (x₀ : M) (i : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀)
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ i ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = Pi.single i 1 := by
  have hz : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_target hy
  have h1 := mpullback_chart (coordField x₀ i) x₀ _ hz
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy] at h1
  exact h1.symm.trans (chartField_coordField x₀ i hy)

/-- `0 a - 0 b = 0` for the zero linear map (helper for the bracket of constant fields). -/
theorem zero_apply_sub_zero_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a b : V) :
    (0 : V →L[ℝ] V) a - (0 : V →L[ℝ] V) b = 0 := by simp

/-- The coordinate vector fields commute. -/
theorem mlieBracket_coordField (x₀ : M) (i j : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    mlieBracket 𝓘(ℝ, Fin n → ℝ) (coordField x₀ i) (coordField x₀ j)
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) = 0 := by
  haveI : IsManifold 𝓘(ℝ, Fin n → ℝ) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by simp [minSmoothness])
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hsymm : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y := by
    have := contMDiffWithinAt_extChartAt_symm_range (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x₀ hy
    simpa [contMDiffWithinAt_univ] using this
  have hm := mpullback_mlieBracket (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ))
    (V := coordField x₀ i) (W := coordField x₀ j) (x₀ := y)
    (f := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) (mdiffAt_coordField x₀ i hp) (mdiffAt_coordField x₀ j hp)
    hsymm (n := ∞) (by simp)
  have hpb : ∀ k : Fin n, mpullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (coordField x₀ k) = chartField x₀ (coordField x₀ k) := by
    intro k
    unfold chartField
    simp [mpullbackWithin_univ]
  have hflat := mlieBracket_flat (V := Fin n → ℝ)
    (mpullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (coordField x₀ i))
    (mpullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (coordField x₀ j)) y
  have hev : ∀ k : Fin n, (mpullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (coordField x₀ k) : (Fin n → ℝ) → (Fin n → ℝ)) =ᶠ[nhds y]
      (fun _ => (Pi.single k 1 : Fin n → ℝ)) := fun k => by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds hy] with z hz
    rw [hpb k]
    exact chartField_coordField x₀ k hz
  have hd : ∀ k : Fin n, fderiv ℝ (mpullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm (coordField x₀ k) : (Fin n → ℝ) → (Fin n → ℝ)) y = 0 := fun k => by
    rw [(hev k).fderiv_eq]
    exact fderiv_const_apply _
  rw [hd i, hd j] at hflat
  have h0 : mpullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
      (mlieBracket 𝓘(ℝ, Fin n → ℝ) (coordField x₀ i) (coordField x₀ j)) y = 0 := by
    rw [hm]
    refine hflat.trans ?_
    exact zero_apply_sub_zero_apply (V := Fin n → ℝ) _ _
  have hA : (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y).IsInvertible := by
    have := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀) hy
    simpa [mfderivWithin_univ] using this
  have h1 : mpullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm
      (mlieBracket 𝓘(ℝ, Fin n → ℝ) (coordField x₀ i) (coordField x₀ j)) y =
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y).inverse
        (mlieBracket 𝓘(ℝ, Fin n → ℝ) (coordField x₀ i) (coordField x₀ j)
          ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) := rfl
  rw [h1] at h0
  exact (hA.inverse_apply_eq.1 h0).trans (map_zero _)

/-- `g(∂ₐ, ∂_b)` is the coordinate component. -/
theorem g_coordField (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) (a b : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (coordField x₀ a ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
      (coordField x₀ b ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) = g.coordMetric x₀ y a b := by
  rw [coordField_apply x₀ a hy, coordField_apply x₀ b hy, g.coordMetric_eq x₀ hy]

/-- The derivative of the pairing of coordinate fields is the partial derivative of the coordinate metric. -/
theorem mvfderiv_gpair_coordField [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
    (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) (a b c : Fin n) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) (gpair g (coordField x₀ a) (coordField x₀ b))
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ c ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) =
      pd c (fun y' => g.coordMetric x₀ y' a b) y := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hg := mdiffAt_gpair g (mdiffAt_coordField x₀ a hp) (mdiffAt_coordField x₀ b hp)
  have hz : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_target hy
  have h1 := mfderiv_eq_chart (gpair g (coordField x₀ a) (coordField x₀ b)) x₀ _ hz hg
    (coordField x₀ c ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))
  rw [mfderiv_chart_coordField x₀ c hy, (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy] at h1
  have hev : (gpair g (coordField x₀ a) (coordField x₀ b) ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) =ᶠ[nhds y]
      (fun y' => g.coordMetric x₀ y' a b) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds hy] with z hz
    exact g_coordField g x₀ a b hz
  rw [hev.fderiv_eq] at h1
  exact h1

/-- A tangent vector over the chart domain is determined by its pairings with the coordinate fields. -/
theorem eq_of_g_coordField (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    {v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)}
    (h : ∀ l, g.g _ v (coordField x₀ l ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) =
      g.g _ w (coordField x₀ l ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y))) : v = w := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  refine eq_of_g_eq g _ fun u => ?_
  rw [← (coordBasis x₀ hp).sum_repr u]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := h l
  rw [coordField_apply x₀ l hy] at this
  simp
  exact Or.inl this

/-- **The Christoffel form of the Levi-Civita connection in a chart**: `∇_{∂ᵢ} ∂ⱼ = Γᵏᵢⱼ ∂ₖ`. -/
theorem leviCivita_coordField [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
    (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (i j : Fin n) :
    leviCivita g (coordField x₀ j) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
        (coordField x₀ i ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) =
      ∑ k, christoffel (g.coordMetric x₀) k i j y •
        coordField x₀ k ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  refine eq_of_g_coordField g x₀ hy fun l => ?_
  rw [g_leviCivita g (mdiffAt_coordField x₀ i hp) (mdiffAt_coordField x₀ j hp) (mdiffAt_coordField x₀ l hp)]
  unfold koszul
  rw [mlieBracket_coordField x₀ i l hy, mlieBracket_coordField x₀ j i hy, mlieBracket_coordField x₀ l j hy,
    mvfderiv_gpair_coordField g x₀ j l i hy, mvfderiv_gpair_coordField g x₀ l i j hy,
    mvfderiv_gpair_coordField g x₀ i j l hy]
  simp only [map_zero, sub_zero, add_zero]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, g_coordField g x₀ _ l hy]
  have hsym := g.coordMetric_transpose x₀ y
  have hdet := g.coordMetric_isUnit_det x₀ hy
  have hinv : ∀ m l : Fin n, ∑ k, (g.coordMetric x₀ y)⁻¹ k m * g.coordMetric x₀ y k l = if m = l then 1 else 0 := by
    intro m l
    have h1 : ((g.coordMetric x₀ y)⁻¹).transpose = (g.coordMetric x₀ y)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hsym]
    have h2 := congrFun (congrFun (Matrix.nonsing_inv_mul _ hdet) m) l
    simp only [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    have h1' : ∀ k m : Fin n, (g.coordMetric x₀ y)⁻¹ k m = (g.coordMetric x₀ y)⁻¹ m k := fun k m => by
      have := congrFun (congrFun h1 m) k
      simpa using this
    exact Finset.sum_congr rfl fun k _ => by rw [h1' k m]
  unfold christoffel
  set T : Fin n → ℝ := fun m => pd i (fun y => g.coordMetric x₀ y m j) y +
    pd j (fun y => g.coordMetric x₀ y m i) y - pd m (fun y => g.coordMetric x₀ y i j) y with hT
  have hsw : ∀ a b : Fin n, g.coordMetric x₀ y a b = g.coordMetric x₀ y b a := fun a b => by
    have := congrFun (congrFun hsym b) a
    simpa using this
  have hfun : (fun y' => g.coordMetric x₀ y' j l) = fun y' => g.coordMetric x₀ y' l j := by
    funext y'
    have := g.coordMetric_transpose x₀ y'
    simpa using congrFun (congrFun this l) j
  have hsum : ∑ x, (1 / 2 * ∑ m, (g.coordMetric x₀ y)⁻¹ x m * T m) * g.coordMetric x₀ y x l =
      ∑ m, (1 / 2 * T m) * ∑ x, (g.coordMetric x₀ y)⁻¹ x m * g.coordMetric x₀ y x l := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun x _ => by ring
  show _ = ∑ x, (1 / 2 * ∑ m, (g.coordMetric x₀ y)⁻¹ x m * T m) * g.coordMetric x₀ y x l
  rw [hsum]
  simp only [hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hfun]
  simp only [hT]
  ring
end Lightlike
