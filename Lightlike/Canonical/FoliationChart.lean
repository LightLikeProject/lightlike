import Lightlike.Canonical.FoliationSmooth
import Lightlike.Canonical.ADM

/-!
# The ADM data of a foliation in coordinates adapted to it

A chart is **adapted** to the time function `τ` when its first coordinate is `τ` (`IsAdaptedChart`). Then the coordinate
field `∂₀` is a time vector (`dτ(∂₀) = 1`) and the fields `∂ᵢ`, `i ≥ 1`, are tangent to the leaves, and the coordinate
components of the metric are the 3+1 quantities (Gourgoulhon, arXiv:gr-qc/0703035, Sec. 4.2.3, eqs. (4.43)–(4.47),
pp. 57-58): with the shift `β` of the time vector `∂₀`,

* `g₀₀ = −N² + g(β, β)` (4.43) (`coordMetric_adapted_00`),
* `g₀ᵢ = g(β, ∂ᵢ) = βᵢ` (4.44)–(4.45) (`coordMetric_adapted_0i`),
* `gᵢⱼ = γ(∂ᵢ, ∂ⱼ) = γᵢⱼ` (4.46) (`coordMetric_adapted_ij`).

`admSliceMetric g q t` is the spatial block `(gᵢⱼ)` of the coordinate metric on the slice `x⁰ = t`, a tensor field on
`ℝᵈ` as in `Lightlike/Canonical/ADM.lean`; in an adapted chart it is the induced metric of the leaf `τ = t` in the
coordinates `xⁱ` (`admSliceMetric_eq_spatialMetric`). This is the map from the foliation to the chart data `h` of the
canonical files. The chart-free statements (4.44)–(4.45) are `g_time_tangent`.
-/

open Bundle Manifold Set Filter VectorField Matrix
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin (m + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (m + 1) → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin (m + 1) → ℝ) 2 M] [T2Space M]

variable {g : NondegMetric 𝓘(ℝ, Fin (m + 1) → ℝ) M} {τ : M → ℝ}

/-- **The mixed components of the metric are the shift** (Gourgoulhon (4.44)–(4.45), chart-free): for a time vector `T`
and a vector `X` tangent to the leaf, `g(T, X) = g(β, X)`. -/
theorem g_time_tangent (h : IsTimeFunction g τ) (T : Π x : M, TangentSpace 𝓘(ℝ, Fin (m + 1) → ℝ) x) {x : M}
    {X : TangentSpace 𝓘(ℝ, Fin (m + 1) → ℝ) x} (hX : dTime τ x X = 0) :
    g.g x (T x) X = g.g x (shift g τ T x) X := by
  have hn : g.g x (unitNormal g τ x) X = 0 := (dTime_eq_zero_iff h x X).1 hX
  conv_lhs => rw [time_eq_lapse_normal_add_shift (g := g) (τ := τ) T x]
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul, hn, mul_zero,
    zero_add]

variable (m τ) in
/-- **A chart adapted to the foliation**: its first coordinate is the time function, `τ ∘ φ⁻¹ = x⁰` on the chart
target (Gourgoulhon Sec. 4.2.1, the coordinates `(t, xⁱ)`). -/
def IsAdaptedChart (q : M) : Prop :=
  ∀ y ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).target, τ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y) = y 0

/-- The coordinate field `∂_a` of the chart at `q`. -/
abbrev coordVec (q : M) (a : Fin (m + 1)) : Π p : M, TangentSpace 𝓘(ℝ, Fin (m + 1) → ℝ) p :=
  Lightlike.cfield q (Pi.single a 1)

omit [T2Space M] in
/-- In an adapted chart, `dτ(∂_a) = δ_{a0}`. -/
theorem dTime_coordVec {q : M} (hτ : ContMDiff 𝓘(ℝ, Fin (m + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ τ) (ha : IsAdaptedChart m τ q)
    {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).source) (a : Fin (m + 1)) :
    dTime τ p (coordVec q a p) = if a = 0 then 1 else 0 := by
  set φ := extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q with hφ
  have hpb : p ∈ (tTriv (E := Fin (m + 1) → ℝ) q).baseSet := by
    simpa [hφ, extChartAt_source, tTriv, TangentBundle.trivializationAt_baseSet] using hp
  have hmd : MDifferentiableAt 𝓘(ℝ, Fin (m + 1) → ℝ) 𝓘(ℝ, ℝ) τ p := (hτ p).mdifferentiableAt (by simp)
  have h1 := mvfderiv_chart_fixed q τ hp hmd (coordVec q a p)
  have h2 : mfderiv 𝓘(ℝ, Fin (m + 1) → ℝ) 𝓘(ℝ, Fin (m + 1) → ℝ) φ p (coordVec q a p) = Pi.single a 1 :=
    mfderiv_chart_symmL q hpb (Pi.single a 1)
  have hy : φ p ∈ φ.target := φ.map_source hp
  have hev : τ ∘ φ.symm =ᶠ[𝓝 (φ p)] fun y => y 0 :=
    Filter.eventually_of_mem ((isOpen_extChartAt_target q).mem_nhds hy) fun y hy' => ha y hy'
  have h3 : fderiv ℝ (τ ∘ φ.symm) (φ p) = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) 0 := by
    rw [hev.fderiv_eq]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) 0).fderiv
  show mvfderiv 𝓘(ℝ, Fin (m + 1) → ℝ) τ p (coordVec q a p) = _
  rw [h1, h2, h3]
  simp [Pi.single_apply, eq_comm]

omit [T2Space M] in
/-- In an adapted chart the fields `∂ᵢ`, `i ≥ 1`, are tangent to the leaves. -/
theorem dTime_coordVec_succ {q : M} (hτ : ContMDiff 𝓘(ℝ, Fin (m + 1) → ℝ) 𝓘(ℝ, ℝ) ∞ τ) (ha : IsAdaptedChart m τ q)
    {p : M} (hp : p ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).source) (i : Fin m) :
    dTime τ p (coordVec q i.succ p) = 0 := by
  rw [dTime_coordVec hτ ha hp]
  simp [Fin.succ_ne_zero]

omit [IsManifold 𝓘(ℝ, Fin (m + 1) → ℝ) 2 M] [T2Space M] in
/-- The coordinate metric at `q` at the chart image of `p` is `g(∂_a, ∂_b)`. -/
theorem coordMetric_chart_eq (q : M) {y : Fin (m + 1) → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).target)
    (a b : Fin (m + 1)) :
    g.coordMetric q y a b =
      g.g ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y)
        (coordVec q a ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y))
        (coordVec q b ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y)) := by
  rw [g.coordMetric_eq q hy, coordBasis_apply, coordBasis_apply]
  rfl

/-- **`g₀₀ = −N² + β_k β^k`** in an adapted chart (Gourgoulhon (4.43)), with the shift of the time vector `∂₀`. -/
theorem coordMetric_adapted_00 (h : IsTimeFunction g τ) {q : M} (ha : IsAdaptedChart m τ q)
    {y : Fin (m + 1) → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).target) :
    g.coordMetric q y 0 0 =
      -(lapse g τ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y)) ^ 2 +
        g.g _ (shift g τ (coordVec q 0) ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y))
          (shift g τ (coordVec q 0) ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y)) := by
  have hp := (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).map_target hy
  rw [coordMetric_chart_eq q hy]
  exact g_time_time h (by rw [dTime_coordVec h.smooth ha hp]; simp)

/-- **`g₀ᵢ = βᵢ`** in an adapted chart (Gourgoulhon (4.45)). -/
theorem coordMetric_adapted_0i (h : IsTimeFunction g τ) {q : M} (ha : IsAdaptedChart m τ q)
    {y : Fin (m + 1) → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).target) (i : Fin m) :
    g.coordMetric q y 0 i.succ =
      g.g _ (shift g τ (coordVec q 0) ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y))
        (coordVec q i.succ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y)) := by
  have hp := (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).map_target hy
  rw [coordMetric_chart_eq q hy]
  exact g_time_tangent h (coordVec q 0) (dTime_coordVec_succ h.smooth ha hp i)

/-- **`gᵢⱼ = γᵢⱼ`** in an adapted chart (Gourgoulhon (4.46)). -/
theorem coordMetric_adapted_ij (h : IsTimeFunction g τ) {q : M} (ha : IsAdaptedChart m τ q)
    {y : Fin (m + 1) → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).target) (i j : Fin m) :
    g.coordMetric q y i.succ j.succ =
      spatialMetric g τ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y)
        (coordVec q i.succ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y))
        (coordVec q j.succ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm y)) := by
  have hp := (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).map_target hy
  rw [coordMetric_chart_eq q hy, spatialMetric_of_tangent h (dTime_coordVec_succ h.smooth ha hp i)]

variable (g) in
/-- **The ADM metric of the slice `x⁰ = t`** in the chart at `q`: the spatial block `(gᵢⱼ)` of the coordinate metric
at `(t, x)`, a tensor field on `ℝᵐ` as the data `h` of `Lightlike/Canonical/ADM.lean`. -/
def admSliceMetric (q : M) (t : ℝ) : TensorField m :=
  fun x => Matrix.of fun i j => g.coordMetric q (Fin.cons t x) i.succ j.succ

/-- **In an adapted chart the ADM metric of a slice is the induced metric of the leaf** in the coordinates `xⁱ`. -/
theorem admSliceMetric_eq_spatialMetric (h : IsTimeFunction g τ) {q : M} (ha : IsAdaptedChart m τ q) {t : ℝ}
    {x : Fin m → ℝ} (hx : (Fin.cons t x : Fin (m + 1) → ℝ) ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).target)
    (i j : Fin m) :
    admSliceMetric g q t x i j =
      spatialMetric g τ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm (Fin.cons t x))
        (coordVec q i.succ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm (Fin.cons t x)))
        (coordVec q j.succ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm (Fin.cons t x))) :=
  coordMetric_adapted_ij h ha hx i j

omit [IsManifold 𝓘(ℝ, Fin (m + 1) → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin (m + 1) → ℝ) 2 M] [T2Space M] in
/-- The points of the slice in an adapted chart lie on the leaf `τ = t`. -/
theorem time_admSlice {q : M} (ha : IsAdaptedChart m τ q) {t : ℝ} {x : Fin m → ℝ}
    (hx : (Fin.cons t x : Fin (m + 1) → ℝ) ∈ (extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).target) :
    τ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm (Fin.cons t x)) = t := by
  rw [ha _ hx]; rfl


omit [T2Space M] in
/-- If the normal is parallel at `x` (`∇n = 0` there), the extrinsic curvature vanishes at `x`. -/
theorem extrinsicCurvature_eq_zero_of_cov {cov : Connection 𝓘(ℝ, Fin (m + 1) → ℝ) M} {x : M}
    (h0 : cov (unitNormal g τ) x = 0) (u v : TangentSpace 𝓘(ℝ, Fin (m + 1) → ℝ) x) :
    extrinsicCurvature g τ cov x u v = 0 := by
  simp [extrinsicCurvature, Hypersurface.secondFF, h0]

variable (g τ) in
/-- **The extrinsic curvature of the slice** in the coordinates `xⁱ`: `K_ij = K(∂ᵢ, ∂ⱼ)` at the point `(t, x)`. -/
def admSliceExtrinsic (cov : Connection 𝓘(ℝ, Fin (m + 1) → ℝ) M) (q : M) (t : ℝ) : TensorField m :=
  fun x => Matrix.of fun i j =>
    extrinsicCurvature g τ cov ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm (Fin.cons t x))
      (coordVec q i.succ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm (Fin.cons t x)))
      (coordVec q j.succ ((extChartAt 𝓘(ℝ, Fin (m + 1) → ℝ) q).symm (Fin.cons t x)))

variable (g τ) in
/-- **The ADM momentum of the slice** `π^{ij} = √det h (K h^{ij} − K^{ij})`, with `K^{ij} = h^{ik} K_kl h^{lj}` and
`K = h^{ij} K_ij` (Gourgoulhon (4.108), p. 67): together with `admSliceMetric` the chart data `(h, π)` of
`Lightlike/Canonical/ADM.lean` of the foliation. -/
def admSliceMomentum (cov : Connection 𝓘(ℝ, Fin (m + 1) → ℝ) M) (q : M) (t : ℝ) : TensorField m :=
  fun x => Real.sqrt (admSliceMetric g q t x).det •
    (((admSliceMetric g q t x)⁻¹ * admSliceExtrinsic g τ cov q t x).trace • (admSliceMetric g q t x)⁻¹ -
      (admSliceMetric g q t x)⁻¹ * admSliceExtrinsic g τ cov q t x * (admSliceMetric g q t x)⁻¹)

omit [IsManifold 𝓘(ℝ, Fin (m + 1) → ℝ) 2 M] [T2Space M] in
/-- The slice metric is symmetric. -/
theorem admSliceMetric_symm (q : M) (t : ℝ) (x : Fin m → ℝ) :
    (admSliceMetric g q t x)ᵀ = admSliceMetric g q t x := by
  ext i j
  have := congrFun (congrFun (g.coordMetric_transpose q (Fin.cons t x)) i.succ) j.succ
  simpa [admSliceMetric, Matrix.transpose_apply] using this

/-- For the Levi-Civita connection the slice extrinsic curvature is symmetric. -/
theorem admSliceExtrinsic_symm (h : IsTimeFunction g τ) {cov : Connection 𝓘(ℝ, Fin (m + 1) → ℝ) M}
    (hc : cov.IsLeviCivita g) (q : M) (t : ℝ) (x : Fin m → ℝ) :
    (admSliceExtrinsic g τ cov q t x)ᵀ = admSliceExtrinsic g τ cov q t x := by
  ext i j
  simp only [Matrix.transpose_apply, admSliceExtrinsic, Matrix.of_apply]
  exact extrinsicCurvature_symm_of_timeFunction h hc _ _ _

/-- **The ADM momentum of the slice is a symmetric tensor** (for the Levi-Civita connection). -/
theorem admSliceMomentum_symm (h : IsTimeFunction g τ) {cov : Connection 𝓘(ℝ, Fin (m + 1) → ℝ) M}
    (hc : cov.IsLeviCivita g) (q : M) (t : ℝ) (x : Fin m → ℝ) :
    (admSliceMomentum g τ cov q t x)ᵀ = admSliceMomentum g τ cov q t x := by
  have hh := admSliceMetric_symm (g := g) q t x
  have hK := admSliceExtrinsic_symm h hc q t x
  have hi : ((admSliceMetric g q t x)⁻¹)ᵀ = (admSliceMetric g q t x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hh]
  simp only [admSliceMomentum, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_mul, hi, hK,
    Matrix.mul_assoc]

end Lightlike.Canonical
