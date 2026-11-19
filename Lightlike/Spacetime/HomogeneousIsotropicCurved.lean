import Lightlike.Spacetime.HomogeneousIsotropic
import Lightlike.Cosmology.FLRW

/-!
# Homogeneity and isotropy give the FLRW form, curved slices (G1-024, `k ≠ 0`)

On `ℝ⁴` (coordinate `0` is time) let `D_k = {1 + k |x|²/4 > 0}` (`|x|²` the spatial norm, `Cosmology.spatialNormSq`): all of
`ℝ⁴` for `k ≥ 0`, a solid cylinder over a ball for `k < 0`. The maximally symmetric 3-metric of curvature `k` in isotropic
coordinates is `δ/(1 + k|x|²/4)²`; its Killing fields are the rotations `x_i ∂_j − x_j ∂_i` and the curved translations
`P_m = (1 − k|x|²/4) ∂_m + (k/2) x_m (x · ∂)` (`curvTrans`; `k = 0` gives the translations `∂_m`).

* `lieDerivMetric_basis`: the Lie derivative of the metric on the coordinate basis fields, for any field;
* `curved_flrw_of_killing`: a smooth metric of any signature for which the three rotations and the three curved translations
  are Killing on `D_k` has, on `D_k`, `g_{0k} = 0`, `g_{ij} = a(t) δ_{ij}/(1 + k|x|²/4)²` and `g_{00} = b(t)`: the FLRW form with
  lapse `b` and scale factor `a`, for every `k` (for `k = 0` this is `flat_flrw_of_killing`).

Proof: at a point `(t, 0)` the rotations give `g_{0k} = 0` and `g_{ij} ∝ δ_{ij}` (isotropy). Along the segment from `(t, 0)` to
`x = (t, w)`, the combination `Σ wₘ Pₘ` of the curved translations is `(1 + k s²|w|²/4) w` and its derivative is `(k s |w|²/2)`
times the spatial projection, so the Killing equation is the linear equation
`(1 + k s²|w|²/4) F' + (k s |w|²/2) c F = 0` for `F(s) = g_{μν}(t, s w)` (`c` the number of spatial indices among `μ, ν`), whose
solutions are `F(s) (1 + k s²|w|²/4)^c = F(0)`.

**Limits.** The metric is given on `ℝ⁴` and the Killing equations on `D_k`; the Killing fields are given in these coordinates
(the passage from an abstract homogeneous and isotropic foliation to adapted coordinates is not proved); the converse (the FLRW
metric has these Killing fields) is not stated here.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

/-- **The Lie derivative of the metric on the coordinate basis fields**:
`(L_X g)(∂_μ, ∂_ν) = X(g_{μν}) + g(DX ∂_μ, ∂_ν) + g(∂_μ, DX ∂_ν)`, for any vector field `X` of `ℝⁿ`. -/
theorem lieDerivMetric_basis {n : ℕ} (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ))
    (X : Π y : Fin n → ℝ, TangentSpace 𝓘(ℝ, Fin n → ℝ) y) (μ ν : Fin n) (x : Fin n → ℝ) :
    lieDerivMetric g X (basisField n μ) (basisField n ν) x =
      fderiv ℝ (metricComp g μ ν) x (X x) +
        g.g x (fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single μ 1)) (Pi.single ν 1) +
        g.g x (Pi.single μ 1) (fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single ν 1)) := by
  unfold lieDerivMetric
  have h1 : ∀ κ : Fin n, mlieBracket 𝓘(ℝ, Fin n → ℝ) X (basisField n κ) x =
      - fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single κ 1) := by
    intro κ
    rw [mlieBracket_flat, fderiv_basisField]
    change (0 : Fin n → ℝ) - fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single κ 1) = _
    exact zero_sub _
  have h3 : mvfderiv 𝓘(ℝ, Fin n → ℝ) (gpair g (basisField n μ) (basisField n ν)) x (X x) =
      fderiv ℝ (metricComp g μ ν) x (X x) := by
    have : gpair g (basisField n μ) (basisField n ν) = metricComp g μ ν := rfl
    rw [this]
    unfold mvfderiv
    rw [mfderiv_eq_fderiv]
    rfl
  rw [h1 μ, h1 ν, h3]
  have e1 : (g.g x (-fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single μ 1))) (Pi.single ν 1) =
      -(g.g x (fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single μ 1))) (Pi.single ν 1) := by
    have := congrArg (fun L => L (Pi.single ν 1))
      (map_neg (g.g x) (fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single μ 1) : TangentSpace 𝓘(ℝ, Fin n → ℝ) x))
    exact this
  have e2 : (g.g x (Pi.single μ 1)) (-fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single ν 1)) =
      -(g.g x (Pi.single μ 1)) (fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single ν 1)) :=
    map_neg ((g.g x) (Pi.single μ 1)) _
  show _ - (g.g x (-fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single μ 1))) (Pi.single ν 1) -
    (g.g x (Pi.single μ 1)) (-fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x (Pi.single ν 1)) = _
  rw [e1, e2]
  ring

/-- The spatial part `x - x⁰ e₀` of a point of `ℝ⁴`. -/
def spatialPart : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.id ℝ _ - (ContinuousLinearMap.proj (0 : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ).smulRight (Pi.single 0 1)

theorem spatialPart_apply (x : Fin 4 → ℝ) (μ : Fin 4) : spatialPart x μ = if μ = 0 then 0 else x μ := by
  by_cases h : μ = 0
  · subst h; simp [spatialPart]
  · simp [spatialPart, h]

/-- The spatial dot product `Σᵢ xⁱ uⁱ`. -/
def sdot (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin 3, x i.succ • (ContinuousLinearMap.proj (i.succ : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ)

theorem sdot_apply (x u : Fin 4 → ℝ) : sdot x u = ∑ i : Fin 3, x i.succ * u i.succ := by
  simp [sdot]

theorem hasFDerivAt_spatialNormSq (x : Fin 4 → ℝ) :
    HasFDerivAt Cosmology.spatialNormSq ((2 : ℝ) • sdot x) x := by
  have h : ∀ i : Fin 3, HasFDerivAt (fun y : Fin 4 → ℝ => y i.succ ^ 2)
      ((2 : ℝ) • x i.succ • (ContinuousLinearMap.proj (i.succ : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ)) x := by
    intro i
    have := ((ContinuousLinearMap.proj (i.succ : Fin 4) : (Fin 4 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := x)).pow 2
    refine this.congr_fderiv ?_
    ext u; simp; ring
  have hs := HasFDerivAt.sum (u := Finset.univ) fun i _ => h i
  unfold Cosmology.spatialNormSq
  convert hs using 1
  · funext y; simp
  · ext u; simp [sdot, Finset.mul_sum]

/-- **The curved translations** `Pₘ = (1 − k|x|²/4) ∂ₘ + (k/2) xₘ (x · ∂)`: with the rotations, the Killing fields of the
maximally symmetric 3-metric `δ/(1 + k|x|²/4)²` of curvature `k`. -/
def curvTransF (k : ℝ) (m : Fin 4) : (Fin 4 → ℝ) → (Fin 4 → ℝ) :=
  fun x => (1 - k * Cosmology.spatialNormSq x / 4) • (Pi.single m 1 : Fin 4 → ℝ) + (k / 2 * x m) • spatialPart x

/-- The curved translation `curvTransF k m` as a vector field of the manifold `ℝ⁴`. -/
def curvTrans (k : ℝ) (m : Fin 4) : Π y : Fin 4 → ℝ, TangentSpace 𝓘(ℝ, Fin 4 → ℝ) y := curvTransF k m

/-- The derivative of a curved translation at `x`. -/
def dCurvTrans (k : ℝ) (m : Fin 4) (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  (-(k / 4) • (2 : ℝ) • sdot x).smulRight (Pi.single m 1 : Fin 4 → ℝ) +
    ((k / 2 * x m) • spatialPart +
      ((k / 2) • (ContinuousLinearMap.proj m : (Fin 4 → ℝ) →L[ℝ] ℝ)).smulRight (spatialPart x))

/-- The derivative of a curved translation. -/
theorem hasFDerivAt_curvTrans (k : ℝ) (m : Fin 4) (x : Fin 4 → ℝ) :
    HasFDerivAt (curvTransF k m) (dCurvTrans k m x) x := by
  have hf : HasFDerivAt (fun y : Fin 4 → ℝ => 1 - k * Cosmology.spatialNormSq y / 4) (-(k / 4) • (2 : ℝ) • sdot x) x := by
    have := ((hasFDerivAt_spatialNormSq x).const_mul (k / 4)).const_sub 1
    have e : (fun y : Fin 4 → ℝ => 1 - k * Cosmology.spatialNormSq y / 4) =
        (fun y => 1 - k / 4 * Cosmology.spatialNormSq y) := by funext y; ring
    rw [e]
    refine this.congr_fderiv ?_
    ext u; simp
  have hh : HasFDerivAt (fun y : Fin 4 → ℝ => k / 2 * y m) ((k / 2) • (ContinuousLinearMap.proj m : (Fin 4 → ℝ) →L[ℝ] ℝ)) x := by
    exact ((ContinuousLinearMap.proj m : (Fin 4 → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul (k / 2)
  exact (hf.smul_const (Pi.single m 1 : Fin 4 → ℝ)).add (hh.smul spatialPart.hasFDerivAt)

/-- The domain `1 + k |x|²/4 > 0` of the isotropic coordinates of curvature `k`. -/
def curvDomain (k : ℝ) : Set (Fin 4 → ℝ) := {x | 0 < 1 + k * Cosmology.spatialNormSq x / 4}

/-- The number of spatial indices among `μ, ν`. -/
def nSpatial (μ ν : Fin 4) : ℕ := (if μ = 0 then 0 else 1) + (if ν = 0 then 0 else 1)

theorem spatialNormSq_ray (t s : ℝ) (w : Fin 4 → ℝ) :
    Cosmology.spatialNormSq ((Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart w) = s ^ 2 * Cosmology.spatialNormSq w := by
  simp only [Cosmology.spatialNormSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, spatialPart_apply, Fin.succ_ne_zero,
    ite_false, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.single_apply, Fin.succ_ne_zero]; ring

/-- Along the ray `s ↦ (t, s w)` the combination `Σ wₘ Pₘ` of the curved translations is `(1 + k s²|w|²/4) w`. -/
theorem sum_curvTrans_ray (k t s : ℝ) (w : Fin 4 → ℝ) :
    ∑ m, spatialPart w m • curvTransF k m ((Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart w) =
      (1 + k * s ^ 2 * Cosmology.spatialNormSq w / 4) • spatialPart w := by
  have hq : ∑ m, spatialPart w m * spatialPart w m = Cosmology.spatialNormSq w := by
    rw [Fin.sum_univ_succ]; simp [spatialPart_apply, Cosmology.spatialNormSq, sq]
  funext μ
  simp only [curvTransF, spatialNormSq_ray, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have e : ∀ m, spatialPart w m * ((1 - k * (s ^ 2 * Cosmology.spatialNormSq w) / 4) * (Pi.single m 1 : Fin 4 → ℝ) μ +
      k / 2 * ((Pi.single 0 t : Fin 4 → ℝ) m + s * spatialPart w m) * spatialPart ((Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart w) μ) =
      (1 - k * (s ^ 2 * Cosmology.spatialNormSq w) / 4) * (spatialPart w m * (Pi.single m 1 : Fin 4 → ℝ) μ) +
      (k / 2 * s ^ 2 * spatialPart w μ) * (spatialPart w m * spatialPart w m) := by
    intro m
    have h1 : spatialPart ((Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart w) μ = s * spatialPart w μ := by
      simp only [spatialPart_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs with h <;> simp [h, Pi.single_apply]
    have h2 : spatialPart w m * (Pi.single 0 t : Fin 4 → ℝ) m = 0 := by
      by_cases hm : m = 0
      · subst hm; simp [spatialPart_apply]
      · simp [Pi.single_apply, hm]
    rw [h1]
    linear_combination (k / 2 * (s * spatialPart w μ)) * h2
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hq]
  have hs : ∑ m, spatialPart w m * (Pi.single m 1 : Fin 4 → ℝ) μ = spatialPart w μ := by
    rw [Finset.sum_eq_single μ]
    · simp
    · intro m _ hm; simp [Pi.single_apply, Ne.symm hm]
    · simp
  rw [hs]
  ring

/-- Along the ray the combination `Σ wₘ DPₘ` of the derivatives is `(k s |w|²/2)` times the spatial projection. -/
theorem sum_dCurvTrans_ray (k t s : ℝ) (w u : Fin 4 → ℝ) :
    ∑ m, spatialPart w m • dCurvTrans k m ((Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart w) u =
      (k * s * Cosmology.spatialNormSq w / 2) • spatialPart u := by
  have hq : ∑ m, spatialPart w m * spatialPart w m = Cosmology.spatialNormSq w := by
    rw [Fin.sum_univ_succ]; simp [spatialPart_apply, Cosmology.spatialNormSq, sq]
  have hsd : sdot ((Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart w) u = s * ∑ m, spatialPart w m * u m := by
    rw [sdot_apply, Fin.sum_univ_succ (f := fun m => spatialPart w m * u m)]
    simp only [spatialPart_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.succ_ne_zero, ite_false, ite_true,
      zero_mul, zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Pi.single_apply, Fin.succ_ne_zero]; ring
  have hsp : spatialPart ((Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart w) = s • spatialPart w := by
    funext μ; simp only [spatialPart_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs with h <;> simp [h, Pi.single_apply]
  have hxm : ∀ m, spatialPart w m * ((Pi.single 0 t : Fin 4 → ℝ) m + s * spatialPart w m) =
      s * (spatialPart w m * spatialPart w m) := by
    intro m
    by_cases hm : m = 0
    · subst hm; simp [spatialPart_apply]
    · simp [Pi.single_apply, hm]; ring
  funext μ
  simp only [dCurvTrans, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply, Finset.sum_apply,
    Pi.add_apply, hsd, hsp]
  have e : ∀ m, spatialPart w m * (-(k / 4) * (2 * (s * ∑ m', spatialPart w m' * u m')) * (Pi.single m 1 : Fin 4 → ℝ) μ +
      (k / 2 * ((Pi.single 0 t : Fin 4 → ℝ) m + s * spatialPart w m) * spatialPart u μ +
        k / 2 * u m * (s * spatialPart w μ))) =
      -(k / 2) * s * (∑ m', spatialPart w m' * u m') * (spatialPart w m * (Pi.single m 1 : Fin 4 → ℝ) μ) +
        (k / 2) * spatialPart u μ * (spatialPart w m * ((Pi.single 0 t : Fin 4 → ℝ) m + s * spatialPart w m)) +
        (k / 2) * s * spatialPart w μ * (spatialPart w m * u m) := by
    intro m; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hxm, hq]
  have hs : ∑ m, spatialPart w m * (Pi.single m 1 : Fin 4 → ℝ) μ = spatialPart w μ := by
    rw [Finset.sum_eq_single μ]
    · simp
    · intro m _ hm; simp [Pi.single_apply, Ne.symm hm]
    · simp
  rw [hs]
  ring

/-- The metric at `y` as a plain bilinear form of `ℝ⁴`. -/
def gform (g : NondegMetric 𝓘(ℝ, Fin 4 → ℝ) (Fin 4 → ℝ)) (y : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ := g.g y

theorem gform_symm (g : NondegMetric 𝓘(ℝ, Fin 4 → ℝ) (Fin 4 → ℝ)) (y v w : Fin 4 → ℝ) : gform g y v w = gform g y w v :=
  g.symm y v w

theorem spatialNormSq_spatialPart (x : Fin 4 → ℝ) : Cosmology.spatialNormSq (spatialPart x) = Cosmology.spatialNormSq x := by
  simp [Cosmology.spatialNormSq, spatialPart_apply, Fin.succ_ne_zero]

theorem single_add_spatialPart (x : Fin 4 → ℝ) : (Pi.single 0 (x 0) : Fin 4 → ℝ) + spatialPart x = x := by
  funext μ; by_cases h : μ = 0
  · subst h; simp [spatialPart_apply]
  · simp [spatialPart_apply, h, Pi.single_apply]

/-- The ray relation: on `D_k`, `g_{μν}(t, x) (1 + k|x|²/4)^c = g_{μν}(t, 0)`, `c` the number of spatial indices, when the curved
translations are Killing. -/
theorem ray_relation (k : ℝ) (g : NondegMetric 𝓘(ℝ, Fin 4 → ℝ) (Fin 4 → ℝ))
    (hdiff : ∀ μ ν, Differentiable ℝ (metricComp g μ ν))
    (htrans : ∀ m : Fin 4, m ≠ 0 → ∀ x ∈ curvDomain k, ∀ μ ν,
      lieDerivMetric g (curvTrans k m) (basisField 4 μ) (basisField 4 ν) x = 0)
    {x : Fin 4 → ℝ} (hx : x ∈ curvDomain k) (μ ν : Fin 4) :
    metricComp g μ ν x * (1 + k * Cosmology.spatialNormSq x / 4) ^ nSpatial μ ν =
      metricComp g μ ν (Pi.single 0 (x 0)) := by
  set q := Cosmology.spatialNormSq x with hq
  set t := x 0
  set σ : ℝ → Fin 4 → ℝ := fun s => (Pi.single 0 t : Fin 4 → ℝ) + s • spatialPart x with hσ
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hx' : 0 < 1 + k * q / 4 := hx
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < 1 + k * s ^ 2 * q / 4 := by
    intro s hs
    have hs2 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
    have hs0 : 0 ≤ s ^ 2 := sq_nonneg s
    rcases le_or_gt 0 k with hk | hk
    · have : 0 ≤ k * s ^ 2 * q := by positivity
      linarith
    · have h3 : 0 ≤ q * (1 - s ^ 2) := mul_nonneg hq0 (by linarith)
      have : k * (q * (1 - s ^ 2)) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk.le h3
      nlinarith
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, σ s ∈ curvDomain k := by
    intro s hs
    show 0 < 1 + k * Cosmology.spatialNormSq (σ s) / 4
    rw [hσ, spatialNormSq_ray]
    have := hpos s hs
    calc (0 : ℝ) < 1 + k * s ^ 2 * q / 4 := this
      _ = 1 + k * (s ^ 2 * q) / 4 := by ring
  -- the Killing equations of the curved translations in coordinates
  have hK : ∀ m : Fin 4, m ≠ 0 → ∀ y ∈ curvDomain k,
      fderiv ℝ (metricComp g μ ν) y (curvTransF k m y) + gform g y (dCurvTrans k m y (Pi.single μ 1)) (Pi.single ν 1) +
        gform g y (Pi.single μ 1) (dCurvTrans k m y (Pi.single ν 1)) = 0 := by
    intro m hm y hy
    have h := htrans m hm y hy μ ν
    rw [lieDerivMetric_basis] at h
    have hd : fderiv ℝ (curvTrans k m : (Fin 4 → ℝ) → (Fin 4 → ℝ)) y = dCurvTrans k m y :=
      (hasFDerivAt_curvTrans k m y).fderiv
    rw [hd] at h
    exact h
  -- the combined equation along the ray
  set F : ℝ → ℝ := fun s => metricComp g μ ν (σ s) with hF
  set F' : ℝ → ℝ := fun s => fderiv ℝ (metricComp g μ ν) (σ s) (spatialPart x) with hF'
  have hFd : ∀ s, HasDerivAt F (F' s) s := by
    intro s
    have h1 : HasDerivAt σ (spatialPart x) s := by
      have := ((hasDerivAt_id s).smul_const (spatialPart x)).const_add (Pi.single 0 t : Fin 4 → ℝ)
      rw [one_smul] at this
      exact this
    exact (hdiff μ ν (σ s)).hasFDerivAt.comp_hasDerivAt s h1
  have hsp : ∀ (y : Fin 4 → ℝ) (μ' ν' : Fin 4), gform g y (spatialPart (Pi.single μ' 1)) (Pi.single ν' 1) =
      (if μ' = 0 then 0 else 1) * metricComp g μ' ν' y := by
    intro y μ' ν'
    have : spatialPart (Pi.single μ' 1 : Fin 4 → ℝ) = (if μ' = 0 then (0 : ℝ) else 1) • (Pi.single μ' 1 : Fin 4 → ℝ) := by
      funext ρ; simp only [spatialPart_apply, Pi.smul_apply, smul_eq_mul]
      by_cases h : μ' = 0
      · subst h; by_cases hρ : ρ = 0 <;> simp [hρ, Pi.single_apply]
      · by_cases hρ : ρ = 0
        · subst hρ; simp [Pi.single_apply, Ne.symm h]
        · simp [h, hρ]
    rw [this, map_smul, smul_apply, smul_eq_mul]
    rfl
  have hEq : ∀ s ∈ Icc (0 : ℝ) 1, (1 + k * s ^ 2 * q / 4) * F' s +
      (k * s * q / 2) * (nSpatial μ ν : ℝ) * F s = 0 := by
    intro s hs
    have hy := hmem s hs
    have hsum : ∑ m, spatialPart x m * (fderiv ℝ (metricComp g μ ν) (σ s) (curvTransF k m (σ s)) +
        gform g (σ s) (dCurvTrans k m (σ s) (Pi.single μ 1)) (Pi.single ν 1) +
        gform g (σ s) (Pi.single μ 1) (dCurvTrans k m (σ s) (Pi.single ν 1))) = 0 := by
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hm : m = 0
      · subst hm; simp [spatialPart_apply]
      · rw [hK m hm (σ s) hy, mul_zero]
    simp only [mul_add, Finset.sum_add_distrib] at hsum
    have e1 : ∑ m, spatialPart x m * fderiv ℝ (metricComp g μ ν) (σ s) (curvTransF k m (σ s)) =
        (1 + k * s ^ 2 * q / 4) * F' s := by
      have := congrArg (fderiv ℝ (metricComp g μ ν) (σ s)) (sum_curvTrans_ray k t s x)
      simp only [map_sum, map_smul, smul_eq_mul] at this
      rw [this]
    have e2 : ∑ m, spatialPart x m * gform g (σ s) (dCurvTrans k m (σ s) (Pi.single μ 1)) (Pi.single ν 1) =
        (k * s * q / 2) * ((if μ = 0 then 0 else 1) * F s) := by
      have := congrArg (fun v => gform g (σ s) v (Pi.single ν 1)) (sum_dCurvTrans_ray k t s x (Pi.single μ 1))
      simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul] at this
      rw [this, hsp]
    have e3 : ∑ m, spatialPart x m * gform g (σ s) (Pi.single μ 1) (dCurvTrans k m (σ s) (Pi.single ν 1)) =
        (k * s * q / 2) * ((if ν = 0 then 0 else 1) * F s) := by
      have := congrArg (fun v => gform g (σ s) (Pi.single μ 1) v) (sum_dCurvTrans_ray k t s x (Pi.single ν 1))
      simp only [map_sum, map_smul, smul_eq_mul] at this
      rw [this, gform_symm, hsp, (show metricComp g ν μ (σ s) = metricComp g μ ν (σ s) from g.symm _ _ _)]
    rw [e1, e2, e3] at hsum
    unfold nSpatial
    push_cast
    linear_combination hsum
  -- the integrating factor
  set n := nSpatial μ ν with hn
  set X : ℝ → ℝ := fun s => 1 + k * s ^ 2 * q / 4 with hX
  have hXd : ∀ s, HasDerivAt X (k * s * q / 2) s := by
    intro s
    have h := ((hasDerivAt_pow 2 s).const_mul (k * q / 4)).const_add 1
    have e1 : (fun r : ℝ => 1 + k * q / 4 * r ^ 2) = X := by funext r; simp only [hX]; ring
    rw [e1] at h
    convert h using 1
    norm_num; ring
  set G : ℝ → ℝ := fun s => F s * X s ^ n with hG
  have hGd : ∀ s, HasDerivAt G (F' s * X s ^ n + F s * ((n : ℝ) * X s ^ (n - 1) * (k * s * q / 2))) s := by
    intro s
    exact (hFd s).mul ((hXd s).pow n)
  have hG0 : ∀ s ∈ Icc (0 : ℝ) 1, F' s * X s ^ n + F s * ((n : ℝ) * X s ^ (n - 1) * (k * s * q / 2)) = 0 := by
    intro s hs
    have hX0 := hpos s hs
    have heq := hEq s hs
    have key : X s * (F' s * X s ^ n + F s * ((n : ℝ) * X s ^ (n - 1) * (k * s * q / 2))) =
        X s ^ n * ((1 + k * s ^ 2 * q / 4) * F' s + (k * s * q / 2) * (n : ℝ) * F s) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos'
      · rw [h0]; simp [hX]
      · have : X s * X s ^ (n - 1) = X s ^ n := by
          rw [← pow_succ']; congr 1; omega
        simp only [hX] at this ⊢
        linear_combination (F s * (n : ℝ) * (k * s * q / 2)) * this
    rw [heq, mul_zero] at key
    exact (mul_eq_zero.1 key).resolve_left hX0.ne'
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope G
    (fun s => F' s * X s ^ n + F s * ((n : ℝ) * X s ^ (n - 1) * (k * s * q / 2))) zero_lt_one
    (fun s _ => (hGd s).continuousAt.continuousWithinAt) (fun s _ => hGd s)
  rw [hG0 c (Ioo_subset_Icc_self hc)] at hc'
  have hG10 : G 1 = G 0 := by linarith [show G 1 - G 0 = 0 by simpa using hc'.symm]
  simp only [hG, hF, hX, hσ] at hG10
  rw [one_smul, single_add_spatialPart, zero_smul, add_zero] at hG10
  simpa using hG10

/-- **Homogeneity and isotropy give the FLRW form for every curvature `k`** (G1-024): a smooth metric of any signature on `ℝ⁴`
for which the three spatial rotations and the three curved translations `Pₘ` are Killing fields on `D_k` (`lieDerivMetric g X = 0`
on the coordinate basis fields) has, at every point of `D_k`, `g_{00} = b(t)`, `g_{0k} = 0` and
`g_{ij} = a(t) δ_{ij}/(1 + k|x|²/4)²`: the FLRW metric `b(t) dt² + a(t) δ/(1 + k|x|²/4)²` with the maximally symmetric slices of
curvature `k` in isotropic coordinates. -/
theorem curved_flrw_of_killing (k : ℝ) (g : NondegMetric 𝓘(ℝ, Fin 4 → ℝ) (Fin 4 → ℝ))
    (hdiff : ∀ μ ν, Differentiable ℝ (metricComp g μ ν))
    (htrans : ∀ m : Fin 4, m ≠ 0 → ∀ x ∈ curvDomain k, ∀ μ ν,
      lieDerivMetric g (curvTrans k m) (basisField 4 μ) (basisField 4 ν) x = 0)
    (hrot : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ x ∈ curvDomain k, ∀ μ ν,
      lieDerivMetric g (affField (rotCLM i j) 0) (basisField 4 μ) (basisField 4 ν) x = 0) :
    ∃ b a : ℝ → ℝ, ∀ x ∈ curvDomain k, metricComp g 0 0 x = b (x 0) ∧
      (∀ j : Fin 4, j ≠ 0 → metricComp g 0 j x = 0) ∧
      (∀ i j : Fin 4, i ≠ 0 → j ≠ 0 →
        metricComp g i j x = (if i = j then a (x 0) else 0) / (1 + k * Cosmology.spatialNormSq x / 4) ^ 2) := by
  have hsymm : ∀ μ ν x, metricComp g μ ν x = metricComp g ν μ x := fun μ ν x => g.symm x _ _
  have horigin : ∀ t : ℝ, (Pi.single 0 t : Fin 4 → ℝ) ∈ curvDomain k := by
    intro t
    show 0 < 1 + k * Cosmology.spatialNormSq (Pi.single 0 t) / 4
    simp [Cosmology.spatialNormSq, Pi.single_apply, Fin.succ_ne_zero]
  -- the rotation relations at the point `(t, 0, 0, 0)`
  have hR : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t μ ν,
      ((if i = μ then metricComp g j ν (Pi.single 0 t) else 0) - (if j = μ then metricComp g i ν (Pi.single 0 t) else 0)) +
      ((if i = ν then metricComp g μ j (Pi.single 0 t) else 0) - (if j = ν then metricComp g μ i (Pi.single 0 t) else 0)) = 0 := by
    intro i j hi hj hij t μ ν
    have h := hrot i j hi hj hij (Pi.single 0 t) (horigin t) μ ν
    rw [lieDerivMetric_affField_basis] at h
    have hz : rotCLM i j ((Pi.single 0 t : Fin 4 → ℝ)) = 0 := by
      rw [rotCLM_apply]; simp [Pi.single_apply, hi.symm, hj.symm]
    simp only [hz, zero_add, g_zero_left, g_zero_right, map_zero, zero_apply] at h
    rw [rotCLM_apply, rotCLM_apply] at h
    simp only [g_sub_left, g_sub_right, g_smul_left, g_smul_right, Pi.single_apply] at h
    unfold metricComp
    split_ifs at h ⊢ <;> linarith
  have hdiag : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t,
      metricComp g j j (Pi.single 0 t) = metricComp g i i (Pi.single 0 t) := by
    intro i j hi hj hij t
    have := hR i j hi hj hij t i j
    simp [hij, Ne.symm hij] at this
    linarith
  have hoff : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t, metricComp g i j (Pi.single 0 t) = 0 := by
    intro i j hi hj hij t
    have := hR i j hi hj hij t i i
    simp [Ne.symm hij] at this
    have := hsymm j i (Pi.single 0 t)
    linarith
  have h0 : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ t, metricComp g 0 j (Pi.single 0 t) = 0 := by
    intro i j hi hj hij t
    have := hR i j hi hj hij t 0 i
    simp [hi, hj, hij, Ne.symm hij] at this
    exact this
  have h0j : ∀ j : Fin 4, j ≠ 0 → ∀ t, metricComp g 0 j (Pi.single 0 t) = 0 := by
    intro j hj t
    fin_cases j
    · exact absurd rfl hj
    · exact h0 2 1 (by decide) (by decide) (by decide) _
    · exact h0 1 2 (by decide) (by decide) (by decide) _
    · exact h0 1 3 (by decide) (by decide) (by decide) _
  have hij0 : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 → ∀ t,
      metricComp g i j (Pi.single 0 t) = if i = j then metricComp g 1 1 (Pi.single 0 t) else 0 := by
    intro i j hi hj t
    fin_cases i <;> fin_cases j <;> simp at hi hj ⊢
    · exact hoff 1 2 (by decide) (by decide) (by decide) _
    · exact hoff 1 3 (by decide) (by decide) (by decide) _
    · exact hoff 2 1 (by decide) (by decide) (by decide) _
    · exact (hdiag 1 2 (by decide) (by decide) (by decide) _)
    · exact hoff 2 3 (by decide) (by decide) (by decide) _
    · exact hoff 3 1 (by decide) (by decide) (by decide) _
    · exact hoff 3 2 (by decide) (by decide) (by decide) _
    · exact (hdiag 1 3 (by decide) (by decide) (by decide) _)
  refine ⟨fun t => metricComp g 0 0 (Pi.single 0 t), fun t => metricComp g 1 1 (Pi.single 0 t), fun x hx => ?_⟩
  have hX : 0 < 1 + k * Cosmology.spatialNormSq x / 4 := hx
  refine ⟨?_, fun j hj => ?_, fun i j hi hj => ?_⟩
  · have := ray_relation k g hdiff htrans hx 0 0
    simpa [nSpatial] using this
  · have := ray_relation k g hdiff htrans hx 0 j
    rw [h0j j hj, show nSpatial 0 j = 1 by simp [nSpatial, hj]] at this
    simpa [hX.ne'] using this
  · have := ray_relation k g hdiff htrans hx i j
    rw [hij0 i j hi hj, show nSpatial i j = 2 by simp [nSpatial, hi, hj]] at this
    rw [eq_div_iff (pow_ne_zero 2 hX.ne'), this]

end Lightlike
