import Lightlike.Spacetime.Curvature
import Mathlib

/-!
# Riemannian metrics in a chart: lengths, energies and the distance

The first step of RC6a (geodesics and the distance expansion, the prerequisite of the
Cheeger–Müller–Schrader convergence theorem). A Riemannian metric on an open set `U ⊆ ℝⁿ` is a
coordinate metric of the core (`Lightlike.IsCoordMetric`: smooth, symmetric, invertible) that is positive
definite. The length and the energy of a curve are the integrals of `√(g(c', c'))` and
`g(c', c')`, and the distance of `(U, g)` is the infimum of the lengths of `C¹` curves in `U`.

## Main results

* `IsRiemMetric g U`: `g` is a Riemannian metric on `U`.
* `normSq g x v = g_x(v, v)`; `eNormSq v = v ⬝ v`, the Euclidean squared norm.
* `length g c a b`, `energy g c a b`: length and energy of a curve on `[a, b]`.
* `IsAdmissible U c x y`: `c` is a `C¹` curve with `c 0 = x`, `c 1 = y` and `c [0, 1] ⊆ U`.
* `dist g U x y`: the infimum of the lengths of admissible curves.

* `exists_bounds_of_isCompact`: on a compact subset of `U` the metric is comparable to the
  Euclidean one, `λ |v|² ≤ g_x(v, v) ≤ Λ |v|²`.
* `length_sq_le_energy`: `L² ≤ (b - a) E` (Cauchy–Schwarz).
* `sqrt_eNormSq_sub_le_integral`: the Euclidean length of a `C¹` curve bounds the Euclidean
  distance of its endpoints; `length_ge_of_bounds`: a lower bound on the metric gives
  `L ≥ √λ |y - x|`.
* `dist_le_length`, `dist_nonneg`, `dist_ge_of_bounds`.
* `dist_euclid`: for the Euclidean metric on a convex set the distance is the Euclidean
  distance (trust check).

## Implementation notes

Mathlib defines the Riemannian distance of a manifold with a Riemannian bundle,
`riemannianEDist` (`Mathlib/Geometry/Manifold/Riemannian/PathELength.lean`), as an infimum over
piecewise `C¹` paths. The chart version here is the one the distance expansion needs (explicit
matrices, curves `[0, 1] → U`); `IsRiemMetric.riemannianEDist_eq`
(`Lightlike/Regge/Geodesic/Riemannian.lean`) proves that the two distances agree whenever an
admissible curve joins the two points.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Graduate Texts in Mathematics 176
  (Springer, 2018), Chapter 2 (lengths of curves and the Riemannian distance).
* M. P. do Carmo, *Riemannian Geometry* (Birkhäuser, 1992), Chapter 9 (the energy of a curve and
  the inequality `L² ≤ (b - a) E`).
-/

open Matrix Real MeasureTheory Set

namespace Lightlike.Geodesic

variable {n : ℕ}

/-! ## Riemannian metrics -/

/-- `g` is a **Riemannian metric** on `U`: a coordinate metric of the core (smooth, symmetric,
invertible on the open set `U`) that is positive definite at every point of `U`. -/
structure IsRiemMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) :
    Prop where
  /-- Smooth, symmetric and invertible on the open set `U`. -/
  coord : Lightlike.IsCoordMetric g U
  /-- Positive definite on `U`. -/
  posDef : ∀ x ∈ U, (g x).PosDef

/-- The squared length `g_x(v, v)` of the vector `v` at the point `x`. -/
def normSq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x v : Fin n → ℝ) : ℝ := v ⬝ᵥ (g x *ᵥ v)

/-- The Euclidean squared norm `v ⬝ v`. -/
def eNormSq (v : Fin n → ℝ) : ℝ := v ⬝ᵥ v

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

theorem eNormSq_nonneg (v : Fin n → ℝ) : 0 ≤ eNormSq v := by
  unfold eNormSq dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem eNormSq_eq_zero {v : Fin n → ℝ} : eNormSq v = 0 ↔ v = 0 := by
  unfold eNormSq
  exact dotProduct_self_eq_zero

/-- A Riemannian metric gives positive squared lengths to nonzero vectors. -/
theorem IsRiemMetric.normSq_pos (hg : IsRiemMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < normSq g x v := by
  have := (hg.posDef x hx).dotProduct_mulVec_pos hv
  simpa [normSq] using this

/-- A Riemannian metric gives nonnegative squared lengths. -/
theorem IsRiemMetric.normSq_nonneg (hg : IsRiemMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (v : Fin n → ℝ) : 0 ≤ normSq g x v := by
  by_cases hv : v = 0
  · simp [normSq, hv]
  · exact (hg.normSq_pos hx hv).le

/-- Squared lengths are quadratic. -/
theorem normSq_smul (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (c : ℝ)
    (v : Fin n → ℝ) : normSq g x (c • v) = c ^ 2 * normSq g x v := by
  simp only [normSq, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- The Euclidean squared norm is quadratic. -/
theorem eNormSq_smul (c : ℝ) (v : Fin n → ℝ) : eNormSq (c • v) = c ^ 2 * eNormSq v := by
  simp only [eNormSq, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- The metric components are continuous on `U`. -/
theorem IsRiemMetric.continuousOn (hg : IsRiemMetric g U) (i j : Fin n) :
    ContinuousOn (fun y => g y i j) U :=
  (hg.coord.smooth i j).continuousOn

/-- `(x, v) ↦ g_x(v, v)` is continuous on `U × ℝⁿ`. -/
theorem IsRiemMetric.continuousOn_normSq (hg : IsRiemMetric g U) :
    ContinuousOn (fun p : (Fin n → ℝ) × (Fin n → ℝ) => normSq g p.1 p.2) (U ×ˢ univ) := by
  have hc : ∀ i j, ContinuousOn (fun p : (Fin n → ℝ) × (Fin n → ℝ) => g p.1 i j) (U ×ˢ univ) :=
    fun i j => (hg.continuousOn i j).comp continuousOn_fst fun p hp => hp.1
  simp only [normSq, dotProduct, mulVec]
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine (continuous_apply i |>.comp continuous_snd).continuousOn.mul ?_
  refine continuousOn_finsetSum _ fun j _ => ?_
  exact (hc i j).mul (continuous_apply j |>.comp continuous_snd).continuousOn

/-- **Comparison with the Euclidean metric.** On a compact subset `K` of `U` there are
`0 < λ ≤ Λ` with `λ |v|² ≤ g_x(v, v) ≤ Λ |v|²` for all `x ∈ K` and all `v`. -/
theorem IsRiemMetric.exists_bounds_of_isCompact (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ l L : ℝ, 0 < l ∧ 0 < L ∧ ∀ x ∈ K, ∀ v, l * eNormSq v ≤ normSq g x v ∧
      normSq g x v ≤ L * eNormSq v := by
  -- the Euclidean unit sphere is compact
  set S : Set (Fin n → ℝ) := {v | eNormSq v = 1}
  have hS : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq (by unfold eNormSq; fun_prop) continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun v hv => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : v i * v i ≤ eNormSq v := by
        unfold eNormSq dotProduct
        exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
          (Finset.mem_univ i)
      rw [hv] at h1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith
  have hKS : IsCompact (K ×ˢ S) := hK.prod hS
  have hcont := hg.continuousOn_normSq.mono (prod_mono hKU (subset_univ S))
  -- the scaling identity
  have scale : ∀ x v, v ≠ 0 → normSq g x v =
      eNormSq v * normSq g x ((√(eNormSq v))⁻¹ • v) := by
    intro x v hv
    have hp : 0 < eNormSq v := lt_of_le_of_ne (eNormSq_nonneg v)
      (fun h => hv (eNormSq_eq_zero.mp h.symm))
    rw [normSq_smul, inv_pow, Real.sq_sqrt hp.le]
    field_simp
  have unit : ∀ v, v ≠ 0 → (√(eNormSq v))⁻¹ • v ∈ S := by
    intro v hv
    have hp : 0 < eNormSq v := lt_of_le_of_ne (eNormSq_nonneg v)
      (fun h => hv (eNormSq_eq_zero.mp h.symm))
    show eNormSq _ = 1
    rw [eNormSq_smul, inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  rcases (K ×ˢ S).eq_empty_or_nonempty with he | hne
  · -- no unit vectors at points of `K`: then `K` is empty or `n = 0`
    refine ⟨1, 1, one_pos, one_pos, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv, normSq, eNormSq]
    · exact absurd (he ▸ mk_mem_prod hx (unit v hv)) (notMem_empty _)
  · obtain ⟨p₀, hp₀, hmin⟩ := hKS.exists_isMinOn hne hcont
    obtain ⟨p₁, hp₁, hmax⟩ := hKS.exists_isMaxOn hne hcont
    have hS0 : ∀ v ∈ S, v ≠ 0 := fun v hv h => by
      have : eNormSq v = 1 := hv
      rw [h] at this
      simp [eNormSq] at this
    have l0 : 0 < normSq g p₀.1 p₀.2 := hg.normSq_pos (hKU hp₀.1) (hS0 _ hp₀.2)
    have L0 : 0 < normSq g p₁.1 p₁.2 := lt_of_lt_of_le l0 (isMinOn_iff.mp hmin p₁ hp₁)
    refine ⟨normSq g p₀.1 p₀.2, normSq g p₁.1 p₁.2, l0, L0, fun x hx v => ?_⟩
    by_cases hv : v = 0
    · simp [hv, normSq, eNormSq]
    · rw [scale x v hv]
      have hm := isMinOn_iff.mp hmin (x, _) (mk_mem_prod hx (unit v hv))
      have hM := isMaxOn_iff.mp hmax (x, _) (mk_mem_prod hx (unit v hv))
      have hp := eNormSq_nonneg v
      constructor
      · rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hm hp
      · rw [mul_comm (normSq g p₁.1 p₁.2)]
        exact mul_le_mul_of_nonneg_left hM hp

/-! ## Lengths and energies of curves -/

/-- The **length** `∫_a^b √(g(c', c'))` of the curve `c` on `[a, b]`. -/
noncomputable def length (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c : ℝ → Fin n → ℝ)
    (a b : ℝ) : ℝ :=
  ∫ t in a..b, √(normSq g (c t) (deriv c t))

/-- The **energy** `∫_a^b g(c', c')` of the curve `c` on `[a, b]`. -/
noncomputable def energy (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (c : ℝ → Fin n → ℝ)
    (a b : ℝ) : ℝ :=
  ∫ t in a..b, normSq g (c t) (deriv c t)

/-- **Cauchy–Schwarz for an interval integral**: `(∫ f)² ≤ (b - a) ∫ f²`. -/
theorem sq_integral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  set c := (∫ t in a..b, f t) / (b - a)
  have hba : 0 < b - a := sub_pos.mpr hlt
  have hnn : 0 ≤ ∫ t in a..b, (f t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have hexp : ∫ t in a..b, (f t - c) ^ 2 =
      (∫ t in a..b, f t ^ 2) - 2 * c * (∫ t in a..b, f t) + c ^ 2 * (b - a) := by
    have h1 : (fun t => (f t - c) ^ 2) = fun t => (f t ^ 2 - 2 * c * f t) + c ^ 2 := by
      funext t; ring
    rw [h1, intervalIntegral.integral_add (hf2.sub (hf.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf2 (hf.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hexp] at hnn
  have : (∫ t in a..b, f t) = c * (b - a) := by
    simp only [c]
    field_simp
  rw [this] at hnn ⊢
  nlinarith

/-- **Length and energy**: `L² ≤ (b - a) E` for a curve with integrable speed. -/
theorem length_sq_le_energy (hg : IsRiemMetric g U) {c : ℝ → Fin n → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ t ∈ Icc a b, c t ∈ U)
    (h1 : IntervalIntegrable (fun t => √(normSq g (c t) (deriv c t))) volume a b)
    (h2 : IntervalIntegrable (fun t => normSq g (c t) (deriv c t)) volume a b) :
    length g c a b ^ 2 ≤ (b - a) * energy g c a b := by
  have hsq : ∀ t ∈ Icc a b, √(normSq g (c t) (deriv c t)) ^ 2 = normSq g (c t) (deriv c t) :=
    fun t ht => Real.sq_sqrt (hg.normSq_nonneg (hmem t ht) _)
  have h2' : IntervalIntegrable (fun t => √(normSq g (c t) (deriv c t)) ^ 2) volume a b :=
    h2.congr fun t ht => (hsq t (Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at ht))).symm
  have := sq_integral_le hab h1 h2'
  rw [length, energy, ← intervalIntegral.integral_congr (fun t ht => hsq t
    (by rwa [uIcc_of_le hab] at ht))]
  exact this

/-! ## Euclidean lower bounds -/

/-- **The Euclidean length bounds the displacement.** For a `C¹` curve `c`,
`|c b - c a| ≤ ∫_a^b |c'|` (Euclidean norms). -/
theorem sqrt_eNormSq_sub_le_integral {c : ℝ → Fin n → ℝ} (hc : ContDiff ℝ 1 c) {a b : ℝ}
    (hab : a ≤ b) :
    √(eNormSq (c b - c a)) ≤ ∫ t in a..b, √(eNormSq (deriv c t)) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have hnorm : ∀ v : Fin n → ℝ, ‖e.symm v‖ = √(eNormSq v) := by
    intro v
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [eNormSq, dotProduct, sq, e]
  have hd : ∀ t, HasDerivAt (fun s => e.symm (c s)) (e.symm (deriv c t)) t := fun t =>
    e.symm.hasFDerivAt.comp_hasDerivAt t ((hc.differentiable one_ne_zero) t).hasDerivAt
  have hcont : Continuous fun t => e.symm (deriv c t) :=
    e.symm.continuous.comp (hc.continuous_deriv le_rfl)
  have hftc : ∫ t in a..b, e.symm (deriv c t) = e.symm (c b) - e.symm (c a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      (hcont.intervalIntegrable a b)
  calc √(eNormSq (c b - c a)) = ‖e.symm (c b) - e.symm (c a)‖ := by
        rw [← map_sub, hnorm]
    _ = ‖∫ t in a..b, e.symm (deriv c t)‖ := by rw [hftc]
    _ ≤ ∫ t in a..b, ‖e.symm (deriv c t)‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, √(eNormSq (deriv c t)) := by simp only [hnorm]

/-- **A lower bound on the metric bounds the length from below**: if `g ≥ λ |·|²` along a `C¹`
curve, its length is at least `√λ |c b - c a|`. -/
theorem length_ge_of_bounds {c : ℝ → Fin n → ℝ} (hc : ContDiff ℝ 1 c)
    {a b : ℝ} (hab : a ≤ b) {l : ℝ} (hl : 0 ≤ l)
    (hbd : ∀ t ∈ Icc a b, ∀ v, l * eNormSq v ≤ normSq g (c t) v)
    (hint : IntervalIntegrable (fun t => √(normSq g (c t) (deriv c t))) volume a b) :
    √l * √(eNormSq (c b - c a)) ≤ length g c a b := by
  have hE : Continuous fun t => √(eNormSq (deriv c t)) := by
    unfold eNormSq
    exact (by fun_prop : Continuous fun v : Fin n → ℝ => √(v ⬝ᵥ v)).comp
      (hc.continuous_deriv le_rfl)
  calc √l * √(eNormSq (c b - c a)) ≤ √l * ∫ t in a..b, √(eNormSq (deriv c t)) :=
        mul_le_mul_of_nonneg_left (sqrt_eNormSq_sub_le_integral hc hab) (Real.sqrt_nonneg l)
    _ = ∫ t in a..b, √l * √(eNormSq (deriv c t)) := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ length g c a b := by
        refine intervalIntegral.integral_mono_on hab ((hE.intervalIntegrable a b).const_mul _)
          hint fun t ht => ?_
        rw [← Real.sqrt_mul hl]
        exact Real.sqrt_le_sqrt (hbd t ht _)

/-! ## The distance -/

/-- `c` is an **admissible curve** from `x` to `y` in `U`: `C¹`, with `c 0 = x`, `c 1 = y`, and
`c t ∈ U` for `t ∈ [0, 1]`. -/
structure IsAdmissible (U : Set (Fin n → ℝ)) (c : ℝ → Fin n → ℝ) (x y : Fin n → ℝ) : Prop where
  /-- `C¹`. -/
  smooth : ContDiff ℝ 1 c
  /-- Stays in `U` on `[0, 1]`. -/
  mem : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ U
  /-- Starts at `x`. -/
  start : c 0 = x
  /-- Ends at `y`. -/
  finish : c 1 = y

/-- The **distance** of `(U, g)`: the infimum of the lengths of admissible curves from `x` to
`y` (`0` if there is none). -/
noncomputable def dist (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (x y : Fin n → ℝ) : ℝ :=
  sInf {L | ∃ c, IsAdmissible U c x y ∧ length g c 0 1 = L}

/-- Lengths of curves in `U` are nonnegative. -/
theorem length_nonneg {c : ℝ → Fin n → ℝ} {a b : ℝ} (hab : a ≤ b) :
    0 ≤ length g c a b :=
  intervalIntegral.integral_nonneg hab fun _ _ => Real.sqrt_nonneg _

/-- The distance is at most the length of any admissible curve. -/
theorem dist_le_length {c : ℝ → Fin n → ℝ} {x y : Fin n → ℝ} (hc : IsAdmissible U c x y) :
    dist g U x y ≤ length g c 0 1 :=
  csInf_le ⟨0, fun _ ⟨_, _, hL⟩ => hL ▸ length_nonneg zero_le_one⟩ ⟨c, hc, rfl⟩

/-- The distance is nonnegative. -/
theorem dist_nonneg {x y : Fin n → ℝ} : 0 ≤ dist g U x y := by
  by_cases h : {L | ∃ c, IsAdmissible U c x y ∧ length g c 0 1 = L}.Nonempty
  · exact le_csInf h fun _ ⟨_, _, hL⟩ => hL ▸ length_nonneg zero_le_one
  · rw [dist, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- The speed of a `C¹` curve in `U` is integrable on `[0, 1]`. -/
theorem IsRiemMetric.intervalIntegrable_speed (hg : IsRiemMetric g U) {c : ℝ → Fin n → ℝ}
    {x y : Fin n → ℝ} (hc : IsAdmissible U c x y) :
    IntervalIntegrable (fun t => √(normSq g (c t) (deriv c t))) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le zero_le_one]
  have h := hg.continuousOn_normSq.comp (s := Icc (0 : ℝ) 1)
    ((hc.smooth.continuous.prodMk (hc.smooth.continuous_deriv le_rfl)).continuousOn)
    (fun t ht => mk_mem_prod (hc.mem t ht) (mem_univ _))
  exact h.sqrt

/-- **A lower bound on the metric bounds the distance from below**, for curves that stay in a set
where `g ≥ λ |·|²`: if every admissible curve from `x` to `y` stays in `K`, then
`dist ≥ √λ |y - x|`. -/
theorem IsRiemMetric.dist_ge_of_bounds (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)} {l : ℝ}
    (hl : 0 ≤ l) (hbd : ∀ z ∈ K, ∀ v, l * eNormSq v ≤ normSq g z v) {x y : Fin n → ℝ}
    (hne : ∃ c, IsAdmissible U c x y)
    (hK : ∀ c, IsAdmissible U c x y → ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ K) :
    √l * √(eNormSq (y - x)) ≤ dist g U x y := by
  obtain ⟨c₀, hc₀⟩ := hne
  refine le_csInf ⟨_, c₀, hc₀, rfl⟩ fun L ⟨c, hc, hL⟩ => ?_
  rw [← hL, ← hc.start, ← hc.finish]
  exact length_ge_of_bounds hc.smooth zero_le_one hl
    (fun t ht v => hbd _ (hK c hc t ht) v) (hg.intervalIntegrable_speed hc)

/-! ## Trust check: the Euclidean metric -/

/-- The Euclidean metric (the identity matrix). -/
def euclid : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun _ => 1

/-- The Euclidean metric is a Riemannian metric on every open set. -/
theorem isRiemMetric_euclid {U : Set (Fin n → ℝ)} (hU : IsOpen U) : IsRiemMetric euclid U where
  coord := ⟨hU, fun _ _ => transpose_one, fun _ _ => by simp [euclid], fun i j => contDiffOn_const⟩
  posDef := fun _ _ => PosDef.one

/-- For the Euclidean metric, `g_x(v, v) = v ⬝ v`. -/
@[simp] theorem normSq_euclid (x v : Fin n → ℝ) : normSq euclid x v = eNormSq v := by
  simp [normSq, euclid, eNormSq]

/-- **Trust check.** For the Euclidean metric on a convex open set, the distance is the
Euclidean distance: the straight segment is admissible with length `|y - x|`, and every curve is
at least that long. -/
theorem dist_euclid {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hconv : Convex ℝ U) {x y : Fin n → ℝ}
    (hx : x ∈ U) (hy : y ∈ U) : dist euclid U x y = √(eNormSq (y - x)) := by
  have hg := isRiemMetric_euclid (n := n) hU
  set c : ℝ → Fin n → ℝ := fun t => x + t • (y - x)
  have hcd : ∀ t, deriv c t = y - x := fun t => by
    have : HasDerivAt c (y - x) t :=
      (((hasDerivAt_id t).smul_const (y - x)).const_add x).congr_deriv (one_smul ℝ _)
    exact this.deriv
  have hadm : IsAdmissible U c x y := by
    refine ⟨by fun_prop, fun t ht => ?_, by simp [c], by simp [c]⟩
    have : c t = (1 - t) • x + t • y := by
      simp only [c, smul_sub, sub_smul, one_smul]
      abel
    rw [this]
    exact hconv hx hy (by linarith [ht.2]) ht.1 (by ring)
  apply le_antisymm
  · calc dist euclid U x y ≤ length euclid c 0 1 := dist_le_length hadm
      _ = √(eNormSq (y - x)) := by simp [length, hcd]
  · have := hg.dist_ge_of_bounds (K := univ) zero_le_one (fun z _ v => by simp) ⟨c, hadm⟩
      (fun _ _ _ _ => mem_univ _)
    simpa using this

end Lightlike.Geodesic
