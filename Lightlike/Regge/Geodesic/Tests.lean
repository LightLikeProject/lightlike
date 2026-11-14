import Lightlike.Regge.Geodesic.Sixth
import Lightlike.Regge.Geodesic.Riemannian
import Lightlike.GR.Schwarzschild

/-!
# Trust checks for the distance and the expansion of its square

Checks of `distJet`, `midJet` and the fifth-order expansions `IsRiemMetric.dist_sq_expansion` and
`IsRiemMetric.dist_sq_expansion_midpoint` (`Lightlike/Regge/Geodesic/DistExpansion.lean`), and of
`distJet5` and the sixth-order expansions `IsRiemMetric.dist_sq_expansion6` and
`IsRiemMetric.dist_sq_expansion_midpoint6` (`Lightlike/Regge/Geodesic/Quintic.lean`,
`Lightlike/Regge/Geodesic/Sixth.lean`), against exactly known distances, and wrong models shown to
fail; and checks of the link with Mathlib's Riemannian distance
(`Lightlike/Regge/Geodesic/Riemannian.lean`).

## Sheared planes

`shearBy q` is the metric `[[1 + q(y₀)², q(y₀)], [q(y₀), 1]]` on `ℝ²`, the pullback of the
Euclidean metric by the shear map `φ(y) = (y₀, y₁ + p(y₀))` with `p' = q` (`shearMapBy`). It is
flat, but in these coordinates it has an off-diagonal entry, non-zero first and second derivatives
and the Christoffel symbol `Γ¹₀₀ = q'(y₀)` (`christoffel_shearBy`). Its distance is
`|φ(y) - φ(x)|` (`dist_shearBy`): the preimage of the straight segment is admissible with that
length, and every admissible curve maps to a curve at least that long. Both jets and the
quintic term `quint` are computed in closed form for any `q` (`jetWith_shearBy`,
`midJetWith_shearBy`, `quint_shearBy`).

## Known values

* The **quadratic shear** `shear` (`p(s) = s²/2`). The squared distance is a polynomial of degree
  four in `w`, and it equals the jet exactly at every point (`dist_sq_shear`:
  `d(x, x + w)² = distJet x w`; `dist_sq_shear_midpoint`: `d(m - Δ/2, m + Δ/2)² = midJet m Δ`).
* The **cubic shear** `cubicShear` (`p(s) = s³/6`). At the origin `Γ = 0` but the second
  derivatives of the metric do not vanish, and the remainders are exactly
  `d(0, w)² - distJet 0 w = w₀⁶/36` (`dist_sq_cubicShear_zero`) and
  `d(-Δ/2, Δ/2)² - midJet 0 Δ = Δ₀⁶/576` (`dist_sq_cubicShear_midpoint_zero`).
* **Sixth order.** On the cubic shear the remainders are exactly
  `d(x, x + w)² - distJet5 x w = w₀⁶/36` (`dist_sq_cubicShear_sixth`) and
  `d(m - Δ/2, m + Δ/2)² - midJet m Δ = Δ₀⁶/576` (`dist_sq_cubicShear_midpoint`) at *every*
  point, where `Γ`, `∂g` and `quint = x₀ w₀⁵/6` do not vanish. On the **quartic shear**
  `quarticShear` (`p(s) = s⁴/24`) at the origin only the third derivative of the metric is
  non-zero, and `d(0, w)² - distJet5 0 w = w₀⁸/576` (`dist_sq_quarticShear_zero`), which checks
  the coefficient `1/24` of the third derivative in `quint`. Both sixth-order bounds are sharp:
  the remainders are not `O(‖w‖⁷)` (`dist_sq_expansion6_sharp`,
  `dist_sq_expansion_midpoint6_sharp`).
* The **Euclidean metric**: both jets are `|w|²` (`distJet_euclid`, `midJet_euclid`), and
  `d(x, x + w)² = distJet x w` (`dist_sq_euclid`).

## The coefficients are forced

`jetWith a b` and `midJetWith a b` are the jets with free coefficients `a` of the second
derivative of the metric and `b` of the Christoffel term (`distJet = jetWith (1/6) (1/12)`,
`midJet = midJetWith (1/24) (1/12)`). The quadratic shear alone fixes only `2a - b`; together
with the cubic shear the fifth-order bound forces `a = 1/6, b = 1/12`
(`jetWith_coeffs_forced`) and `a = 1/24, b = 1/12` (`midJetWith_coeffs_forced`).

## Wrong models

* Dropping the Christoffel term (`b = 0`) leaves an error `t⁴/12` along `w = (t, 0)` on the
  quadratic shear, so the fifth-order bound fails at every point (`jetWith_noChr_shear_fails`,
  `midJetWith_noChr_shear_fails`). This matches the numerical control in
  `scripts/regge/distance_expansion_check.py`, where the remainder of the model without the
  Christoffel term has order 4 instead of 5.
* Dropping the quintic term (`distJet` in place of `distJet5`) leaves the error
  `x₀ t⁵/6 + t⁶/36` on the cubic shear, so the sixth-order bound fails at every point with
  `x₀ ≠ 0` (`distJet_cubicShear_not_sixth`).

## Non-vacuity

* The hypotheses of both expansion theorems hold for the quadratic shear on the closed unit ball
  (`shear_dist_sq_expansion`, `shear_dist_sq_expansion_midpoint`).
* The hypotheses of `IsRiemMetric.exists_localJet3` and of both sixth-order expansion theorems
  hold for the cubic shear on the closed unit ball, where the remainders are not zero
  (`cubicShear_exists_localJet3`, `cubicShear_dist_sq_expansion6`,
  `cubicShear_dist_sq_expansion_midpoint6`).

## Mathlib's Riemannian distance

* **Known value (Mathlib).** For the Euclidean metric on `ℝⁿ` the Riemannian distance of our
  bundle is Mathlib's Riemannian distance of the inner product space `EuclideanSpace ℝ (Fin n)`
  between the same points (`riemannianEDist_euclid`), which Mathlib proves to be the Euclidean
  distance.
* **Known value.** For the quadratic shear the Riemannian distance from `0` to `(1, 0)` is
  `√5/2` (`riemannianEDist_shear`). **Wrong input:** the Euclidean metric gives `1` between the
  same points (`riemannianEDist_shear_ne_euclid`).
* **The connecting curve is needed.** On the punctured line `{x₀ ≠ 0}` no admissible curve joins
  `-1` and `1` (intermediate value theorem), so the Riemannian distance is `⊤` while `dist` is
  the junk value `0` (`riemannianEDist_puncturedLine`). The hypothesis of
  `IsRiemMetric.riemannianEDist_eq` cannot be dropped.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ}

/-! ## Sheared planes -/

/-- The **sheared plane** with shear `p`, written through `q = p'`: the pullback of the
Euclidean metric of `ℝ²` by `φ(y) = (y₀, y₁ + p(y₀))`, i.e.
`g = Dφᵀ Dφ = [[1 + q(y₀)², q(y₀)], [q(y₀), 1]]`. -/
def shearBy (q : ℝ → ℝ) : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ :=
  fun y => !![1 + q (y 0) ^ 2, q (y 0); q (y 0), 1]

/-- The shear map `φ(y) = (y₀, y₁ + p(y₀))`, an isometry from `shearBy p'` to the Euclidean
plane (`dist_shearBy`). -/
def shearMapBy (p : ℝ → ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![y 0, y 1 + p (y 0)]

variable {p q q₁ q₂ : ℝ → ℝ}

/-- The inverse of the sheared metric: `[[1, -q], [-q, 1 + q²]]` (its determinant is `1`). -/
theorem shearBy_inv (q : ℝ → ℝ) (y : Fin 2 → ℝ) :
    (shearBy q y)⁻¹ = !![1, -q (y 0); -q (y 0), 1 + q (y 0) ^ 2] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shearBy, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A sheared plane with smooth `q` is a Riemannian metric on the whole plane. -/
theorem isRiemMetric_shearBy (hq : ContDiff ℝ ∞ q) : IsRiemMetric (shearBy q) univ where
  coord := by
    refine ⟨isOpen_univ, fun x _ => ?_, fun x _ => ?_, fun i j => ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [shearBy]
    · simp only [shearBy, Matrix.det_fin_two_of]
      exact isUnit_iff_ne_zero.mpr (by ring_nf; norm_num)
    · fin_cases i <;> fin_cases j <;> simp [shearBy] <;> fun_prop
  posDef := fun x _ => by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v hv => ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [shearBy]
    · simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two, shearBy,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      have e : v 0 * ((1 + q (x 0) ^ 2) * v 0 + q (x 0) * v 1)
          + v 1 * (q (x 0) * v 0 + 1 * v 1) = v 0 ^ 2 + (v 1 + q (x 0) * v 0) ^ 2 := by ring
      rw [e]
      by_cases h0 : v 0 = 0
      · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
        rw [h0]; simpa using pow_pos (abs_pos.mpr h1) 2
      · nlinarith [pow_pos (abs_pos.mpr h0) 2, sq_abs (v 0), sq_nonneg (v 1 + q (x 0) * v 0)]

/-- The first partial derivatives of `shearBy q` (with `q₁ = q'`):
`∂₀ g = [[2 q q₁, q₁], [q₁, 0]]`, `∂₁ g = 0`. -/
def dshearBy (q q₁ : ℝ → ℝ) (k : Fin 2) (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = 0 then !![2 * q (y 0) * q₁ (y 0), q₁ (y 0); q₁ (y 0), 0] else 0

/-- The second partial derivatives of `shearBy q` (with `q₁ = q'`, `q₂ = q''`): only
`∂₀∂₀ g = [[2 (q₁² + q q₂), q₂], [q₂, 0]]` is non-zero. -/
def ddshearBy (q q₁ q₂ : ℝ → ℝ) (k l : Fin 2) (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = 0 ∧ l = 0 then !![2 * (q₁ (y 0) ^ 2 + q (y 0) * q₂ (y 0)), q₂ (y 0); q₂ (y 0), 0]
  else 0

/-- `∂_k g_ij` of the sheared metric. -/
theorem pd_shearBy (hq : ∀ s, HasDerivAt q (q₁ s) s) (i j k : Fin 2) (x : Fin 2 → ℝ) :
    Lightlike.pd k (fun y => shearBy q y i j) x = dshearBy q q₁ k x i j := by
  have h00 : ∀ k : Fin 2, Lightlike.pd k (fun y : Fin 2 → ℝ => 1 + q (y 0) ^ 2) x =
      if k = 0 then 2 * q (x 0) * q₁ (x 0) else 0 := fun k =>
    pd_coord (f := fun s => 1 + q s ^ 2) 0 k
      ((((hq (x 0)).pow 2).const_add 1).congr_deriv (by simp))
  have h01 : ∀ k : Fin 2, Lightlike.pd k (fun y : Fin 2 → ℝ => q (y 0)) x =
      if k = 0 then q₁ (x 0) else 0 := fun k => pd_coord (f := q) 0 k (hq (x 0))
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [shearBy, dshearBy, h00, h01, pd_const]

/-- `∂_l ∂_k g_ij` of the sheared metric. -/
theorem pd_pd_shearBy (hq : ∀ s, HasDerivAt q (q₁ s) s) (hq₁ : ∀ s, HasDerivAt q₁ (q₂ s) s)
    (i j k l : Fin 2) (x : Fin 2 → ℝ) :
    Lightlike.pd l (Lightlike.pd k (fun y => shearBy q y i j)) x = ddshearBy q q₁ q₂ k l x i j := by
  have e : Lightlike.pd k (fun y => shearBy q y i j) = fun y => dshearBy q q₁ k y i j :=
    funext fun y => pd_shearBy hq i j k y
  have h0 : ∀ l : Fin 2, Lightlike.pd l (fun y : Fin 2 → ℝ => 2 * q (y 0) * q₁ (y 0)) x =
      if l = 0 then 2 * (q₁ (x 0) ^ 2 + q (x 0) * q₂ (x 0)) else 0 := fun l =>
    pd_coord (f := fun s => 2 * q s * q₁ s) 0 l
      ((((hq (x 0)).const_mul 2).mul (hq₁ (x 0))).congr_deriv (by ring))
  have h1 : ∀ l : Fin 2, Lightlike.pd l (fun y : Fin 2 → ℝ => q₁ (y 0)) x =
      if l = 0 then q₂ (x 0) else 0 := fun l => pd_coord (f := q₁) 0 l (hq₁ (x 0))
  rw [e]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [dshearBy, ddshearBy, h0, h1, pd_const]

/-- The Christoffel symbols of the sheared metric: `Γ¹₀₀ = q'(x₀)`, all others vanish. -/
theorem christoffel_shearBy (hq : ∀ s, HasDerivAt q (q₁ s) s) (i j k : Fin 2) (x : Fin 2 → ℝ) :
    Lightlike.christoffel (shearBy q) i j k x = if i = 1 ∧ j = 0 ∧ k = 0 then q₁ (x 0) else 0 := by
  simp only [Lightlike.christoffel, pd_shearBy hq, shearBy_inv, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [dshearBy] <;> ring

/-- The Christoffel contraction of the sheared metric: `Γ(u, v) = (0, q'(x₀) u₀ v₀)`. -/
theorem chr_shearBy (hq : ∀ s, HasDerivAt q (q₁ s) s) (x u v : Fin 2 → ℝ) :
    chr (shearBy q) x u v = ![0, q₁ (x 0) * u 0 * v 0] := by
  funext i
  fin_cases i <;> simp [chr, christoffel_shearBy hq, Fin.sum_univ_two]

/-! ## The jets with free coefficients -/

/-- The jet family `g(w, w) + ½ ∂_w g(w, w) + a ∂_w ∂_w g(w, w) - b g(Γ(w, w), Γ(w, w))` at `x`;
`distJet` is `jetWith (1/6) (1/12)` (`jetWith_distJet`). -/
noncomputable def jetWith (a b : ℝ) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x w : Fin n → ℝ) : ℝ :=
  w ⬝ᵥ (g x *ᵥ w) + (1 / 2) * (w ⬝ᵥ (dmat g x w *ᵥ w)) + a * (w ⬝ᵥ (ddmat g x w w *ᵥ w))
    - b * (chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w))

/-- The midpoint jet family `g(Δ, Δ) + a ∂_Δ ∂_Δ g(Δ, Δ) - b g(Γ(Δ, Δ), Γ(Δ, Δ))` at `m`;
`midJet` is `midJetWith (1/24) (1/12)` (`midJetWith_midJet`). -/
noncomputable def midJetWith (a b : ℝ) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (m Δ : Fin n → ℝ) : ℝ :=
  Δ ⬝ᵥ (g m *ᵥ Δ) + a * (Δ ⬝ᵥ (ddmat g m Δ Δ *ᵥ Δ)) - b * (chr g m Δ Δ ⬝ᵥ (g m *ᵥ chr g m Δ Δ))

/-- `distJet` is the member `a = 1/6, b = 1/12` of the family. -/
theorem jetWith_distJet (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    jetWith (1 / 6) (1 / 12) g x w = distJet g x w := rfl

/-- `midJet` is the member `a = 1/24, b = 1/12` of the family. -/
theorem midJetWith_midJet (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (m Δ : Fin n → ℝ) :
    midJetWith (1 / 24) (1 / 12) g m Δ = midJet g m Δ := rfl

/-- The jet family on a sheared plane, in closed form. -/
theorem jetWith_shearBy (hq : ∀ s, HasDerivAt q (q₁ s) s) (hq₁ : ∀ s, HasDerivAt q₁ (q₂ s) s)
    (a b : ℝ) (x w : Fin 2 → ℝ) :
    jetWith a b (shearBy q) x w = w 0 ^ 2 + (w 1 + q (x 0) * w 0) ^ 2
      + q₁ (x 0) * w 0 ^ 2 * (w 1 + q (x 0) * w 0)
      + 2 * a * w 0 ^ 3 * (q₁ (x 0) ^ 2 * w 0 + q₂ (x 0) * (w 1 + q (x 0) * w 0))
      - b * q₁ (x 0) ^ 2 * w 0 ^ 4 := by
  simp only [jetWith, dmat, ddmat, chr_shearBy hq, pd_shearBy hq, pd_pd_shearBy hq hq₁,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  simp [shearBy, dshearBy, ddshearBy]
  ring

/-- The midpoint jet family on a sheared plane, in closed form. -/
theorem midJetWith_shearBy (hq : ∀ s, HasDerivAt q (q₁ s) s)
    (hq₁ : ∀ s, HasDerivAt q₁ (q₂ s) s) (a b : ℝ) (m Δ : Fin 2 → ℝ) :
    midJetWith a b (shearBy q) m Δ = Δ 0 ^ 2 + (Δ 1 + q (m 0) * Δ 0) ^ 2
      + 2 * a * Δ 0 ^ 3 * (q₁ (m 0) ^ 2 * Δ 0 + q₂ (m 0) * (Δ 1 + q (m 0) * Δ 0))
      - b * q₁ (m 0) ^ 2 * Δ 0 ^ 4 := by
  simp only [midJetWith, ddmat, chr_shearBy hq, pd_pd_shearBy hq hq₁, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two]
  simp [shearBy, ddshearBy]
  ring


/-! ## The distance of a sheared plane -/

/-- The shear map is `C¹` if `p` is. -/
theorem contDiff_shearMapBy (hp : ContDiff ℝ 1 p) : ContDiff ℝ 1 (shearMapBy p) :=
  contDiff_pi.mpr fun i => by fin_cases i <;> simp [shearMapBy] <;> fun_prop

/-- Along a differentiable curve the squared speed in the sheared metric is the Euclidean squared
speed of the image under the shear map. -/
theorem normSq_shearBy_deriv (hp : ∀ s, HasDerivAt p (q s) s) {c : ℝ → Fin 2 → ℝ} {t : ℝ}
    (hc : DifferentiableAt ℝ c t) :
    normSq (shearBy q) (c t) (deriv c t) = eNormSq (deriv (shearMapBy p ∘ c) t) := by
  have h0 : HasDerivAt (fun s => c s 0) (deriv c t 0) t := hasDerivAt_pi.mp hc.hasDerivAt 0
  have h1 : HasDerivAt (fun s => c s 1) (deriv c t 1) t := hasDerivAt_pi.mp hc.hasDerivAt 1
  have h : HasDerivAt (shearMapBy p ∘ c)
      ![deriv c t 0, deriv c t 1 + q (c t 0) * deriv c t 0] t := by
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa [shearMapBy] using h0
    · have h1' : HasDerivAt (fun s => c s 1 + p (c s 0))
          (deriv c t 1 + q (c t 0) * deriv c t 0) t := h1.add ((hp (c t 0)).comp t h0)
      simpa [shearMapBy] using h1'
  rw [h.deriv]
  simp only [normSq, eNormSq, shearBy, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  simp
  ring

/-- The length of a `C¹` curve in a sheared plane is the Euclidean length of its image. -/
theorem length_shearBy (hp : ∀ s, HasDerivAt p (q s) s) {c : ℝ → Fin 2 → ℝ}
    (hc : ContDiff ℝ 1 c) :
    length (shearBy q) c 0 1 = ∫ t in (0 : ℝ)..1, √(eNormSq (deriv (shearMapBy p ∘ c) t)) := by
  unfold length
  exact intervalIntegral.integral_congr fun t _ => by
    rw [normSq_shearBy_deriv hp ((hc.differentiable one_ne_zero) t)]

/-- **Known value.** The distance of a sheared plane is the Euclidean distance of the images
under the shear map: the preimage of the straight segment is admissible with that length, and
every admissible curve is at least that long. -/
theorem dist_shearBy (hp : ∀ s, HasDerivAt p (q s) s) (hp₁ : ContDiff ℝ 1 p)
    (x y : Fin 2 → ℝ) :
    dist (shearBy q) univ x y = √(eNormSq (shearMapBy p y - shearMapBy p x)) := by
  set D := shearMapBy p y - shearMapBy p x
  set c : ℝ → Fin 2 → ℝ := fun t =>
    ![shearMapBy p x 0 + t * D 0, shearMapBy p x 1 + t * D 1 - p (shearMapBy p x 0 + t * D 0)]
  have hφc : shearMapBy p ∘ c = fun t => shearMapBy p x + t • D := by
    funext t i
    fin_cases i <;> simp [c, shearMapBy]
  have hc : ContDiff ℝ 1 c :=
    contDiff_pi.mpr fun i => by fin_cases i <;> simp [c] <;> fun_prop
  have hadm : IsAdmissible univ c x y := by
    refine ⟨hc, fun _ _ => mem_univ _, ?_, ?_⟩ <;> funext i <;> fin_cases i <;>
      simp [c, D, shearMapBy]
  apply le_antisymm
  · calc dist (shearBy q) univ x y ≤ length (shearBy q) c 0 1 := dist_le_length hadm
      _ = √(eNormSq D) := by
        rw [length_shearBy hp hc, hφc]
        have hd : ∀ t, deriv (fun t : ℝ => shearMapBy p x + t • D) t = D := fun t =>
          ((((hasDerivAt_id t).smul_const D).const_add (shearMapBy p x)).congr_deriv
            (one_smul ℝ D)).deriv
        simp [hd]
  · refine le_csInf ⟨_, c, hadm, rfl⟩ ?_
    rintro L ⟨c', hc', rfl⟩
    rw [length_shearBy hp hc'.smooth]
    have := sqrt_eNormSq_sub_le_integral ((contDiff_shearMapBy hp₁).comp hc'.smooth) zero_le_one
    simpa [hc'.start, hc'.finish] using this

/-! ## The quadratic and the cubic shear -/

/-- The **quadratic shear**: `p(s) = s²/2`, `q(s) = s`, i.e. `g = [[1 + y₀², y₀], [y₀, 1]]`,
with `Γ¹₀₀ = 1`. -/
abbrev shear : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := shearBy fun s => s

/-- The **cubic shear**: `p(s) = s³/6`, `q(s) = s²/2`, i.e.
`g = [[1 + y₀⁴/4, y₀²/2], [y₀²/2, 1]]`, with `Γ¹₀₀ = y₀`. -/
noncomputable abbrev cubicShear : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ :=
  shearBy fun s => s ^ 2 / 2

/-- `(s²/2)' = s`. -/
theorem hasDerivAt_half_sq (s : ℝ) : HasDerivAt (fun s : ℝ => s ^ 2 / 2) s s :=
  ((hasDerivAt_pow 2 s).div_const 2).congr_deriv (by simp)

/-- `(s³/6)' = s²/2`. -/
theorem hasDerivAt_sixth_cube (s : ℝ) : HasDerivAt (fun s : ℝ => s ^ 3 / 6) (s ^ 2 / 2) s :=
  ((hasDerivAt_pow 3 s).div_const 6).congr_deriv (by simp; ring)

/-- The quadratic shear is a Riemannian metric on the plane. -/
theorem isRiemMetric_shear : IsRiemMetric shear univ :=
  isRiemMetric_shearBy contDiff_id

/-- The squared distance of the quadratic shear:
`(y₀ - x₀)² + (y₁ - x₁ + (y₀² - x₀²)/2)²`. -/
theorem dist_sq_shear_eq (x y : Fin 2 → ℝ) :
    dist shear univ x y ^ 2 = (y 0 - x 0) ^ 2 + (y 1 - x 1 + (y 0 ^ 2 - x 0 ^ 2) / 2) ^ 2 := by
  rw [dist_shearBy hasDerivAt_half_sq (by fun_prop), Real.sq_sqrt (eNormSq_nonneg _)]
  simp [shearMapBy, eNormSq, dotProduct, Fin.sum_univ_two]
  ring

/-- The squared distance of the cubic shear: `(y₀ - x₀)² + (y₁ - x₁ + (y₀³ - x₀³)/6)²`. -/
theorem dist_sq_cubicShear_eq (x y : Fin 2 → ℝ) :
    dist cubicShear univ x y ^ 2
      = (y 0 - x 0) ^ 2 + (y 1 - x 1 + (y 0 ^ 3 - x 0 ^ 3) / 6) ^ 2 := by
  rw [dist_shearBy hasDerivAt_sixth_cube (by fun_prop), Real.sq_sqrt (eNormSq_nonneg _)]
  simp [shearMapBy, eNormSq, dotProduct, Fin.sum_univ_two]
  ring

/-- **Trust check (exact).** On the quadratic shear the squared distance *equals* the jet
`distJet` for every `x` and `w`: the remainder of `IsRiemMetric.dist_sq_expansion` vanishes
identically. -/
theorem dist_sq_shear (x w : Fin 2 → ℝ) : dist shear univ x (x + w) ^ 2 = distJet shear x w := by
  rw [dist_sq_shear_eq, ← jetWith_distJet,
    jetWith_shearBy (fun s => hasDerivAt_id' s) (fun s => hasDerivAt_const s (1 : ℝ))]
  simp
  ring

/-- **Trust check (exact).** On the quadratic shear the squared distance between `m ∓ Δ/2`
*equals* the midpoint jet `midJet` (the remainder of
`IsRiemMetric.dist_sq_expansion_midpoint` vanishes identically). -/
theorem dist_sq_shear_midpoint (m Δ : Fin 2 → ℝ) :
    dist shear univ (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2 = midJet shear m Δ := by
  rw [dist_sq_shear_eq, ← midJetWith_midJet,
    midJetWith_shearBy (fun s => hasDerivAt_id' s) (fun s => hasDerivAt_const s (1 : ℝ))]
  simp
  ring

/-- **Trust check (exact).** On the cubic shear at the origin, where `Γ = 0` but the second
derivatives of the metric do not vanish, the remainder of the jet is exactly `w₀⁶/36`. -/
theorem dist_sq_cubicShear_zero (w : Fin 2 → ℝ) :
    dist cubicShear univ 0 (0 + w) ^ 2 = distJet cubicShear 0 w + w 0 ^ 6 / 36 := by
  rw [dist_sq_cubicShear_eq, ← jetWith_distJet,
    jetWith_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s)]
  simp
  ring

/-- **Trust check (exact).** On the cubic shear about the origin the remainder of the midpoint
jet is exactly `Δ₀⁶/576`. -/
theorem dist_sq_cubicShear_midpoint_zero (Δ : Fin 2 → ℝ) :
    dist cubicShear univ (0 - (1 / 2 : ℝ) • Δ) (0 + (1 / 2 : ℝ) • Δ) ^ 2
      = midJet cubicShear 0 Δ + Δ 0 ^ 6 / 576 := by
  rw [dist_sq_cubicShear_eq, ← midJetWith_midJet,
    midJetWith_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s)]
  simp
  ring


/-! ## The coefficients are forced -/

/-- A non-zero quartic `a t⁴` is not `O(|t|⁵)` near `0`. -/
theorem not_quartic_le_quintic {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ C r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| ≤ r → |a * t ^ 4| ≤ C * |t| ^ 5 := by
  rintro ⟨C, r, hr, h⟩
  have hA := abs_pos.mpr ha
  set t := min r (|a| / (2 * (|C| + 1)))
  have ht : 0 < t := lt_min hr (by positivity)
  have h1 := h t (by rw [abs_of_pos ht]; exact min_le_left _ _)
  rw [abs_mul, abs_pow, abs_of_pos ht] at h1
  have h2 : |a| * t ^ 4 ≤ (|C| * t) * t ^ 4 :=
    calc |a| * t ^ 4 ≤ C * t ^ 5 := h1
      _ ≤ |C| * t ^ 5 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = (|C| * t) * t ^ 4 := by ring
  have h3 : |a| ≤ |C| * t := le_of_mul_le_mul_right h2 (by positivity)
  have h4 : |C| * t ≤ |C| * (|a| / (2 * (|C| + 1))) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg C)
  have h5 : |C| * (|a| / (2 * (|C| + 1))) < |a| := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

/-- If `a t⁴ + e t⁶ = O(|t|⁵)` near `0`, then `a = 0`. -/
theorem eq_zero_of_quartic_le_quintic {a e : ℝ}
    (h : ∃ C r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| ≤ r → |a * t ^ 4 + e * t ^ 6| ≤ C * |t| ^ 5) :
    a = 0 := by
  by_contra ha
  obtain ⟨C, r, hr, h⟩ := h
  refine not_quartic_le_quintic ha ⟨C + |e|, min r 1, lt_min hr one_pos, fun t ht => ?_⟩
  have ht1 : |t| ≤ 1 := ht.trans (min_le_right _ _)
  have h1 := h t (ht.trans (min_le_left _ _))
  have h6 : |e * t ^ 6| ≤ |e| * |t| ^ 5 := by
    rw [abs_mul, abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg e)
    calc |t| ^ 6 = |t| ^ 5 * |t| := by ring
      _ ≤ |t| ^ 5 * 1 := mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ = |t| ^ 5 := mul_one _
  calc |a * t ^ 4| = |(a * t ^ 4 + e * t ^ 6) - e * t ^ 6| := by rw [add_sub_cancel_right]
    _ ≤ |a * t ^ 4 + e * t ^ 6| + |e * t ^ 6| := abs_sub _ _
    _ ≤ C * |t| ^ 5 + |e| * |t| ^ 5 := add_le_add h1 h6
    _ = (C + |e|) * |t| ^ 5 := by ring

/-- The direction `(t, 0)` has sup norm `|t|`. -/
theorem norm_dir0 (t : ℝ) : ‖(![t, 0] : Fin 2 → ℝ)‖ = |t| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg t)).mpr fun i => ?_) ?_
  · fin_cases i <;> simp
  · simpa using norm_le_pi_norm (![t, 0] : Fin 2 → ℝ) 0

/-- The direction `(t, t)` has sup norm `|t|`. -/
theorem norm_diag (t : ℝ) : ‖(fun _ => t : Fin 2 → ℝ)‖ = |t| := by
  rw [pi_norm_const, Real.norm_eq_abs]

/-- **The coefficients of `distJet` are forced.** If a jet `jetWith a b` satisfies the
fifth-order bound at the origin of both the quadratic and the cubic shear, then `a = 1/6` and
`b = 1/12`. The quadratic shear along `(t, 0)` gives `2a - b = 1/4`; the cubic shear along
`(t, t)` gives `2a = 1/3`. -/
theorem jetWith_coeffs_forced {a b : ℝ}
    (h₁ : ∃ C r : ℝ, 0 < r ∧ ∀ w : Fin 2 → ℝ, ‖w‖ ≤ r →
      |dist shear univ 0 (0 + w) ^ 2 - jetWith a b shear 0 w| ≤ C * ‖w‖ ^ 5)
    (h₂ : ∃ C r : ℝ, 0 < r ∧ ∀ w : Fin 2 → ℝ, ‖w‖ ≤ r →
      |dist cubicShear univ 0 (0 + w) ^ 2 - jetWith a b cubicShear 0 w| ≤ C * ‖w‖ ^ 5) :
    a = 1 / 6 ∧ b = 1 / 12 := by
  obtain ⟨C₁, r₁, hr₁, h₁⟩ := h₁
  obtain ⟨C₂, r₂, hr₂, h₂⟩ := h₂
  have hb : 1 / 4 - 2 * a + b = 0 := eq_zero_of_quartic_le_quintic (e := 0)
    ⟨C₁, r₁, hr₁, fun t ht => by
      have h := h₁ ![t, 0] (by rw [norm_dir0]; exact ht)
      rw [norm_dir0, dist_sq_shear_eq,
        jetWith_shearBy (fun s => hasDerivAt_id' s) (fun s => hasDerivAt_const s (1 : ℝ))] at h
      convert h using 2
      simp
      ring⟩
  have ha : 1 / 3 - 2 * a = 0 := eq_zero_of_quartic_le_quintic (e := 1 / 36)
    ⟨C₂, r₂, hr₂, fun t ht => by
      have h := h₂ (fun _ => t) (by rw [norm_diag]; exact ht)
      rw [norm_diag, dist_sq_cubicShear_eq,
        jetWith_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s)] at h
      convert h using 2
      simp
      ring⟩
  constructor <;> linarith

/-- **The coefficients of `midJet` are forced.** If a midpoint jet `midJetWith a b` satisfies
the fifth-order bound about the origin of both the quadratic and the cubic shear, then
`a = 1/24` and `b = 1/12`. The quadratic shear along `(t, 0)` gives `b = 2a`; the cubic shear
along `(t, t)` gives `2a = 1/12`. -/
theorem midJetWith_coeffs_forced {a b : ℝ}
    (h₁ : ∃ C r : ℝ, 0 < r ∧ ∀ Δ : Fin 2 → ℝ, ‖Δ‖ ≤ r →
      |dist shear univ (0 - (1 / 2 : ℝ) • Δ) (0 + (1 / 2 : ℝ) • Δ) ^ 2
        - midJetWith a b shear 0 Δ| ≤ C * ‖Δ‖ ^ 5)
    (h₂ : ∃ C r : ℝ, 0 < r ∧ ∀ Δ : Fin 2 → ℝ, ‖Δ‖ ≤ r →
      |dist cubicShear univ (0 - (1 / 2 : ℝ) • Δ) (0 + (1 / 2 : ℝ) • Δ) ^ 2
        - midJetWith a b cubicShear 0 Δ| ≤ C * ‖Δ‖ ^ 5) :
    a = 1 / 24 ∧ b = 1 / 12 := by
  obtain ⟨C₁, r₁, hr₁, h₁⟩ := h₁
  obtain ⟨C₂, r₂, hr₂, h₂⟩ := h₂
  have hb : b - 2 * a = 0 := eq_zero_of_quartic_le_quintic (e := 0)
    ⟨C₁, r₁, hr₁, fun t ht => by
      have h := h₁ ![t, 0] (by rw [norm_dir0]; exact ht)
      rw [norm_dir0, dist_sq_shear_eq,
        midJetWith_shearBy (fun s => hasDerivAt_id' s) (fun s => hasDerivAt_const s (1 : ℝ))] at h
      convert h using 2
      simp
      ring⟩
  have ha : 1 / 12 - 2 * a = 0 := eq_zero_of_quartic_le_quintic (e := 1 / 576)
    ⟨C₂, r₂, hr₂, fun t ht => by
      have h := h₂ (fun _ => t) (by rw [norm_diag]; exact ht)
      rw [norm_diag, dist_sq_cubicShear_eq,
        midJetWith_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s)] at h
      convert h using 2
      simp
      ring⟩
  constructor <;> linarith


/-! ## Wrong models -/

/-- **Wrong model fails.** Without its Christoffel term (`b = 0`) the jet is off by `t⁴/12` along
`w = (t, 0)` on the quadratic shear, so the fifth-order expansion fails at every point. -/
theorem jetWith_noChr_shear_fails (x : Fin 2 → ℝ) :
    ¬ ∃ C r : ℝ, 0 < r ∧ ∀ w : Fin 2 → ℝ, ‖w‖ ≤ r →
      |dist shear univ x (x + w) ^ 2 - jetWith (1 / 6) 0 shear x w| ≤ C * ‖w‖ ^ 5 := by
  rintro ⟨C, r, hr, h⟩
  refine not_quartic_le_quintic (a := -(1 / 12)) (by norm_num) ⟨C, r, hr, fun t ht => ?_⟩
  have h' := h ![t, 0] (by rw [norm_dir0]; exact ht)
  rw [norm_dir0, dist_sq_shear_eq,
    jetWith_shearBy (fun s => hasDerivAt_id' s) (fun s => hasDerivAt_const s (1 : ℝ))] at h'
  convert h' using 2
  simp
  ring

/-- **Wrong model fails.** Without its Christoffel term (`b = 0`) the midpoint jet is off by
`t⁴/12` along `Δ = (t, 0)` on the quadratic shear, so the fifth-order midpoint expansion fails
at every point. -/
theorem midJetWith_noChr_shear_fails (m : Fin 2 → ℝ) :
    ¬ ∃ C r : ℝ, 0 < r ∧ ∀ Δ : Fin 2 → ℝ, ‖Δ‖ ≤ r →
      |dist shear univ (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2
        - midJetWith (1 / 24) 0 shear m Δ| ≤ C * ‖Δ‖ ^ 5 := by
  rintro ⟨C, r, hr, h⟩
  refine not_quartic_le_quintic (a := -(1 / 12)) (by norm_num) ⟨C, r, hr, fun t ht => ?_⟩
  have h' := h ![t, 0] (by rw [norm_dir0]; exact ht)
  rw [norm_dir0, dist_sq_shear_eq,
    midJetWith_shearBy (fun s => hasDerivAt_id' s) (fun s => hasDerivAt_const s (1 : ℝ))] at h'
  convert h' using 2
  simp
  ring

/-! ## The Euclidean metric and non-vacuity -/

/-- For the Euclidean metric every derivative of the metric and every Christoffel symbol
vanishes, so `dmat`, `ddmat` and `chr` are `0`. -/
theorem euclid_jets_eq_zero (x u v : Fin n → ℝ) :
    dmat euclid x u = 0 ∧ ddmat euclid x u v = 0 ∧ chr euclid x u v = 0 := by
  have h1 : ∀ i j k : Fin n, Lightlike.pd k (fun y => euclid y i j) = fun _ => 0 := fun i j k =>
    funext fun y => Lightlike.pd_const k _ y
  have h2 : ∀ i j k : Fin n, Lightlike.christoffel euclid i j k x = 0 := fun i j k =>
    congrFun (Lightlike.christoffel_const (1 : Matrix (Fin n) (Fin n) ℝ) i j k) x
  refine ⟨?_, ?_, ?_⟩
  · ext i j; simp [dmat, h1]
  · ext i j; simp [ddmat, h1, Lightlike.pd_const]
  · funext i; simp [chr, h2]

/-- **Known value.** For the Euclidean metric the jet is `|w|²`. -/
theorem distJet_euclid (x w : Fin n → ℝ) : distJet euclid x w = eNormSq w := by
  obtain ⟨h1, h2, h3⟩ := euclid_jets_eq_zero x w w
  simp [distJet, h1, h2, h3, euclid, eNormSq]

/-- **Known value.** For the Euclidean metric the midpoint jet is `|Δ|²`. -/
theorem midJet_euclid (m Δ : Fin n → ℝ) : midJet euclid m Δ = eNormSq Δ := by
  obtain ⟨-, h2, h3⟩ := euclid_jets_eq_zero m Δ Δ
  simp [midJet, h2, h3, euclid, eNormSq]

/-- **Trust check (exact).** For the Euclidean metric on `ℝⁿ` the squared distance equals the jet:
both are `|w|²`. -/
theorem dist_sq_euclid (x w : Fin n → ℝ) :
    dist euclid univ x (x + w) ^ 2 = distJet euclid x w := by
  rw [dist_euclid isOpen_univ convex_univ (mem_univ _) (mem_univ _), add_sub_cancel_left,
    Real.sq_sqrt (eNormSq_nonneg _), distJet_euclid]

/-- **Non-vacuity.** The hypotheses of `IsRiemMetric.dist_sq_expansion` hold for the quadratic
shear and the closed unit ball. -/
theorem shear_dist_sq_expansion :
    ∃ C r : ℝ, 0 < r ∧ ∀ x ∈ Metric.closedBall (0 : Fin 2 → ℝ) 1, ∀ w : Fin 2 → ℝ, ‖w‖ ≤ r →
      |dist shear univ x (x + w) ^ 2 - distJet shear x w| ≤ C * ‖w‖ ^ 5 :=
  isRiemMetric_shear.dist_sq_expansion (isCompact_closedBall 0 1) (subset_univ _)

/-- **Non-vacuity.** The hypotheses of `IsRiemMetric.dist_sq_expansion_midpoint` hold for the
quadratic shear and the closed unit ball. -/
theorem shear_dist_sq_expansion_midpoint :
    ∃ C r : ℝ, 0 < r ∧ ∀ m ∈ Metric.closedBall (0 : Fin 2 → ℝ) 1, ∀ Δ : Fin 2 → ℝ, ‖Δ‖ ≤ r →
      |dist shear univ (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2 - midJet shear m Δ|
        ≤ C * ‖Δ‖ ^ 5 :=
  isRiemMetric_shear.dist_sq_expansion_midpoint (isCompact_closedBall 0 1) (subset_univ _)

/-! ## The expansions to sixth order -/

/-- The third partial derivatives of `shearBy q` (with `q₁ = q'`, `q₂ = q''`, `q₃ = q'''`): only
`∂₀∂₀∂₀ g = [[2 (3 q₁ q₂ + q q₃), q₃], [q₃, 0]]` is non-zero. -/
def dddshearBy (q q₁ q₂ q₃ : ℝ → ℝ) (k l p : Fin 2) (y : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  if k = 0 ∧ l = 0 ∧ p = 0 then
    !![2 * (3 * q₁ (y 0) * q₂ (y 0) + q (y 0) * q₃ (y 0)), q₃ (y 0); q₃ (y 0), 0]
  else 0

/-- `∂_p ∂_l ∂_k g_ij` of the sheared metric. -/
theorem pd_pd_pd_shearBy {q₃ : ℝ → ℝ} (hq : ∀ s, HasDerivAt q (q₁ s) s)
    (hq₁ : ∀ s, HasDerivAt q₁ (q₂ s) s) (hq₂ : ∀ s, HasDerivAt q₂ (q₃ s) s)
    (i j k l p : Fin 2) (x : Fin 2 → ℝ) :
    Lightlike.pd p (Lightlike.pd l (Lightlike.pd k (fun y => shearBy q y i j))) x
      = dddshearBy q q₁ q₂ q₃ k l p x i j := by
  have e : Lightlike.pd l (Lightlike.pd k (fun y => shearBy q y i j)) = fun y => ddshearBy q q₁ q₂ k l y i j :=
    funext fun y => pd_pd_shearBy hq hq₁ i j k l y
  have h0 : ∀ p : Fin 2,
      Lightlike.pd p (fun y : Fin 2 → ℝ => 2 * (q₁ (y 0) ^ 2 + q (y 0) * q₂ (y 0))) x =
        if p = 0 then 2 * (3 * q₁ (x 0) * q₂ (x 0) + q (x 0) * q₃ (x 0)) else 0 := fun p =>
    pd_coord (f := fun s => 2 * (q₁ s ^ 2 + q s * q₂ s)) 0 p
      (((((hq₁ (x 0)).pow 2).add ((hq (x 0)).mul (hq₂ (x 0)))).const_mul 2).congr_deriv
        (by simp; ring))
  have h1 : ∀ p : Fin 2, Lightlike.pd p (fun y : Fin 2 → ℝ => q₂ (y 0)) x =
      if p = 0 then q₃ (x 0) else 0 := fun p => pd_coord (f := q₂) 0 p (hq₂ (x 0))
  rw [e]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases p <;>
    simp [ddshearBy, dddshearBy, h0, h1, pd_const]

/-- The quintic term `quint` on a sheared plane, in closed form:
`q₁ q₂ w₀⁵/6 + q₃ w₀⁴ (w₁ + q w₀)/12` at `x₀`. It is the term of order five of the exact squared
distance `w₀² + (w₁ + p(x₀ + w₀) - p(x₀))²`. -/
theorem quint_shearBy {q₃ : ℝ → ℝ} (hq : ∀ s, HasDerivAt q (q₁ s) s)
    (hq₁ : ∀ s, HasDerivAt q₁ (q₂ s) s) (hq₂ : ∀ s, HasDerivAt q₂ (q₃ s) s) (x w : Fin 2 → ℝ) :
    quint (shearBy q) x w = q₁ (x 0) * q₂ (x 0) * w 0 ^ 5 / 6
      + q₃ (x 0) * w 0 ^ 4 * (w 1 + q (x 0) * w 0) / 12 := by
  simp only [quint, dmat, ddmat, dddmat, chr_shearBy hq, pd_shearBy hq, pd_pd_shearBy hq hq₁,
    pd_pd_pd_shearBy hq hq₁ hq₂, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  simp [dshearBy, ddshearBy, dddshearBy]
  ring

/-- The **quartic shear**: `p(s) = s⁴/24`, `q(s) = s³/6`, with `Γ¹₀₀ = y₀²/2`. At the origin
the metric is Euclidean to second order and only its third derivative `∂₀³ g₀₁ = 1` is
non-zero. -/
noncomputable abbrev quarticShear : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ :=
  shearBy fun s => s ^ 3 / 6

/-- `(s⁴/24)' = s³/6`. -/
theorem hasDerivAt_quartic (s : ℝ) : HasDerivAt (fun s : ℝ => s ^ 4 / 24) (s ^ 3 / 6) s :=
  ((hasDerivAt_pow 4 s).div_const 24).congr_deriv (by simp; ring)

/-- The squared distance of the quartic shear: `(y₀ - x₀)² + (y₁ - x₁ + (y₀⁴ - x₀⁴)/24)²`. -/
theorem dist_sq_quarticShear_eq (x y : Fin 2 → ℝ) :
    dist quarticShear univ x y ^ 2
      = (y 0 - x 0) ^ 2 + (y 1 - x 1 + (y 0 ^ 4 - x 0 ^ 4) / 24) ^ 2 := by
  rw [dist_shearBy hasDerivAt_quartic (by fun_prop), Real.sq_sqrt (eNormSq_nonneg _)]
  simp [shearMapBy, eNormSq, dotProduct, Fin.sum_univ_two]
  ring

/-- **Trust check (exact).** On the cubic shear the remainder of the sixth-order expansion
`IsRiemMetric.dist_sq_expansion6` is exactly `w₀⁶/36`, at every point `x`. Here
`quint = x₀ w₀⁵/6` is non-zero away from `x₀ = 0`, and the Christoffel symbols and the first two
derivatives of the metric all enter. -/
theorem dist_sq_cubicShear_sixth (x w : Fin 2 → ℝ) :
    dist cubicShear univ x (x + w) ^ 2 = distJet5 cubicShear x w + w 0 ^ 6 / 36 := by
  rw [dist_sq_cubicShear_eq, distJet5, ← jetWith_distJet,
    jetWith_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s),
    quint_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s)
      (fun s => hasDerivAt_const s (1 : ℝ))]
  simp
  ring

/-- **Trust check (exact).** On the quartic shear at the origin, where only the third derivative
of the metric is non-zero, the remainder of `IsRiemMetric.dist_sq_expansion6` is exactly
`w₀⁸/576`: the term `(1/24) ∂_w ∂_w ∂_w g(w, w) = w₀⁴ w₁/12` of `quint` is the whole term of
order five of the squared distance. -/
theorem dist_sq_quarticShear_zero (w : Fin 2 → ℝ) :
    dist quarticShear univ 0 (0 + w) ^ 2 = distJet5 quarticShear 0 w + w 0 ^ 8 / 576 := by
  rw [dist_sq_quarticShear_eq, distJet5, ← jetWith_distJet,
    jetWith_shearBy hasDerivAt_sixth_cube hasDerivAt_half_sq,
    quint_shearBy hasDerivAt_sixth_cube hasDerivAt_half_sq (fun s => hasDerivAt_id' s)]
  simp
  ring

/-- **Trust check (exact).** On the cubic shear the remainder of the midpoint expansion
`IsRiemMetric.dist_sq_expansion_midpoint6` is exactly `Δ₀⁶/576`, at every midpoint `m`: the
terms of order three and five vanish about the midpoint although the Christoffel symbols and the
first derivatives of the metric do not vanish at `m` when `m₀ ≠ 0`. -/
theorem dist_sq_cubicShear_midpoint (m Δ : Fin 2 → ℝ) :
    dist cubicShear univ (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2
      = midJet cubicShear m Δ + Δ 0 ^ 6 / 576 := by
  rw [dist_sq_cubicShear_eq, ← midJetWith_midJet,
    midJetWith_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s)]
  simp
  ring

/-- A non-zero monomial `a tᵏ` is not `O(|t|ᵏ⁺¹)` near `0`. -/
theorem not_pow_le_pow_succ {a : ℝ} (ha : a ≠ 0) (k : ℕ) :
    ¬ ∃ C r : ℝ, 0 < r ∧ ∀ t : ℝ, |t| ≤ r → |a * t ^ k| ≤ C * |t| ^ (k + 1) := by
  rintro ⟨C, r, hr, h⟩
  have hA := abs_pos.mpr ha
  set t := min r (|a| / (2 * (|C| + 1)))
  have ht : 0 < t := lt_min hr (by positivity)
  have h1 := h t (by rw [abs_of_pos ht]; exact min_le_left _ _)
  rw [abs_mul, abs_pow, abs_of_pos ht] at h1
  have h2 : |a| * t ^ k ≤ (|C| * t) * t ^ k :=
    calc |a| * t ^ k ≤ C * t ^ (k + 1) := h1
      _ ≤ |C| * t ^ (k + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = (|C| * t) * t ^ k := by ring
  have h3 : |a| ≤ |C| * t := le_of_mul_le_mul_right h2 (by positivity)
  have h4 : |C| * t ≤ |C| * (|a| / (2 * (|C| + 1))) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (abs_nonneg C)
  have h5 : |C| * (|a| / (2 * (|C| + 1))) < |a| := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

/-- **The order six is sharp.** On the cubic shear the remainder of
`IsRiemMetric.dist_sq_expansion6` is not `O(‖w‖⁷)` at any point (it is `t⁶/36` along
`w = (t, 0)`). -/
theorem dist_sq_expansion6_sharp (x : Fin 2 → ℝ) :
    ¬ ∃ C r : ℝ, 0 < r ∧ ∀ w : Fin 2 → ℝ, ‖w‖ ≤ r →
      |dist cubicShear univ x (x + w) ^ 2 - distJet5 cubicShear x w| ≤ C * ‖w‖ ^ 7 := by
  rintro ⟨C, r, hr, h⟩
  refine not_pow_le_pow_succ (a := 1 / 36) (by norm_num) 6 ⟨C, r, hr, fun t ht => ?_⟩
  have h' := h ![t, 0] (by rw [norm_dir0]; exact ht)
  rw [norm_dir0, dist_sq_cubicShear_sixth, add_sub_cancel_left] at h'
  simp only [Matrix.cons_val_zero] at h'
  calc |1 / 36 * t ^ 6| = |t ^ 6 / 36| := by congr 1; ring
    _ ≤ C * |t| ^ 7 := h'

/-- **The order six is sharp about the midpoint.** On the cubic shear the remainder of
`IsRiemMetric.dist_sq_expansion_midpoint6` is not `O(‖Δ‖⁷)` at any midpoint (it is `t⁶/576`
along `Δ = (t, 0)`). -/
theorem dist_sq_expansion_midpoint6_sharp (m : Fin 2 → ℝ) :
    ¬ ∃ C r : ℝ, 0 < r ∧ ∀ Δ : Fin 2 → ℝ, ‖Δ‖ ≤ r →
      |dist cubicShear univ (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2
        - midJet cubicShear m Δ| ≤ C * ‖Δ‖ ^ 7 := by
  rintro ⟨C, r, hr, h⟩
  refine not_pow_le_pow_succ (a := 1 / 576) (by norm_num) 6 ⟨C, r, hr, fun t ht => ?_⟩
  have h' := h ![t, 0] (by rw [norm_dir0]; exact ht)
  rw [norm_dir0, dist_sq_cubicShear_midpoint, add_sub_cancel_left] at h'
  simp only [Matrix.cons_val_zero] at h'
  calc |1 / 576 * t ^ 6| = |t ^ 6 / 576| := by congr 1; ring
    _ ≤ C * |t| ^ 7 := h'

/-- **Wrong model fails.** Without its quintic term the jet `distJet` does not give the
sixth-order expansion: on the cubic shear at a point with `x₀ ≠ 0` the remainder along
`w = (t, 0)` is `x₀ t⁵/6 + t⁶/36`, which is not `O(‖w‖⁶)`. -/
theorem distJet_cubicShear_not_sixth {x : Fin 2 → ℝ} (hx : x 0 ≠ 0) :
    ¬ ∃ C r : ℝ, 0 < r ∧ ∀ w : Fin 2 → ℝ, ‖w‖ ≤ r →
      |dist cubicShear univ x (x + w) ^ 2 - distJet cubicShear x w| ≤ C * ‖w‖ ^ 6 := by
  rintro ⟨C, r, hr, h⟩
  refine not_pow_le_pow_succ (a := x 0 / 6) (div_ne_zero hx (by norm_num)) 5
    ⟨C + 1 / 36, r, hr, fun t ht => ?_⟩
  have h' := h ![t, 0] (by rw [norm_dir0]; exact ht)
  have e : dist cubicShear univ x (x + ![t, 0]) ^ 2 - distJet cubicShear x ![t, 0]
      = x 0 / 6 * t ^ 5 + t ^ 6 / 36 := by
    rw [dist_sq_cubicShear_sixth, distJet5,
      quint_shearBy hasDerivAt_half_sq (fun s => hasDerivAt_id' s)
        (fun s => hasDerivAt_const s (1 : ℝ))]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [norm_dir0, e] at h'
  have h6 : |t ^ 6 / 36| = |t| ^ 6 / 36 := by rw [abs_div, abs_pow]; norm_num
  calc |x 0 / 6 * t ^ 5| = |(x 0 / 6 * t ^ 5 + t ^ 6 / 36) - t ^ 6 / 36| := by
        rw [add_sub_cancel_right]
    _ ≤ |x 0 / 6 * t ^ 5 + t ^ 6 / 36| + |t ^ 6 / 36| := abs_sub _ _
    _ ≤ C * |t| ^ 6 + |t| ^ 6 / 36 := add_le_add h' h6.le
    _ = (C + 1 / 36) * |t| ^ (5 + 1) := by ring

/-- The cubic shear is a Riemannian metric on the plane. -/
theorem isRiemMetric_cubicShear : IsRiemMetric cubicShear univ :=
  isRiemMetric_shearBy (by fun_prop)

/-- **Non-vacuity.** The hypotheses of `IsRiemMetric.exists_localJet3` hold for the cubic shear
and the closed unit ball. -/
theorem cubicShear_exists_localJet3 :
    ∃ B δ l : ℝ, ∀ x ∈ Metric.closedBall (0 : Fin 2 → ℝ) 1, LocalJet3 cubicShear univ x B δ l :=
  isRiemMetric_cubicShear.exists_localJet3 (isCompact_closedBall 0 1) (subset_univ _)

/-- **Non-vacuity.** The hypotheses of `IsRiemMetric.dist_sq_expansion6` hold for the cubic shear
and the closed unit ball, where the remainder is not zero (`dist_sq_cubicShear_sixth`). -/
theorem cubicShear_dist_sq_expansion6 :
    ∃ C r : ℝ, 0 < r ∧ ∀ x ∈ Metric.closedBall (0 : Fin 2 → ℝ) 1, ∀ w : Fin 2 → ℝ, ‖w‖ ≤ r →
      |dist cubicShear univ x (x + w) ^ 2 - distJet5 cubicShear x w| ≤ C * ‖w‖ ^ 6 :=
  isRiemMetric_cubicShear.dist_sq_expansion6 (isCompact_closedBall 0 1) (subset_univ _)

/-- **Non-vacuity.** The hypotheses of `IsRiemMetric.dist_sq_expansion_midpoint6` hold for the
cubic shear and the closed unit ball, where the remainder is not zero
(`dist_sq_cubicShear_midpoint`). -/
theorem cubicShear_dist_sq_expansion_midpoint6 :
    ∃ C r : ℝ, 0 < r ∧ ∀ m ∈ Metric.closedBall (0 : Fin 2 → ℝ) 1, ∀ Δ : Fin 2 → ℝ, ‖Δ‖ ≤ r →
      |dist cubicShear univ (m - (1 / 2 : ℝ) • Δ) (m + (1 / 2 : ℝ) • Δ) ^ 2
        - midJet cubicShear m Δ| ≤ C * ‖Δ‖ ^ 6 :=
  isRiemMetric_cubicShear.dist_sq_expansion_midpoint6 (isCompact_closedBall 0 1) (subset_univ _)

/-! ## Mathlib's Riemannian distance -/

section RiemannianDistance

open Manifold Bundle
open scoped Manifold

/-- The Euclidean metric on `ℝⁿ`, viewed as the open set `⊤`. -/
theorem isRiemMetric_euclid_top :
    IsRiemMetric (euclid (n := n)) ((⊤ : TopologicalSpace.Opens (Fin n → ℝ)) : Set _) :=
  isRiemMetric_euclid (⊤ : TopologicalSpace.Opens (Fin n → ℝ)).isOpen

/-- **Known value (Mathlib).** For the Euclidean metric on `ℝⁿ`, Mathlib's Riemannian distance
of our bundle is Mathlib's Riemannian distance of the inner product space
`EuclideanSpace ℝ (Fin n)` between the same points, i.e. the Euclidean distance. -/
theorem riemannianEDist_euclid (x y : (⊤ : TopologicalSpace.Opens (Fin n → ℝ))) :
    letI := (isRiemMetric_euclid_top (n := n)).riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y
      = riemannianEDist 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          (WithLp.toLp 2 (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin n))
          (WithLp.toLp 2 (y : Fin n → ℝ)) := by
  let := isRiemMetric_euclid_top (n := n).riemannianBundle
  rw [isRiemMetric_euclid_top.riemannianEDist_eq_of_isPreconnected isPreconnected_univ,
    TopologicalSpace.Opens.coe_top, dist_euclid isOpen_univ convex_univ (mem_univ _) (mem_univ _),
    ← IsRiemannianManifold.out, edist_dist, EuclideanSpace.dist_eq]
  congr 2
  simp only [eNormSq, dotProduct, Real.dist_eq, sq_abs, Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The quadratic shear on the plane, viewed as the open set `⊤`. -/
theorem isRiemMetric_shear_top :
    IsRiemMetric shear ((⊤ : TopologicalSpace.Opens (Fin 2 → ℝ)) : Set _) :=
  isRiemMetric_shear

/-- **Known value.** For the quadratic shear, Mathlib's Riemannian distance from `0` to `(1, 0)`
is `√5/2`: the shear map sends the two points to `0` and `(1, 1/2)`. -/
theorem riemannianEDist_shear :
    letI := isRiemMetric_shear_top.riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin 2 → ℝ) (⟨0, mem_univ _⟩ : (⊤ : TopologicalSpace.Opens (Fin 2 → ℝ)))
      ⟨![1, 0], mem_univ _⟩ = ENNReal.ofReal (√5 / 2) := by
  let := isRiemMetric_shear_top.riemannianBundle
  rw [isRiemMetric_shear_top.riemannianEDist_eq_of_isPreconnected isPreconnected_univ]
  congr 1
  have h2 : dist shear univ 0 ![1, 0] ^ 2 = (√5 / 2) ^ 2 := by
    rw [dist_sq_shear_eq, div_pow, Real.sq_sqrt (by norm_num)]
    simp
    norm_num
  exact (pow_left_inj₀ (dist_nonneg (g := shear) (U := univ)) (by positivity) two_ne_zero).mp h2

/-- **Wrong input gives a different answer.** The Euclidean metric gives Mathlib's Riemannian
distance `1` between the same two points, not the value `√5/2` of the shear. -/
theorem riemannianEDist_shear_ne_euclid :
    (letI := isRiemMetric_shear_top.riemannianBundle;
      riemannianEDist 𝓘(ℝ, Fin 2 → ℝ)
        (⟨0, mem_univ _⟩ : (⊤ : TopologicalSpace.Opens (Fin 2 → ℝ))) ⟨![1, 0], mem_univ _⟩) ≠
    (letI := (isRiemMetric_euclid_top (n := 2)).riemannianBundle;
      riemannianEDist 𝓘(ℝ, Fin 2 → ℝ)
        (⟨0, mem_univ _⟩ : (⊤ : TopologicalSpace.Opens (Fin 2 → ℝ))) ⟨![1, 0], mem_univ _⟩) := by
  rw [riemannianEDist_shear, riemannianEDist_euclid, ← IsRiemannianManifold.out, edist_dist,
    EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two]
  intro h
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

/-- The punctured line `{x ∈ ℝ¹ | x₀ ≠ 0}`, an open set with two components. -/
def puncturedLine : TopologicalSpace.Opens (Fin 1 → ℝ) :=
  ⟨{x | x 0 ≠ 0}, isOpen_ne_fun (continuous_apply 0) continuous_const⟩

/-- `-1` lies in the punctured line. -/
theorem neg_one_mem_puncturedLine : (fun _ => -1 : Fin 1 → ℝ) ∈ puncturedLine :=
  show (-1 : ℝ) ≠ 0 by norm_num

/-- `1` lies in the punctured line. -/
theorem one_mem_puncturedLine : (fun _ => 1 : Fin 1 → ℝ) ∈ puncturedLine :=
  show (1 : ℝ) ≠ 0 by norm_num

/-- No admissible curve in the punctured line joins `-1` and `1`: by the intermediate value
theorem every continuous curve from `-1` to `1` passes through `0`. -/
theorem not_exists_isAdmissible_puncturedLine :
    ¬ ∃ c, IsAdmissible (puncturedLine : Set (Fin 1 → ℝ)) c (fun _ => -1) (fun _ => 1) := by
  rintro ⟨c, hc⟩
  have hcont : ContinuousOn (fun t => c t 0) (Icc 0 1) :=
    ((continuous_apply 0).comp hc.smooth.continuous).continuousOn
  have h0 : (0 : ℝ) ∈ Icc (c 0 0) (c 1 0) := by
    rw [hc.start, hc.finish]
    constructor <;> norm_num
  obtain ⟨t, ht, hct⟩ := intermediate_value_Icc zero_le_one hcont h0
  exact hc.mem t ht hct

/-- **The hypothesis of `IsRiemMetric.riemannianEDist_eq` is needed.** On the punctured line no
admissible curve joins `-1` and `1`, so Mathlib's Riemannian distance is `⊤` while `dist` is
the junk value `0`. -/
theorem riemannianEDist_puncturedLine :
    letI := (isRiemMetric_euclid puncturedLine.isOpen).riemannianBundle
    riemannianEDist 𝓘(ℝ, Fin 1 → ℝ) (⟨_, neg_one_mem_puncturedLine⟩ : puncturedLine)
        ⟨_, one_mem_puncturedLine⟩ = ⊤ ∧
      dist euclid (puncturedLine : Set (Fin 1 → ℝ)) (fun _ => -1) (fun _ => 1) = 0 := by
  let := (isRiemMetric_euclid puncturedLine.isOpen).riemannianBundle
  have h := (isRiemMetric_euclid puncturedLine.isOpen).riemannianEDist_eq_top
    (x := ⟨_, neg_one_mem_puncturedLine⟩) (y := ⟨_, one_mem_puncturedLine⟩)
    not_exists_isAdmissible_puncturedLine
  refine ⟨h, ?_⟩
  rw [(isRiemMetric_euclid puncturedLine.isOpen).dist_eq_toReal_riemannianEDist
    ⟨_, neg_one_mem_puncturedLine⟩ ⟨_, one_mem_puncturedLine⟩, h, ENNReal.toReal_top]

end RiemannianDistance

end Lightlike.Geodesic
