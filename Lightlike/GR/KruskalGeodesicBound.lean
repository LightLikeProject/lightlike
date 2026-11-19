import Lightlike.GR.KruskalGeodesic
import Mathlib.Analysis.ODE.Gronwall

/-!
# Geodesics of the Kruskal manifold: constants of motion and the radial equation

Gap row G1-020, toward maximality. Along a geodesic of the Kruskal manifold in the global chart `(T, x)`, with
`X = log |x|`, `h = kh r`:

* the boost charge `h (T X' - X T')`, the squared angular momentum `r⁴ ω` and `g(w, w)` are constant
  (`kruskalC_hasDerivAt_boost`, `kruskalC_hasDerivAt_L2`, `kruskalC_hasDerivAt_kQ`);
* the radius obeys `r' = 2 G'(s) (X X' - T T')` (`kruskalC_hasDerivAt_r`).
-/

open Matrix Real Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

open Lightlike.Geodesic

variable {M : ℝ} {c w : ℝ → Fin 4 → ℝ} {I : Set ℝ}

/-- The quadratic form in terms of `T'`, `X'` and the angular velocity. -/
lemma kQ_eq (z v : Fin 4 → ℝ) (hρ : rhoSq z ≠ 0) :
    kQ M z v = kh M (krC M z) * (kXd z v ^ 2 - v 0 ^ 2) + krC M z ^ 2 * kOm z v := by
  simp only [kQ, kOm, kXd]
  field_simp
  ring

/-- `X = ½ log |x|²` has velocity `X' = (x·w)/|x|²`. -/
lemma kruskalC_hasDerivAt_X (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => 1 / 2 * log (rhoSq (c s))) (kXd (c t) (w t)) t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have hρ : HasDerivAt (fun s => rhoSq (c s)) (2 * xdot (c t) (w t)) t := by
    have := (((hpos 1).fun_pow 2).fun_add ((hpos 2).fun_pow 2)).fun_add ((hpos 3).fun_pow 2)
    refine this.congr_deriv ?_
    have e : (2 : ℕ) - 1 = 1 := rfl
    simp only [e, pow_one, Nat.cast_ofNat, xdot]
    ring
  refine ((hρ.log hct.1.ne').const_mul (1 / 2 : ℝ)).congr_deriv ?_
  simp only [kXd]
  ring

/-- **The radial velocity**: `r' = 2 G'(s) (X X' - T T')`. -/
lemma kruskalC_hasDerivAt_r (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => krC M (c s))
      (dkG M (krC M (c t)) * (2 * (1 / 2 * log (rhoSq (c t))) * kXd (c t) (w t) - 2 * c t 0 * w t 0)) t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have hs : HasDerivAt (fun s => sC (c s))
      (2 * (1 / 2 * log (rhoSq (c t))) * kXd (c t) (w t) - 2 * c t 0 * w t 0) t := by
    have := ((kruskalC_hasDerivAt_X hgeo ht hct).fun_pow 2).fun_sub ((hpos 0).fun_pow 2)
    refine this.congr_deriv ?_
    have e : (2 : ℕ) - 1 = 1 := rfl
    simp only [e, pow_one, Nat.cast_ofNat]
  exact (hasDerivAt_kG M hM hct.2).comp t hs

/-- **The boost charge `h (T X' - X T')` is conserved.** -/
theorem kruskalC_hasDerivAt_boost (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => c s 0 * (kh M (krC M (c s)) * kXd (c s) (w s)) -
      1 / 2 * log (rhoSq (c s)) * (kh M (krC M (c s)) * w s 0)) 0 t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have h1 := ((hpos 0).mul (kruskalC_hasDerivAt_pX hM hgeo ht hct)).sub
    ((kruskalC_hasDerivAt_X hgeo ht hct).mul (kruskalC_hasDerivAt_pT hM hgeo ht hct))
  refine h1.congr_deriv ?_
  ring

/-- The squared angular momentum `r⁴ ω`. -/
def kL2 (M : ℝ) (z v : Fin 4 → ℝ) : ℝ := krC M z ^ 4 * kOm z v

/-- **The squared angular momentum is conserved.** -/
theorem kruskalC_hasDerivAt_L2 (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => kL2 M (c s) (w s)) 0 t := by
  have h1 : HasDerivAt (fun s => krC M (c s) ^ 2 / rhoSq (c s) * (c s 2 * w s 3 - c s 3 * w s 2)) 0 t := by
    simpa using kruskalC_hasDerivAt_angular hM hgeo ht hct ![0, 1, 0, 0]
  have h2 : HasDerivAt (fun s => krC M (c s) ^ 2 / rhoSq (c s) * (c s 3 * w s 1 - c s 1 * w s 3)) 0 t := by
    simpa using kruskalC_hasDerivAt_angular hM hgeo ht hct ![0, 0, 1, 0]
  have h3 : HasDerivAt (fun s => krC M (c s) ^ 2 / rhoSq (c s) * (c s 1 * w s 2 - c s 2 * w s 1)) 0 t := by
    simpa using kruskalC_hasDerivAt_angular hM hgeo ht hct ![0, 0, 0, 1]
  have hsum := ((h1.fun_pow 2).fun_add (h2.fun_pow 2)).fun_add (h3.fun_pow 2)
  have hev : ∀ᶠ s in 𝓝 t, c s ∈ kruskalC :=
    (hgeo.pos t ht).continuousAt.preimage_mem_nhds (isOpen_kruskalC.mem_nhds hct)
  have hfun : (fun s => kL2 M (c s) (w s)) =ᶠ[𝓝 t] fun s =>
      (krC M (c s) ^ 2 / rhoSq (c s) * (c s 2 * w s 3 - c s 3 * w s 2)) ^ 2 +
        (krC M (c s) ^ 2 / rhoSq (c s) * (c s 3 * w s 1 - c s 1 * w s 3)) ^ 2 +
        (krC M (c s) ^ 2 / rhoSq (c s) * (c s 1 * w s 2 - c s 2 * w s 1)) ^ 2 := by
    filter_upwards [hev] with s hs
    have hρ : rhoSq (c s) ≠ 0 := hs.1.ne'
    have hρd : rhoSq (c s) = c s 1 ^ 2 + c s 2 ^ 2 + c s 3 ^ 2 := rfl
    simp only [kL2, kOm, kXd, xdot]
    field_simp
    rw [hρd]
    ring
  refine (hsum.congr_of_eventuallyEq hfun).congr_deriv ?_
  simp

/-- **`g(w, w)` is conserved**, in the form of the quadratic form `kQ`. -/
theorem kruskalC_hasDerivAt_kQ (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => kQ M (c s) (w s)) 0 t := by
  have h1 := hgeo.hasDerivAt_speed (isCoordMetric_kruskalC M hM) ht hct
  have hfun : (fun s => kQ M (c s) (w s)) = fun s => normSq (kruskalCMetric M) (c s) (w s) := by
    funext s
    rw [← quad_kruskalC]
    simp only [normSq, dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hfun]
  exact h1

end Lightlike
