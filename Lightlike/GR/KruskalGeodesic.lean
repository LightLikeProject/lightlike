import Lightlike.GR.KruskalManifold
import Lightlike.Spacetime.GeodesicMomentum

/-!
# Geodesics of the Kruskal manifold: the equations of motion

Gap row G1-020, toward maximality. In the global chart `(T, x)` of the Kruskal manifold, the quadratic form of
the metric is `Q(z, v) = -h v₀² + ((h - r²)/|x|⁴) (x·v)² + (r²/|x|²) |v|²` (`quad_kruskalC`), and its derivative
along a line `z + s K` is computed in closed form (`contraction_kruskalC`). With Noether's formula
(`IsGeodesicOn.hasDerivAt_noether`) this gives the equations of motion without Christoffel symbols.
-/

open Matrix Real Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- The derivative of `kG` at `s > -1` is `4M² e^{-r/2M}/r`, `r = kG s`. -/
def dkG (r : ℝ) : ℝ := 4 * M ^ 2 * exp (-(r / (2 * M))) / r

/-- The derivative of `kG`, the inverse of `kF`, at `s > -1` is `dkG M (kG M s)`. -/
lemma hasDerivAt_kG (hM : 0 < M) {s : ℝ} (hs : -1 < s) : HasDerivAt (kG M) (dkG M (kG M s)) s := by
  set r := kG M s with hrdef
  have hr : 0 < r := kG_pos M hM hs
  have hG : HasDerivAt (kG M) (deriv (kG M) s) s :=
    ((contDiffAt_kG M hM hs).differentiableAt (by simp)).hasDerivAt
  have hcomp : HasDerivAt (kF M ∘ kG M)
      (r / (4 * M ^ 2) * exp (r / (2 * M)) * deriv (kG M) s) s :=
    (hasDerivAt_kF M hM.ne' r).comp s hG
  have hid : HasDerivAt (kF M ∘ kG M) 1 s := by
    refine (hasDerivAt_id s).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
    exact kF_kG M hM hx
  have h1 := hcomp.unique hid
  have hc0 : r / (4 * M ^ 2) * exp (r / (2 * M)) ≠ 0 := kF_deriv_ne M hM hr
  have h2 : deriv (kG M) s = dkG M r := by
    unfold dkG
    rw [Real.exp_neg]
    have he : exp (r / (2 * M)) ≠ 0 := (exp_pos _).ne'
    field_simp
    field_simp at h1
    linarith
  rw [← h2]
  exact hG

/-- The derivative of `kh`. -/
def dkh (r : ℝ) : ℝ := -(kh M r * (1 / r + 1 / (2 * M)))

/-- The derivative of `kh` at `r > 0` is `dkh M r = -kh(r) (1/r + 1/(2M))`. -/
lemma hasDerivAt_kh (hM : 0 < M) {r : ℝ} (hr : 0 < r) : HasDerivAt (kh M) (dkh M r) r := by
  have h1 : HasDerivAt (fun r : ℝ => 32 * M ^ 3 / r) (-(32 * M ^ 3) / r ^ 2) r := by
    have := (hasDerivAt_const r (32 * M ^ 3)).fun_div (hasDerivAt_id' r) hr.ne'
    simpa using this
  have h2 : HasDerivAt (fun r : ℝ => exp (-(r / (2 * M)))) (exp (-(r / (2 * M))) * -(1 / (2 * M))) r :=
    (((hasDerivAt_id' r).div_const (2 * M)).neg).exp
  refine (h1.mul h2).congr_deriv ?_
  simp only [dkh, kh]
  field_simp
  ring

/-- The Euclidean product of the space parts. -/
def xdot (z v : Fin 4 → ℝ) : ℝ := z 1 * v 1 + z 2 * v 2 + z 3 * v 3

/-- The quadratic form of the Kruskal metric in the global chart. -/
def kQ (z v : Fin 4 → ℝ) : ℝ :=
  -kh M (krC M z) * v 0 ^ 2 + (kh M (krC M z) - krC M z ^ 2) / rhoSq z ^ 2 * xdot z v ^ 2 +
    krC M z ^ 2 / rhoSq z * xdot v v

lemma quad_kruskalC (z v : Fin 4 → ℝ) :
    ∑ m, ∑ l, kruskalCMetric M z m l * v m * v l = kQ M z v := by
  simp [Fin.sum_univ_four, kruskalCMetric, kQ, xdot]
  ring

/-- The momenta `p_k = Σⱼ g_{kj} vʲ` in the global chart. -/
lemma momentum_kruskalC_zero (z v : Fin 4 → ℝ) :
    ∑ j, kruskalCMetric M z 0 j * v j = -kh M (krC M z) * v 0 := by
  simp [Fin.sum_univ_four, kruskalCMetric]

/-- The derivative of the quadratic form along curves of the data `(h, r, |x|², x·v)`. -/
lemma hasDerivAt_quadForm {h r ρ q : ℝ → ℝ} {h' r' ρ' q' : ℝ} (hh : HasDerivAt h h' 0)
    (hr : HasDerivAt r r' 0) (hρ : HasDerivAt ρ ρ' 0) (hq : HasDerivAt q q' 0) (hρ0 : ρ 0 ≠ 0)
    (a b : ℝ) :
    HasDerivAt (fun s => -h s * a + (h s - r s ^ 2) / ρ s ^ 2 * q s ^ 2 + r s ^ 2 / ρ s * b)
      (-h' * a + (((h' - 2 * r 0 * r') * ρ 0 ^ 2 - (h 0 - r 0 ^ 2) * (2 * ρ 0 * ρ')) / (ρ 0 ^ 2) ^ 2 * q 0 ^ 2 +
        (h 0 - r 0 ^ 2) / ρ 0 ^ 2 * (2 * q 0 * q')) +
        (2 * r 0 * r' * ρ 0 - r 0 ^ 2 * ρ') / ρ 0 ^ 2 * b) 0 := by
  have h1 := (hh.neg.mul_const a)
  have hr2 : HasDerivAt (fun s => r s ^ 2) (2 * r 0 * r') 0 := by
    simpa using hr.fun_pow 2
  have hρ2 : HasDerivAt (fun s => ρ s ^ 2) (2 * ρ 0 * ρ') 0 := by
    simpa using hρ.fun_pow 2
  have hq2 : HasDerivAt (fun s => q s ^ 2) (2 * q 0 * q') 0 := by
    simpa using hq.fun_pow 2
  have h2 := ((hh.sub hr2).div hρ2 (pow_ne_zero 2 hρ0)).mul hq2
  have h3 := (hr2.div hρ hρ0).mul_const b
  exact (h1.add h2).add h3

/-- The derivative of the radius along the line `z + s K`. -/
def krLine (z K : Fin 4 → ℝ) : ℝ :=
  dkG M (krC M z) * (log (rhoSq z) * (xdot z K / rhoSq z) - 2 * z 0 * K 0)

/-- The derivative of `Q(z + s K, v)` at `s = 0`, in closed form. -/
def kQline (z K v : Fin 4 → ℝ) : ℝ :=
  -(dkh M (krC M z) * krLine M z K) * v 0 ^ 2 +
    (((dkh M (krC M z) * krLine M z K - 2 * krC M z * krLine M z K) * rhoSq z ^ 2 -
        (kh M (krC M z) - krC M z ^ 2) * (2 * rhoSq z * (2 * xdot z K))) / (rhoSq z ^ 2) ^ 2 * xdot z v ^ 2 +
      (kh M (krC M z) - krC M z ^ 2) / rhoSq z ^ 2 * (2 * xdot z v * xdot K v)) +
    (2 * krC M z * krLine M z K * rhoSq z - krC M z ^ 2 * (2 * xdot z K)) / rhoSq z ^ 2 * xdot v v

lemma hasDerivAt_kQ_line (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalC) (K v : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => kQ M (z + s • K) v) (kQline M z K v) 0 := by
  have h0 : z + (0 : ℝ) • K = z := by simp
  have hco : ∀ i : Fin 4, HasDerivAt (fun s : ℝ => (z + s • K) i) (K i) 0 := fun i => by
    have : HasDerivAt (fun s : ℝ => z i + s * K i) (K i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (K i)).const_add (z i)
    simpa using this
  have hρ : HasDerivAt (fun s : ℝ => rhoSq (z + s • K)) (2 * xdot z K) 0 := by
    have := (((hco 1).fun_pow 2).fun_add ((hco 2).fun_pow 2)).fun_add ((hco 3).fun_pow 2)
    refine this.congr_deriv ?_
    have e : (2 : ℕ) - 1 = 1 := rfl
    simp only [h0, e, pow_one, Nat.cast_ofNat, xdot]
    ring
  have hρ0 : rhoSq (z + (0 : ℝ) • K) ≠ 0 := by rw [h0]; exact hz.1.ne'
  have hs : HasDerivAt (fun s : ℝ => sC (z + s • K))
      (log (rhoSq z) * (xdot z K / rhoSq z) - 2 * z 0 * K 0) 0 := by
    have hl : HasDerivAt (fun s : ℝ => 1 / 2 * log (rhoSq (z + s • K)))
        (1 / 2 * (2 * xdot z K / rhoSq z)) 0 := by
      have := (hρ.log hρ0).const_mul (1 / 2 : ℝ)
      simpa only [h0] using this
    have := (hl.fun_pow 2).fun_sub ((hco 0).fun_pow 2)
    refine this.congr_deriv ?_
    have e : (2 : ℕ) - 1 = 1 := rfl
    simp only [h0, e, pow_one, Nat.cast_ofNat]
    ring
  have hr : HasDerivAt (fun s : ℝ => krC M (z + s • K))
      (dkG M (krC M z) * (log (rhoSq z) * (xdot z K / rhoSq z) - 2 * z 0 * K 0)) 0 := by
    have hG : HasDerivAt (kG M) (dkG M (kG M (sC z))) (sC (z + (0 : ℝ) • K)) := by
      rw [h0]; exact hasDerivAt_kG M hM hz.2
    exact hG.comp 0 hs
  have hh : HasDerivAt (fun s : ℝ => kh M (krC M (z + s • K)))
      (dkh M (krC M z) * (dkG M (krC M z) * (log (rhoSq z) * (xdot z K / rhoSq z) - 2 * z 0 * K 0))) 0 := by
    have hk : HasDerivAt (kh M) (dkh M (krC M z)) (krC M (z + (0 : ℝ) • K)) := by
      rw [h0]; exact hasDerivAt_kh M hM (krC_pos M hM hz)
    exact hk.comp 0 hr
  have hq : HasDerivAt (fun s : ℝ => xdot (z + s • K) v) (xdot K v) 0 := by
    have := (((hco 1).mul_const (v 1)).add ((hco 2).mul_const (v 2))).add ((hco 3).mul_const (v 3))
    exact this
  have := hasDerivAt_quadForm hh hr hρ hq hρ0 (v 0 ^ 2) (xdot v v)
  simpa only [kQ, kQline, krLine, h0] using this

/-- **The contraction `Σ_k K^k ∂_k g(v, v)` of the Kruskal metric**, in closed form. -/
theorem contraction_kruskalC (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalC) (K v : Fin 4 → ℝ) :
    ∑ k, K k * ∑ m, ∑ l, pd k (fun y => kruskalCMetric M y m l) z * v m * v l = kQline M z K v := by
  have h1 := Lightlike.Geodesic.hasDerivAt_quadratic_line (isCoordMetric_kruskalC M hM) hz K v
  simp only [quad_kruskalC] at h1
  exact h1.unique (hasDerivAt_kQ_line M hM hz K v)

/-- `X' = (x·v)/|x|²`, the velocity of `X = log |x|`. -/
def kXd (z v : Fin 4 → ℝ) : ℝ := xdot z v / rhoSq z

/-- The squared angular velocity `|v|²/|x|² - X'²`. -/
def kOm (z v : Fin 4 → ℝ) : ℝ := xdot v v / rhoSq z - kXd z v ^ 2

/-- The common factor of the equations of motion: `h'(r) (X'² - T'²) + 2 r ω`. -/
def kXi (z v : Fin 4 → ℝ) : ℝ :=
  dkh M (krC M z) * (kXd z v ^ 2 - v 0 ^ 2) + 2 * krC M z * kOm z v

section motion

open Lightlike.Geodesic

variable {M} {c w : ℝ → Fin 4 → ℝ} {I : Set ℝ}

/-- **The equation of motion of `T`**: `(h T')' = T G'(s) Ξ`. -/
theorem kruskalC_hasDerivAt_pT (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => kh M (krC M (c s)) * w s 0)
      (c t 0 * dkG M (krC M (c t)) * kXi M (c t) (w t)) t := by
  have hK : HasDerivAt (fun _ : ℝ => (Pi.single 0 1 : Fin 4 → ℝ)) 0 t := hasDerivAt_const t _
  have h1 := (hgeo.hasDerivAt_noether (isCoordMetric_kruskalC M hM) ht hct hK).neg
  have hfun : (fun s => kh M (krC M (c s)) * w s 0) =
      -fun s => ∑ k, (Pi.single 0 1 : Fin 4 → ℝ) k * ∑ j, kruskalCMetric M (c s) k j * w s j := by
    funext s
    simp [Fin.sum_univ_four, kruskalCMetric]
  rw [hfun]
  refine h1.congr_deriv ?_
  rw [contraction_kruskalC M hM hct]
  have hρ : rhoSq (c t) ≠ 0 := hct.1.ne'
  simp only [kQline, krLine, kXi, kOm, kXd, xdot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add,
    Pi.single_eq_same, Pi.single_eq_of_ne (show (1 : Fin 4) ≠ 0 by decide),
    Pi.single_eq_of_ne (show (2 : Fin 4) ≠ 0 by decide), Pi.single_eq_of_ne (show (3 : Fin 4) ≠ 0 by decide)]
  field_simp
  ring

/-- **The equation of motion of `X`**: `(h X')' = X G'(s) Ξ`, `X = ½ log |x|²`. -/
theorem kruskalC_hasDerivAt_pX (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => kh M (krC M (c s)) * kXd (c s) (w s))
      (1 / 2 * log (rhoSq (c t)) * dkG M (krC M (c t)) * kXi M (c t) (w t)) t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have hK : HasDerivAt (fun s : ℝ => ![0, c s 1, c s 2, c s 3]) ![0, w t 1, w t 2, w t 3] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_const t (0 : ℝ)
    · exact hpos 1
    · exact hpos 2
    · exact hpos 3
  have h1 := hgeo.hasDerivAt_noether (isCoordMetric_kruskalC M hM) ht hct hK
  have hev : ∀ᶠ s in 𝓝 t, c s ∈ kruskalC :=
    (hgeo.pos t ht).continuousAt.preimage_mem_nhds (isOpen_kruskalC.mem_nhds hct)
  have hfun : (fun s => ∑ k, (![0, c s 1, c s 2, c s 3] : Fin 4 → ℝ) k *
        ∑ j, kruskalCMetric M (c s) k j * w s j) =ᶠ[𝓝 t]
      fun s => kh M (krC M (c s)) * kXd (c s) (w s) := by
    filter_upwards [hev] with s hs
    have hρ : rhoSq (c s) ≠ 0 := hs.1.ne'
    have hρd : rhoSq (c s) = c s 1 ^ 2 + c s 2 ^ 2 + c s 3 ^ 2 := rfl
    simp only [Fin.sum_univ_four, kruskalCMetric, kXd, xdot]
    simp
    field_simp
    rw [hρd]
    ring
  refine (h1.congr_of_eventuallyEq hfun.symm).congr_deriv ?_
  rw [contraction_kruskalC M hM hct]
  have hρ : rhoSq (c t) ≠ 0 := hct.1.ne'
  have hρd : rhoSq (c t) = c t 1 ^ 2 + c t 2 ^ 2 + c t 3 ^ 2 := rfl
  simp only [Fin.sum_univ_four, kruskalCMetric, kQline, krLine, kXi, kOm, kXd, xdot]
  simp
  field_simp
  rw [hρd]
  ring

/-- **The angular momentum is conserved**: for every axis `n`, `(r²/|x|²) n·(x × v)` is constant. -/
theorem kruskalC_hasDerivAt_angular (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) (n : Fin 4 → ℝ) :
    HasDerivAt (fun s => krC M (c s) ^ 2 / rhoSq (c s) *
      (n 1 * (c s 2 * w s 3 - c s 3 * w s 2) + n 2 * (c s 3 * w s 1 - c s 1 * w s 3) +
        n 3 * (c s 1 * w s 2 - c s 2 * w s 1))) 0 t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have hK : HasDerivAt (fun s : ℝ => ![0, n 2 * c s 3 - n 3 * c s 2, n 3 * c s 1 - n 1 * c s 3,
        n 1 * c s 2 - n 2 * c s 1])
      ![0, n 2 * w t 3 - n 3 * w t 2, n 3 * w t 1 - n 1 * w t 3, n 1 * w t 2 - n 2 * w t 1] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_const t (0 : ℝ)
    · exact ((hpos 3).const_mul (n 2)).sub ((hpos 2).const_mul (n 3))
    · exact ((hpos 1).const_mul (n 3)).sub ((hpos 3).const_mul (n 1))
    · exact ((hpos 2).const_mul (n 1)).sub ((hpos 1).const_mul (n 2))
  have h1 := hgeo.hasDerivAt_noether (isCoordMetric_kruskalC M hM) ht hct hK
  have hfun : (fun s => ∑ k, (![0, n 2 * c s 3 - n 3 * c s 2, n 3 * c s 1 - n 1 * c s 3,
        n 1 * c s 2 - n 2 * c s 1] : Fin 4 → ℝ) k * ∑ j, kruskalCMetric M (c s) k j * w s j) =
      fun s => krC M (c s) ^ 2 / rhoSq (c s) *
      (n 1 * (c s 2 * w s 3 - c s 3 * w s 2) + n 2 * (c s 3 * w s 1 - c s 1 * w s 3) +
        n 3 * (c s 1 * w s 2 - c s 2 * w s 1)) := by
    funext s
    simp only [Fin.sum_univ_four, kruskalCMetric]
    simp
    ring
  rw [hfun] at h1
  refine h1.congr_deriv ?_
  rw [contraction_kruskalC M hM hct]
  simp only [Fin.sum_univ_four, kruskalCMetric, kQline, krLine, xdot]
  simp
  ring

end motion

end Lightlike
