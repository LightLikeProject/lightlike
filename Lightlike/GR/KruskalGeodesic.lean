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

end Lightlike
