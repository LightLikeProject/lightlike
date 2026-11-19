import Lightlike.Geodesic.Radial

/-!
# The lowered geodesic equation and the derivative of the metric pairing

Two computations for the Gauss lemma, for a coordinate metric `g` on `U`:

* `Lightlike.Geodesic.lowered_accel_add`: the geodesic equation with the index lowered,
  `g_{ij} a^i + (∂_k g_{ij}) v^k v^i = ½ (∂_j g_{kl}) v^k v^l` with `a = -Γ(v, v)` the
  acceleration. Along a geodesic this is the Euler–Lagrange equation
  `d/dt (g_{ij} v^i) = ½ (∂_j g_{kl}) v^k v^l` of the energy.
* `Lightlike.Geodesic.hasDerivAt_pairing`: the derivative of `s ↦ g(γ s)(a s, b s)`.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The lowered geodesic equation**: at a point `y ∈ U` and for a velocity `v`,
`∑ i, g_{ij} a^i + ∑ i k, v^k (∂_k g_{ij}) v^i = ½ ∑ k l, (∂_j g_{kl}) v^k v^l`,
where `a = accel g y v` is the acceleration of the geodesic through `y` with velocity `v`. -/
theorem lowered_accel_add (hg : Lightlike.IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (v : Fin n → ℝ) (j : Fin n) :
    ∑ i, g y i j * accel g y v i +
        ∑ i, (∑ k, v k * Lightlike.pd k (fun z => g z i j) y) * v i =
      (1 / 2) * ∑ k, ∑ l, Lightlike.pd j (fun z => g z k l) y * v k * v l := by
  have hsym : ∀ i, g y i j = g y j i := fun i => by
    have := congrFun (congrFun (hg.symm y hy) j) i
    simpa [Matrix.transpose_apply] using this
  have hlow : ∑ i, g y i j * accel g y v i =
      -∑ k, ∑ l, Lightlike.christoffelFirst g j k l y * v k * v l := by
    simp only [accel, mul_neg, Finset.sum_neg_distrib, neg_inj]
    simp only [hsym, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hg.lower_christoffel hy j k l, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  set D : Fin n → Fin n → Fin n → ℝ := fun k i l => Lightlike.pd k (fun z => g z i l) y with hD
  have hDs : ∀ k i l, D k i l = D k l i := fun k i l => by
    simp only [hD]
    rw [hg.pd_eq_christoffelFirst hy k i l, hg.pd_eq_christoffelFirst hy k l i, add_comm]
  set A : ℝ := ∑ k, ∑ l, D k j l * v k * v l with hA
  set C : ℝ := ∑ k, ∑ l, D j k l * v k * v l with hC
  have hB : ∑ k, ∑ l, D l j k * v k * v l = A := by
    rw [hA, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hsecond : ∑ i, (∑ k, v k * D k i j) * v i = A := by
    rw [hA, Finset.sum_comm]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hDs l k j]; ring
  have hfirst : ∑ k, ∑ l, Lightlike.christoffelFirst g j k l y * v k * v l =
      (1 / 2) * (A + A - C) := by
    have hterm : ∀ k l, Lightlike.christoffelFirst g j k l y * v k * v l =
        (1 / 2) * (D k j l * v k * v l) + (1 / 2) * (D l j k * v k * v l) -
          (1 / 2) * (D j k l * v k * v l) := fun k l => by
      simp only [Lightlike.christoffelFirst, hD]; ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hB]
    ring
  rw [hlow, hfirst]
  show -((1 / 2) * (A + A - C)) + ∑ i, (∑ k, v k * D k i j) * v i = (1 / 2) * C
  rw [hsecond]
  ring

/-- **The derivative of the metric pairing along curves**: for curves `γ`, `a`, `b` with
derivatives `γ'`, `a'`, `b'` at `s`, the function `s ↦ ∑ i j, a^i g_{ij}(γ) b^j` has derivative
`∑ i j, (a'^i g_{ij} b^j + a^i ((∑ k, γ'^k ∂_k g_{ij}) b^j + g_{ij} b'^j))`. -/
theorem hasDerivAt_pairing {γ a b : ℝ → Fin n → ℝ} {γ' a' b' : Fin n → ℝ} {s : ℝ}
    (hdiff : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) (γ s)) (hγ : HasDerivAt γ γ' s)
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun s => ∑ i, ∑ j, a s i * (g (γ s) i j * b s j))
      (∑ i, ∑ j, (a' i * (g (γ s) i j * b s j) +
        a s i * ((∑ k, γ' k * Lightlike.pd k (fun y => g y i j) (γ s)) * b s j +
          g (γ s) i j * b' j))) s := by
  have hgij : ∀ i j, HasDerivAt (fun s => g (γ s) i j)
      (∑ k, γ' k * Lightlike.pd k (fun y => g y i j) (γ s)) s :=
    fun i j => hasDerivAt_comp_pd (hdiff i j) hγ
  have hai : ∀ i, HasDerivAt (fun s => a s i) (a' i) s := fun i => hasDerivAt_pi.mp ha i
  have hbi : ∀ i, HasDerivAt (fun s => b s i) (b' i) s := fun i => hasDerivAt_pi.mp hb i
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hai i).mul ((hgij i j).mul (hbi j))
  refine hd.congr_deriv ?_
  simp only [Pi.mul_apply]

/-- The algebraic identity behind the Gauss lemma: with `G` symmetric and the lowered geodesic
equation `hE` for the velocity `a` and acceleration `acc`, the derivative of `g(a, b)` along the
geodesic (for a variation field `b` with derivative `c`) is half the derivative of `g(a, a)` in
the direction of the variation. -/
theorem gauss_algebra (G : Fin n → Fin n → ℝ) (D : Fin n → Fin n → Fin n → ℝ)
    (acc a b c : Fin n → ℝ) (hsym : ∀ i j, G i j = G j i)
    (hE : ∀ j, ∑ i, G i j * acc i + ∑ i, (∑ k, a k * D k i j) * a i =
      (1 / 2) * ∑ k, ∑ l, D j k l * a k * a l) :
    ∑ i, ∑ j, (acc i * (G i j * b j) + a i * ((∑ k, a k * D k i j) * b j + G i j * c j)) =
      (1 / 2) * ∑ i, ∑ j, (c i * (G i j * a j) +
        a i * ((∑ k, b k * D k i j) * a j + G i j * c j)) := by
  set Q : ℝ := ∑ i, ∑ j, a i * (G i j * c j) with hQ
  set S : Fin n → ℝ := fun j => ∑ k, ∑ l, D j k l * a k * a l with hS
  have e1 : ∑ i, ∑ j, acc i * (G i j * b j) = ∑ j, b j * ∑ i, G i j * acc i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, ∑ j, a i * ((∑ k, a k * D k i j) * b j) =
      ∑ j, b j * ∑ i, (∑ k, a k * D k i j) * a i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, ∑ j, c i * (G i j * a j) = Q := by
    rw [hQ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsym j i]; ring
  have e4 : ∑ i, ∑ j, a i * ((∑ k, b k * D k i j) * a j) = ∑ j, b j * S j := by
    have h1 : ∀ i j, a i * ((∑ k, b k * D k i j) * a j) =
        ∑ k, b k * (D k i j * a i * a j) := fun i j => by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [h1]
    rw [show (∑ i, ∑ j, ∑ k, b k * (D k i j * a i * a j)) =
        ∑ i, ∑ k, ∑ j, b k * (D k i j * a i * a j) from
      Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hS, Finset.mul_sum]
  have hL : ∑ i, ∑ j, (acc i * (G i j * b j) +
      a i * ((∑ k, a k * D k i j) * b j + G i j * c j)) =
      (∑ i, ∑ j, acc i * (G i j * b j)) + (∑ i, ∑ j, a i * ((∑ k, a k * D k i j) * b j)) + Q := by
    simp only [hQ, mul_add, Finset.sum_add_distrib]
    ring
  have hR : ∑ i, ∑ j, (c i * (G i j * a j) +
      a i * ((∑ k, b k * D k i j) * a j + G i j * c j)) =
      (∑ i, ∑ j, c i * (G i j * a j)) + (∑ i, ∑ j, a i * ((∑ k, b k * D k i j) * a j)) + Q := by
    simp only [hQ, mul_add, Finset.sum_add_distrib]
    ring
  have hsum : (∑ j, b j * ∑ i, G i j * acc i) + (∑ j, b j * ∑ i, (∑ k, a k * D k i j) * a i) =
      (1 / 2) * ∑ j, b j * S j := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_add, hE j]
    ring
  rw [hL, hR, e1, e2, e3, e4, hsum]
  ring

end Lightlike.Geodesic
