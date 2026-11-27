import Mathlib
import Lightlike.Geometry.HeatKernel.WorldFunctionJet
import Lightlike.Geometry.HeatKernel.JetInvariants

/-!
# The fourth derivatives of the world function at the diagonal

The derivatives of the inverse metric contracted with the metric (`sum_pd_inv_mul_metric_right`,
`sum_pd_inv_mul_metric_left`, and, through the twice differentiated identity `g⁻¹ g = 1`, `sum_pd_pd_inv_mul_metric`:
`∂_a ∂_b g^{xy} g_{cx} g_{dy} = (∂_a g g⁻¹ ∂_b g + ∂_b g g⁻¹ ∂_a g - ∂_a ∂_b g)_{cd}`), and the order-four differentiated
eikonal equation at the diagonal with those contractions done (`eikonal_fourth`): an identity between the fourth and the
third derivatives of the world function at `p` and the 2-jet of the metric. Its 58 terms are those of the Leibniz expansion
over the splits of `[a, b, c, d]`.

## References

* `basile-2024`: I. Basile et al., *Lectures in Quantum Gravity*, arXiv:2412.08690v3, §4.2.5, eq. (4.92) (the fourth
  coincidence limit, "after a lengthier (but completely analogous) computation", not derived there).
-/

open Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U S : Set (Fin n → ℝ)} {s : (Fin n → ℝ) → ℝ}

/-- The derivative of the inverse metric as a matrix: `∂_a g⁻¹ = -g⁻¹ (∂_a g) g⁻¹`. -/
lemma pd_inv_matrix (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (a x y : Fin n) :
    pd a (fun z => (g z)⁻¹ x y) p =
      -((g p)⁻¹ * Matrix.of (fun i l => pd a (fun z => g z i l) p) * (g p)⁻¹) x y := by
  rw [Regge.Conv3.pd_inv hg hp a x y, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `∂_a g^{xy}` contracted with the metric in its second slot: `Σ_y ∂_a g^{xy} t g_{cy} = -t (g⁻¹ ∂_a g)_{xc}`. -/
lemma sum_pd_inv_mul_metric_right (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (a c : Fin n)
    (X : Fin n → ℝ) (t : ℝ) :
    ∑ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (X x * (t * g p c y)) =
      -(t * ∑ x, X x * ∑ i, (g p)⁻¹ x i * pd a (fun z => g z i c) p) := by
  have hu := hg.isUnit_det p hp
  have hsym := hg.symm p hp
  set Dm : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i l => pd a (fun z => g z i l) p with hDm
  have key : ∀ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * g p c y = -∑ i, (g p)⁻¹ x i * Dm i c := by
    intro x
    have hm : ((g p)⁻¹ * Dm * (g p)⁻¹ * (g p).transpose) x c = ((g p)⁻¹ * Dm) x c := by
      rw [hsym, Matrix.mul_assoc _ (g p)⁻¹, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    rw [Matrix.mul_apply, Matrix.mul_apply] at hm
    simp only [Matrix.transpose_apply] at hm
    rw [← hm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [pd_inv_matrix hg hp a x y, ← hDm]
    ring
  calc ∑ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (X x * (t * g p c y))
      = ∑ x, t * X x * ∑ y, pd a (fun z => (g z)⁻¹ x y) p * g p c y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = _ := by
        simp only [key, hDm, Matrix.of_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring

/-- `∂_a g^{xy}` contracted with the metric in its first slot: `Σ_x ∂_a g^{xy} t g_{bx} = -t (∂_a g g⁻¹)_{by}`. -/
lemma sum_pd_inv_mul_metric_left (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (a b : Fin n)
    (Y : Fin n → ℝ) (t : ℝ) :
    ∑ x, ∑ y, pd a (fun z => (g z)⁻¹ x y) p * (t * g p b x * Y y) =
      -(t * ∑ y, Y y * ∑ i, (g p)⁻¹ y i * pd a (fun z => g z i b) p) := by
  have hsymi : ∀ x y, pd a (fun z => (g z)⁻¹ x y) p = pd a (fun z => (g z)⁻¹ y x) p := fun x y =>
    pd_congr_on hg.isOpen hp (fun z hz => by
      have hs : ((g z)⁻¹).transpose = (g z)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hg.symm z hz]
      have := congrFun (congrFun hs y) x
      rwa [Matrix.transpose_apply] at this) a
  rw [Finset.sum_comm, ← sum_pd_inv_mul_metric_right hg hp a b Y t]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [hsymi]; ring

/-- **The second derivative of the inverse metric contracted twice with the metric**:
`∂_a ∂_b g^{xy} (t g_{cx}) (t g_{dy}) = t² ((∂_a g) g⁻¹ (∂_b g) + (∂_b g) g⁻¹ (∂_a g) - ∂_a ∂_b g)_{cd}`. -/
lemma sum_pd_pd_inv_mul_metric (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (a b c d : Fin n) (t : ℝ) :
    ∑ x, ∑ y, pd a (pd b fun z => (g z)⁻¹ x y) p * (t * g p c x * (t * g p d y)) =
      t * t * (∑ j, ∑ i, pd a (fun z => g z c i) p * (g p)⁻¹ i j * pd b (fun z => g z j d) p +
        ∑ j, ∑ i, pd b (fun z => g z c i) p * (g p)⁻¹ i j * pd a (fun z => g z j d) p -
          pd a (fun z => pd b (fun w => g w c d) z) p) := by
  have hU := hg.isOpen
  have hu := hg.isUnit_det p hp
  have hsym := hg.symm p hp
  have hG : ∀ i j, ContDiffOn ℝ ∞ (fun z => (g z)⁻¹ i j) U := fun i j => Regge.Conv3.cdo_inv g hg i j
  -- `Σ_l g^{xl} g_{ly} = δ` on `U`, differentiated along `[a, b]`
  have hid : ∀ x y, pdL [a, b] (fun z => ∑ l, (g z)⁻¹ x l * g z l y) p = 0 := by
    intro x y
    have hc : EqOn (fun z => ∑ l, (g z)⁻¹ x l * g z l y) (fun _ => if x = y then 1 else 0) U := fun z hz => by
      have := congrFun (congrFun (Matrix.nonsing_inv_mul _ (hg.isUnit_det z hz)) x) y
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    rw [pdL_congr_on hU hc [a, b] p hp]
    simp only [pdL_cons, pdL_nil]
    rw [show (pd b fun _ : Fin n → ℝ => if x = y then (1 : ℝ) else 0) = fun _ => 0 from funext fun z => by simp [pd]]
    simp [pd]
  set G : Matrix (Fin n) (Fin n) ℝ := (g p)⁻¹ with hGdef
  set M2 : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun x y => pd a (pd b fun z => (g z)⁻¹ x y) p with hM2
  set Ga : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun x y => pd a (fun z => (g z)⁻¹ x y) p with hGa
  set Gb : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun x y => pd b (fun z => (g z)⁻¹ x y) p with hGb
  set Da : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun x y => pd a (fun z => g z x y) p with hDa
  set Db : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun x y => pd b (fun z => g z x y) p with hDb
  set Eab : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun x y => pd a (fun z => pd b (fun w => g w x y) z) p with hEab
  have hmat : M2 * g p + Ga * Db + Gb * Da + G * Eab = 0 := by
    ext x y
    have h := hid x y
    rw [pdL_sum _ (fun l _ => (hG x l).mul (hg.smooth l y)) hU [a, b] p hp] at h
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply, hM2, hGa, hGb, hDa, hDb, hEab, hGdef,
      Matrix.of_apply, ← Finset.sum_add_distrib]
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pdL_mul (hG x l) (hg.smooth l y) hU [a, b] p hp]
    simp only [splits, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.sum_cons, List.sum_nil, pdL_cons, pdL_nil]
    ring
  have hGa' : Ga = -(G * Da * G) := by
    ext x y
    rw [hGa, Matrix.of_apply, pd_inv_matrix hg hp a x y]
    rfl
  have hGb' : Gb = -(G * Db * G) := by
    ext x y
    rw [hGb, Matrix.of_apply, pd_inv_matrix hg hp b x y]
    rfl
  have hgG : g p * G = 1 := Matrix.mul_nonsing_inv _ hu
  have hGg : G * g p = 1 := Matrix.nonsing_inv_mul _ hu
  have key : g p * M2 * (g p).transpose = Da * G * Db + Db * G * Da - Eab := by
    have hM : M2 = -(Ga * Db + Gb * Da + G * Eab) * G := by
      have : M2 * g p * G = -(Ga * Db + Gb * Da + G * Eab) * G := by
        rw [show M2 * g p = -(Ga * Db + Gb * Da + G * Eab) by
          rw [eq_neg_iff_add_eq_zero, ← add_assoc, ← add_assoc]; exact hmat]
      rwa [Matrix.mul_assoc, hgG, Matrix.mul_one] at this
    rw [hM, hsym, hGa', hGb']
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hGg, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, hgG, Matrix.one_mul]
    abel
  have h1 : ∑ x, ∑ y, pd a (pd b fun z => (g z)⁻¹ x y) p * (t * g p c x * (t * g p d y)) =
      t * t * ∑ x, ∑ y, M2 x y * (g p c x * g p d y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [hM2, Matrix.of_apply]; ring
  rw [h1, sum_sum_mul_mul, key]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, hDa, hDb, hEab, hGdef, Matrix.of_apply,
    Finset.sum_mul]


/-- **The differentiated eikonal equation of order four at the diagonal**, with the derivatives of the inverse metric
contracted against `∂²s(p) = 2 g(p)`: an identity between the fourth and third derivatives of `s` at `p` and the jet of
the metric. -/
theorem eikonal_fourth (hg : IsCoordMetric g U) (hS : IsOpen S) (hSU : S ⊆ U) (hs : ContDiffOn ℝ ∞ s S)
    (heik : ∀ y ∈ S, coordGradPair g s s y = 4 * s y) {p : Fin n → ℝ} (hp : p ∈ S) (hs1 : ∀ i, pd i s p = 0)
    (hs2 : ∀ i j, pd i (pd j s) p = 2 * g p i j) (a b c d : Fin n) :
    (4 : ℝ) * (∑ j, ∑ i, pd a (fun z => g z c i) p * (g p)⁻¹ i j * pd b (fun z => g z j d) p) + (4 : ℝ) * (∑ j, ∑ i, pd b (fun z => g z c i) p * (g p)⁻¹ i j * pd a (fun z => g z j d) p) + (-4 : ℝ) * (pd a (fun z => pd b (fun w => g w c d) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd a (fun z => g z d i) p * (g p)⁻¹ i j * pd b (fun z => g z j c) p) + (4 : ℝ) * (∑ j, ∑ i, pd b (fun z => g z d i) p * (g p)⁻¹ i j * pd a (fun z => g z j c) p) + (-4 : ℝ) * (pd a (fun z => pd b (fun w => g w d c) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd a (fun z => g z b i) p * (g p)⁻¹ i j * pd c (fun z => g z j d) p) + (4 : ℝ) * (∑ j, ∑ i, pd c (fun z => g z b i) p * (g p)⁻¹ i j * pd a (fun z => g z j d) p) + (-4 : ℝ) * (pd a (fun z => pd c (fun w => g w b d) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd a (fun z => g z d i) p * (g p)⁻¹ i j * pd c (fun z => g z j b) p) + (4 : ℝ) * (∑ j, ∑ i, pd c (fun z => g z d i) p * (g p)⁻¹ i j * pd a (fun z => g z j b) p) + (-4 : ℝ) * (pd a (fun z => pd c (fun w => g w d b) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd a (fun z => g z b i) p * (g p)⁻¹ i j * pd d (fun z => g z j c) p) + (4 : ℝ) * (∑ j, ∑ i, pd d (fun z => g z b i) p * (g p)⁻¹ i j * pd a (fun z => g z j c) p) + (-4 : ℝ) * (pd a (fun z => pd d (fun w => g w b c) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd a (fun z => g z c i) p * (g p)⁻¹ i j * pd d (fun z => g z j b) p) + (4 : ℝ) * (∑ j, ∑ i, pd d (fun z => g z c i) p * (g p)⁻¹ i j * pd a (fun z => g z j b) p) + (-4 : ℝ) * (pd a (fun z => pd d (fun w => g w c b) z) p) + (-4 : ℝ) * (∑ x, pd b (pd c (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd a (fun z => g z i d) p) + (-4 : ℝ) * (∑ x, pd b (pd d (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd a (fun z => g z i c) p) + (-4 : ℝ) * (∑ x, pd c (pd d (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd a (fun z => g z i b) p) + (4 : ℝ) * (∑ j, ∑ i, pd b (fun z => g z a i) p * (g p)⁻¹ i j * pd c (fun z => g z j d) p) + (4 : ℝ) * (∑ j, ∑ i, pd c (fun z => g z a i) p * (g p)⁻¹ i j * pd b (fun z => g z j d) p) + (-4 : ℝ) * (pd b (fun z => pd c (fun w => g w a d) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd b (fun z => g z d i) p * (g p)⁻¹ i j * pd c (fun z => g z j a) p) + (4 : ℝ) * (∑ j, ∑ i, pd c (fun z => g z d i) p * (g p)⁻¹ i j * pd b (fun z => g z j a) p) + (-4 : ℝ) * (pd b (fun z => pd c (fun w => g w d a) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd b (fun z => g z a i) p * (g p)⁻¹ i j * pd d (fun z => g z j c) p) + (4 : ℝ) * (∑ j, ∑ i, pd d (fun z => g z a i) p * (g p)⁻¹ i j * pd b (fun z => g z j c) p) + (-4 : ℝ) * (pd b (fun z => pd d (fun w => g w a c) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd b (fun z => g z c i) p * (g p)⁻¹ i j * pd d (fun z => g z j a) p) + (4 : ℝ) * (∑ j, ∑ i, pd d (fun z => g z c i) p * (g p)⁻¹ i j * pd b (fun z => g z j a) p) + (-4 : ℝ) * (pd b (fun z => pd d (fun w => g w c a) z) p) + (-4 : ℝ) * (∑ x, pd a (pd c (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd b (fun z => g z i d) p) + (-4 : ℝ) * (∑ x, pd a (pd d (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd b (fun z => g z i c) p) + (-4 : ℝ) * (∑ x, pd c (pd d (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd b (fun z => g z i a) p) + (4 : ℝ) * (∑ j, ∑ i, pd c (fun z => g z a i) p * (g p)⁻¹ i j * pd d (fun z => g z j b) p) + (4 : ℝ) * (∑ j, ∑ i, pd d (fun z => g z a i) p * (g p)⁻¹ i j * pd c (fun z => g z j b) p) + (-4 : ℝ) * (pd c (fun z => pd d (fun w => g w a b) z) p) + (4 : ℝ) * (∑ j, ∑ i, pd c (fun z => g z b i) p * (g p)⁻¹ i j * pd d (fun z => g z j a) p) + (4 : ℝ) * (∑ j, ∑ i, pd d (fun z => g z b i) p * (g p)⁻¹ i j * pd c (fun z => g z j a) p) + (-4 : ℝ) * (pd c (fun z => pd d (fun w => g w b a) z) p) + (-4 : ℝ) * (∑ x, pd a (pd b (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd c (fun z => g z i d) p) + (-4 : ℝ) * (∑ x, pd a (pd d (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd c (fun z => g z i b) p) + (-4 : ℝ) * (∑ x, pd b (pd d (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd c (fun z => g z i a) p) + (-4 : ℝ) * (∑ x, pd a (pd b (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd d (fun z => g z i c) p) + (-4 : ℝ) * (∑ x, pd a (pd c (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd d (fun z => g z i b) p) + (-4 : ℝ) * (∑ x, pd b (pd c (pd x s)) p * ∑ i, (g p)⁻¹ x i * pd d (fun z => g z i a) p) + (4 : ℝ) * (pd a (pd b (pd c (pd d s))) p) + (4 : ℝ) * (pd a (pd b (pd d (pd c s))) p) + (1 : ℝ) * (∑ x, ∑ y, (g p)⁻¹ x y * (pd a (pd b (pd x s)) p * pd c (pd d (pd y s)) p)) + (4 : ℝ) * (pd a (pd c (pd d (pd b s))) p) + (1 : ℝ) * (∑ x, ∑ y, (g p)⁻¹ x y * (pd a (pd c (pd x s)) p * pd b (pd d (pd y s)) p)) + (1 : ℝ) * (∑ x, ∑ y, (g p)⁻¹ x y * (pd a (pd d (pd x s)) p * pd b (pd c (pd y s)) p)) + (4 : ℝ) * (pd b (pd c (pd d (pd a s))) p) + (1 : ℝ) * (∑ x, ∑ y, (g p)⁻¹ x y * (pd b (pd c (pd x s)) p * pd a (pd d (pd y s)) p)) + (1 : ℝ) * (∑ x, ∑ y, (g p)⁻¹ x y * (pd b (pd d (pd x s)) p * pd a (pd c (pd y s)) p)) + (1 : ℝ) * (∑ x, ∑ y, (g p)⁻¹ x y * (pd c (pd d (pd x s)) p * pd a (pd b (pd y s)) p)) = 4 * pd a (pd b (pd c (pd d s))) p := by
  have hpU := hSU hp
  have E := eikonal_pdL hg hS hSU hs heik [a, b, c, d] hp
  simp only [splits, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.cons_append, List.nil_append, pdL_nil, pdL_cons, hs1, hs2, mul_zero, zero_mul, add_zero, zero_add] at E
  simp only [mul_add, Finset.sum_add_distrib, sum_inv_mul_metric hg hpU, sum_inv_mul_metric' hg hpU,
    sum_pd_inv_mul_metric_right hg hpU, sum_pd_inv_mul_metric_left hg hpU, sum_pd_pd_inv_mul_metric hg hpU] at E
  linear_combination E

end Lightlike
