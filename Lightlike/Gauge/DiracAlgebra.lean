import Mathlib

/-!
# The algebra behind the Jacobi identity of the Dirac bracket

Pure algebra, at one point of the phase space. Three observables are indexed by `κ`, the `m` constraints by
`ι`, `c` is the antisymmetric inverse of the bracket matrix of the constraints, `P u a = {u, φ_a}`, and
`T u p q = {u, {p, q}}` for `u, p, q` among the observables and the constraints (`κ ⊕ ι`), antisymmetric in
`p, q` and satisfying the Jacobi identity `T u p q + T p q u + T q u p = 0`. Then the Dirac bracket of `u` with
`D(v, w) = {v, w} - ∑ {v, φ_a} c_{ab} {φ_b, w}`, written out with the derivative `d c = - c (dC) c`
(`Jac`), is cyclically antisymmetric: `Jac u v w + Jac v w u + Jac w u v = 0` (`Jac_cyc`). The terms are grouped
by their degree in `c`; each degree cancels by the Jacobi identity for the corresponding triples
(`E1_cyc`, `E2_cyc`, `Tri_cyc`).

## References

* M. Henneaux and C. Teitelboim, *Quantization of Gauge Systems*, Princeton University Press (1992), Chapter 1.
-/

namespace Lightlike.Gauge
open Finset

variable {κ ι : Type} [Fintype ι]

/-- The covector `a_u = P_u^T c`. -/
def rowC (c : ι → ι → ℝ) (P : κ → ι → ℝ) (u : κ) (d : ι) : ℝ := ∑ a, P u a * c a d

theorem sum_c_P (c : ι → ι → ℝ) (hc : ∀ a b, c a b = -c b a) (P : κ → ι → ℝ) (w : κ) (a : ι) :
    ∑ b, c a b * P w b = -rowC c P w a := by
  simp only [rowC, hc a, neg_mul, sum_neg_distrib]
  congr 1
  exact sum_congr rfl fun b _ => by ring

theorem sum_sum_rowC (c : ι → ι → ℝ) (P : κ → ι → ℝ) (v : κ) (F : ι → ℝ) :
    ∑ a, ∑ b, P v a * c a b * F b = ∑ b, rowC c P v b * F b := by
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  simp only [rowC, sum_mul]

/-- degree-one part of the Jacobiator -/
noncomputable def E1 (c : ι → ι → ℝ) (P : κ → ι → ℝ) (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u v w : κ) : ℝ :=
  (∑ a, T (.inl u) (.inl v) (.inr a) * (∑ b, c a b * P w b)) +
  (∑ a, ∑ b, P v a * c a b * T (.inl u) (.inl w) (.inr b)) -
  (∑ e, ∑ e', P u e * c e e' * T (.inr e') (.inl v) (.inl w))

theorem E1_cyc (c : ι → ι → ℝ) (hc : ∀ a b, c a b = -c b a) (P : κ → ι → ℝ)
    (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (hT : ∀ u p q, T u p q = -T u q p)
    (hJ : ∀ u p q, T u p q + T p q u + T q u p = 0) (u v w : κ) :
    E1 c P T u v w + E1 c P T v w u + E1 c P T w u v = 0 := by
  have h1 : ∀ u v w : κ, E1 c P T u v w =
      ∑ a, (-(rowC c P w a) * T (.inl u) (.inl v) (.inr a) + rowC c P v a * T (.inl u) (.inl w) (.inr a)
        - rowC c P u a * T (.inr a) (.inl v) (.inl w)) := by
    intro u v w
    unfold E1
    simp only [sum_c_P c hc, sum_add_distrib, sum_sub_distrib]
    rw [sum_sum_rowC c P v (fun b => T (.inl u) (.inl w) (.inr b))]
    have h3 : ∑ e, ∑ e', P u e * c e e' * T (.inr e') (.inl v) (.inl w) =
        ∑ e', rowC c P u e' * T (.inr e') (.inl v) (.inl w) :=
      sum_sum_rowC c P u (fun e' => T (.inr e') (.inl v) (.inl w))
    rw [h3]
    have h4 : (∑ x, T (.inl u) (.inl v) (.inr x) * -rowC c P w x) =
        ∑ x, -rowC c P w x * T (.inl u) (.inl v) (.inr x) := sum_congr rfl fun x _ => mul_comm _ _
    rw [h4]
  have h2 : ∀ a, (-(rowC c P w a) * T (.inl u) (.inl v) (.inr a) + rowC c P v a * T (.inl u) (.inl w) (.inr a)
        - rowC c P u a * T (.inr a) (.inl v) (.inl w)) +
      (-(rowC c P u a) * T (.inl v) (.inl w) (.inr a) + rowC c P w a * T (.inl v) (.inl u) (.inr a)
        - rowC c P v a * T (.inr a) (.inl w) (.inl u)) +
      (-(rowC c P v a) * T (.inl w) (.inl u) (.inr a) + rowC c P u a * T (.inl w) (.inl v) (.inr a)
        - rowC c P w a * T (.inr a) (.inl u) (.inl v)) = 0 := by
    intro a
    have e1 : T (.inl u) (.inl v) (.inr a) - T (.inl v) (.inl u) (.inr a) + T (.inr a) (.inl u) (.inl v) = 0 := by
      linarith [hJ (.inl u) (.inl v) (.inr a), hT (.inl v) (.inr a) (.inl u)]
    have e2 : T (.inl v) (.inl w) (.inr a) - T (.inl w) (.inl v) (.inr a) + T (.inr a) (.inl v) (.inl w) = 0 := by
      linarith [hJ (.inl v) (.inl w) (.inr a), hT (.inl w) (.inr a) (.inl v)]
    have e3 : T (.inl w) (.inl u) (.inr a) - T (.inl u) (.inl w) (.inr a) + T (.inr a) (.inl w) (.inl u) = 0 := by
      linarith [hJ (.inl w) (.inl u) (.inr a), hT (.inl u) (.inr a) (.inl w)]
    linear_combination (-(rowC c P w a)) * e1 + (-(rowC c P u a)) * e2 + (-(rowC c P v a)) * e3
  rw [h1 u v w, h1 v w u, h1 w u v, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_eq_zero fun a _ => h2 a

theorem quad_rows (c : ι → ι → ℝ) (P : κ → ι → ℝ) (v w : κ) (S : ℝ) (c' d : ι) :
    ∑ a, ∑ b, P v a * c a c' * S * c d b * P w b =
      rowC c P v c' * S * ∑ b, c d b * P w b := by
  have h : ∀ a b : ι, P v a * c a c' * S * c d b * P w b = (P v a * c a c') * (S * (c d b * P w b)) :=
    fun a b => by ring
  simp only [h]
  rw [← sum_mul_sum]
  simp only [rowC, ← mul_sum]
  ring

theorem quad_all (c : ι → ι → ℝ) (P : κ → ι → ℝ) (v w : κ) (S : ι → ι → ℝ) :
    ∑ a, ∑ c', ∑ d, ∑ b, P v a * c a c' * S c' d * c d b * P w b =
      ∑ c', ∑ d, rowC c P v c' * S c' d * ∑ b, c d b * P w b := by
  rw [sum_comm]
  refine sum_congr rfl fun c' _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  exact quad_rows c P v w (S c' d) c' d

/-- degree-two part of the Jacobiator -/
noncomputable def E2 (c : ι → ι → ℝ) (P : κ → ι → ℝ) (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u v w : κ) : ℝ :=
  -(∑ a, ∑ c', ∑ d, ∑ b, P v a * c a c' * T (.inl u) (.inr c') (.inr d) * c d b * P w b) -
  (∑ e, ∑ e', P u e * c e e' *
      (∑ a, T (.inr e') (.inl v) (.inr a) * ∑ b, c a b * P w b)) -
  (∑ e, ∑ e', P u e * c e e' *
      (∑ a, ∑ b, P v a * c a b * T (.inr e') (.inl w) (.inr b)))

theorem E2_eq (c : ι → ι → ℝ) (hc : ∀ a b, c a b = -c b a) (P : κ → ι → ℝ)
    (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u v w : κ) :
    E2 c P T u v w =
      (∑ c', ∑ d, rowC c P v c' * T (.inl u) (.inr c') (.inr d) * rowC c P w d) +
      (∑ e, ∑ a, rowC c P u e * T (.inr e) (.inl v) (.inr a) * rowC c P w a) -
      (∑ e, ∑ b, rowC c P u e * T (.inr e) (.inl w) (.inr b) * rowC c P v b) := by
  unfold E2
  rw [quad_all c P v w (fun c' d => T (.inl u) (.inr c') (.inr d))]
  have s1 : (∑ c', ∑ d, rowC c P v c' * T (.inl u) (.inr c') (.inr d) * ∑ b, c d b * P w b) =
      -∑ c', ∑ d, rowC c P v c' * T (.inl u) (.inr c') (.inr d) * rowC c P w d := by
    simp only [sum_c_P c hc, mul_neg, sum_neg_distrib]
  have s2 : (∑ e, ∑ e', P u e * c e e' *
      (∑ a, T (.inr e') (.inl v) (.inr a) * ∑ b, c a b * P w b)) =
      -∑ e, ∑ a, rowC c P u e * T (.inr e) (.inl v) (.inr a) * rowC c P w a := by
    rw [sum_sum_rowC c P u (fun e' => ∑ a, T (.inr e') (.inl v) (.inr a) * ∑ b, c a b * P w b)]
    simp only [sum_c_P c hc, mul_neg, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun e _ => sum_congr rfl fun a _ => by ring
  have s3 : (∑ e, ∑ e', P u e * c e e' *
      (∑ a, ∑ b, P v a * c a b * T (.inr e') (.inl w) (.inr b))) =
      ∑ e, ∑ b, rowC c P u e * T (.inr e) (.inl w) (.inr b) * rowC c P v b := by
    rw [sum_sum_rowC c P u (fun e' => ∑ a, ∑ b, P v a * c a b * T (.inr e') (.inl w) (.inr b))]
    simp only [sum_sum_rowC c P v, mul_sum]
    refine sum_congr rfl fun e _ => sum_congr rfl fun b _ => by ring
  rw [s1, s2, s3]
  ring

/-- the bilinear form of `Z_u (e, d) = T(φ_e; u, φ_d)` on two covectors -/
def Zf (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u : κ) (x y : ι → ℝ) : ℝ :=
  ∑ e, ∑ d, x e * T (.inr e) (.inl u) (.inr d) * y d

theorem E2_cyc (c : ι → ι → ℝ) (hc : ∀ a b, c a b = -c b a) (P : κ → ι → ℝ)
    (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (hT : ∀ u p q, T u p q = -T u q p)
    (hJ : ∀ u p q, T u p q + T p q u + T q u p = 0) (u v w : κ) :
    E2 c P T u v w + E2 c P T v w u + E2 c P T w u v = 0 := by
  have hS : ∀ (u : κ) (x y : ι → ℝ), (∑ c', ∑ d, x c' * T (.inl u) (.inr c') (.inr d) * y d) =
      Zf T u x y - Zf T u y x := by
    intro u x y
    have h : ∀ c' d : ι, T (.inl u) (.inr c') (.inr d) =
        T (.inr c') (.inl u) (.inr d) - T (.inr d) (.inl u) (.inr c') := by
      intro c' d
      have := hJ (.inr c') (.inl u) (.inr d)
      have h2 := hT (.inr d) (.inr c') (.inl u)
      have h3 := hT (.inl u) (.inr d) (.inr c')
      have h4 := hT (.inr d) (.inl u) (.inr c')
      linarith
    simp only [h, Zf, mul_sub, sub_mul, sum_sub_distrib]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => by ring
  simp only [E2_eq c hc P T, hS]
  unfold Zf
  ring

/-- degree-three part of the Jacobiator -/
noncomputable def E3 (c : ι → ι → ℝ) (P : κ → ι → ℝ) (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u v w : κ) : ℝ :=
  ∑ e, ∑ e', P u e * c e e' *
    (∑ a, ∑ c', ∑ d, ∑ b, P v a * c a c' * T (.inr e') (.inr c') (.inr d) * c d b * P w b)

/-- the trilinear form of `R (e, c, d) = T(φ_e; φ_c, φ_d)` -/
def Tri (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (x y z : ι → ℝ) : ℝ :=
  ∑ e, ∑ c', ∑ d, x e * y c' * z d * T (.inr e) (.inr c') (.inr d)

theorem E3_eq (c : ι → ι → ℝ) (hc : ∀ a b, c a b = -c b a) (P : κ → ι → ℝ)
    (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u v w : κ) :
    E3 c P T u v w = -Tri T (rowC c P u) (rowC c P v) (rowC c P w) := by
  unfold E3 Tri
  have h : ∀ e' : ι, (∑ a, ∑ c', ∑ d, ∑ b, P v a * c a c' * T (.inr e') (.inr c') (.inr d) * c d b * P w b)
      = -∑ c', ∑ d, rowC c P v c' * rowC c P w d * T (.inr e') (.inr c') (.inr d) := by
    intro e'
    rw [quad_all c P v w (fun c' d => T (.inr e') (.inr c') (.inr d))]
    simp only [sum_c_P c hc, mul_neg, sum_neg_distrib]
    congr 1
    exact sum_congr rfl fun c' _ => sum_congr rfl fun d _ => by ring
  simp only [h]
  rw [sum_sum_rowC c P u (fun e' => -∑ c', ∑ d, rowC c P v c' * rowC c P w d * T (.inr e') (.inr c') (.inr d))]
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun e _ => ?_
  simp only [mul_neg, mul_sum]
  congr 1
  exact sum_congr rfl fun c' _ => sum_congr rfl fun d _ => by ring

theorem sum3_rot (F : ι → ι → ι → ℝ) :
    ∑ e, ∑ c, ∑ d, F e c d = ∑ d, ∑ e, ∑ c, F e c d := by
  calc ∑ e, ∑ c, ∑ d, F e c d = ∑ e, ∑ d, ∑ c, F e c d := sum_congr rfl fun e _ => sum_comm
    _ = ∑ d, ∑ e, ∑ c, F e c d := sum_comm

theorem Tri_cyc (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ)
    (hJ : ∀ u p q, T u p q + T p q u + T q u p = 0) (x y z : ι → ℝ) :
    Tri T x y z + Tri T y z x + Tri T z x y = 0 := by
  have h2 : Tri T y z x = ∑ i, ∑ j, ∑ k, x i * y j * z k * T (.inr j) (.inr k) (.inr i) := by
    unfold Tri
    rw [sum3_rot]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  have h3 : Tri T z x y = ∑ i, ∑ j, ∑ k, x i * y j * z k * T (.inr k) (.inr i) (.inr j) := by
    unfold Tri
    rw [sum3_rot, sum3_rot]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  rw [h2, h3]
  unfold Tri
  simp only [← sum_add_distrib]
  refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun k _ => ?_
  have := hJ (.inr i) (.inr j) (.inr k)
  linear_combination (x i * y j * z k) * this

/-- The derivative `∂_u D(g, h)` of the Dirac bracket of `v` and `w`, in terms of the triple brackets `T`
and the covectors `P`. -/
noncomputable def Dd (c : ι → ι → ℝ) (P : κ → ι → ℝ) (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ)
    (u : κ ⊕ ι) (v w : κ) : ℝ :=
  T u (.inl v) (.inl w) + (∑ a, T u (.inl v) (.inr a) * ∑ b, c a b * P w b)
    - (∑ a, ∑ c', ∑ d, ∑ b, P v a * c a c' * T u (.inr c') (.inr d) * c d b * P w b)
    + (∑ a, ∑ b, P v a * c a b * T u (.inl w) (.inr b))

/-- The Dirac bracket of `u` with `D(v, w)`, expanded. -/
noncomputable def Jac (c : ι → ι → ℝ) (P : κ → ι → ℝ) (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u v w : κ) : ℝ :=
  Dd c P T (.inl u) v w - ∑ e, ∑ e', P u e * c e e' * Dd c P T (.inr e') v w

theorem Jac_eq (c : ι → ι → ℝ) (P : κ → ι → ℝ) (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (u v w : κ) :
    Jac c P T u v w = T (.inl u) (.inl v) (.inl w) + E1 c P T u v w + E2 c P T u v w + E3 c P T u v w := by
  unfold Jac Dd E1 E2 E3
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  ring

/-- **The cyclic cancellation** behind the Jacobi identity of the Dirac bracket. -/
theorem Jac_cyc (c : ι → ι → ℝ) (hc : ∀ a b, c a b = -c b a) (P : κ → ι → ℝ)
    (T : κ ⊕ ι → κ ⊕ ι → κ ⊕ ι → ℝ) (hT : ∀ u p q, T u p q = -T u q p)
    (hJ : ∀ u p q, T u p q + T p q u + T q u p = 0) (u v w : κ) :
    Jac c P T u v w + Jac c P T v w u + Jac c P T w u v = 0 := by
  have e0 := hJ (.inl u) (.inl v) (.inl w)
  have e1 := E1_cyc c hc P T hT hJ u v w
  have e2 := E2_cyc c hc P T hT hJ u v w
  have e3 := Tri_cyc T hJ (rowC c P u) (rowC c P v) (rowC c P w)
  simp only [Jac_eq, E3_eq c hc]
  linarith

end Lightlike.Gauge
