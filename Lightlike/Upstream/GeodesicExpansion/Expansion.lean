import Lightlike.Upstream.GeodesicExpansion.Taylor
import Mathlib

/-!
# The expansion of the distance: the jet and the radial field

For a Riemannian metric `g` on `U` (in a chart), the quartic jet of the squared distance is

`distJet g x w = g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))`,

with `g`, its derivatives and the Christoffel contraction `Γ` taken at `x`.

The lower bound for the distance is a calibration. The field
`P = w - ½ Γ(w, w) + ½ g⁻¹ ell(w)` (`radial`) satisfies `dF = 2 g(P, ·) + O(‖w‖⁴)` and
`g(P, P) = F + O(‖w‖⁵)`; both are polynomial identities proved exactly here
(`IsCoordMetric.distJetDeriv_eq`, `IsCoordMetric.radial_quad_eq`). `LocalJet` packages the uniform
bounds used to estimate the remainders.

## Main declarations

* `distJet`, `distJetDeriv`, `hasDerivAt_distJet`
* `radial`, `radialErr1`, `radialErr2`
* `IsCoordMetric.distJetDeriv_eq`, `IsCoordMetric.radial_quad_eq`
* `LocalJet`
-/

open Matrix Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## The quartic jet of the squared distance -/

/-- The quartic Taylor polynomial of `d(x, x + w)²`:
`g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))` at `x`. -/
def distJet (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) : ℝ :=
  w ⬝ᵥ (g x *ᵥ w) + (1 / 2) * (w ⬝ᵥ (dmat g x w *ᵥ w))
    + (1 / 6) * (w ⬝ᵥ (ddmat g x w w *ᵥ w))
    - (1 / 12) * (chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w))

/-- The derivative of `distJet g x` at `w` in the direction `v`. -/
def distJetDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x w v : Fin n → ℝ) : ℝ :=
  (v ⬝ᵥ (g x *ᵥ w) + w ⬝ᵥ (g x *ᵥ v))
    + (1 / 2) * (v ⬝ᵥ (dmat g x w *ᵥ w) + w ⬝ᵥ (dmat g x v *ᵥ w + dmat g x w *ᵥ v))
    + (1 / 6) * (v ⬝ᵥ (ddmat g x w w *ᵥ w)
      + w ⬝ᵥ (ddmat g x v w *ᵥ w + ddmat g x w v *ᵥ w + ddmat g x w w *ᵥ v))
    - (1 / 12) * ((chr g x v w + chr g x w v) ⬝ᵥ (g x *ᵥ chr g x w w)
      + chr g x w w ⬝ᵥ (g x *ᵥ (chr g x v w + chr g x w v)))

/-! ### Derivatives along curves -/

theorem hasDerivAt_dot {p q : ℝ → Fin n → ℝ} {p' q' : Fin n → ℝ} {t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => p s ⬝ᵥ q s) (p' ⬝ᵥ q t + p t ⬝ᵥ q') t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_pi.1 hp i).mul (hasDerivAt_pi.1 hq i)
  simp only [dotProduct]
  convert h using 1
  rw [← Finset.sum_add_distrib]

theorem hasDerivAt_mulVec_const (M : Matrix (Fin n) (Fin n) ℝ) {p : ℝ → Fin n → ℝ}
    {p' : Fin n → ℝ} {t : ℝ} (hp : HasDerivAt p p' t) :
    HasDerivAt (fun s => M *ᵥ p s) (M *ᵥ p') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_pi.1 hp j).const_mul (M i j)

theorem hasDerivAt_dmat_mulVec (x : Fin n → ℝ) {p q : ℝ → Fin n → ℝ} {p' q' : Fin n → ℝ}
    {t : ℝ} (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => dmat g x (p s) *ᵥ q s) (dmat g x p' *ᵥ q t + dmat g x (p t) *ᵥ q') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, dmat, Matrix.of_apply, Pi.add_apply]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_pi.1 hp k).mul_const (pd k (fun y => g y i j) x)).mul (hasDerivAt_pi.1 hq j)
  convert h using 1
  rw [← Finset.sum_add_distrib]

theorem hasDerivAt_ddmat_mulVec (x : Fin n → ℝ) {p r q : ℝ → Fin n → ℝ} {p' r' q' : Fin n → ℝ}
    {t : ℝ} (hp : HasDerivAt p p' t) (hr : HasDerivAt r r' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => ddmat g x (p s) (r s) *ᵥ q s)
      (ddmat g x p' (r t) *ᵥ q t + ddmat g x (p t) r' *ᵥ q t + ddmat g x (p t) (r t) *ᵥ q') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, ddmat, Matrix.of_apply, Pi.add_apply]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => HasDerivAt.fun_sum (u := Finset.univ)
      fun l _ => ((hasDerivAt_pi.1 hp k).mul (hasDerivAt_pi.1 hr l)).mul_const
        (pd l (pd k (fun y => g y i j)) x)).mul (hasDerivAt_pi.1 hq j)
  convert h using 1
  simp only [Pi.mul_apply, add_mul, Finset.sum_add_distrib]

theorem hasDerivAt_chr (x : Fin n → ℝ) {p q : ℝ → Fin n → ℝ} {p' q' : Fin n → ℝ} {t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => chr g x (p s) (q s)) (chr g x p' (q t) + chr g x (p t) q') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [chr, Pi.add_apply]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => HasDerivAt.fun_sum (u := Finset.univ)
    fun k _ => ((hasDerivAt_pi.1 hp j).const_mul (christoffel g i j k x)).mul
      (hasDerivAt_pi.1 hq k)
  convert h using 1
  simp only [Finset.sum_add_distrib]

/-- The derivative of the quartic jet along a curve. -/
theorem hasDerivAt_distJet (x : Fin n → ℝ) {W : ℝ → Fin n → ℝ} {W' : Fin n → ℝ} {t : ℝ}
    (hW : HasDerivAt W W' t) :
    HasDerivAt (fun s => distJet g x (W s)) (distJetDeriv g x (W t) W') t := by
  have h1 := hasDerivAt_dot hW (hasDerivAt_mulVec_const (g x) hW)
  have h2 := hasDerivAt_dot hW (hasDerivAt_dmat_mulVec (g := g) x hW hW)
  have h3 := hasDerivAt_dot hW (hasDerivAt_ddmat_mulVec (g := g) x hW hW hW)
  have hc := hasDerivAt_chr (g := g) x hW hW
  have h4 := hasDerivAt_dot hc (hasDerivAt_mulVec_const (g x) hc)
  unfold distJet
  exact (((h1.add (h2.const_mul (1 / 2))).add (h3.const_mul (1 / 6))).sub
    (h4.const_mul (1 / 12))).congr_deriv (by unfold distJetDeriv; ring)

/-! ## The radial field -/

/-- The cubic part of `½ dF - g(w - ½ Γ(w, w), ·)`, a linear form in `v`; raising its index
gives the cubic term of the radial field. -/
def ell (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w v : Fin n → ℝ) : ℝ :=
  (1 / 6) * (v ⬝ᵥ (ddmat g x w w *ᵥ w)
      + w ⬝ᵥ (ddmat g x v w *ᵥ w + ddmat g x w v *ᵥ w + ddmat g x w w *ᵥ v))
    - (1 / 12) * ((chr g x v w + chr g x w v) ⬝ᵥ (g x *ᵥ chr g x w w)
      + chr g x w w ⬝ᵥ (g x *ᵥ (chr g x v w + chr g x w v)))
    + chr g x w w ⬝ᵥ (dmat g x w *ᵥ v) - w ⬝ᵥ (ddmat g x w w *ᵥ v)

/-- The vector of the linear form `ell g x w`. -/
def ellVec (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ell g x w fun j => if i = j then 1 else 0

/-- The quadratic term `-½ Γ(w, w)` of the radial field. -/
def radial2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  (-(1 / 2) : ℝ) • chr g x w w

/-- The cubic term `½ g⁻¹ ell` of the radial field. -/
def radial3 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  (1 / 2 : ℝ) • ((g x)⁻¹ *ᵥ ellVec g x w)

/-- The **radial field** `P(w) = w - ½ Γ(w, w) + ½ g⁻¹ ell(w)`, an approximation of half the
gradient of `d(x, ·)²` at `x + w`. -/
def radial (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  w + radial2 g x w + radial3 g x w

/-- The second-order Taylor polynomial of the metric at `x`, evaluated at `x + u`. -/
def taylorMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  g x + dmat g x u + (1 / 2 : ℝ) • ddmat g x u u

theorem ell_add (x w v v' : Fin n → ℝ) : ell g x w (v + v') = ell g x w v + ell g x w v' := by
  unfold ell
  simp only [ddmat_add_left, ddmat_add_right, chr_add_left, chr_add_right, Matrix.add_mulVec,
    Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

theorem ell_smul (x w v : Fin n → ℝ) (c : ℝ) : ell g x w (c • v) = c * ell g x w v := by
  unfold ell
  simp only [ddmat_smul_left, ddmat_smul_right, chr_smul_left, chr_smul_right,
    Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem ell_eq_dot (x w v : Fin n → ℝ) : ell g x w v = ellVec g x w ⬝ᵥ v := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := ell g x w
      map_add' := ell_add x w
      map_smul' := fun c v => by simp [ell_smul] }
  have h := L.pi_apply_eq_sum_univ v
  simp only [dotProduct, ellVec]
  rw [show ell g x w v = L v from rfl, h]
  exact Finset.sum_congr rfl fun i _ => by simp [L, smul_eq_mul, mul_comm]

/-- Raising and lowering an index: `g(g⁻¹ a, v) = a ⬝ v` on `U`. -/
theorem IsCoordMetric.inv_mulVec_dot (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (a v : Fin n → ℝ) : ((g x)⁻¹ *ᵥ a) ⬝ᵥ (g x *ᵥ v) = a ⬝ᵥ v := by
  rw [dot_mulVec_comm (hg.symm x hx), Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (hg.isUnit_det x hx), Matrix.one_mulVec, dotProduct_comm]

/-- The remainder in `dF_w(v) = 2 T_w(P, v) - R₁`, of order `‖w‖⁴ ‖v‖`. -/
def radialErr1 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w v : Fin n → ℝ) :
    ℝ :=
  2 * (radial3 g x w ⬝ᵥ (dmat g x w *ᵥ v)) + radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)
    + radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)

/-- The remainder in `T_w(P, P) = F(w) + R₂`, of order `‖w‖⁵`. -/
def radialErr2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    ℝ :=
  radial2 g x w ⬝ᵥ (g x *ᵥ radial3 g x w) + radial3 g x w ⬝ᵥ (g x *ᵥ radial2 g x w)
    + radial3 g x w ⬝ᵥ (g x *ᵥ radial3 g x w)
    + w ⬝ᵥ (dmat g x w *ᵥ radial3 g x w) + radial3 g x w ⬝ᵥ (dmat g x w *ᵥ w)
    + (radial2 g x w + radial3 g x w) ⬝ᵥ (dmat g x w *ᵥ (radial2 g x w + radial3 g x w))
    + (1 / 2) * (w ⬝ᵥ (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w))
      + (radial2 g x w + radial3 g x w) ⬝ᵥ (ddmat g x w w *ᵥ w)
      + (radial2 g x w + radial3 g x w) ⬝ᵥ (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w)))

/-- **The radial field computes the derivative of the jet**, up to explicit terms of order
`‖w‖⁴ ‖v‖`: `dF_w(v) = 2 T_w(P, v) - R₁`, where `T_w` is the second-order Taylor polynomial of
the metric. -/
theorem IsCoordMetric.distJetDeriv_eq (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (w v : Fin n → ℝ) :
    distJetDeriv g x w v = 2 * (radial g x w ⬝ᵥ (taylorMetric g x w *ᵥ v))
      - radialErr1 g x w v := by
  unfold radialErr1
  have h0 := dot_mulVec_comm (hg.symm x hx) v w
  have h1 := dot_mulVec_comm (hg.dmat_transpose hx w) v w
  have hΓ := hg.dot_mulVec_chr hx v w w
  have hΓ' := dot_mulVec_comm (hg.symm x hx) (chr g x w w) v
  have hS := hg.inv_mulVec_dot hx (ellVec g x w) v
  rw [← ell_eq_dot] at hS
  unfold ell at hS
  simp only [radial, radial2, radial3, taylorMetric, Matrix.add_mulVec, Matrix.smul_mulVec,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold distJetDeriv
  simp only [add_dotProduct, dotProduct_add, Matrix.mulVec_add] at hS ⊢
  linear_combination (-1) * hS + h0 + (3 / 2) * h1 + hΓ' + hΓ

/-- **The radial field has the squared length of the jet**, up to explicit terms of order
`‖w‖⁵`: `T_w(P, P) = F(w) + R₂`. -/
theorem IsCoordMetric.radial_quad_eq (hg : IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (w : Fin n → ℝ) :
    radial g x w ⬝ᵥ (taylorMetric g x w *ᵥ radial g x w) = distJet g x w + radialErr2 g x w := by
  unfold radialErr2
  have hΓw := hg.dot_mulVec_chr hx w w w
  have hΓsym := dot_mulVec_comm (hg.symm x hx) (chr g x w w) w
  have hSw := hg.inv_mulVec_dot hx (ellVec g x w) w
  rw [← ell_eq_dot] at hSw
  unfold ell at hSw
  have hSsym := dot_mulVec_comm (hg.symm x hx) w ((g x)⁻¹ *ᵥ ellVec g x w)
  have hdsym := dot_mulVec_comm (hg.dmat_transpose hx w) (chr g x w w) w
  simp only [radial, radial2, radial3, taylorMetric, distJet, Matrix.add_mulVec,
    Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  simp only [add_dotProduct, dotProduct_add, Matrix.mulVec_add] at hSw
  linear_combination (-1 / 2) * hΓsym - hΓw + (1 / 2) * hSsym + hSw + (1 / 2) * hdsym

/-! ## Uniform bounds near a point -/

/-- `a b c ≤ a' b' c'` for nonnegative factors. -/
theorem mul_le_mul3 {a b c a' b' c' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) : a * b * c ≤ a' * b' * c' :=
  mul_le_mul (mul_le_mul ha hb hb0 (ha0.trans ha)) hc hc0
    (mul_nonneg (ha0.trans ha) (hb0.trans hb))

/-- `‖v‖² ≤ v ⬝ v` for the sup norm. -/
theorem norm_sq_le_eNormSq (v : Fin n → ℝ) : ‖v‖ ^ 2 ≤ eNormSq v := by
  have h0 := eNormSq_nonneg v
  have h : ‖v‖ ≤ √(eNormSq v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    unfold eNormSq dotProduct
    rw [sq]
    exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
      (Finset.mem_univ i)
  calc ‖v‖ ^ 2 ≤ √(eNormSq v) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) h 2
    _ = eNormSq v := Real.sq_sqrt h0

/-- **Uniform bounds at `x`**, with a constant `B ≥ 1`, on the ball of radius `δ ≤ 1` about `x`
(sup norms): the bilinear forms of `g`, `∂_u g` and `∂_u ∂_{u'} g`, the Christoffel contraction
and `g⁻¹` at `x` are bounded by `B`; the second-order Taylor polynomial of `g` at `x` approximates
`g(x + u)` to third order; and `g ≥ l (·) ⬝ (·)` on the ball. -/
structure LocalJet (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (B δ l : ℝ) : Prop where
  /-- `B ≥ 1`. -/
  one_le : 1 ≤ B
  /-- The radius is positive. -/
  δ_pos : 0 < δ
  /-- The radius is at most `1`. -/
  δ_le_one : δ ≤ 1
  /-- The lower bound is positive. -/
  l_pos : 0 < l
  /-- The ball lies in `U`. -/
  mem : ∀ u : Fin n → ℝ, ‖u‖ ≤ δ → x + u ∈ U
  /-- The metric at `x`. -/
  g_le : ∀ p q : Fin n → ℝ, |p ⬝ᵥ (g x *ᵥ q)| ≤ B * ‖p‖ * ‖q‖
  /-- The first derivatives at `x`. -/
  d_le : ∀ u p q : Fin n → ℝ, |p ⬝ᵥ (dmat g x u *ᵥ q)| ≤ B * ‖u‖ * ‖p‖ * ‖q‖
  /-- The second derivatives at `x`. -/
  dd_le : ∀ u u' p q : Fin n → ℝ,
    |p ⬝ᵥ (ddmat g x u u' *ᵥ q)| ≤ B * ‖u‖ * ‖u'‖ * ‖p‖ * ‖q‖
  /-- The Christoffel contraction at `x`. -/
  chr_le : ∀ u v : Fin n → ℝ, ‖chr g x u v‖ ≤ B * ‖u‖ * ‖v‖
  /-- The inverse metric at `x`. -/
  inv_le : ∀ a : Fin n → ℝ, ‖(g x)⁻¹ *ᵥ a‖ ≤ B * ‖a‖
  /-- Taylor's theorem for the metric on the ball. -/
  tay_le : ∀ u : Fin n → ℝ, ‖u‖ ≤ δ → ∀ p q : Fin n → ℝ,
    |p ⬝ᵥ ((g (x + u) - taylorMetric g x u) *ᵥ q)| ≤ B * ‖u‖ ^ 3 * ‖p‖ * ‖q‖
  /-- The metric is bounded below on the ball. -/
  low : ∀ u : Fin n → ℝ, ‖u‖ ≤ δ → ∀ v, l * eNormSq v ≤ normSq g (x + u) v

end Lightlike.Upstream.GeodesicExpansion
