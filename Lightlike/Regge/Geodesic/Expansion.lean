import Lightlike.Regge.Geodesic.Jet

/-!
# The expansion of the distance

Step 4 of RC6a. For a Riemannian metric `g` on `U` and a compact set `K ⊆ U`,

`d(x, x + w)² = F_x(w) + O(‖w‖⁵)` uniformly for `x ∈ K`, where
`F_x(w) = g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))`,

with `g`, its derivatives and the Christoffel contraction `Γ` taken at `x` (`distJet`). About
the midpoint `m` of the two points, with `Δ` their difference, the cubic term drops out:
`d(m - Δ/2, m + Δ/2)² = g_m(Δ, Δ) + Q_m(Δ) + O(‖Δ‖⁵)` with
`Q_m(Δ) = (1/24) ∂_Δ ∂_Δ g_m(Δ, Δ) - (1/12) g_m(Γ_m(Δ, Δ), Γ_m(Δ, Δ))`.

The upper bound uses the trial curve `t ↦ x + t w + ½ t (1 - t) Γ(w, w)`, whose energy is
`F_x(w) + O(‖w‖⁵)` by Taylor's theorem for `g`, and `L² ≤ E`.

The lower bound is a calibration. The field `P = w - ½ Γ(w, w) + p₃(w)` (`radial`, with a cubic
term `p₃` obtained by raising an index) satisfies `dF = 2 g(P, ·) + O(‖w‖⁴)` and
`g(P, P) = F + O(‖w‖⁵)`, two polynomial identities proven exactly. Hence
`|dF(v)| ≤ 2 √F (1 + C ρ³) |v|_g` on the ball of radius `ρ`, so along any curve from `x` that
stays in the ball, `√(F + η²)` grows at most `(1 + C ρ³)` times as fast as the length; curves
that leave the ball are long because `g` is comparable with the Euclidean metric.
-/

open Set Filter Topology Metric
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## The quartic jet of the squared distance -/

/-- The quartic Taylor polynomial of `d(x, x + w)²`:
`g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))` at `x`. -/
noncomputable def distJet (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) : ℝ :=
  w ⬝ᵥ (g x *ᵥ w) + (1 / 2) * (w ⬝ᵥ (dmat g x w *ᵥ w))
    + (1 / 6) * (w ⬝ᵥ (ddmat g x w w *ᵥ w))
    - (1 / 12) * (chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w))

/-- The derivative of `distJet g x` at `w` in the direction `v`. -/
noncomputable def distJetDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
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
      (hasDerivAt_pi.1 hp k).mul_const (Lightlike.pd k (fun y => g y i j) x)).mul (hasDerivAt_pi.1 hq j)
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
        (Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) x)).mul (hasDerivAt_pi.1 hq j)
  convert h using 1
  simp only [Pi.mul_apply, add_mul, Finset.sum_add_distrib]

theorem hasDerivAt_chr (x : Fin n → ℝ) {p q : ℝ → Fin n → ℝ} {p' q' : Fin n → ℝ} {t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => chr g x (p s) (q s)) (chr g x p' (q t) + chr g x (p t) q') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [chr, Pi.add_apply]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => HasDerivAt.fun_sum (u := Finset.univ)
    fun k _ => ((hasDerivAt_pi.1 hp j).const_mul (Lightlike.christoffel g i j k x)).mul
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
noncomputable def ell (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w v : Fin n → ℝ) : ℝ :=
  (1 / 6) * (v ⬝ᵥ (ddmat g x w w *ᵥ w)
      + w ⬝ᵥ (ddmat g x v w *ᵥ w + ddmat g x w v *ᵥ w + ddmat g x w w *ᵥ v))
    - (1 / 12) * ((chr g x v w + chr g x w v) ⬝ᵥ (g x *ᵥ chr g x w w)
      + chr g x w w ⬝ᵥ (g x *ᵥ (chr g x v w + chr g x w v)))
    + chr g x w w ⬝ᵥ (dmat g x w *ᵥ v) - w ⬝ᵥ (ddmat g x w w *ᵥ v)

/-- The vector of the linear form `ell g x w`. -/
noncomputable def ellVec (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ell g x w fun j => if i = j then 1 else 0

/-- The quadratic term `-½ Γ(w, w)` of the radial field. -/
noncomputable def radial2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  (-(1 / 2) : ℝ) • chr g x w w

/-- The cubic term `½ g⁻¹ ell` of the radial field. -/
noncomputable def radial3 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  (1 / 2 : ℝ) • ((g x)⁻¹ *ᵥ ellVec g x w)

/-- The **radial field** `P(w) = w - ½ Γ(w, w) + ½ g⁻¹ ell(w)`, an approximation of half the
gradient of `d(x, ·)²` at `x + w`. -/
noncomputable def radial (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  w + radial2 g x w + radial3 g x w

/-- The second-order Taylor polynomial of the metric at `x`, evaluated at `x + u`. -/
noncomputable def taylorMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x u : Fin n → ℝ) :
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
theorem _root_.Lightlike.IsCoordMetric.inv_mulVec_dot (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (a v : Fin n → ℝ) : ((g x)⁻¹ *ᵥ a) ⬝ᵥ (g x *ᵥ v) = a ⬝ᵥ v := by
  rw [dot_mulVec_comm (hg.symm x hx), Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (hg.isUnit_det x hx), Matrix.one_mulVec, dotProduct_comm]

/-- The remainder in `dF_w(v) = 2 T_w(P, v) - R₁`, of order `‖w‖⁴ ‖v‖`. -/
noncomputable def radialErr1 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w v : Fin n → ℝ) :
    ℝ :=
  2 * (radial3 g x w ⬝ᵥ (dmat g x w *ᵥ v)) + radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)
    + radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)

/-- The remainder in `T_w(P, P) = F(w) + R₂`, of order `‖w‖⁵`. -/
noncomputable def radialErr2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
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
theorem _root_.Lightlike.IsCoordMetric.distJetDeriv_eq (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
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
theorem _root_.Lightlike.IsCoordMetric.radial_quad_eq (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
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

namespace LocalJet

variable {x : Fin n → ℝ} {B δ l : ℝ}

theorem B_nonneg (h : LocalJet g U x B δ l) : 0 ≤ B := zero_le_one.trans h.one_le

theorem pow_le_pow (h : LocalJet g U x B δ l) {a b : ℕ} (hab : a ≤ b) : B ^ a ≤ B ^ b :=
  pow_le_pow_right₀ h.one_le hab

theorem le_pow (h : LocalJet g U x B δ l) {k : ℕ} (hk : 1 ≤ k) : B ≤ B ^ k := by
  simpa using h.pow_le_pow hk

/-- Monomials `B^a ‖w‖^b` decrease as `a` decreases and `b` increases, for `‖w‖ ≤ 1`. -/
theorem monom_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) {a a' b b' : ℕ}
    (ha : a ≤ a') (hb : b' ≤ b) : B ^ a * ‖w‖ ^ b ≤ B ^ a' * ‖w‖ ^ b' :=
  mul_le_mul (h.pow_le_pow ha) (pow_le_pow_of_le_one (norm_nonneg w) hw hb) (by positivity)
    (pow_nonneg h.B_nonneg _)

theorem norm_chr_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖chr g x w w‖ ≤ B * ‖w‖ ^ 2 :=
  (h.chr_le w w).trans_eq (by ring)

theorem norm_radial2_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖radial2 g x w‖ ≤ B * ‖w‖ ^ 2 := by
  unfold radial2
  rw [norm_smul, Real.norm_eq_abs, show |(-(1 / 2) : ℝ)| = 1 / 2 by norm_num]
  have := h.norm_chr_le w
  have := norm_nonneg (chr g x w w)
  linarith

/-- The cubic form `ell` is bounded by `3 B³ ‖w‖³ ‖v‖`. -/
theorem abs_ell_le (h : LocalJet g U x B δ l) (w v : Fin n → ℝ) :
    |ell g x w v| ≤ 3 * B ^ 3 * ‖w‖ ^ 3 * ‖v‖ := by
  have hB := h.B_nonneg
  have hε := norm_nonneg w
  have hν := norm_nonneg v
  have hX : 0 ≤ ‖w‖ ^ 3 * ‖v‖ := by positivity
  have hB1 : B * (‖w‖ ^ 3 * ‖v‖) ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖) :=
    mul_le_mul_of_nonneg_right (h.le_pow (by norm_num)) hX
  have hB2 : B ^ 2 * (‖w‖ ^ 3 * ‖v‖) ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖) :=
    mul_le_mul_of_nonneg_right (h.pow_le_pow (by norm_num)) hX
  have hΓ := h.norm_chr_le w
  have hΓ0 := norm_nonneg (chr g x w w)
  have k1 : ∀ u u' : Fin n → ℝ, ‖chr g x u u'‖ ≤ B * ‖u‖ * ‖u'‖ →
      B * ‖chr g x u u'‖ * ‖chr g x w w‖ ≤ B * (B * ‖u‖ * ‖u'‖) * (B * ‖w‖ ^ 2) :=
    fun u u' hu => mul_le_mul3 le_rfl hu hΓ hB (norm_nonneg _) hΓ0
  have k2 : ∀ u u' : Fin n → ℝ, ‖chr g x u u'‖ ≤ B * ‖u‖ * ‖u'‖ →
      B * ‖chr g x w w‖ * ‖chr g x u u'‖ ≤ B * (B * ‖w‖ ^ 2) * (B * ‖u‖ * ‖u'‖) :=
    fun u u' hu => mul_le_mul3 le_rfl hΓ hu hB hΓ0 (norm_nonneg _)
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.dd_le w w v w).trans_eq (by ring) :
    |v ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.dd_le v w w w).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x v w *ᵥ w)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.dd_le w v w w).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w v *ᵥ w)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a4, b4⟩ := abs_le.mp ((h.dd_le w w w v).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ B * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a5, b5⟩ := abs_le.mp (((h.g_le _ _).trans (k1 v w (h.chr_le v w))).trans_eq (by ring) :
    |chr g x v w ⬝ᵥ (g x *ᵥ chr g x w w)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a6, b6⟩ := abs_le.mp (((h.g_le _ _).trans (k1 w v (h.chr_le w v))).trans_eq (by ring) :
    |chr g x w v ⬝ᵥ (g x *ᵥ chr g x w w)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a7, b7⟩ := abs_le.mp (((h.g_le _ _).trans (k2 v w (h.chr_le v w))).trans_eq (by ring) :
    |chr g x w w ⬝ᵥ (g x *ᵥ chr g x v w)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a8, b8⟩ := abs_le.mp (((h.g_le _ _).trans (k2 w v (h.chr_le w v))).trans_eq (by ring) :
    |chr g x w w ⬝ᵥ (g x *ᵥ chr g x w v)| ≤ B ^ 3 * (‖w‖ ^ 3 * ‖v‖))
  obtain ⟨a9, b9⟩ := abs_le.mp (((h.d_le w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hΓ (mul_nonneg hB hε)) hν)).trans_eq (by ring) :
    |chr g x w w ⬝ᵥ (dmat g x w *ᵥ v)| ≤ B ^ 2 * (‖w‖ ^ 3 * ‖v‖))
  unfold ell
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  rw [abs_le]
  constructor <;> nlinarith

/-- The vector of `ell` is bounded by `3 B³ ‖w‖³`. -/
theorem norm_ellVec_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖ellVec g x w‖ ≤ 3 * B ^ 3 * ‖w‖ ^ 3 := by
  have hc : 0 ≤ 3 * B ^ 3 * ‖w‖ ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h.B_nonneg 3)) (pow_nonneg (norm_nonneg w) 3)
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have he : ‖(fun j => if i = j then (1 : ℝ) else 0)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    show ‖(if i = j then (1 : ℝ) else 0)‖ ≤ 1
    split_ifs <;> simp
  calc |ellVec g x w i| = |ell g x w fun j => if i = j then 1 else 0| := rfl
    _ ≤ 3 * B ^ 3 * ‖w‖ ^ 3 * ‖(fun j => if i = j then (1 : ℝ) else 0)‖ := h.abs_ell_le w _
    _ ≤ 3 * B ^ 3 * ‖w‖ ^ 3 * 1 := mul_le_mul_of_nonneg_left he hc
    _ = _ := mul_one _

theorem norm_radial3_le (h : LocalJet g U x B δ l) (w : Fin n → ℝ) :
    ‖radial3 g x w‖ ≤ 2 * B ^ 4 * ‖w‖ ^ 3 := by
  unfold radial3
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 : ‖(g x)⁻¹ *ᵥ ellVec g x w‖ ≤ 3 * (B ^ 4 * ‖w‖ ^ 3) :=
    (h.inv_le _).trans ((mul_le_mul_of_nonneg_left (h.norm_ellVec_le w) h.B_nonneg).trans_eq
      (by ring))
  have hM : 0 ≤ B ^ 4 * ‖w‖ ^ 3 := mul_nonneg (by positivity) (pow_nonneg (norm_nonneg w) 3)
  linarith

theorem norm_radial23_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    ‖radial2 g x w + radial3 g x w‖ ≤ 3 * (B ^ 4 * ‖w‖ ^ 2) := by
  have h1 := (norm_add_le _ _).trans (add_le_add (h.norm_radial2_le w) (h.norm_radial3_le w))
  have e1 : B ^ 1 * ‖w‖ ^ 2 ≤ B ^ 4 * ‖w‖ ^ 2 := h.monom_le hw (by norm_num) le_rfl
  have e2 : B ^ 4 * ‖w‖ ^ 3 ≤ B ^ 4 * ‖w‖ ^ 2 := h.monom_le hw le_rfl (by norm_num)
  simp only [pow_one] at e1
  linarith

theorem norm_radial_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    ‖radial g x w‖ ≤ 4 * (B ^ 4 * ‖w‖) := by
  have h1 : ‖radial g x w‖ ≤ ‖w‖ + ‖radial2 g x w + radial3 g x w‖ := by
    unfold radial; rw [add_assoc]; exact norm_add_le _ _
  have h2 := h.norm_radial23_le hw
  have e1 : B ^ 0 * ‖w‖ ^ 1 ≤ B ^ 4 * ‖w‖ ^ 1 := h.monom_le hw (by norm_num) le_rfl
  have e2 : B ^ 4 * ‖w‖ ^ 2 ≤ B ^ 4 * ‖w‖ ^ 1 := h.monom_le hw le_rfl (by norm_num)
  simp only [pow_zero, pow_one, one_mul] at e1 e2
  linarith

/-- `|R₁| ≤ 7 B⁵ ‖w‖⁴ ‖v‖`. -/
theorem abs_radialErr1_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1)
    (v : Fin n → ℝ) : |radialErr1 g x w v| ≤ 7 * (B ^ 5 * ‖w‖ ^ 4) * ‖v‖ := by
  have hB := h.B_nonneg
  have hε := norm_nonneg w
  have hν := norm_nonneg v
  have r2 := h.norm_radial2_le w
  have r3 := h.norm_radial3_le w
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.d_le w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r3 (mul_nonneg hB hε)) hν) |>.trans_eq (by ring) :
    |radial3 g x w ⬝ᵥ (dmat g x w *ᵥ v)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 4) * ‖v‖)
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.dd_le w w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r2 (by positivity)) hν) |>.trans_eq (by ring) :
    |radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ (B ^ 2 * ‖w‖ ^ 4) * ‖v‖)
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.dd_le w w _ v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r3 (by positivity)) hν) |>.trans_eq (by ring) :
    |radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 5) * ‖v‖)
  have e2 := mul_le_mul_of_nonneg_right (h.monom_le hw (a := 2) (a' := 5) (b := 4) (b' := 4)
    (by norm_num) le_rfl) hν
  have e3 := mul_le_mul_of_nonneg_right (h.monom_le hw (a := 5) (a' := 5) (b := 5) (b' := 4)
    le_rfl (by norm_num)) hν
  unfold radialErr1
  rw [abs_le]
  constructor <;> linarith

/-- `|R₂| ≤ 30 B⁹ ‖w‖⁵`. -/
theorem abs_radialErr2_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    |radialErr2 g x w| ≤ 30 * (B ^ 9 * ‖w‖ ^ 5) := by
  have hB := h.B_nonneg
  have hε := norm_nonneg w
  have r2 := h.norm_radial2_le w
  have r3 := h.norm_radial3_le w
  have rs := h.norm_radial23_le hw
  have n2 := norm_nonneg (radial2 g x w)
  have n3 := norm_nonneg (radial3 g x w)
  have ns := norm_nonneg (radial2 g x w + radial3 g x w)
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl r2 r3 hB n2 n3)
    |>.trans_eq (by ring) : |radial2 g x w ⬝ᵥ (g x *ᵥ radial3 g x w)| ≤ 2 * (B ^ 6 * ‖w‖ ^ 5))
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl r3 r2 hB n3 n2)
    |>.trans_eq (by ring) : |radial3 g x w ⬝ᵥ (g x *ᵥ radial2 g x w)| ≤ 2 * (B ^ 6 * ‖w‖ ^ 5))
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl r3 r3 hB n3 n3)
    |>.trans_eq (by ring) : |radial3 g x w ⬝ᵥ (g x *ᵥ radial3 g x w)| ≤ 4 * (B ^ 9 * ‖w‖ ^ 6))
  obtain ⟨a4, b4⟩ := abs_le.mp ((h.d_le w w _).trans (mul_le_mul_of_nonneg_left r3
    (by positivity)) |>.trans_eq (by ring) :
    |w ⬝ᵥ (dmat g x w *ᵥ radial3 g x w)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a5, b5⟩ := abs_le.mp ((h.d_le w _ w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left r3 (mul_nonneg hB hε)) hε) |>.trans_eq (by ring) :
    |radial3 g x w ⬝ᵥ (dmat g x w *ᵥ w)| ≤ 2 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a6, b6⟩ := abs_le.mp ((h.d_le w _ _).trans (mul_le_mul3 le_rfl rs rs
    (mul_nonneg hB hε) ns ns) |>.trans_eq (by ring) :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (dmat g x w *ᵥ (radial2 g x w + radial3 g x w))| ≤
      9 * (B ^ 9 * ‖w‖ ^ 5))
  obtain ⟨a7, b7⟩ := abs_le.mp ((h.dd_le w w w _).trans (mul_le_mul_of_nonneg_left rs
    (by positivity)) |>.trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w))| ≤ 3 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a8, b8⟩ := abs_le.mp ((h.dd_le w w _ w).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left rs (by positivity)) hε) |>.trans_eq (by ring) :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ 3 * (B ^ 5 * ‖w‖ ^ 5))
  obtain ⟨a9, b9⟩ := abs_le.mp ((h.dd_le w w _ _).trans (mul_le_mul3 le_rfl rs rs
    (by positivity) ns ns) |>.trans_eq (by ring) :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w))| ≤
      9 * (B ^ 9 * ‖w‖ ^ 6))
  have e6 := h.monom_le hw (a := 6) (a' := 9) (b := 5) (b' := 5) (by norm_num) le_rfl
  have e5 := h.monom_le hw (a := 5) (a' := 9) (b := 5) (b' := 5) (by norm_num) le_rfl
  have e96 := h.monom_le hw (a := 9) (a' := 9) (b := 6) (b' := 5) le_rfl (by norm_num)
  unfold radialErr2
  rw [abs_le]
  constructor <;> linarith

/-- The jet differs from `g(w, w)` by at most `B³ ‖w‖³`. -/
theorem abs_distJet_sub_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    |distJet g x w - w ⬝ᵥ (g x *ᵥ w)| ≤ B ^ 3 * ‖w‖ ^ 3 := by
  have hB := h.B_nonneg
  have hΓ := h.norm_chr_le w
  have hΓ0 := norm_nonneg (chr g x w w)
  obtain ⟨a1, b1⟩ := abs_le.mp ((h.d_le w w w).trans_eq (by ring) :
    |w ⬝ᵥ (dmat g x w *ᵥ w)| ≤ B ^ 1 * ‖w‖ ^ 3)
  obtain ⟨a2, b2⟩ := abs_le.mp ((h.dd_le w w w w).trans_eq (by ring) :
    |w ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ B ^ 1 * ‖w‖ ^ 4)
  obtain ⟨a3, b3⟩ := abs_le.mp ((h.g_le _ _).trans (mul_le_mul3 le_rfl hΓ hΓ hB hΓ0 hΓ0)
    |>.trans_eq (by ring) : |chr g x w w ⬝ᵥ (g x *ᵥ chr g x w w)| ≤ B ^ 3 * ‖w‖ ^ 4)
  have e1 := h.monom_le hw (a := 1) (a' := 3) (b := 3) (b' := 3) (by norm_num) le_rfl
  have e2 := h.monom_le hw (a := 1) (a' := 3) (b := 4) (b' := 3) (by norm_num) (by norm_num)
  have e3 := h.monom_le hw (a := 3) (a' := 3) (b := 4) (b' := 3) le_rfl (by norm_num)
  unfold distJet
  rw [abs_le]
  constructor <;> linarith

/-- The jet is at most `2 B³ ‖w‖²`. -/
theorem distJet_le (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    distJet g x w ≤ 2 * (B ^ 3 * ‖w‖ ^ 2) := by
  have h1 := (abs_le.mp (h.abs_distJet_sub_le hw)).2
  have h2 := (abs_le.mp ((h.g_le w w).trans_eq (by ring) :
    |w ⬝ᵥ (g x *ᵥ w)| ≤ B ^ 1 * ‖w‖ ^ 2)).2
  have e1 := h.monom_le hw (a := 1) (a' := 3) (b := 2) (b' := 2) (by norm_num) le_rfl
  have e2 := h.monom_le hw (a := 3) (a' := 3) (b := 3) (b' := 2) le_rfl (by norm_num)
  linarith

/-- The jet is at least `l ‖w‖² - B³ ‖w‖³`. -/
theorem distJet_ge (h : LocalJet g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    l * ‖w‖ ^ 2 - B ^ 3 * ‖w‖ ^ 3 ≤ distJet g x w := by
  have h1 := (abs_le.mp (h.abs_distJet_sub_le hw)).1
  have h2 := h.low 0 (by simpa using h.δ_pos.le) w
  rw [add_zero] at h2
  unfold normSq at h2
  have h3 := mul_le_mul_of_nonneg_left (norm_sq_le_eNormSq w) h.l_pos.le
  linarith

end LocalJet

/-- **Uniform local bounds on a compact set**: for a compact `K ⊆ U` one triple `B, δ, l` gives
`LocalJet g U x B δ l` at every `x ∈ K`. -/
theorem IsRiemMetric.exists_localJet (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) : ∃ B δ l : ℝ, ∀ x ∈ K, LocalJet g U x B δ l := by
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hδ : 0 < min δ₀ 1 := lt_min hδ₀ one_pos
  have hK' : IsCompact (cthickening (min δ₀ 1) K) := hK.cthickening
  have hK'U : cthickening (min δ₀ 1) K ⊆ U :=
    (cthickening_mono (min_le_left _ _) K).trans hδ₀U
  have hball : ∀ x ∈ K, ∀ u : Fin n → ℝ, ‖u‖ ≤ min δ₀ 1 → x + u ∈ cthickening (min δ₀ 1) K :=
    fun x hx u hu => closedBall_subset_cthickening hx _
      (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hu)
  obtain ⟨m, hm0, hm⟩ := hg.coord.exists_jet_bound hK' hK'U
  obtain ⟨l, L, hl, -, hlL⟩ := hg.exists_bounds_of_isCompact hK' hK'U
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have p1 := mul_nonneg hn hm0
  have p2 := mul_nonneg (pow_nonneg hn 2) hm0
  have p3 := mul_nonneg (pow_nonneg hn 3) hm0
  have p4 := mul_nonneg (pow_nonneg hn 4) hm0
  have p5 := mul_nonneg (pow_nonneg hn 5) hm0
  set B : ℝ := n ^ 5 * m + n ^ 4 * m + n ^ 3 * m + n ^ 2 * m + n * m + 1 with hB
  have t1 : (n : ℝ) * m ≤ B := by linarith
  have t2 : (n : ℝ) ^ 2 * m ≤ B := by linarith
  have t3 : (n : ℝ) ^ 3 * m ≤ B := by linarith
  have t4 : (n : ℝ) ^ 4 * m ≤ B := by linarith
  have t5 : (n : ℝ) ^ 5 * m ≤ B := by linarith
  refine ⟨B, min δ₀ 1, l, fun x hx => ?_⟩
  have hx' : x ∈ cthickening (min δ₀ 1) K := self_subset_cthickening K hx
  have hseg : ∀ u : Fin n → ℝ, ‖u‖ ≤ min δ₀ 1 → ∀ s ∈ Icc (0 : ℝ) 1,
      x + s • u ∈ cthickening (min δ₀ 1) K := fun u hu s hs => hball x hx _ (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg u])
  refine ⟨by linarith, hδ, min_le_right _ _, hl, fun u hu => hK'U (hball x hx u hu), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro p q
    calc _ ≤ _ := abs_dot_mulVec_le hm0 (fun i j => (hm x hx' i j i i i).1) p q
      _ ≤ B * ‖p‖ * ‖q‖ := by gcongr
  · intro u p q
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity)
          (fun i j => abs_dmat_le (fun i j k => (hm x hx' i j k k k).2.2.1) i j) p q
      _ = n ^ 3 * m * ‖u‖ * ‖p‖ * ‖q‖ := by ring
      _ ≤ B * ‖u‖ * ‖p‖ * ‖q‖ := by gcongr
  · intro u u' p q
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity)
          (fun i j => abs_ddmat_le (fun i j k l => (hm x hx' i j k l l).2.2.2.1) i j) p q
      _ = n ^ 4 * m * ‖u‖ * ‖u'‖ * ‖p‖ * ‖q‖ := by ring
      _ ≤ B * ‖u‖ * ‖u'‖ * ‖p‖ * ‖q‖ := by gcongr
  · intro u v
    calc _ ≤ _ := norm_chr_le hm0 (fun i j k => (hm x hx' i j k k k).2.2.2.2.2.1)
      _ ≤ B * ‖u‖ * ‖v‖ := by gcongr
  · intro a
    calc _ ≤ _ := norm_mulVec_le hm0 (fun i j => (hm x hx' i j i i i).2.1) a
      _ ≤ B * ‖a‖ := by gcongr
  · intro u hu p q
    have hE : ∀ i j, |(g (x + u) - taylorMetric g x u) i j| ≤ n ^ 3 * m * ‖u‖ ^ 3 := by
      intro i j
      have h := taylor_three (f := fun y => g y i j) (hg.coord.smooth i j) hg.coord.isOpen
        (fun s hs => hK'U (hseg u hu s hs))
        (fun s hs k l p => (hm _ (hseg u hu s hs) i j k l p).2.2.2.2.1)
      have e : (g (x + u) - taylorMetric g x u) i j = g (x + u) i j - g x i j
          - ∑ k, u k * Lightlike.pd k (fun y => g y i j) x
          - (1 / 2) * ∑ k, ∑ l, u k * u l * Lightlike.pd l (Lightlike.pd k (fun y => g y i j)) x := by
        simp only [taylorMetric, dmat, ddmat, Matrix.sub_apply, Matrix.add_apply,
          Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
        ring
      rw [e]; exact h
    calc _ ≤ _ := abs_dot_mulVec_le (by positivity) hE p q
      _ = n ^ 5 * m * ‖u‖ ^ 3 * ‖p‖ * ‖q‖ := by ring
      _ ≤ B * ‖u‖ ^ 3 * ‖p‖ * ‖q‖ := by gcongr
  · intro u hu v
    exact (hlL _ (hball x hx u hu) v).1

/-! ## The calibration estimate -/

/-- **Cauchy–Schwarz** for the metric: `|g(p, v)| ≤ |p|_g |v|_g`. -/
theorem IsRiemMetric.abs_dot_le (hg : IsRiemMetric g U) {z : Fin n → ℝ} (hz : z ∈ U)
    (p v : Fin n → ℝ) : |p ⬝ᵥ (g z *ᵥ v)| ≤ √(normSq g z p) * √(normSq g z v) := by
  have hsym := dot_mulVec_comm (hg.coord.symm z hz) v p
  have hq : ∀ s : ℝ, 0 ≤ normSq g z p * (s * s) + 2 * (p ⬝ᵥ (g z *ᵥ v)) * s + normSq g z v := by
    intro s
    have h := hg.normSq_nonneg hz (v + s • p)
    have e : normSq g z (v + s • p) =
        normSq g z p * (s * s) + 2 * (p ⬝ᵥ (g z *ᵥ v)) * s + normSq g z v := by
      unfold normSq
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      linear_combination s * hsym
    rw [← e]; exact h
  have hd := discrim_le_zero hq
  unfold discrim at hd
  rw [← Real.sqrt_mul (hg.normSq_nonneg hz p)]
  exact Real.abs_le_sqrt (by nlinarith [hd])

/-- The real-variable step of the calibration: if `F ≥ μ ε²`, `|A| ≤ √PP V` with
`PP ≤ F + D ε⁵`, `√l a ≤ V` and `|dF| ≤ 2 |A| + E ε⁴ a`, then
`|dF| ≤ 2 √F V (1 + κ ε³)` with `κ = D / (2μ) + E / (2 √μ √l)`. -/
theorem calib_real {F μ ε D E V a A PP dF l : ℝ} (hε : 0 ≤ ε) (hμ : 0 < μ) (hl : 0 < l)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (ha : 0 ≤ a) (hF : μ * ε ^ 2 ≤ F) (hA : |A| ≤ √PP * V)
    (hPP : PP ≤ F + D * ε ^ 5) (hV : √l * a ≤ V) (hdF : |dF| ≤ 2 * |A| + E * ε ^ 4 * a) :
    |dF| ≤ 2 * √F * V * (1 + (D / (2 * μ) + E / (2 * (√μ * √l))) * ε ^ 3) := by
  have hF0 : 0 ≤ F := le_trans (by positivity) hF
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  have hs0 : 0 ≤ √F := Real.sqrt_nonneg _
  have hss : √F ^ 2 = F := Real.sq_sqrt hF0
  have hsμ : √μ * ε ≤ √F := by
    have := Real.sqrt_le_sqrt hF
    rwa [Real.sqrt_mul hμ.le, Real.sqrt_sq hε] at this
  have hk1 : 0 ≤ D / (2 * μ) * ε ^ 3 := by positivity
  have h1 : F + D * ε ^ 5 ≤ (√F * (1 + D / (2 * μ) * ε ^ 3)) ^ 2 := by
    have e : 2 * (D / (2 * μ) * ε ^ 3) * F = D * ε ^ 3 * (F / μ) := by field_simp
    have hFμ : ε ^ 2 ≤ F / μ := by rw [le_div_iff₀ hμ]; linarith
    have h3 : D * ε ^ 5 ≤ 2 * (D / (2 * μ) * ε ^ 3) * F := by
      rw [e]
      calc D * ε ^ 5 = D * ε ^ 3 * ε ^ 2 := by ring
        _ ≤ D * ε ^ 3 * (F / μ) := by gcongr
    have e2 : (√F * (1 + D / (2 * μ) * ε ^ 3)) ^ 2 =
        F + 2 * (D / (2 * μ) * ε ^ 3) * F + (D / (2 * μ) * ε ^ 3) ^ 2 * F := by
      rw [mul_pow, hss]; ring
    rw [e2]
    nlinarith [sq_nonneg (D / (2 * μ) * ε ^ 3)]
  have h2 : √PP ≤ √F * (1 + D / (2 * μ) * ε ^ 3) :=
    calc √PP ≤ √(F + D * ε ^ 5) := Real.sqrt_le_sqrt hPP
      _ ≤ √((√F * (1 + D / (2 * μ) * ε ^ 3)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = √F * (1 + D / (2 * μ) * ε ^ 3) := Real.sqrt_sq (by positivity)
  have hsl : 0 < √l := Real.sqrt_pos.2 hl
  have hsm : 0 < √μ := Real.sqrt_pos.2 hμ
  have h3 : E * ε ^ 4 * a ≤ 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ 3) := by
    have e : 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ 3) = √F * V * E * ε ^ 3 / (√μ * √l) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc E * ε ^ 4 * a * (√μ * √l) = (E * ε ^ 3) * (√μ * ε) * (√l * a) := by ring
      _ ≤ (E * ε ^ 3) * √F * V := by gcongr
      _ = √F * V * E * ε ^ 3 := by ring
  have h4 : |A| ≤ √F * (1 + D / (2 * μ) * ε ^ 3) * V := hA.trans (mul_le_mul_of_nonneg_right h2 hV0)
  calc |dF| ≤ 2 * |A| + E * ε ^ 4 * a := hdF
    _ ≤ 2 * (√F * (1 + D / (2 * μ) * ε ^ 3) * V)
        + 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ 3) := add_le_add (by linarith) h3
    _ = 2 * √F * V * (1 + (D / (2 * μ) + E / (2 * (√μ * √l))) * ε ^ 3) := by ring

/-- The constant of the calibration estimate. -/
noncomputable def calibConst (B l : ℝ) : ℝ :=
  46 * B ^ 9 / (2 * (l / 2)) + 15 * B ^ 5 / (2 * (√(l / 2) * √l))

theorem calibConst_nonneg {B l : ℝ} (hB : 0 ≤ B) (hl : 0 < l) : 0 ≤ calibConst B l := by
  unfold calibConst; positivity

/-- **The calibration estimate.** Near `x`, the differential of the jet `F = distJet g x` is
bounded by the metric: `|dF_u(v)| ≤ 2 √F(u) |v|_g (1 + κ ‖u‖³)`, with `|v|_g` the length at
`x + u`. -/
theorem LocalJet.abs_distJetDeriv_le (hg : IsRiemMetric g U) {x : Fin n → ℝ} {B δ l : ℝ}
    (h : LocalJet g U x B δ l) {u : Fin n → ℝ} (hu : ‖u‖ ≤ δ) (hul : B ^ 3 * ‖u‖ ≤ l / 2)
    (v : Fin n → ℝ) :
    |distJetDeriv g x u v| ≤
      2 * √(distJet g x u) * √(normSq g (x + u) v) * (1 + calibConst B l * ‖u‖ ^ 3) := by
  have hu1 : ‖u‖ ≤ 1 := hu.trans h.δ_le_one
  have hx : x ∈ U := by simpa using h.mem 0 (by simpa using h.δ_pos.le)
  have hxu : x + u ∈ U := h.mem u hu
  have hB := h.B_nonneg
  have hε := norm_nonneg u
  have hν := norm_nonneg v
  have hP := h.norm_radial_le hu1
  have hP0 := norm_nonneg (radial g x u)
  have split : ∀ q, radial g x u ⬝ᵥ (taylorMetric g x u *ᵥ q) =
      radial g x u ⬝ᵥ (g (x + u) *ᵥ q)
        - radial g x u ⬝ᵥ ((g (x + u) - taylorMetric g x u) *ᵥ q) := by
    intro q; rw [Matrix.sub_mulVec, dotProduct_sub]; ring
  have tv : |radial g x u ⬝ᵥ ((g (x + u) - taylorMetric g x u) *ᵥ v)| ≤
      4 * (B ^ 5 * ‖u‖ ^ 4) * ‖v‖ := (h.tay_le u hu _ v).trans (by
    calc B * ‖u‖ ^ 3 * ‖radial g x u‖ * ‖v‖ ≤ B * ‖u‖ ^ 3 * (4 * (B ^ 4 * ‖u‖)) * ‖v‖ := by
          gcongr
      _ = _ := by ring)
  have tp : |radial g x u ⬝ᵥ ((g (x + u) - taylorMetric g x u) *ᵥ radial g x u)| ≤
      16 * (B ^ 9 * ‖u‖ ^ 5) := (h.tay_le u hu _ _).trans (by
    calc B * ‖u‖ ^ 3 * ‖radial g x u‖ * ‖radial g x u‖ ≤
          B * ‖u‖ ^ 3 * (4 * (B ^ 4 * ‖u‖)) * (4 * (B ^ 4 * ‖u‖)) := by gcongr
      _ = _ := by ring)
  have hPP : normSq g (x + u) (radial g x u) ≤ distJet g x u + 46 * B ^ 9 * ‖u‖ ^ 5 := by
    have e := split (radial g x u)
    rw [hg.coord.radial_quad_eq hx u] at e
    have a1 := (abs_le.mp (h.abs_radialErr2_le hu1)).2
    have a2 := (abs_le.mp tp).2
    unfold normSq
    linarith
  have hdF : |distJetDeriv g x u v| ≤
      2 * |radial g x u ⬝ᵥ (g (x + u) *ᵥ v)| + 15 * B ^ 5 * ‖u‖ ^ 4 * ‖v‖ := by
    rw [hg.coord.distJetDeriv_eq hx u v, split v]
    have a1 := abs_le.mp (h.abs_radialErr1_le hu1 v)
    have a2 := abs_le.mp tv
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (radial g x u ⬝ᵥ (g (x + u) *ᵥ v)),
        neg_abs_le (radial g x u ⬝ᵥ (g (x + u) *ᵥ v))]
  have hF : l / 2 * ‖u‖ ^ 2 ≤ distJet g x u := by
    have a1 := h.distJet_ge hu1
    have a2 : B ^ 3 * ‖u‖ ^ 3 ≤ l / 2 * ‖u‖ ^ 2 :=
      calc B ^ 3 * ‖u‖ ^ 3 = B ^ 3 * ‖u‖ * ‖u‖ ^ 2 := by ring
        _ ≤ l / 2 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hul (sq_nonneg _)
    linarith
  have hV : √l * ‖v‖ ≤ √(normSq g (x + u) v) := by
    have := Real.sqrt_le_sqrt
      ((mul_le_mul_of_nonneg_left (norm_sq_le_eNormSq v) h.l_pos.le).trans (h.low u hu v))
    rwa [Real.sqrt_mul h.l_pos.le, Real.sqrt_sq hν] at this
  unfold calibConst
  exact calib_real hε (by linarith [h.l_pos]) h.l_pos (by positivity) (by positivity) hν hF
    (hg.abs_dot_le hxu _ v) hPP hV hdF

end Lightlike.Geodesic
