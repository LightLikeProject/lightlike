import Lightlike.Regge.Geodesic.Jet3

/-!
# The quintic term of the squared distance and its radial field

Part of the sixth-order expansion of the squared geodesic distance (step 4 of RC6a). In
coordinates, with all coefficients at `x`, `G = g`, `A(u) = ∂_u g`, `B(u, v) = ∂_u ∂_v g`,
`C(u, v, s) = ∂_u ∂_v ∂_s g` and `γ = Γ(w, w)`, the squared distance from `x` to `x + w` is
`F₅(w) + O(‖w‖⁶)` with `F₅ = distJet + quint` and

  `quint(w) = (1/24) w·C(w,w,w)w − (1/12) w·B(w,w)γ + (1/24) w·B(w,γ)w + (1/24) γ·A(w)γ`.

This is the coordinate expansion of the squared distance (twice Synge's world function) about one
end point, to one order beyond `distJet`; see L. Brewin, *Riemann normal coordinate expansions
using Cadabra*, arXiv:0903.2087 (2009), Section 9, for the geodesic expansions it rests on.

The lower bound uses a calibration with the radial field `P₅ = P + P₄`, where `P` is the radial
field of `Expansion.lean` and `P₄ = ½ g⁻¹ ℓ₄`, with `ℓ₄` the quartic part of `½ dF₅ − g(P, ·)`.
With `T₃` the third-order Taylor polynomial of the metric, two polynomial identities hold exactly:

* `distJet5Deriv_eq`: `dF₅_w(v) = 2 T₃(P₅, v) − R₁`, with `R₁ = O(‖w‖⁵ ‖v‖)`;
* `radial5_quad_eq`: `T₃(P₅, P₅) = F₅(w) + R₂`, with `R₂ = O(‖w‖⁶)`.

The order-5 terms cancel by `quint_key`: `4 quint = ⅙ w·C(w,w,w)w + ½ ℓ(w; γ) − ¼ γ·A(w)γ`,
where `ℓ` is the cubic form `ell` of `Expansion.lean`.
-/

open Set Filter Topology Metric
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-! ## The quintic term and its derivative -/

/-- The quintic term of the squared distance from `x` to `x + w`:
`(1/24) w·C(w,w,w)w − (1/12) w·B(w,w)γ + (1/24) w·B(w,γ)w + (1/24) γ·A(w)γ` with
`γ = Γ_x(w, w)`. -/
noncomputable def quint (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) : ℝ :=
  (1 / 24) * (w ⬝ᵥ (dddmat g x w w w *ᵥ w)) - (1 / 12) * (w ⬝ᵥ (ddmat g x w w *ᵥ chr g x w w))
    + (1 / 24) * (w ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ w))
    + (1 / 24) * (chr g x w w ⬝ᵥ (dmat g x w *ᵥ chr g x w w))

/-- The quintic jet `F₅ = distJet + quint` of the squared distance from `x`. -/
noncomputable def distJet5 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) : ℝ :=
  distJet g x w + quint g x w

/-- The derivative of `quint g x` at `w` in the direction `v`. -/
noncomputable def quintDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w v : Fin n → ℝ) :
    ℝ :=
  (1 / 24) * (v ⬝ᵥ (dddmat g x w w w *ᵥ w) + w ⬝ᵥ (dddmat g x v w w *ᵥ w
      + dddmat g x w v w *ᵥ w + dddmat g x w w v *ᵥ w + dddmat g x w w w *ᵥ v))
    - (1 / 12) * (v ⬝ᵥ (ddmat g x w w *ᵥ chr g x w w) + w ⬝ᵥ (ddmat g x v w *ᵥ chr g x w w
      + ddmat g x w v *ᵥ chr g x w w + ddmat g x w w *ᵥ (chr g x v w + chr g x w v)))
    + (1 / 24) * (v ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ w) + w ⬝ᵥ (ddmat g x v (chr g x w w) *ᵥ w
      + ddmat g x w (chr g x v w + chr g x w v) *ᵥ w + ddmat g x w (chr g x w w) *ᵥ v))
    + (1 / 24) * ((chr g x v w + chr g x w v) ⬝ᵥ (dmat g x w *ᵥ chr g x w w)
      + chr g x w w ⬝ᵥ (dmat g x v *ᵥ chr g x w w + dmat g x w *ᵥ (chr g x v w + chr g x w v)))

/-- The derivative of the quintic jet `distJet5 g x` at `w` in the direction `v`. -/
noncomputable def distJet5Deriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x w v : Fin n → ℝ) : ℝ :=
  distJetDeriv g x w v + quintDeriv g x w v

theorem hasDerivAt_dddmat_mulVec (x : Fin n → ℝ) {p r s q : ℝ → Fin n → ℝ}
    {p' r' s' q' : Fin n → ℝ} {t : ℝ} (hp : HasDerivAt p p' t) (hr : HasDerivAt r r' t)
    (hs : HasDerivAt s s' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun τ => dddmat g x (p τ) (r τ) (s τ) *ᵥ q τ)
      (dddmat g x p' (r t) (s t) *ᵥ q t + dddmat g x (p t) r' (s t) *ᵥ q t
        + dddmat g x (p t) (r t) s' *ᵥ q t + dddmat g x (p t) (r t) (s t) *ᵥ q') t := by
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, dddmat, Matrix.of_apply, Pi.add_apply]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) fun k _ => HasDerivAt.fun_sum (u := Finset.univ)
      fun l _ => HasDerivAt.fun_sum (u := Finset.univ) fun m _ =>
        (((hasDerivAt_pi.1 hp k).mul (hasDerivAt_pi.1 hr l)).mul (hasDerivAt_pi.1 hs m)).mul_const
          (Lightlike.pd m (Lightlike.pd l (Lightlike.pd k (fun y => g y i j))) x)).mul (hasDerivAt_pi.1 hq j)
  convert h using 1
  simp only [Pi.mul_apply, add_mul, Finset.sum_add_distrib]

/-- The derivative of the quintic term along a curve. -/
theorem hasDerivAt_quint (x : Fin n → ℝ) {W : ℝ → Fin n → ℝ} {W' : Fin n → ℝ} {t : ℝ}
    (hW : HasDerivAt W W' t) :
    HasDerivAt (fun s => quint g x (W s)) (quintDeriv g x (W t) W') t := by
  have hc := hasDerivAt_chr (g := g) x hW hW
  have h1 := hasDerivAt_dot hW (hasDerivAt_dddmat_mulVec (g := g) x hW hW hW hW)
  have h2 := hasDerivAt_dot hW (hasDerivAt_ddmat_mulVec (g := g) x hW hW hc)
  have h3 := hasDerivAt_dot hW (hasDerivAt_ddmat_mulVec (g := g) x hW hc hW)
  have h4 := hasDerivAt_dot hc (hasDerivAt_dmat_mulVec (g := g) x hW hc)
  unfold quint
  exact ((((h1.const_mul (1 / 24)).sub (h2.const_mul (1 / 12))).add (h3.const_mul (1 / 24))).add
    (h4.const_mul (1 / 24))).congr_deriv (by unfold quintDeriv; ring)

/-- The derivative of the quintic jet along a curve. -/
theorem hasDerivAt_distJet5 (x : Fin n → ℝ) {W : ℝ → Fin n → ℝ} {W' : Fin n → ℝ} {t : ℝ}
    (hW : HasDerivAt W W' t) :
    HasDerivAt (fun s => distJet5 g x (W s)) (distJet5Deriv g x (W t) W') t :=
  (hasDerivAt_distJet x hW).add (hasDerivAt_quint x hW)

/-- Euler's relation for the homogeneous quintic term: `d quint_w(w) = 5 quint(w)`. -/
theorem quintDeriv_self (x w : Fin n → ℝ) : quintDeriv g x w w = 5 * quint g x w := by
  unfold quintDeriv quint
  simp only [ddmat_add_right, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add,
    add_dotProduct]
  ring

/-- **The order-5 identity**: `4 quint = ⅙ w·C(w,w,w)w + ½ ℓ(w; γ) − ¼ γ·A(w)γ` with
`γ = Γ(w, w)`; it makes the order-5 terms of `T₃(P₅, P₅) − F₅` cancel. -/
theorem _root_.Lightlike.IsCoordMetric.quint_key (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (w : Fin n → ℝ) :
    4 * quint g x w = (1 / 6) * (w ⬝ᵥ (dddmat g x w w w *ᵥ w))
      + (1 / 2) * ell g x w (chr g x w w)
      - (1 / 4) * (chr g x w w ⬝ᵥ (dmat g x w *ᵥ chr g x w w)) := by
  have hB1 := dot_mulVec_comm (hg.ddmat_transpose hx w w) (chr g x w w) w
  have hS1 := dot_mulVec_comm (hg.symm x hx) (chr g x (chr g x w w) w) (chr g x w w)
  have hS2 := dot_mulVec_comm (hg.symm x hx) (chr g x w (chr g x w w)) (chr g x w w)
  have hC1 := hg.dot_mulVec_chr hx (chr g x w w) (chr g x w w) w
  have hC2 := hg.dot_mulVec_chr hx (chr g x w w) w (chr g x w w)
  have hA := dot_mulVec_comm (hg.dmat_transpose hx (chr g x w w)) (chr g x w w) w
  unfold quint ell
  rw [hg.ddmat_comm hx (chr g x w w) w]
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  linear_combination (-1 / 12) * hB1 + (1 / 24) * hS1 + (1 / 24) * hS2 + (1 / 12) * hC1
    + (1 / 12) * hC2 + (1 / 24) * hA

/-! ## The quartic term of the radial field -/

/-- The quartic part of `½ dF₅ − g(P, ·)`, a linear form in `v`; raising its index gives the
quartic term of the radial field. -/
noncomputable def ell4 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w v : Fin n → ℝ) : ℝ :=
  quintDeriv g x w v - 2 * (radial3 g x w ⬝ᵥ (dmat g x w *ᵥ v))
    - radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ v) - (1 / 3) * (w ⬝ᵥ (dddmat g x w w w *ᵥ v))

/-- The vector of the linear form `ell4 g x w`. -/
noncomputable def ell4Vec (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ell4 g x w fun j => if i = j then 1 else 0

/-- The quartic term `½ g⁻¹ ℓ₄` of the radial field. -/
noncomputable def radial4 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  (1 / 2 : ℝ) • ((g x)⁻¹ *ᵥ ell4Vec g x w)

/-- The **radial field of order four** `P₅ = P + ½ g⁻¹ ℓ₄`, an approximation of half the gradient
of `d(x, ·)²` at `x + w` to one order beyond `radial`. -/
noncomputable def radial5 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    Fin n → ℝ :=
  radial g x w + radial4 g x w

theorem ell4_add (x w v v' : Fin n → ℝ) :
    ell4 g x w (v + v') = ell4 g x w v + ell4 g x w v' := by
  unfold ell4 quintDeriv
  simp only [dddmat_add_left, dddmat_add_mid, dddmat_add_right, ddmat_add_left, ddmat_add_right,
    dmat_add, chr_add_left, chr_add_right, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add,
    add_dotProduct]
  ring

theorem ell4_smul (x w v : Fin n → ℝ) (c : ℝ) : ell4 g x w (c • v) = c * ell4 g x w v := by
  unfold ell4 quintDeriv
  simp only [dddmat_smul_left, dddmat_smul_mid, dddmat_smul_right, ddmat_smul_left,
    ddmat_smul_right, ddmat_add_right, dmat_smul, chr_smul_left, chr_smul_right,
    Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem ell4_eq_dot (x w v : Fin n → ℝ) : ell4 g x w v = ell4Vec g x w ⬝ᵥ v := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := ell4 g x w
      map_add' := ell4_add x w
      map_smul' := fun c v => by simp [ell4_smul] }
  have h := L.pi_apply_eq_sum_univ v
  simp only [dotProduct, ell4Vec]
  rw [show ell4 g x w v = L v from rfl, h]
  exact Finset.sum_congr rfl fun i _ => by simp [L, smul_eq_mul, mul_comm]

/-- The remainder in `dF₅_w(v) = 2 T₃(P₅, v) − R₁`, of order `‖w‖⁵ ‖v‖`. -/
noncomputable def radial5Err1 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w v : Fin n → ℝ) :
    ℝ :=
  (1 / 3) * ((radial2 g x w + radial3 g x w) ⬝ᵥ (dddmat g x w w w *ᵥ v))
    + 2 * (radial4 g x w ⬝ᵥ (dmat g x w *ᵥ v)) + radial4 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)
    + (1 / 3) * (radial4 g x w ⬝ᵥ (dddmat g x w w w *ᵥ v))
    + radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)

/-- The part `A + ½ B + ⅙ C` of `T₃ − G` at `w`. -/
noncomputable def taylorMetric3Var (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  dmat g x w + (1 / 2 : ℝ) • ddmat g x w w + (1 / 6 : ℝ) • dddmat g x w w w

/-- The remainder in `T₃(P₅, P₅) = F₅(w) + R₂`, of order `‖w‖⁶`. -/
noncomputable def radial5Err2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w : Fin n → ℝ) :
    ℝ :=
  radial3 g x w ⬝ᵥ (g x *ᵥ radial3 g x w)
    + radial2 g x w ⬝ᵥ (dmat g x w *ᵥ radial3 g x w)
    + radial3 g x w ⬝ᵥ (dmat g x w *ᵥ radial2 g x w)
    + radial3 g x w ⬝ᵥ (dmat g x w *ᵥ radial3 g x w)
    + (1 / 2) * (w ⬝ᵥ (ddmat g x w w *ᵥ radial3 g x w) + radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ w)
      + (radial2 g x w + radial3 g x w) ⬝ᵥ (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w)))
    + (1 / 6) * ((radial2 g x w + radial3 g x w) ⬝ᵥ (dddmat g x w w w *ᵥ radial g x w)
      + w ⬝ᵥ (dddmat g x w w w *ᵥ (radial2 g x w + radial3 g x w)))
    + radial4 g x w ⬝ᵥ (g x *ᵥ (radial2 g x w + radial3 g x w))
    + (radial2 g x w + radial3 g x w) ⬝ᵥ (g x *ᵥ radial4 g x w)
    + radial4 g x w ⬝ᵥ (taylorMetric3Var g x w *ᵥ radial g x w)
    + radial g x w ⬝ᵥ (taylorMetric3Var g x w *ᵥ radial4 g x w)
    + radial4 g x w ⬝ᵥ (taylorMetric3 g x w *ᵥ radial4 g x w)

theorem _root_.Lightlike.IsCoordMetric.radial4_dot (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (w v : Fin n → ℝ) :
    radial4 g x w ⬝ᵥ (g x *ᵥ v) = (1 / 2) * ell4 g x w v := by
  unfold radial4
  rw [smul_dotProduct, hg.inv_mulVec_dot hx, ← ell4_eq_dot, smul_eq_mul]

/-- **The radial field of order four computes the derivative of `F₅`**, up to explicit terms of
order `‖w‖⁵ ‖v‖`: `dF₅_w(v) = 2 T₃(P₅, v) − R₁`. -/
theorem _root_.Lightlike.IsCoordMetric.distJet5Deriv_eq (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (w v : Fin n → ℝ) :
    distJet5Deriv g x w v = 2 * (radial5 g x w ⬝ᵥ (taylorMetric3 g x w *ᵥ v))
      - radial5Err1 g x w v := by
  have h1 := hg.distJetDeriv_eq hx w v
  have hP4 := hg.radial4_dot hx w v
  have hell4 : ell4 g x w v = quintDeriv g x w v - 2 * (radial3 g x w ⬝ᵥ (dmat g x w *ᵥ v))
      - radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ v) - (1 / 3) * (w ⬝ᵥ (dddmat g x w w w *ᵥ v)) := rfl
  simp only [radial, taylorMetric, radialErr1, Matrix.add_mulVec, Matrix.smul_mulVec,
    add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul] at h1
  simp only [distJet5Deriv, radial5, radial, taylorMetric3, taylorMetric, radial5Err1,
    Matrix.add_mulVec, Matrix.smul_mulVec, add_dotProduct, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  linear_combination h1 - 2 * hP4 - hell4

/-- **The radial field of order four has the squared length of `F₅`**, up to explicit terms of
order `‖w‖⁶`: `T₃(P₅, P₅) = F₅(w) + R₂`. -/
theorem _root_.Lightlike.IsCoordMetric.radial5_quad_eq (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (w : Fin n → ℝ) :
    radial5 g x w ⬝ᵥ (taylorMetric3 g x w *ᵥ radial5 g x w) = distJet5 g x w
      + radial5Err2 g x w := by
  have h := hg.radial_quad_eq hx w
  have hk := hg.quint_key hx w
  have hE := quintDeriv_self (g := g) x w
  have hP4 := hg.radial4_dot hx w w
  have hell4 : ell4 g x w w = quintDeriv g x w w - 2 * (radial3 g x w ⬝ᵥ (dmat g x w *ᵥ w))
      - radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ w) - (1 / 3) * (w ⬝ᵥ (dddmat g x w w w *ᵥ w)) := rfl
  have hS' := dot_mulVec_comm (hg.symm x hx) w (radial4 g x w)
  have hGs := dot_mulVec_comm (hg.symm x hx) (radial2 g x w) (radial3 g x w)
  have hAs := dot_mulVec_comm (hg.dmat_transpose hx w) w (radial3 g x w)
  have hBs := dot_mulVec_comm (hg.ddmat_transpose hx w w) w (radial2 g x w)
  have hr : radial3 g x w ⬝ᵥ (g x *ᵥ radial2 g x w) = -(1 / 4) * ell g x w (chr g x w w) := by
    unfold radial2 radial3
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, hg.inv_mulVec_dot hx,
      ← ell_eq_dot, smul_eq_mul, smul_eq_mul]
    ring
  have hr2 : radial2 g x w ⬝ᵥ (dmat g x w *ᵥ radial2 g x w) =
      (1 / 4) * (chr g x w w ⬝ᵥ (dmat g x w *ᵥ chr g x w w)) := by
    unfold radial2
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  simp only [radial, taylorMetric, radialErr2, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.smul_mulVec, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul] at h
  simp only [distJet5, radial5, radial, taylorMetric3, taylorMetric, radial5Err2,
    taylorMetric3Var, Matrix.add_mulVec, Matrix.mulVec_add, Matrix.smul_mulVec, add_dotProduct,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  linear_combination h + hGs + hAs + (1 / 2) * hBs + hS' + 2 * hP4 + hell4 + hE + 2 * hr + hr2
    + hk

/-! ## Bounds near `x` -/

/-- The jet vanishes at `w = 0`. -/
theorem distJet5_zero (x : Fin n → ℝ) : distJet5 g x 0 = 0 := by
  simp [distJet5, distJet_zero, quint, chr_zero_left, dmat_zero, ddmat_zero_left,
    dddmat_zero_left]

/-- `T₃ = G + (A + ½ B + ⅙ C)` applied to a vector. -/
theorem taylorMetric3_mulVec (x w q : Fin n → ℝ) :
    taylorMetric3 g x w *ᵥ q = g x *ᵥ q + taylorMetric3Var g x w *ᵥ q := by
  simp only [taylorMetric3, taylorMetric, taylorMetric3Var, Matrix.add_mulVec, add_assoc]

namespace LocalJet

variable {x : Fin n → ℝ} {B δ l : ℝ}

/-- The bound `g_le` with the norms replaced by upper bounds. -/
theorem g_le_of (h : LocalJet g U x B δ l) {p q : Fin n → ℝ} {c d : ℝ} (hp : ‖p‖ ≤ c)
    (hq : ‖q‖ ≤ d) : |p ⬝ᵥ (g x *ᵥ q)| ≤ B * c * d := by
  have := (norm_nonneg p).trans hp
  have := (norm_nonneg q).trans hq
  have := h.B_nonneg
  exact (h.g_le p q).trans (by gcongr)

/-- The bound `d_le` with the norms replaced by upper bounds. -/
theorem d_le_of (h : LocalJet g U x B δ l) {u p q : Fin n → ℝ} {a c d : ℝ} (hu : ‖u‖ ≤ a)
    (hp : ‖p‖ ≤ c) (hq : ‖q‖ ≤ d) : |p ⬝ᵥ (dmat g x u *ᵥ q)| ≤ B * a * c * d := by
  have := (norm_nonneg u).trans hu
  have := (norm_nonneg p).trans hp
  have := (norm_nonneg q).trans hq
  have := h.B_nonneg
  exact (h.d_le u p q).trans (by gcongr)

/-- The bound `dd_le` with the norms replaced by upper bounds. -/
theorem dd_le_of (h : LocalJet g U x B δ l) {u u' p q : Fin n → ℝ} {a b c d : ℝ}
    (hu : ‖u‖ ≤ a) (hu' : ‖u'‖ ≤ b) (hp : ‖p‖ ≤ c) (hq : ‖q‖ ≤ d) :
    |p ⬝ᵥ (ddmat g x u u' *ᵥ q)| ≤ B * a * b * c * d := by
  have := (norm_nonneg u).trans hu
  have := (norm_nonneg u').trans hu'
  have := (norm_nonneg p).trans hp
  have := (norm_nonneg q).trans hq
  have := h.B_nonneg
  exact (h.dd_le u u' p q).trans (by gcongr)

end LocalJet

namespace LocalJet3

variable {x : Fin n → ℝ} {B δ l : ℝ}

/-- The bound `ddd_le` with the norms replaced by upper bounds. -/
theorem ddd_le_of (h : LocalJet3 g U x B δ l) {u v s p q : Fin n → ℝ} {a b c d e : ℝ}
    (hu : ‖u‖ ≤ a) (hv : ‖v‖ ≤ b) (hs : ‖s‖ ≤ c) (hp : ‖p‖ ≤ d) (hq : ‖q‖ ≤ e) :
    |p ⬝ᵥ (dddmat g x u v s *ᵥ q)| ≤ B * a * b * c * d * e := by
  have := (norm_nonneg u).trans hu
  have := (norm_nonneg v).trans hv
  have := (norm_nonneg s).trans hs
  have := (norm_nonneg p).trans hp
  have := (norm_nonneg q).trans hq
  have := h.toLocalJet.B_nonneg
  exact (h.ddd_le u v s p q).trans (by gcongr)

/-- `|A(w) + ½ B(w, w) + ⅙ C(w, w, w)| ≤ 2 B ‖w‖` as a bilinear form, for `‖w‖ ≤ 1`. -/
theorem abs_taylorMetric3Var_le (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1)
    {p q : Fin n → ℝ} {c d : ℝ} (hp : ‖p‖ ≤ c) (hq : ‖q‖ ≤ d) :
    |p ⬝ᵥ (taylorMetric3Var g x w *ᵥ q)| ≤ 2 * B * ‖w‖ * c * d := by
  have j := h.toLocalJet
  have hB := j.B_nonneg
  have hε := norm_nonneg w
  have hc := (norm_nonneg p).trans hp
  have hd := (norm_nonneg q).trans hq
  have hcd : 0 ≤ B * c * d := by positivity
  have m2 := mul_le_mul_of_nonneg_left (pow_le_of_le_one hε hw (by norm_num : (2 : ℕ) ≠ 0)) hcd
  have m3 := mul_le_mul_of_nonneg_left (pow_le_of_le_one hε hw (by norm_num : (3 : ℕ) ≠ 0)) hcd
  have e0 : 0 ≤ B * ‖w‖ * c * d := by positivity
  obtain ⟨a1, b1⟩ := abs_le.mp (j.d_le_of le_rfl hp hq : |p ⬝ᵥ (dmat g x w *ᵥ q)| ≤ _)
  obtain ⟨a2, b2⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl hp hq :
    |p ⬝ᵥ (ddmat g x w w *ᵥ q)| ≤ _)
  obtain ⟨a3, b3⟩ := abs_le.mp (h.ddd_le_of le_rfl le_rfl le_rfl hp hq :
    |p ⬝ᵥ (dddmat g x w w w *ᵥ q)| ≤ _)
  unfold taylorMetric3Var
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [abs_le]
  constructor <;> linarith

/-- `|T₃(w)| ≤ 3 B` as a bilinear form, for `‖w‖ ≤ 1`. -/
theorem abs_taylorMetric3_le (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1)
    {p q : Fin n → ℝ} {c d : ℝ} (hp : ‖p‖ ≤ c) (hq : ‖q‖ ≤ d) :
    |p ⬝ᵥ (taylorMetric3 g x w *ᵥ q)| ≤ 3 * B * c * d := by
  have j := h.toLocalJet
  have hB := j.B_nonneg
  have hc := (norm_nonneg p).trans hp
  have hd := (norm_nonneg q).trans hq
  have hcd : 0 ≤ B * c * d := by positivity
  have m := mul_le_mul_of_nonneg_left hw hcd
  obtain ⟨a1, b1⟩ := abs_le.mp (j.g_le_of hp hq)
  obtain ⟨a2, b2⟩ := abs_le.mp (h.abs_taylorMetric3Var_le hw hp hq)
  rw [taylorMetric3_mulVec, dotProduct_add, abs_le]
  constructor <;> linarith

/-- `|dquint_w(v)| ≤ 2 B³ ‖w‖⁴ ‖v‖`. -/
theorem abs_quintDeriv_le (h : LocalJet3 g U x B δ l) (w v : Fin n → ℝ) :
    |quintDeriv g x w v| ≤ 2 * (B ^ 3 * ‖w‖ ^ 4) * ‖v‖ := by
  have j := h.toLocalJet
  have hB := j.B_nonneg
  have hν := norm_nonneg v
  have hγ := j.norm_chr_le w
  have hc1 : ‖chr g x v w‖ ≤ B * ‖v‖ * ‖w‖ := j.chr_le v w
  have hc2 : ‖chr g x w v‖ ≤ B * ‖w‖ * ‖v‖ := j.chr_le w v
  have X0 : 0 ≤ ‖w‖ ^ 4 * ‖v‖ := by positivity
  have e1 := mul_le_mul_of_nonneg_right (j.pow_le_pow (by norm_num : 1 ≤ 3)) X0
  have e2 := mul_le_mul_of_nonneg_right (j.pow_le_pow (by norm_num : 2 ≤ 3)) X0
  have e3 : 0 ≤ B ^ 3 * (‖w‖ ^ 4 * ‖v‖) := by positivity
  simp only [pow_one] at e1
  obtain ⟨a1, b1⟩ := abs_le.mp (h.ddd_le w w w v w)
  obtain ⟨a2, b2⟩ := abs_le.mp (h.ddd_le v w w w w)
  obtain ⟨a3, b3⟩ := abs_le.mp (h.ddd_le w v w w w)
  obtain ⟨a4, b4⟩ := abs_le.mp (h.ddd_le w w v w w)
  obtain ⟨a5, b5⟩ := abs_le.mp (h.ddd_le w w w w v)
  obtain ⟨a6, b6⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl le_rfl hγ :
    |v ⬝ᵥ (ddmat g x w w *ᵥ chr g x w w)| ≤ _)
  obtain ⟨a7, b7⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl le_rfl hγ :
    |w ⬝ᵥ (ddmat g x v w *ᵥ chr g x w w)| ≤ _)
  obtain ⟨a8, b8⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl le_rfl hγ :
    |w ⬝ᵥ (ddmat g x w v *ᵥ chr g x w w)| ≤ _)
  obtain ⟨a9, b9⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl le_rfl hc1 :
    |w ⬝ᵥ (ddmat g x w w *ᵥ chr g x v w)| ≤ _)
  obtain ⟨a10, b10⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl le_rfl hc2 :
    |w ⬝ᵥ (ddmat g x w w *ᵥ chr g x w v)| ≤ _)
  obtain ⟨a11, b11⟩ := abs_le.mp (j.dd_le_of le_rfl hγ le_rfl le_rfl :
    |v ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ w)| ≤ _)
  obtain ⟨a12, b12⟩ := abs_le.mp (j.dd_le_of le_rfl hγ le_rfl le_rfl :
    |w ⬝ᵥ (ddmat g x v (chr g x w w) *ᵥ w)| ≤ _)
  obtain ⟨a13, b13⟩ := abs_le.mp (j.dd_le_of le_rfl hc1 le_rfl le_rfl :
    |w ⬝ᵥ (ddmat g x w (chr g x v w) *ᵥ w)| ≤ _)
  obtain ⟨a14, b14⟩ := abs_le.mp (j.dd_le_of le_rfl hc2 le_rfl le_rfl :
    |w ⬝ᵥ (ddmat g x w (chr g x w v) *ᵥ w)| ≤ _)
  obtain ⟨a15, b15⟩ := abs_le.mp (j.dd_le_of le_rfl hγ le_rfl le_rfl :
    |w ⬝ᵥ (ddmat g x w (chr g x w w) *ᵥ v)| ≤ _)
  obtain ⟨a16, b16⟩ := abs_le.mp (j.d_le_of le_rfl hc1 hγ :
    |chr g x v w ⬝ᵥ (dmat g x w *ᵥ chr g x w w)| ≤ _)
  obtain ⟨a17, b17⟩ := abs_le.mp (j.d_le_of le_rfl hc2 hγ :
    |chr g x w v ⬝ᵥ (dmat g x w *ᵥ chr g x w w)| ≤ _)
  obtain ⟨a18, b18⟩ := abs_le.mp (j.d_le_of le_rfl hγ hγ :
    |chr g x w w ⬝ᵥ (dmat g x v *ᵥ chr g x w w)| ≤ _)
  obtain ⟨a19, b19⟩ := abs_le.mp (j.d_le_of le_rfl hγ hc1 :
    |chr g x w w ⬝ᵥ (dmat g x w *ᵥ chr g x v w)| ≤ _)
  obtain ⟨a20, b20⟩ := abs_le.mp (j.d_le_of le_rfl hγ hc2 :
    |chr g x w w ⬝ᵥ (dmat g x w *ᵥ chr g x w v)| ≤ _)
  unfold quintDeriv
  simp only [Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add, add_dotProduct,
    ddmat_add_right]
  rw [abs_le]
  constructor <;> linarith

/-- `|quint(w)| ≤ B³ ‖w‖⁵`. -/
theorem abs_quint_le (h : LocalJet3 g U x B δ l) (w : Fin n → ℝ) :
    |quint g x w| ≤ B ^ 3 * ‖w‖ ^ 5 := by
  have h1 := h.abs_quintDeriv_le w w
  rw [quintDeriv_self, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)] at h1
  have : 0 ≤ B ^ 3 * ‖w‖ ^ 5 := by have := h.toLocalJet.B_nonneg; positivity
  linarith

/-- `F₅(w) ≥ l ‖w‖² - 2 B³ ‖w‖³`. -/
theorem distJet5_ge (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    l * ‖w‖ ^ 2 - 2 * (B ^ 3 * ‖w‖ ^ 3) ≤ distJet5 g x w := by
  have j := h.toLocalJet
  have h1 := j.distJet_ge hw
  have h2 := (abs_le.mp (h.abs_quint_le w)).1
  have e := j.monom_le hw (a := 3) (a' := 3) (b := 5) (b' := 3) le_rfl (by norm_num)
  unfold distJet5
  linarith

/-- Where `B³ ‖u‖ ≤ l / 4`, `F₅(u) ≥ (l / 2) ‖u‖²`. -/
theorem distJet5_ge_half (h : LocalJet3 g U x B δ l) {u : Fin n → ℝ} (hu : ‖u‖ ≤ 1)
    (hul : B ^ 3 * ‖u‖ ≤ l / 4) : l / 2 * ‖u‖ ^ 2 ≤ distJet5 g x u := by
  have h1 := h.distJet5_ge hu
  have h2 : B ^ 3 * ‖u‖ ^ 3 ≤ l / 4 * ‖u‖ ^ 2 :=
    calc B ^ 3 * ‖u‖ ^ 3 = B ^ 3 * ‖u‖ * ‖u‖ ^ 2 := by ring
      _ ≤ l / 4 * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right hul (sq_nonneg _)
  linarith

/-- `F₅(w) ≤ 3 B³ ‖w‖²`. -/
theorem distJet5_le (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    distJet5 g x w ≤ 3 * (B ^ 3 * ‖w‖ ^ 2) := by
  have j := h.toLocalJet
  have h1 := j.distJet_le hw
  have h2 := (abs_le.mp (h.abs_quint_le w)).2
  have e := j.monom_le hw (a := 3) (a' := 3) (b := 5) (b' := 2) le_rfl (by norm_num)
  unfold distJet5
  linarith

/-- `|ℓ₄(w; v)| ≤ 8 B⁵ ‖w‖⁴ ‖v‖`. -/
theorem abs_ell4_le (h : LocalJet3 g U x B δ l) (w v : Fin n → ℝ) :
    |ell4 g x w v| ≤ 8 * (B ^ 5 * ‖w‖ ^ 4) * ‖v‖ := by
  have j := h.toLocalJet
  have hB := j.B_nonneg
  have hν := norm_nonneg v
  have X0 : 0 ≤ ‖w‖ ^ 4 * ‖v‖ := by positivity
  have e1 := mul_le_mul_of_nonneg_right (j.pow_le_pow (by norm_num : 1 ≤ 5)) X0
  have e2 := mul_le_mul_of_nonneg_right (j.pow_le_pow (by norm_num : 2 ≤ 5)) X0
  have e3 := mul_le_mul_of_nonneg_right (j.pow_le_pow (by norm_num : 3 ≤ 5)) X0
  have e5 : 0 ≤ B ^ 5 * (‖w‖ ^ 4 * ‖v‖) := by positivity
  simp only [pow_one] at e1
  obtain ⟨a0, b0⟩ := abs_le.mp (h.abs_quintDeriv_le w v)
  obtain ⟨a1, b1⟩ := abs_le.mp (j.d_le_of le_rfl (j.norm_radial3_le w) le_rfl :
    |radial3 g x w ⬝ᵥ (dmat g x w *ᵥ v)| ≤ _)
  obtain ⟨a2, b2⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl (j.norm_radial2_le w) le_rfl :
    |radial2 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ _)
  obtain ⟨a3, b3⟩ := abs_le.mp (h.ddd_le w w w w v)
  unfold ell4
  rw [abs_le]
  constructor <;> linarith

/-- The vector of `ℓ₄` is bounded by `8 B⁵ ‖w‖⁴`. -/
theorem norm_ell4Vec_le (h : LocalJet3 g U x B δ l) (w : Fin n → ℝ) :
    ‖ell4Vec g x w‖ ≤ 8 * (B ^ 5 * ‖w‖ ^ 4) := by
  have hc : 0 ≤ 8 * (B ^ 5 * ‖w‖ ^ 4) := by have := h.toLocalJet.B_nonneg; positivity
  refine (pi_norm_le_iff_of_nonneg hc).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have he : ‖(fun j => if i = j then (1 : ℝ) else 0)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    show ‖(if i = j then (1 : ℝ) else 0)‖ ≤ 1
    split_ifs <;> simp
  calc |ell4Vec g x w i| = |ell4 g x w fun j => if i = j then 1 else 0| := rfl
    _ ≤ 8 * (B ^ 5 * ‖w‖ ^ 4) * ‖(fun j => if i = j then (1 : ℝ) else 0)‖ := h.abs_ell4_le w _
    _ ≤ 8 * (B ^ 5 * ‖w‖ ^ 4) * 1 := mul_le_mul_of_nonneg_left he hc
    _ = _ := mul_one _

/-- The quartic term of the radial field is bounded by `4 B⁶ ‖w‖⁴`. -/
theorem norm_radial4_le (h : LocalJet3 g U x B δ l) (w : Fin n → ℝ) :
    ‖radial4 g x w‖ ≤ 4 * (B ^ 6 * ‖w‖ ^ 4) := by
  have j := h.toLocalJet
  unfold radial4
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 : ‖(g x)⁻¹ *ᵥ ell4Vec g x w‖ ≤ 8 * (B ^ 6 * ‖w‖ ^ 4) :=
    (j.inv_le _).trans ((mul_le_mul_of_nonneg_left (h.norm_ell4Vec_le w) j.B_nonneg).trans_eq
      (by ring))
  linarith

/-- The radial field `P₅` is bounded by `8 B⁶ ‖w‖` for `‖w‖ ≤ 1`. -/
theorem norm_radial5_le (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    ‖radial5 g x w‖ ≤ 8 * (B ^ 6 * ‖w‖) := by
  have j := h.toLocalJet
  have h1 := (norm_add_le _ _).trans (add_le_add (j.norm_radial_le hw) (h.norm_radial4_le w))
  have e1 : B ^ 4 * ‖w‖ ^ 1 ≤ B ^ 6 * ‖w‖ ^ 1 := j.monom_le hw (by norm_num) le_rfl
  have e2 : B ^ 6 * ‖w‖ ^ 4 ≤ B ^ 6 * ‖w‖ ^ 1 := j.monom_le hw le_rfl (by norm_num)
  simp only [pow_one] at e1 e2
  unfold radial5
  linarith

/-- `|R₁| ≤ 17 B⁷ ‖w‖⁵ ‖v‖` for the remainder of `distJet5Deriv_eq`. -/
theorem abs_radial5Err1_le (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1)
    (v : Fin n → ℝ) : |radial5Err1 g x w v| ≤ 17 * (B ^ 7 * ‖w‖ ^ 5) * ‖v‖ := by
  have j := h.toLocalJet
  have hν := norm_nonneg v
  have r3 := j.norm_radial3_le w
  have rs := j.norm_radial23_le hw
  have r4 := h.norm_radial4_le w
  obtain ⟨a1, b1⟩ := abs_le.mp (h.ddd_le_of le_rfl le_rfl le_rfl rs le_rfl :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (dddmat g x w w w *ᵥ v)| ≤ _)
  obtain ⟨a2, b2⟩ := abs_le.mp (j.d_le_of le_rfl r4 le_rfl :
    |radial4 g x w ⬝ᵥ (dmat g x w *ᵥ v)| ≤ _)
  obtain ⟨a3, b3⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl r4 le_rfl :
    |radial4 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ _)
  obtain ⟨a4, b4⟩ := abs_le.mp (h.ddd_le_of le_rfl le_rfl le_rfl r4 le_rfl :
    |radial4 g x w ⬝ᵥ (dddmat g x w w w *ᵥ v)| ≤ _)
  obtain ⟨a5, b5⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl r3 le_rfl :
    |radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ v)| ≤ _)
  have e55 := mul_le_mul_of_nonneg_right (j.monom_le hw (a := 5) (a' := 7) (b := 5) (b' := 5)
    (by norm_num) le_rfl) hν
  have e76 := mul_le_mul_of_nonneg_right (j.monom_le hw (a := 7) (a' := 7) (b := 6) (b' := 5)
    le_rfl (by norm_num)) hν
  have e77 := mul_le_mul_of_nonneg_right (j.monom_le hw (a := 7) (a' := 7) (b := 7) (b' := 5)
    le_rfl (by norm_num)) hν
  unfold radial5Err1
  rw [abs_le]
  constructor <;> linarith

/-- `|R₂| ≤ 160 B¹³ ‖w‖⁶` for the remainder of `radial5_quad_eq`. -/
theorem abs_radial5Err2_le (h : LocalJet3 g U x B δ l) {w : Fin n → ℝ} (hw : ‖w‖ ≤ 1) :
    |radial5Err2 g x w| ≤ 160 * (B ^ 13 * ‖w‖ ^ 6) := by
  have j := h.toLocalJet
  have r2 := j.norm_radial2_le w
  have r3 := j.norm_radial3_le w
  have rs := j.norm_radial23_le hw
  have r1 := j.norm_radial_le hw
  have r4 := h.norm_radial4_le w
  obtain ⟨a1, b1⟩ := abs_le.mp (j.g_le_of r3 r3 : |radial3 g x w ⬝ᵥ (g x *ᵥ radial3 g x w)| ≤ _)
  obtain ⟨a2, b2⟩ := abs_le.mp (j.d_le_of le_rfl r2 r3 :
    |radial2 g x w ⬝ᵥ (dmat g x w *ᵥ radial3 g x w)| ≤ _)
  obtain ⟨a3, b3⟩ := abs_le.mp (j.d_le_of le_rfl r3 r2 :
    |radial3 g x w ⬝ᵥ (dmat g x w *ᵥ radial2 g x w)| ≤ _)
  obtain ⟨a4, b4⟩ := abs_le.mp (j.d_le_of le_rfl r3 r3 :
    |radial3 g x w ⬝ᵥ (dmat g x w *ᵥ radial3 g x w)| ≤ _)
  obtain ⟨a5, b5⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl le_rfl r3 :
    |w ⬝ᵥ (ddmat g x w w *ᵥ radial3 g x w)| ≤ _)
  obtain ⟨a6, b6⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl r3 le_rfl :
    |radial3 g x w ⬝ᵥ (ddmat g x w w *ᵥ w)| ≤ _)
  obtain ⟨a7, b7⟩ := abs_le.mp (j.dd_le_of le_rfl le_rfl rs rs :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ
      (ddmat g x w w *ᵥ (radial2 g x w + radial3 g x w))| ≤ _)
  obtain ⟨a8, b8⟩ := abs_le.mp (h.ddd_le_of le_rfl le_rfl le_rfl rs r1 :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (dddmat g x w w w *ᵥ radial g x w)| ≤ _)
  obtain ⟨a9, b9⟩ := abs_le.mp (h.ddd_le_of le_rfl le_rfl le_rfl le_rfl rs :
    |w ⬝ᵥ (dddmat g x w w w *ᵥ (radial2 g x w + radial3 g x w))| ≤ _)
  obtain ⟨a10, b10⟩ := abs_le.mp (j.g_le_of r4 rs :
    |radial4 g x w ⬝ᵥ (g x *ᵥ (radial2 g x w + radial3 g x w))| ≤ _)
  obtain ⟨a11, b11⟩ := abs_le.mp (j.g_le_of rs r4 :
    |(radial2 g x w + radial3 g x w) ⬝ᵥ (g x *ᵥ radial4 g x w)| ≤ _)
  obtain ⟨a12, b12⟩ := abs_le.mp (h.abs_taylorMetric3Var_le hw r4 r1 :
    |radial4 g x w ⬝ᵥ (taylorMetric3Var g x w *ᵥ radial g x w)| ≤ _)
  obtain ⟨a13, b13⟩ := abs_le.mp (h.abs_taylorMetric3Var_le hw r1 r4 :
    |radial g x w ⬝ᵥ (taylorMetric3Var g x w *ᵥ radial4 g x w)| ≤ _)
  obtain ⟨a14, b14⟩ := abs_le.mp (h.abs_taylorMetric3_le hw r4 r4 :
    |radial4 g x w ⬝ᵥ (taylorMetric3 g x w *ᵥ radial4 g x w)| ≤ _)
  have e96 := j.monom_le hw (a := 9) (a' := 13) (b := 6) (b' := 6) (by norm_num) le_rfl
  have e66 := j.monom_le hw (a := 6) (a' := 13) (b := 6) (b' := 6) (by norm_num) le_rfl
  have e97 := j.monom_le hw (a := 9) (a' := 13) (b := 7) (b' := 6) (by norm_num) (by norm_num)
  have e56 := j.monom_le hw (a := 5) (a' := 13) (b := 6) (b' := 6) (by norm_num) le_rfl
  have e116 := j.monom_le hw (a := 11) (a' := 13) (b := 6) (b' := 6) (by norm_num) le_rfl
  have e138 := j.monom_le hw (a := 13) (a' := 13) (b := 8) (b' := 6) le_rfl (by norm_num)
  unfold radial5Err2
  rw [abs_le]
  constructor <;> linarith

end LocalJet3

/-! ## The calibration estimate of order four -/

/-- The real-number core of the calibration estimate, with the order `p` of the relative error
as a parameter (`calib_real` is the case `p = 3`). -/
theorem calib_real_gen (p : ℕ) {F μ ε D E V a A PP dF l : ℝ} (hε : 0 ≤ ε) (hμ : 0 < μ)
    (hl : 0 < l) (hD : 0 ≤ D) (hE : 0 ≤ E) (ha : 0 ≤ a) (hF : μ * ε ^ 2 ≤ F)
    (hA : |A| ≤ √PP * V) (hPP : PP ≤ F + D * ε ^ (p + 2)) (hV : √l * a ≤ V)
    (hdF : |dF| ≤ 2 * |A| + E * ε ^ (p + 1) * a) :
    |dF| ≤ 2 * √F * V * (1 + (D / (2 * μ) + E / (2 * (√μ * √l))) * ε ^ p) := by
  have hF0 : 0 ≤ F := le_trans (by positivity) hF
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  have hs0 : 0 ≤ √F := Real.sqrt_nonneg _
  have hss : √F ^ 2 = F := Real.sq_sqrt hF0
  have hsμ : √μ * ε ≤ √F := by
    have := Real.sqrt_le_sqrt hF
    rwa [Real.sqrt_mul hμ.le, Real.sqrt_sq hε] at this
  have hk1 : 0 ≤ D / (2 * μ) * ε ^ p := by positivity
  have h1 : F + D * ε ^ (p + 2) ≤ (√F * (1 + D / (2 * μ) * ε ^ p)) ^ 2 := by
    have e : 2 * (D / (2 * μ) * ε ^ p) * F = D * ε ^ p * (F / μ) := by field_simp
    have hFμ : ε ^ 2 ≤ F / μ := by rw [le_div_iff₀ hμ]; linarith
    have h3 : D * ε ^ (p + 2) ≤ 2 * (D / (2 * μ) * ε ^ p) * F := by
      rw [e]
      calc D * ε ^ (p + 2) = D * ε ^ p * ε ^ 2 := by ring
        _ ≤ D * ε ^ p * (F / μ) := by gcongr
    have e2 : (√F * (1 + D / (2 * μ) * ε ^ p)) ^ 2 =
        F + 2 * (D / (2 * μ) * ε ^ p) * F + (D / (2 * μ) * ε ^ p) ^ 2 * F := by
      rw [mul_pow, hss]; ring
    rw [e2]
    nlinarith [sq_nonneg (D / (2 * μ) * ε ^ p)]
  have h2 : √PP ≤ √F * (1 + D / (2 * μ) * ε ^ p) :=
    calc √PP ≤ √(F + D * ε ^ (p + 2)) := Real.sqrt_le_sqrt hPP
      _ ≤ √((√F * (1 + D / (2 * μ) * ε ^ p)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = √F * (1 + D / (2 * μ) * ε ^ p) := Real.sqrt_sq (by positivity)
  have hsl : 0 < √l := Real.sqrt_pos.2 hl
  have hsm : 0 < √μ := Real.sqrt_pos.2 hμ
  have h3 : E * ε ^ (p + 1) * a ≤ 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ p) := by
    have e : 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ p) = √F * V * E * ε ^ p / (√μ * √l) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc E * ε ^ (p + 1) * a * (√μ * √l) = (E * ε ^ p) * (√μ * ε) * (√l * a) := by ring
      _ ≤ (E * ε ^ p) * √F * V := by gcongr
      _ = √F * V * E * ε ^ p := by ring
  have h4 : |A| ≤ √F * (1 + D / (2 * μ) * ε ^ p) * V :=
    hA.trans (mul_le_mul_of_nonneg_right h2 hV0)
  calc |dF| ≤ 2 * |A| + E * ε ^ (p + 1) * a := hdF
    _ ≤ 2 * (√F * (1 + D / (2 * μ) * ε ^ p) * V)
        + 2 * √F * V * (E / (2 * (√μ * √l)) * ε ^ p) := add_le_add (by linarith) h3
    _ = 2 * √F * V * (1 + (D / (2 * μ) + E / (2 * (√μ * √l))) * ε ^ p) := by ring

/-- The constant of the calibration estimate of order four. -/
noncomputable def calibConst5 (B l : ℝ) : ℝ :=
  224 * B ^ 13 / (2 * (l / 2)) + 33 * B ^ 7 / (2 * (√(l / 2) * √l))

theorem calibConst5_nonneg {B l : ℝ} (hB : 0 ≤ B) (hl : 0 < l) : 0 ≤ calibConst5 B l := by
  unfold calibConst5; positivity

namespace LocalJet3

variable {x : Fin n → ℝ} {B δ l : ℝ}

/-- **The calibration estimate of order four.** Near `x`, the differential of the quintic jet
`F₅ = distJet5 g x` is bounded by the metric: `|dF₅_u(v)| ≤ 2 √F₅(u) |v|_g (1 + κ₅ ‖u‖⁴)`, with
`|v|_g` the length at `x + u` and `κ₅ = calibConst5 B l`. -/
theorem abs_distJet5Deriv_le (hg : IsRiemMetric g U) (h : LocalJet3 g U x B δ l)
    {u : Fin n → ℝ} (hu : ‖u‖ ≤ δ) (hul : B ^ 3 * ‖u‖ ≤ l / 4) (v : Fin n → ℝ) :
    |distJet5Deriv g x u v| ≤
      2 * √(distJet5 g x u) * √(normSq g (x + u) v) * (1 + calibConst5 B l * ‖u‖ ^ 4) := by
  have j := h.toLocalJet
  have hu1 : ‖u‖ ≤ 1 := hu.trans j.δ_le_one
  have hx : x ∈ U := by simpa using j.mem 0 (by simpa using j.δ_pos.le)
  have hxu : x + u ∈ U := j.mem u hu
  have hB := j.B_nonneg
  have hε := norm_nonneg u
  have hν := norm_nonneg v
  have hP := h.norm_radial5_le hu1
  have hP0 := norm_nonneg (radial5 g x u)
  have split : ∀ q, radial5 g x u ⬝ᵥ (taylorMetric3 g x u *ᵥ q) =
      radial5 g x u ⬝ᵥ (g (x + u) *ᵥ q)
        - radial5 g x u ⬝ᵥ ((g (x + u) - taylorMetric3 g x u) *ᵥ q) := by
    intro q; rw [Matrix.sub_mulVec, dotProduct_sub]; ring
  have tv : |radial5 g x u ⬝ᵥ ((g (x + u) - taylorMetric3 g x u) *ᵥ v)| ≤
      8 * (B ^ 7 * ‖u‖ ^ 5) * ‖v‖ := (h.tay3_le u hu _ v).trans (by
    calc B * ‖u‖ ^ 4 * ‖radial5 g x u‖ * ‖v‖ ≤ B * ‖u‖ ^ 4 * (8 * (B ^ 6 * ‖u‖)) * ‖v‖ := by
          gcongr
      _ = _ := by ring)
  have tp : |radial5 g x u ⬝ᵥ ((g (x + u) - taylorMetric3 g x u) *ᵥ radial5 g x u)| ≤
      64 * (B ^ 13 * ‖u‖ ^ 6) := (h.tay3_le u hu _ _).trans (by
    calc B * ‖u‖ ^ 4 * ‖radial5 g x u‖ * ‖radial5 g x u‖ ≤
          B * ‖u‖ ^ 4 * (8 * (B ^ 6 * ‖u‖)) * (8 * (B ^ 6 * ‖u‖)) := by gcongr
      _ = _ := by ring)
  have hPP : normSq g (x + u) (radial5 g x u) ≤ distJet5 g x u + 224 * B ^ 13 * ‖u‖ ^ 6 := by
    have e := split (radial5 g x u)
    rw [hg.coord.radial5_quad_eq hx u] at e
    have a1 := (abs_le.mp (h.abs_radial5Err2_le hu1)).2
    have a2 := (abs_le.mp tp).2
    unfold normSq
    linarith
  have hdF : |distJet5Deriv g x u v| ≤
      2 * |radial5 g x u ⬝ᵥ (g (x + u) *ᵥ v)| + 33 * B ^ 7 * ‖u‖ ^ 5 * ‖v‖ := by
    rw [hg.coord.distJet5Deriv_eq hx u v, split v]
    have a1 := abs_le.mp (h.abs_radial5Err1_le hu1 v)
    have a2 := abs_le.mp tv
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (radial5 g x u ⬝ᵥ (g (x + u) *ᵥ v)),
        neg_abs_le (radial5 g x u ⬝ᵥ (g (x + u) *ᵥ v))]
  have hF := h.distJet5_ge_half hu1 hul
  have hV : √l * ‖v‖ ≤ √(normSq g (x + u) v) := by
    have := Real.sqrt_le_sqrt
      ((mul_le_mul_of_nonneg_left (norm_sq_le_eNormSq v) j.l_pos.le).trans (j.low u hu v))
    rwa [Real.sqrt_mul j.l_pos.le, Real.sqrt_sq hν] at this
  unfold calibConst5
  exact calib_real_gen 4 hε (by linarith [j.l_pos]) j.l_pos (by positivity) (by positivity) hν hF
    (hg.abs_dot_le hxu _ v) hPP hV hdF

/-- On the ball of radius `ρ ≤ δ` with `B³ ρ ≤ l / 4`, the quintic jet `F₅` is nonnegative and
calibrated with constant `1 + κ₅ ρ⁴` (`κ₅ = calibConst5 B l`). -/
theorem distJet5_calib (hg : IsRiemMetric g U) (h : LocalJet3 g U x B δ l) {ρ : ℝ} (hρ : ρ ≤ δ)
    (hρl : B ^ 3 * ρ ≤ l / 4) :
    (∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → 0 ≤ distJet5 g x u) ∧
      ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → ∀ v, |distJet5Deriv g x u v| ≤
        2 * √(distJet5 g x u) * √(normSq g (x + u) v) * (1 + calibConst5 B l * ρ ^ 4) := by
  have j := h.toLocalJet
  have hκ := calibConst5_nonneg j.B_nonneg j.l_pos
  have hul : ∀ u : Fin n → ℝ, ‖u‖ ≤ ρ → B ^ 3 * ‖u‖ ≤ l / 4 := fun u hu =>
    (mul_le_mul_of_nonneg_left hu (pow_nonneg j.B_nonneg 3)).trans hρl
  refine ⟨fun u hu => le_trans (by have := j.l_pos; positivity)
    (h.distJet5_ge_half ((hu.trans hρ).trans j.δ_le_one) (hul u hu)), fun u hu v => ?_⟩
  refine (h.abs_distJet5Deriv_le hg (hu.trans hρ) (hul u hu) v).trans ?_
  have := pow_le_pow_left₀ (norm_nonneg _) hu 4
  gcongr

/-- **The lower bound of order four for one curve**: with `A ≥ 1`, `3 B³ ≤ l A` and the ball of
radius `A ‖w‖` inside the region of `LocalJet3` and of the calibration, every admissible curve
from `x` to `x + w` has length at least `√F₅(w) / (1 + κ₅ (A ‖w‖)⁴)`. -/
theorem sqrt_distJet5_le_length_of_admissible (hg : IsRiemMetric g U)
    (h : LocalJet3 g U x B δ l) {A : ℝ} (hA : 1 ≤ A) (hAl : 3 * B ^ 3 ≤ l * A)
    {w : Fin n → ℝ} (hw : A * ‖w‖ ≤ δ) (hwl : B ^ 3 * (A * ‖w‖) ≤ l / 4)
    {c : ℝ → Fin n → ℝ} (hc : IsAdmissible U c x (x + w)) :
    √(distJet5 g x w) ≤ (1 + calibConst5 B l * (A * ‖w‖) ^ 4) * length g c 0 1 := by
  have j := h.toLocalJet
  have hκ := calibConst5_nonneg j.B_nonneg j.l_pos
  have hL : 0 ≤ length g c 0 1 := length_nonneg zero_le_one
  have hk1 : 1 ≤ 1 + calibConst5 B l * (A * ‖w‖) ^ 4 := by
    have : 0 ≤ calibConst5 B l * (A * ‖w‖) ^ 4 := by positivity
    linarith
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [distJet5_zero, Real.sqrt_zero]; positivity
  have hρ0 : 0 < A * ‖w‖ := mul_pos (by linarith) (norm_pos_iff.2 hw0)
  have hw1 : ‖w‖ ≤ 1 :=
    le_trans (le_mul_of_one_le_left (norm_nonneg w) hA) (hw.trans j.δ_le_one)
  have hA2 : 3 * B ^ 3 ≤ l * A ^ 2 :=
    hAl.trans (mul_le_mul_of_nonneg_left (by nlinarith) j.l_pos.le)
  have hFl : distJet5 g x w ≤ l * (A * ‖w‖) ^ 2 :=
    calc distJet5 g x w ≤ 3 * (B ^ 3 * ‖w‖ ^ 2) := h.distJet5_le hw1
      _ = 3 * B ^ 3 * ‖w‖ ^ 2 := by ring
      _ ≤ l * A ^ 2 * ‖w‖ ^ 2 := by gcongr
      _ = _ := by ring
  obtain ⟨hpos, hcal⟩ := h.distJet5_calib hg hw hwl
  exact j.sqrt_le_length_of_calib_admissible hg (fun hW => hasDerivAt_distJet5 x hW)
    (distJet5_zero x) hρ0 hw hk1 hpos hcal hFl hc

/-- **The lower bound of order four for the distance**: under the hypotheses of
`sqrt_distJet5_le_length_of_admissible`, if some admissible curve joins `x` and `x + w`, then
`√F₅(w) ≤ (1 + κ₅ (A ‖w‖)⁴) d(x, x + w)`. -/
theorem sqrt_distJet5_le_dist (hg : IsRiemMetric g U) (h : LocalJet3 g U x B δ l)
    {A : ℝ} (hA : 1 ≤ A) (hAl : 3 * B ^ 3 ≤ l * A) {w : Fin n → ℝ} (hw : A * ‖w‖ ≤ δ)
    (hwl : B ^ 3 * (A * ‖w‖) ≤ l / 4) (hne : ∃ c, IsAdmissible U c x (x + w)) :
    √(distJet5 g x w) ≤ (1 + calibConst5 B l * (A * ‖w‖) ^ 4) * dist g U x (x + w) := by
  have hk : 0 < 1 + calibConst5 B l * (A * ‖w‖) ^ 4 := by
    have := calibConst5_nonneg h.toLocalJet.B_nonneg h.toLocalJet.l_pos
    positivity
  exact le_mul_dist_of_le_mul_length hk hne fun c hc =>
    h.sqrt_distJet5_le_length_of_admissible hg hA hAl hw hwl hc

end LocalJet3

end Lightlike.Geodesic
