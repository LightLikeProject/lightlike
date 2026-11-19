import Lightlike.Canonical.Triad
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The spin connection of a co-triad and its compatibility

For a co-triad `e` of a spatial metric `h` on the chart `ℝ³`, with the Levi-Civita covariant derivative of `h` built from
`Lightlike.christoffel h` (`Lightlike/Spacetime/Curvature.lean`):

* `covTriad`: `∇_a e^k_b = ∂_a e^k_b − Γ^c_{ab} e^k_c`, the covariant derivative of the co-triad in its spatial index;
* `triadOmega`: `ω_a^{jk} = e^b_j ∇_a e^k_b`;
* `spinConn`: the **spin connection** `Γ^i_a = −½ ε_ijk e^b_j ∇_a e^k_b` (Holst, arXiv:gr-qc/9511026, eq. (6), p. 2, with
  the internal indices raised and lowered by `δ`).

Results: `ω` is antisymmetric (`triadOmega_antisymm`, from the metric compatibility of the Christoffel symbols,
`IsCoordMetric.pd_eq_christoffelFirst`); the triad is covariantly constant for the total covariant derivative,
`∇_a e^k_b + ε_ijk Γ^i_a e^j_b = 0` (`covTriad_add_spin`); and the **compatibility** `de^k + ε^k_ij Γ^i ∧ e^j = 0`
(`spin_compat`), Ashtekar–Lewandowski, arXiv:gr-qc/0404018, eq. (2.17), p. 16.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

/-- `∇_a e^k_b = ∂_a e^k_b − Γ^c_{ab} e^k_c`: the Levi-Civita covariant derivative of the co-triad in its spatial index. -/
def covTriad (e : CoTriad) (h : TensorField 3) (x : Fin 3 → ℝ) (a k b : Fin 3) : ℝ :=
  Lightlike.pd a (fun y => e y k b) x - ∑ c, Lightlike.christoffel h c a b x * e x k c

/-- `ω_a^{jk} = e^b_j ∇_a e^k_b`. -/
def triadOmega (e : CoTriad) (h : TensorField 3) (x : Fin 3 → ℝ) (a j k : Fin 3) : ℝ :=
  ∑ b, (e x)⁻¹ b j * covTriad e h x a k b

/-- **The spin connection** of the co-triad, `Γ^i_a = −½ ε_ijk e^b_j ∇_a e^k_b` (Holst (6)), as a matrix with row `a`
(spatial) and column `i` (internal). -/
def spinConn (e : CoTriad) (h : TensorField 3) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a i => -(1 / 2) * ∑ j, ∑ k, eps3 i j k * triadOmega e h x a j k

/-- The values of `ε_ijk`. -/
lemma eps3_apply (i j k : Fin 3) :
    eps3 i j k = if i = 0 ∧ j = 1 ∧ k = 2 ∨ i = 1 ∧ j = 2 ∧ k = 0 ∨ i = 2 ∧ j = 0 ∧ k = 1 then 1
      else if i = 0 ∧ j = 2 ∧ k = 1 ∨ i = 2 ∧ j = 1 ∧ k = 0 ∨ i = 1 ∧ j = 0 ∧ k = 2 then -1 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [eps3, Matrix.det_fin_three]

/-- **Inversion of the dual**: for an antisymmetric `W`, `W_jk = ½ Σ_i ε_ijk Σ_lm ε_ilm W_lm`. -/
lemma eps3_dual_inv (W : Matrix (Fin 3) (Fin 3) ℝ) (hW : ∀ j k, W j k + W k j = 0) (j k : Fin 3) :
    W j k = -∑ i, eps3 i j k * (-(1 / 2) * ∑ l, ∑ m, eps3 i l m * W l m) := by
  have h00 := hW 0 0; have h11 := hW 1 1; have h22 := hW 2 2
  have h01 := hW 0 1; have h02 := hW 0 2; have h12 := hW 1 2
  fin_cases j <;> fin_cases k <;> simp [Fin.sum_univ_three, eps3_apply] <;> linarith

/-- The metric of a co-triad, entrywise: `h_bc = Σ_i e^i_b e^i_c`. -/
lemma coTriad_entry {e : CoTriad} {h : TensorField 3} (he : IsCoTriad e h) (y : Fin 3 → ℝ) (b c : Fin 3) :
    h y b c = ∑ i, e y i b * e y i c := by
  rw [← (he y).2]; simp [Matrix.mul_apply, Matrix.transpose_apply]

variable {e : CoTriad} {h : TensorField 3} {U : Set (Fin 3 → ℝ)} {x : Fin 3 → ℝ}

/-- `Σ_d Γ^d_{ab} h_dc` is the Christoffel symbol of the first kind `Γ_{cab}`. -/
lemma sum_christoffel_mul (hg : IsCoordMetric h U) (hx : x ∈ U) (a b c : Fin 3) :
    ∑ d, Lightlike.christoffel h d a b x * h x d c = Lightlike.christoffelFirst h c a b x := by
  simp only [Lightlike.christoffel_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hu := hg.isUnit_det x hx
  have hs : ∀ d, h x d c = h x c d := fun d => by
    have := congrFun (congrFun (hg.symm x hx) c) d; simpa [Matrix.transpose_apply] using this
  have key : ∀ l, ∑ d, (h x)⁻¹ d l * Lightlike.christoffelFirst h l a b x * h x d c =
      (if c = l then 1 else 0) * Lightlike.christoffelFirst h l a b x := by
    intro l
    have hm : (h x * (h x)⁻¹) c l = (1 : Matrix (Fin 3) (Fin 3) ℝ) c l := by rw [mul_nonsing_inv _ hu]
    rw [Matrix.mul_apply, Matrix.one_apply] at hm
    rw [← hm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hs d]; ring
  simp only [key, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Metric compatibility of the triad derivative**: `Σ_i (∇_a e^i_b e^i_c + e^i_b ∇_a e^i_c) = 0`. -/
lemma covTriad_metric (he : IsCoTriad e h) (hg : IsCoordMetric h U) (hx : x ∈ U)
    (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (a b c : Fin 3) :
    ∑ i, (covTriad e h x a i b * e x i c + e x i b * covTriad e h x a i c) = 0 := by
  have hpd : Lightlike.pd a (fun y => h y b c) x =
      ∑ i, (Lightlike.pd a (fun y => e y i b) x * e x i c + e x i b * Lightlike.pd a (fun y => e y i c) x) := by
    have hf : (fun y => h y b c) = fun y => ∑ i, e y i b * e y i c := funext fun y => coTriad_entry he y b c
    rw [hf, Lightlike.pd_sum (f := fun i y => e y i b * e y i c) _ (fun i _ => (hd i b).mul (hd i c))]
    exact Finset.sum_congr rfl fun i _ => Lightlike.pd_mul (hd i b) (hd i c) a
  have hc := hg.pd_eq_christoffelFirst hx a b c
  have s1 := sum_christoffel_mul hg hx a b c
  have s2 := sum_christoffel_mul hg hx a c b
  have hs : ∀ d c', h x d c' = ∑ i, e x i d * e x i c' := fun d c' => coTriad_entry he x d c'
  rw [hc] at hpd
  simp only [hs] at s1 s2
  simp only [covTriad]
  simp only [Fin.sum_univ_three] at hpd s1 s2 ⊢
  linear_combination -hpd - s1 - s2

/-- The covariant derivative of the co-triad as a matrix, `C_a = (∇_a e^i_b)` (row `i` internal, column `b` spatial). -/
def covTriadMat (e : CoTriad) (h : TensorField 3) (x : Fin 3 → ℝ) (a : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i b => covTriad e h x a i b

/-- Metric compatibility in matrix form: `C_aᵀ e + eᵀ C_a = 0` for `C_a = (∇_a e^i_b)`, i.e. `∇_a h = 0` for
`h = eᵀ e` (`covTriad_metric`). -/
lemma covTriad_metric_mat (he : IsCoTriad e h) (hg : IsCoordMetric h U) (hx : x ∈ U)
    (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (a : Fin 3) :
    (covTriadMat e h x a)ᵀ * e x + (e x)ᵀ * covTriadMat e h x a = 0 := by
  ext b c
  have := covTriad_metric he hg hx hd a b c
  simpa [covTriadMat, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_add_distrib] using this

/-- `ω_a = (e⁻¹)ᵀ C_aᵀ` as a matrix `(ω_a^{jk})`. -/
lemma triadOmega_mat (a j k : Fin 3) :
    triadOmega e h x a j k = (((e x)⁻¹)ᵀ * (covTriadMat e h x a)ᵀ) j k := by
  simp [triadOmega, covTriadMat, Matrix.mul_apply, Matrix.transpose_apply]

/-- **`ω_a^{jk}` is antisymmetric** in `j, k` (metric compatibility). -/
theorem triadOmega_antisymm (he : IsCoTriad e h) (hg : IsCoordMetric h U) (hx : x ∈ U)
    (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (a j k : Fin 3) :
    triadOmega e h x a j k + triadOmega e h x a k j = 0 := by
  have hu := (he x).1
  set f := (e x)⁻¹ with hf
  set C := covTriadMat e h x a with hC
  have hm := covTriad_metric_mat he hg hx hd a
  rw [← hC] at hm
  have hef : e x * f = 1 := mul_nonsing_inv _ hu
  have hfe : fᵀ * (e x)ᵀ = 1 := by rw [← Matrix.transpose_mul, hef, Matrix.transpose_one]
  have key : fᵀ * Cᵀ + (fᵀ * Cᵀ)ᵀ = 0 := by
    have h1 : fᵀ * (Cᵀ * e x + (e x)ᵀ * C) * f = 0 := by rw [hm]; simp
    rw [Matrix.mul_add, Matrix.add_mul] at h1
    rw [show fᵀ * (Cᵀ * e x) * f = fᵀ * Cᵀ * (e x * f) by simp only [Matrix.mul_assoc], hef, Matrix.mul_one,
      show fᵀ * ((e x)ᵀ * C) * f = (fᵀ * (e x)ᵀ) * (C * f) by simp only [Matrix.mul_assoc], hfe, Matrix.one_mul] at h1
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose]
    exact h1
  have := congrFun (congrFun key j) k
  rw [Matrix.add_apply, Matrix.transpose_apply, Matrix.zero_apply] at this
  rw [triadOmega_mat, triadOmega_mat, ← hf, ← hC]
  exact this

/-- `∇_a e^k_b = Σ_j e^j_b ω_a^{jk}`. -/
lemma covTriad_eq_omega (he : IsCoTriad e h) (a k b : Fin 3) :
    covTriad e h x a k b = ∑ j, e x j b * triadOmega e h x a j k := by
  have hu := (he x).1
  have hfe : (e x)⁻¹ * e x = 1 := nonsing_inv_mul _ hu
  simp only [triadOmega, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ c, ∑ j, e x j b * ((e x)⁻¹ c j * covTriad e h x a k c) =
      (if c = b then 1 else 0) * covTriad e h x a k c := by
    intro c
    have hm := congrFun (congrFun hfe c) b
    rw [Matrix.mul_apply, Matrix.one_apply] at hm
    rw [← hm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [key, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **The co-triad is covariantly constant**: `∇_a e^k_b + Σ_ij ε_ijk Γ^i_a e^j_b = 0`. -/
theorem covTriad_add_spin (he : IsCoTriad e h) (hg : IsCoordMetric h U) (hx : x ∈ U)
    (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (a k b : Fin 3) :
    covTriad e h x a k b + ∑ i, ∑ j, eps3 i j k * spinConn e h x a i * e x j b = 0 := by
  have hW : ∀ j k, triadOmega e h x a j k + triadOmega e h x a k j = 0 :=
    fun j k => triadOmega_antisymm he hg hx hd a j k
  have hinv := eps3_dual_inv (Matrix.of fun j k => triadOmega e h x a j k) (by simpa using hW)
  rw [covTriad_eq_omega he a k b]
  have : ∀ j, triadOmega e h x a j k = -∑ i, eps3 i j k * spinConn e h x a i := fun j => by
    simpa [spinConn] using hinv j k
  simp only [this]
  simp only [Fin.sum_univ_three]
  ring

/-- **Compatibility of the spin connection** (Ashtekar–Lewandowski (2.17)): `de^k + ε^k_ij Γ^i ∧ e^j = 0`, i.e.
`∂_a e^k_b − ∂_b e^k_a + Σ_ij ε_kij (Γ^i_a e^j_b − Γ^i_b e^j_a) = 0`. -/
theorem spin_compat (he : IsCoTriad e h) (hg : IsCoordMetric h U) (hx : x ∈ U)
    (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (k a b : Fin 3) :
    Lightlike.pd a (fun y => e y k b) x - Lightlike.pd b (fun y => e y k a) x +
      ∑ i, ∑ j, eps3 k i j * (spinConn e h x a i * e x j b - spinConn e h x b i * e x j a) = 0 := by
  have h1 := covTriad_add_spin he hg hx hd a k b
  have h2 := covTriad_add_spin he hg hx hd b k a
  have hsym : ∀ c, Lightlike.christoffel h c a b x = Lightlike.christoffel h c b a x := fun c =>
    (hg.eventuallyEq_christoffel_symm hx c a b).self_of_nhds
  have hcyc : ∀ i j, eps3 k i j = eps3 i j k := fun i j => by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp [eps3_apply]
  simp only [covTriad, hsym] at h1 h2
  simp only [hcyc]
  simp only [Fin.sum_univ_three] at h1 h2 ⊢
  linear_combination h1 - h2

/-! ### The Ashtekar–Barbero connection and the Gauss constraint -/

/-- **The Ashtekar–Barbero connection** `A^i_a = Γ^i_a + γ K^i_a` (Ashtekar–Lewandowski (2.20) with `σ = −1`;
Barbero–Immirzi parameter `γ`), row `a`, column `i`. -/
def abConn (γ : ℝ) (e : CoTriad) (h K : TensorField 3) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  spinConn e h x + γ • triadK e K x

/-- **The Gauss constraint** `G_i = ∂_a E^a_i + ε_ijk A^j_a E^a_k` of a connection `A` and a densitized triad `E`
(Ashtekar–Lewandowski (2.23), with `P = E/(kγ)`; the constant factor is dropped). -/
def gaussConstraint (A E : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ a, Lightlike.pd a (fun y => E y a i) x + ∑ j, ∑ k, eps3 i j k * ∑ a, A x a j * E x a k

/-- For a positively oriented co-triad the densitized triad is the cofactor polynomial
`E^a_i = ½ ε_ijk ε_abc e^j_b e^k_c` (Ashtekar–Lewandowski (2.20), `P^a_i = (1/2kγ) e^j_b e^k_c η^{abc} ε_ijk`). -/
lemma densTriad_eq_poly {y : Fin 3 → ℝ} (hpos : 0 < (e y).det) (a i : Fin 3) :
    densTriad e y a i = ∑ j, ∑ k, ∑ b, ∑ c, (1 / 2) * (eps3 i j k * eps3 a b c) * (e y j b * e y k c) := by
  have hadj : densTriad e y = adjugate (e y) := by
    unfold densTriad
    rw [abs_of_pos hpos, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hpos.ne', one_smul]
  rw [hadj, Matrix.adjugate_fin_three]
  fin_cases a <;> fin_cases i <;> simp [Fin.sum_univ_three, eps3_apply] <;> ring

/-- The partial derivative of a quadratic polynomial in the co-triad. -/
lemma pd_quad (C : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (a : Fin 3) :
    Lightlike.pd a (fun y => ∑ j, ∑ k, ∑ b, ∑ c, C j k b c * (e y j b * e y k c)) x =
      ∑ j, ∑ k, ∑ b, ∑ c, C j k b c *
        (Lightlike.pd a (fun y => e y j b) x * e x k c + e x j b * Lightlike.pd a (fun y => e y k c) x) := by
  have d4 : ∀ j k b c, DifferentiableAt ℝ (fun y => C j k b c * (e y j b * e y k c)) x :=
    fun j k b c => ((hd j b).mul (hd k c)).const_mul _
  have d3 : ∀ j k b, DifferentiableAt ℝ (fun y => ∑ c, C j k b c * (e y j b * e y k c)) x :=
    fun j k b => DifferentiableAt.fun_sum fun c _ => d4 j k b c
  have d2 : ∀ j k, DifferentiableAt ℝ (fun y => ∑ b, ∑ c, C j k b c * (e y j b * e y k c)) x :=
    fun j k => DifferentiableAt.fun_sum fun b _ => d3 j k b
  have d1 : ∀ j, DifferentiableAt ℝ (fun y => ∑ k, ∑ b, ∑ c, C j k b c * (e y j b * e y k c)) x :=
    fun j => DifferentiableAt.fun_sum fun k _ => d2 j k
  rw [Lightlike.pd_sum (f := fun j y => ∑ k, ∑ b, ∑ c, C j k b c * (e y j b * e y k c)) _ (fun j _ => d1 j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Lightlike.pd_sum (f := fun k y => ∑ b, ∑ c, C j k b c * (e y j b * e y k c)) _ (fun k _ => d2 j k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Lightlike.pd_sum (f := fun b y => ∑ c, C j k b c * (e y j b * e y k c)) _ (fun b _ => d3 j k b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Lightlike.pd_sum (f := fun c y => C j k b c * (e y j b * e y k c)) _ (fun c _ => d4 j k b c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Lightlike.pd_const_mul (f := fun y => e y j b * e y k c) _ ((hd j b).mul (hd k c)),
    Lightlike.pd_mul (hd j b) (hd k c)]

set_option maxHeartbeats 600000 in
/-- **The spin connection solves the Gauss constraint of the densitized triad**: `∂_a E^a_i + ε_ijk Γ^j_a E^a_k = 0`
(`D_a E^a_i = 0`), for a positively oriented co-triad. -/
theorem gauss_spinConn (he : IsCoTriad e h) (hg : IsCoordMetric h U) (hx : x ∈ U)
    (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (hpos : ∀ᶠ y in nhds x, 0 < (e y).det) (i : Fin 3) :
    gaussConstraint (spinConn e h) (densTriad e) x i = 0 := by
  have hcomp := fun k a b => spin_compat he hg hx hd k a b
  have hE : ∀ a, (fun y => densTriad e y a i) =ᶠ[nhds x]
      fun y => ∑ j, ∑ k, ∑ b, ∑ c, (1 / 2) * (eps3 i j k * eps3 a b c) * (e y j b * e y k c) := fun a => by
    filter_upwards [hpos] with y hy
    exact densTriad_eq_poly hy a i
  have hEx : ∀ a k, densTriad e x a k =
      ∑ j, ∑ l, ∑ b, ∑ c, (1 / 2) * (eps3 k j l * eps3 a b c) * (e x j b * e x l c) := fun a k =>
    densTriad_eq_poly hpos.self_of_nhds a k
  have hsum : ∑ j, ∑ a, ∑ b, ((1 / 2) * ∑ k, ∑ c, eps3 i j k * eps3 a b c * e x k c) *
      (Lightlike.pd a (fun y => e y j b) x - Lightlike.pd b (fun y => e y j a) x +
        ∑ l, ∑ m, eps3 j l m * (spinConn e h x a l * e x m b - spinConn e h x b l * e x m a)) = 0 := by
    simp [hcomp]
  have hpdE : ∀ a, Lightlike.pd a (fun y => densTriad e y a i) x =
      Lightlike.pd a (fun y => ∑ j, ∑ k, ∑ b, ∑ c, (1 / 2) * (eps3 i j k * eps3 a b c) * (e y j b * e y k c)) x :=
    fun a => Lightlike.pd_congr (hE a) a
  unfold gaussConstraint
  simp only [hpdE, pd_quad _ hd, hEx]
  fin_cases i <;> simp only [Fin.sum_univ_three, eps3_apply] at hsum ⊢ <;> norm_num at hsum ⊢ <;>
    linear_combination hsum

/-- **The Ashtekar–Barbero variables of ADM data satisfy the Gauss constraint**: for a positively oriented co-triad of
`h` and a symmetric extrinsic curvature `K`, `G_i(A, E) = 0` with `A = Γ + γK` and `E` the densitized triad, for every
Barbero–Immirzi parameter `γ`. -/
theorem gauss_abConn (γ : ℝ) {K : TensorField 3} (he : IsCoTriad e h) (hg : IsCoordMetric h U) (hx : x ∈ U)
    (hd : ∀ i b, DifferentiableAt ℝ (fun y => e y i b) x) (hpos : ∀ᶠ y in nhds x, 0 < (e y).det)
    (hK : (K x)ᵀ = K x) (i : Fin 3) :
    gaussConstraint (abConn γ e h K) (densTriad e) x i = 0 := by
  have h1 := gauss_spinConn he hg hx hd hpos i
  have h2 := (gaussK_eq_zero_iff e K x (he x).1).2 hK i
  unfold gaussConstraint at h1 ⊢
  unfold gaussK at h2
  simp only [abConn, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_three] at h1 h2 ⊢
  linear_combination h1 + γ * h2

/-! ### Trust checks -/

/-- The flat co-triad `e = 1` of the flat metric. -/
lemma isCoTriad_one : IsCoTriad (fun _ => 1) (fun _ => 1) := fun _ => by simp

/-- **The flat triad has zero spin connection.** -/
theorem spinConn_one (x : Fin 3 → ℝ) : spinConn (fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ => 1) x = 0 := by
  ext a i
  simp [spinConn, triadOmega, covTriad, Lightlike.christoffel_const, Lightlike.pd_const]

/-- **Trust check: an antisymmetric extrinsic curvature violates the Gauss constraint** of the Ashtekar–Barbero
variables (flat triad, `γ ≠ 0`), so `gauss_abConn` uses the symmetry of `K`. -/
theorem gauss_abConn_antisymm_violates (γ : ℝ) (hγ : γ ≠ 0) (x : Fin 3 → ℝ) :
    gaussConstraint (abConn γ (fun _ => 1) (fun _ => 1) (fun _ => !![0, 1, 0; -1, 0, 0; 0, 0, 0]))
      (densTriad fun _ => 1) x 2 ≠ 0 := by
  unfold gaussConstraint abConn
  rw [spinConn_one]
  simp [densTriad, triadK, Lightlike.pd_const, Fin.sum_univ_three, eps3_apply]
  exact hγ

end Lightlike.Canonical
