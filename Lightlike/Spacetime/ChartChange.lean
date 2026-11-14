module

public import Lightlike.Spacetime.RiemannSymmetry
public import Lightlike.GR.Einstein

/-!
# Change of coordinates: how Christoffel symbols transform

Let `φ : V → U` be a smooth change of coordinates (`IsChartChange φ V U`: `V` open, `φ` maps `V`
into `U`, components `C^∞`, Jacobian invertible) and `g` a coordinate metric on `U`. The metric in
the new coordinates is the pullback `g'_{ab}(y) = J^μ_a(y) g_{μν}(φ y) J^ν_b(y)` with
`J^μ_a = ∂_a φ^μ` (`jac`).

Main result (`christoffel_pullback`): the classical transformation law

  `J^μ_a Γ'^a_{bc}(y) = Γ^μ_{νλ}(φ y) J^ν_b J^λ_c + ∂_b ∂_c φ^μ(y)`.

The inhomogeneous second-derivative term is why Christoffel symbols are *not* a tensor. This is
the first half of chart-independence of curvature; the Riemann transformation law is
built on it.

**References.** R. M. Wald, *General Relativity* (University of Chicago Press, 1984), ch. 2 (tensor fields and their transformation under a change of coordinates); J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed. (Springer, 2018).
-/

@[expose] public section

open Matrix Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- Jacobian `J^μ_a(y) = ∂_a φ^μ(y)` (row `μ` = target index, column `a` = source index). -/
def jac (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun μ a => pd a (fun z => φ z μ) y

/-- Second derivatives `H^μ_{ab}(y) = ∂_a ∂_b φ^μ(y)`. -/
def hess (φ : (Fin n → ℝ) → (Fin n → ℝ)) (μ a b : Fin n) (y : Fin n → ℝ) : ℝ :=
  pd a (pd b (fun z => φ z μ)) y

/-- The pulled-back metric `g'_{ab}(y) = Σ_{μν} J^μ_a g_{μν}(φ y) J^ν_b`. -/
def pullback (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => ∑ μ, ∑ ν, jac φ y μ a * g (φ y) μ ν * jac φ y ν b

lemma pullback_eq_mul (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) :
    pullback g φ y = (jac φ y)ᵀ * g (φ y) * jac φ y := by
  ext a b
  simp only [pullback, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A smooth change of coordinates from the open set `V` into `U`. -/
structure IsChartChange (φ : (Fin n → ℝ) → (Fin n → ℝ)) (V U : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen V
  mapsTo : Set.MapsTo φ V U
  smooth : ∀ μ, ContDiffOn ℝ ∞ (fun y => φ y μ) V
  isUnit_det : ∀ y ∈ V, IsUnit (jac φ y).det

/-! ## Chain rule for `pd` -/

/-- **Chain rule** for coordinate derivatives: `∂_b (f ∘ φ)(y) = Σ_l (∂_l f)(φ y) J^l_b(y)`. -/
lemma pd_comp {f : (Fin n → ℝ) → ℝ} {φ : (Fin n → ℝ) → (Fin n → ℝ)} {y : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f (φ y)) (hφ : ∀ μ, DifferentiableAt ℝ (fun z => φ z μ) y)
    (b : Fin n) : pd b (fun z => f (φ z)) y = ∑ l, pd l f (φ y) * jac φ y l b := by
  set Φ' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun μ => fderiv ℝ (fun z => φ z μ) y
  have hΦ : HasFDerivAt φ Φ' y := hasFDerivAt_pi'' fun μ => by
    simpa [Φ'] using (hφ μ).hasFDerivAt
  have hc := (hf.hasFDerivAt.comp y hΦ).fderiv
  simp only [pd, jac]
  rw [show (fun z => f (φ z)) = f ∘ φ from rfl, hc, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [← Finset.univ_sum_single (Φ' (Pi.single b 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hs : Pi.single l ((Φ' (Pi.single b 1)) l) =
      ((Φ' (Pi.single b 1)) l) • (Pi.single l (1 : ℝ) : Fin n → ℝ) := by
    ext j; by_cases h : j = l <;> simp [h]
  rw [hs, map_smul, smul_eq_mul, mul_comm]
  simp [Φ']

/-! ## Smoothness facts -/

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U V : Set (Fin n → ℝ)}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}

lemma IsChartChange.contDiffOn (hφ : IsChartChange φ V U) : ContDiffOn ℝ ∞ φ V :=
  contDiffOn_pi.mpr hφ.smooth

lemma IsChartChange.contDiffOn_jac (hφ : IsChartChange φ V U) (μ a : Fin n) :
    ContDiffOn ℝ ∞ (fun z => jac φ z μ a) V :=
  contDiffOn_pd (hφ.smooth μ) hφ.isOpen a

lemma IsChartChange.hess_symm (hφ : IsChartChange φ V U) {y : Fin n → ℝ} (hy : y ∈ V)
    (μ a b : Fin n) : hess φ μ a b y = hess φ μ b a y :=
  pd_pd_comm (hφ.smooth μ) hφ.isOpen hy a b

lemma contDiffOn_comp_entry (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) (μ ν : Fin n) :
    ContDiffOn ℝ ∞ (fun z => g (φ z) μ ν) V :=
  (hg.smooth μ ν).comp hφ.contDiffOn hφ.mapsTo

/-! ## Derivative of the pulled-back metric -/

/-- Bilinear contraction `S(u, w) = Σ_{μν} u_μ g_{μν} w_ν` at a point. -/
def bil (G : Matrix (Fin n) (Fin n) ℝ) (u w : Fin n → ℝ) : ℝ := ∑ μ, ∑ ν, u μ * G μ ν * w ν

/-- Trilinear contraction `T(u, v, w) = Σ_{μνl} u_μ v_ν w_l ∂_l g_{μν}` at the point `p`. -/
def tri (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) (u v w : Fin n → ℝ) : ℝ :=
  ∑ μ, ∑ ν, ∑ l, u μ * v ν * w l * pd l (fun z => g z μ ν) p

/-- Column `a` of the Jacobian. -/
def jcol (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) (a : Fin n) : Fin n → ℝ :=
  fun μ => jac φ y μ a

/-- The vector `(∂_a∂_b φ^μ)_μ`. -/
def hcol (φ : (Fin n → ℝ) → (Fin n → ℝ)) (y : Fin n → ℝ) (a b : Fin n) : Fin n → ℝ :=
  fun μ => hess φ μ a b y

lemma pd_triple {A B C : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (hA : DifferentiableAt ℝ A y)
    (hB : DifferentiableAt ℝ B y) (hC : DifferentiableAt ℝ C y) (k : Fin n) :
    pd k (fun z => A z * B z * C z) y =
      pd k A y * B y * C y + A y * pd k B y * C y + A y * B y * pd k C y := by
  rw [pd_mul (f₁ := fun z => A z * B z) (hA.mul hB) hC, pd_mul hA hB]; ring

/-- Derivative of the pulled-back metric `g'_{ac} = J^μ_a g_{μν}(φ) J^ν_c` (product and chain
rules): `∂_b g'_{ac} = (∂_b∂_a φ)·g·J_c + J_a J_c J_b·∂g + J_a·g·(∂_b∂_c φ)`. -/
lemma pd_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) (a c b : Fin n) :
    pd b (fun z => pullback g φ z a c) y =
      bil (g (φ y)) (hcol φ y b a) (jcol φ y c) + tri g (φ y) (jcol φ y a) (jcol φ y c) (jcol φ y b)
        + bil (g (φ y)) (jcol φ y a) (hcol φ y b c) := by
  have hJ : ∀ μ a, DifferentiableAt ℝ (fun z => jac φ z μ a) y := fun μ a =>
    differentiableAt_of_contDiffOn (hφ.contDiffOn_jac μ a) hφ.isOpen hy
  have hG : ∀ μ ν, DifferentiableAt ℝ (fun z => g (φ z) μ ν) y := fun μ ν =>
    differentiableAt_of_contDiffOn (contDiffOn_comp_entry hg hφ μ ν) hφ.isOpen hy
  have hφd : ∀ μ, DifferentiableAt ℝ (fun z => φ z μ) y := fun μ =>
    differentiableAt_of_contDiffOn (hφ.smooth μ) hφ.isOpen hy
  have hgd : ∀ μ ν, DifferentiableAt ℝ (fun w => g w μ ν) (φ y) := fun μ ν =>
    differentiableAt_of_contDiffOn (hg.smooth μ ν) hg.isOpen (hφ.mapsTo hy)
  have hterm : ∀ μ ν, DifferentiableAt ℝ
      (fun z => jac φ z μ a * g (φ z) μ ν * jac φ z ν c) y := fun μ ν =>
    ((hJ μ a).mul (hG μ ν)).mul (hJ ν c)
  simp only [pullback]
  rw [pd_sum (f := fun μ z => ∑ ν, jac φ z μ a * g (φ z) μ ν * jac φ z ν c) Finset.univ
    (fun μ _ => DifferentiableAt.fun_sum fun ν _ => hterm μ ν)]
  simp only [bil, tri, jcol, hcol, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pd_sum (f := fun ν z => jac φ z μ a * g (φ z) μ ν * jac φ z ν c) Finset.univ
    (fun ν _ => hterm μ ν)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [pd_triple (hJ μ a) (hG μ ν) (hJ ν c),
    pd_comp (f := fun w => g w μ ν) (hgd μ ν) hφd b]
  simp only [hess, jac, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ## Christoffel symbols of the first kind -/

lemma IsCoordMetric.bil_symm (hg : IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U)
    (u w : Fin n → ℝ) : bil (g p) u w = bil (g p) w u := by
  simp only [bil]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  have : g p ν μ = g p μ ν := by rw [← Matrix.transpose_apply (g p) μ ν, hg.symm p hp]
  rw [this]; ring

/-- `Σ_{μνl} u_μ v_ν w_l Γ_{μνl} = ½(T(u,w,v) + T(u,v,w) - T(v,w,u))`. -/
lemma sum_christoffelFirst (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ)
    (u v w : Fin n → ℝ) :
    ∑ μ, ∑ ν, ∑ l, u μ * v ν * w l * christoffelFirst g μ ν l p =
      (1 / 2) * (tri g p u w v + tri g p u v w - tri g p v w u) := by
  have hA : ∑ μ, ∑ ν, ∑ l, u μ * v ν * w l * pd ν (fun z => g z μ l) p = tri g p u w v := by
    simp only [tri]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => by ring
  have hB : ∑ μ, ∑ ν, ∑ l, u μ * v ν * w l * pd l (fun z => g z μ ν) p = tri g p u v w := by
    simp only [tri]
  have hC : ∑ μ, ∑ ν, ∑ l, u μ * v ν * w l * pd μ (fun z => g z ν l) p = tri g p v w u := by
    simp only [tri]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_comm]
    try exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun μ _ => by ring
  rw [← hA, ← hB, ← hC]
  simp only [christoffelFirst, mul_add, mul_sub, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun l _ => by ring

/-- **First-kind transformation law**:
`Γ'_{abc} = Σ J^μ_a J^ν_b J^l_c Γ_{μνl}(φ y) + Σ J^μ_a g_{μν}(φ y) ∂_b∂_c φ^ν`. -/
theorem christoffelFirst_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U)
    {y : Fin n → ℝ} (hy : y ∈ V) (a b c : Fin n) :
    christoffelFirst (pullback g φ) a b c y =
      ∑ μ, ∑ ν, ∑ l, jcol φ y a μ * jcol φ y b ν * jcol φ y c l * christoffelFirst g μ ν l (φ y)
        + bil (g (φ y)) (jcol φ y a) (hcol φ y b c) := by
  have hp := hφ.mapsTo hy
  have h1 : hcol φ y b a = hcol φ y a b := funext fun μ => hφ.hess_symm hy μ b a
  have h2 : hcol φ y c a = hcol φ y a c := funext fun μ => hφ.hess_symm hy μ c a
  have h3 : hcol φ y c b = hcol φ y b c := funext fun μ => hφ.hess_symm hy μ c b
  rw [sum_christoffelFirst]
  simp only [christoffelFirst]
  rw [pd_pullback hg hφ hy a c b, pd_pullback hg hφ hy a b c, pd_pullback hg hφ hy b c a,
    h1, h2, h3, hg.bil_symm hp (jcol φ y b) (hcol φ y a c)]
  ring

/-! ## The transformation law for Christoffel symbols -/

/-- The vector `W_κ = Σ_{νl} J^ν_b J^l_c Γ_{κνl}(φ y) + Σ_ν g_{κν}(φ y) ∂_b∂_c φ^ν`, so that
`Γ'_{·bc} = Jᵀ W`. -/
def wvec (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (y : Fin n → ℝ) (b c : Fin n) : Fin n → ℝ :=
  fun κ => ∑ ν, ∑ l, jac φ y ν b * jac φ y l c * christoffelFirst g κ ν l (φ y) +
    ∑ ν, g (φ y) κ ν * hess φ ν b c y

lemma christoffelFirst_pullback_eq_mulVec (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U)
    {y : Fin n → ℝ} (hy : y ∈ V) (b c : Fin n) :
    (fun d => christoffelFirst (pullback g φ) d b c y) = (jac φ y)ᵀ *ᵥ wvec g φ y b c := by
  funext d
  rw [christoffelFirst_pullback hg hφ hy]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, wvec, bil, jcol, hcol, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

/-- `J (Jᵀ G J)⁻¹ Jᵀ = G⁻¹` for invertible `J`. -/
lemma jac_mul_inv_pullback_mul (G J : Matrix (Fin n) (Fin n) ℝ) (hJ : IsUnit J.det) :
    J * (Jᵀ * G * J)⁻¹ * Jᵀ = G⁻¹ := by
  have hJt : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJt, Matrix.mul_one]

/-- **Transformation law for Christoffel symbols** under a smooth change of coordinates `φ`:
`J^μ_a Γ'^a_{bc}(y) = Γ^μ_{νλ}(φ y) J^ν_b J^λ_c + ∂_b ∂_c φ^μ(y)`. -/
theorem christoffel_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U)
    {y : Fin n → ℝ} (hy : y ∈ V) (μ b c : Fin n) :
    ∑ a, jac φ y μ a * christoffel (pullback g φ) a b c y =
      ∑ ν, ∑ l, christoffel g μ ν l (φ y) * jac φ y ν b * jac φ y l c + hess φ μ b c y := by
  have hp := hφ.mapsTo hy
  -- LHS = (J (Jᵀ G J)⁻¹ Jᵀ W)_μ = (G⁻¹ W)_μ
  have hL : ∑ a, jac φ y μ a * christoffel (pullback g φ) a b c y =
      ((g (φ y))⁻¹ *ᵥ wvec g φ y b c) μ := by
    have hΓ : (fun a => christoffel (pullback g φ) a b c y) =
        (pullback g φ y)⁻¹ *ᵥ ((jac φ y)ᵀ *ᵥ wvec g φ y b c) := by
      funext a
      rw [christoffel_eq_sum, ← christoffelFirst_pullback_eq_mulVec hg hφ hy b c]
      rfl
    have : ∑ a, jac φ y μ a * christoffel (pullback g φ) a b c y =
        (jac φ y *ᵥ (fun a => christoffel (pullback g φ) a b c y)) μ := rfl
    rw [this, hΓ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, pullback_eq_mul,
      jac_mul_inv_pullback_mul _ _ (hφ.isUnit_det y hy)]
  rw [hL]
  have hGinv : (g (φ y))⁻¹ * g (φ y) = 1 := Matrix.nonsing_inv_mul _ (hg.isUnit_det _ hp)
  simp only [Matrix.mulVec, dotProduct, wvec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [christoffel_eq_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun κ _ => by ring
  · rw [Finset.sum_comm]
    have : ∀ ν, ∑ κ, (g (φ y))⁻¹ μ κ * (g (φ y) κ ν * hess φ ν b c y) =
        ((g (φ y))⁻¹ * g (φ y)) μ ν * hess φ ν b c y := fun ν => by
      rw [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun κ _ => by ring
    simp only [this, hGinv, Matrix.one_apply]
    simp

/-! ## The pulled-back metric is a coordinate metric -/

/-- The pullback of a coordinate metric along a chart change is a coordinate metric on `V`. -/
theorem isCoordMetric_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) :
    IsCoordMetric (pullback g φ) V where
  isOpen := hφ.isOpen
  symm y hy := by
    rw [pullback_eq_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hg.symm _ (hφ.mapsTo hy), Matrix.mul_assoc]
  isUnit_det y hy := by
    rw [pullback_eq_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact ((hφ.isUnit_det y hy).mul (hg.isUnit_det _ (hφ.mapsTo hy))).mul (hφ.isUnit_det y hy)
  smooth a b := ContDiffOn.sum fun μ _ => ContDiffOn.sum fun ν _ =>
    ((hφ.contDiffOn_jac μ a).mul (contDiffOn_comp_entry hg hφ μ ν)).mul (hφ.contDiffOn_jac ν b)

/-! ## The transformation law for the Riemann tensor -/

section RiemannLaw

variable (g φ)

/-- `G2^m(u, v) = Σ_{νl} Γ^m_{νl}(p) u_ν v_l`. -/
def G2 (p : Fin n → ℝ) (m : Fin n) (u v : Fin n → ℝ) : ℝ :=
  ∑ ν, ∑ l, christoffel g m ν l p * u ν * v l

/-- `D3^m(u, v, w) = Σ_{κνl} ∂_κΓ^m_{νl}(p) u_κ v_ν w_l`. -/
def D3 (p : Fin n → ℝ) (m : Fin n) (u v w : Fin n → ℝ) : ℝ :=
  ∑ κ, ∑ ν, ∑ l, pd κ (christoffel g m ν l) p * u κ * v ν * w l

/-- `Q^m(u, v, w) = Σ_{νl} Γ^m_{νl}(p) u_ν G2^l(v, w)`. -/
def Q3 (p : Fin n → ℝ) (m : Fin n) (u v w : Fin n → ℝ) : ℝ :=
  ∑ ν, ∑ l, christoffel g m ν l p * u ν * G2 g p l v w

variable {g φ}

lemma G2_add_right (p : Fin n → ℝ) (m : Fin n) (u v w : Fin n → ℝ) :
    G2 g p m u (v + w) = G2 g p m u v + G2 g p m u w := by
  simp only [G2, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The Christoffel law in `G2` notation, valid at every point of `V`. -/
lemma christoffel_law (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {z : Fin n → ℝ}
    (hz : z ∈ V) (m b c : Fin n) :
    ∑ a, jac φ z m a * christoffel (pullback g φ) a b c z =
      G2 g (φ z) m (jcol φ z b) (jcol φ z c) + hess φ m b c z := by
  rw [christoffel_pullback hg hφ hz]
  rfl

/-- Step A: differentiate the Christoffel law in direction `c`. -/
lemma jac_pd_christoffel (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) (m c d b : Fin n) :
    ∑ a, jac φ y m a * pd c (christoffel (pullback g φ) a d b) y =
      D3 g (φ y) m (jcol φ y c) (jcol φ y d) (jcol φ y b)
        + G2 g (φ y) m (hcol φ y c d) (jcol φ y b) + G2 g (φ y) m (jcol φ y d) (hcol φ y c b)
        + pd c (hess φ m d b) y
        - ∑ a, hess φ m c a y * christoffel (pullback g φ) a d b y := by
  have hp := hφ.mapsTo hy
  have hg' := isCoordMetric_pullback hg hφ
  have hJ : ∀ μ a, DifferentiableAt ℝ (fun z => jac φ z μ a) y := fun μ a =>
    differentiableAt_of_contDiffOn (hφ.contDiffOn_jac μ a) hφ.isOpen hy
  have hΓ' : ∀ a j k, DifferentiableAt ℝ (christoffel (pullback g φ) a j k) y := fun a j k =>
    differentiableAt_of_contDiffOn (hg'.contDiffOn_christoffel a j k) hφ.isOpen hy
  have hΓp : ∀ i j k, DifferentiableAt ℝ (christoffel g i j k) (φ y) := fun i j k =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_christoffel i j k) hg.isOpen hp
  have hφd : ∀ μ, DifferentiableAt ℝ (fun z => φ z μ) y := fun μ =>
    differentiableAt_of_contDiffOn (hφ.smooth μ) hφ.isOpen hy
  have hΓφ : ∀ i j k, DifferentiableAt ℝ (fun z => christoffel g i j k (φ z)) y := fun i j k =>
    (hΓp i j k).comp y (differentiableAt_pi.mpr hφd)
  have hH : DifferentiableAt ℝ (hess φ m d b) y :=
    differentiableAt_of_contDiffOn
      (contDiffOn_pd (contDiffOn_pd (hφ.smooth m) hφ.isOpen b) hφ.isOpen d) hφ.isOpen hy
  -- the law holds near `y`, so its two sides have equal derivatives at `y`
  have hev : (fun z => ∑ a, jac φ z m a * christoffel (pullback g φ) a d b z) =ᶠ[𝓝 y]
      (fun z => ∑ ν, ∑ l, christoffel g m ν l (φ z) * jac φ z ν d * jac φ z l b + hess φ m d b z) :=
    eventually_of_mem (hφ.isOpen.mem_nhds hy) fun z hz => christoffel_pullback hg hφ hz m d b
  have hL : pd c (fun z => ∑ a, jac φ z m a * christoffel (pullback g φ) a d b z) y =
      ∑ a, (hess φ m c a y * christoffel (pullback g φ) a d b y +
        jac φ y m a * pd c (christoffel (pullback g φ) a d b) y) := by
    rw [pd_sum (f := fun a z => jac φ z m a * christoffel (pullback g φ) a d b z) Finset.univ
      (fun a _ => (hJ m a).mul (hΓ' a d b))]
    exact Finset.sum_congr rfl fun a _ => pd_mul (hJ m a) (hΓ' a d b) c
  have hR : pd c (fun z => ∑ ν, ∑ l, christoffel g m ν l (φ z) * jac φ z ν d * jac φ z l b +
      hess φ m d b z) y =
      D3 g (φ y) m (jcol φ y c) (jcol φ y d) (jcol φ y b)
        + G2 g (φ y) m (hcol φ y c d) (jcol φ y b) + G2 g (φ y) m (jcol φ y d) (hcol φ y c b)
        + pd c (hess φ m d b) y := by
    have hterm : ∀ ν l, DifferentiableAt ℝ
        (fun z => christoffel g m ν l (φ z) * jac φ z ν d * jac φ z l b) y := fun ν l =>
      ((hΓφ m ν l).mul (hJ ν d)).mul (hJ l b)
    rw [pd_add (DifferentiableAt.fun_sum fun ν _ => DifferentiableAt.fun_sum fun l _ => hterm ν l)
      hH]
    rw [pd_sum (f := fun ν z => ∑ l, christoffel g m ν l (φ z) * jac φ z ν d * jac φ z l b)
      Finset.univ (fun ν _ => DifferentiableAt.fun_sum fun l _ => hterm ν l)]
    have hinner : ∀ ν, pd c (fun z => ∑ l, christoffel g m ν l (φ z) * jac φ z ν d * jac φ z l b) y =
        ∑ l, ((∑ κ, pd κ (christoffel g m ν l) (φ y) * jac φ y κ c) * jac φ y ν d * jac φ y l b
          + christoffel g m ν l (φ y) * hess φ ν c d y * jac φ y l b
          + christoffel g m ν l (φ y) * jac φ y ν d * hess φ l c b y) := by
      intro ν
      rw [pd_sum (f := fun l z => christoffel g m ν l (φ z) * jac φ z ν d * jac φ z l b)
        Finset.univ (fun l _ => hterm ν l)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [pd_triple (hΓφ m ν l) (hJ ν d) (hJ l b), pd_comp (hΓp m ν l) hφd c]
      rfl
    simp only [hinner, Finset.sum_add_distrib]
    have hD : ∑ ν, ∑ l, (∑ κ, pd κ (christoffel g m ν l) (φ y) * jac φ y κ c) * jac φ y ν d *
        jac φ y l b = D3 g (φ y) m (jcol φ y c) (jcol φ y d) (jcol φ y b) := by
      simp only [D3, jcol, Finset.sum_mul]
      refine ((Finset.sum_congr rfl fun ν _ => Finset.sum_comm).trans Finset.sum_comm).trans ?_
      exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun ν _ =>
        Finset.sum_congr rfl fun l _ => by ring
    rw [hD]
    simp only [G2, jcol, hcol]
  have := pd_congr hev c
  rw [hL, hR, Finset.sum_add_distrib] at this
  linarith

/-- Quadratic terms: `J^m_a Γ'^a_{ce} Γ'^e_{db} = Q(J_c, J_d, J_b) + G2(J_c, H_{db}) + H^m_{ce}Γ'^e_{db}`. -/
lemma jac_quad (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) (m c d b : Fin n) :
    ∑ a, jac φ y m a * ∑ e, christoffel (pullback g φ) a c e y * christoffel (pullback g φ) e d b y =
      Q3 g (φ y) m (jcol φ y c) (jcol φ y d) (jcol φ y b)
        + G2 g (φ y) m (jcol φ y c) (hcol φ y d b)
        + ∑ e, hess φ m c e y * christoffel (pullback g φ) e d b y := by
  -- swap sums and use the law for `(m; c, e)`
  have h1 : ∑ a, jac φ y m a * ∑ e, christoffel (pullback g φ) a c e y *
        christoffel (pullback g φ) e d b y =
      ∑ e, (G2 g (φ y) m (jcol φ y c) (jcol φ y e) + hess φ m c e y) *
        christoffel (pullback g φ) e d b y := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← christoffel_law hg hφ hy m c e, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- `Σ_e G2(J_c, J_e) Γ'^e_{db} = G2(J_c, Σ_e J_e Γ'^e_{db})` and the law for `(l; d, b)`
  have h2 : ∑ e, G2 g (φ y) m (jcol φ y c) (jcol φ y e) * christoffel (pullback g φ) e d b y =
      G2 g (φ y) m (jcol φ y c) (fun l => ∑ e, jac φ y l e * christoffel (pullback g φ) e d b y) := by
    simp only [G2, jcol, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun e _ => by ring
  have h3 : (fun l => ∑ e, jac φ y l e * christoffel (pullback g φ) e d b y) =
      (fun l => G2 g (φ y) l (jcol φ y d) (jcol φ y b)) + hcol φ y d b := by
    funext l
    rw [christoffel_law hg hφ hy l d b]
    rfl
  rw [h1]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [h2, h3, G2_add_right]
  rfl

lemma d3_reindex (p : Fin n → ℝ) (m : Fin n) (u v w : Fin n → ℝ) :
    ∑ ν, ∑ κ, ∑ l, pd κ (christoffel g m l ν) p * w ν * u κ * v l = D3 g p m u v w := by
  simp only [D3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => by ring

lemma q3_reindex (p : Fin n → ℝ) (m : Fin n) (u v w : Fin n → ℝ) :
    ∑ ν, ∑ κ, ∑ l, (∑ e, christoffel g m κ e p * christoffel g e l ν p) * w ν * u κ * v l =
      Q3 g p m u v w := by
  simp only [Q3, G2, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans ?_
  refine (Finset.sum_congr rfl fun κ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun κ _ => Finset.sum_comm).trans ?_
  exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun e _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => by ring

/-- The contraction `R^m_{νκλ}(p) B^ν C^κ D^λ` in terms of `D3` and `Q3`. -/
lemma riemann_contract (p : Fin n → ℝ) (m : Fin n) (B C D : Fin n → ℝ) :
    ∑ ν, ∑ κ, ∑ l, riemann g m ν κ l p * B ν * C κ * D l =
      D3 g p m C D B - D3 g p m D C B + Q3 g p m C D B - Q3 g p m D C B := by
  have e2 : ∑ ν, ∑ κ, ∑ l, pd l (christoffel g m κ ν) p * B ν * C κ * D l = D3 g p m D C B := by
    refine (Finset.sum_congr rfl fun ν _ => Finset.sum_comm).trans ?_
    rw [← d3_reindex p m D C B]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring
  have e4 : ∑ ν, ∑ κ, ∑ l, (∑ e, christoffel g m l e p * christoffel g e κ ν p) * B ν * C κ * D l
      = Q3 g p m D C B := by
    refine (Finset.sum_congr rfl fun ν _ => Finset.sum_comm).trans ?_
    rw [← q3_reindex p m D C B]
    exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring
  rw [← d3_reindex p m C D B, ← e2, ← q3_reindex p m C D B, ← e4]
  simp only [riemann, Finset.sum_sub_distrib, add_mul, sub_mul, Finset.sum_add_distrib]
  ring

/-- **Transformation law for the Riemann tensor** under a smooth change of coordinates `φ`
(`J = ∂φ`, `g' = Jᵀ (g∘φ) J`):
`J^m_a R'^a_{bcd}(y) = R^m_{νκλ}(φ y) J^ν_b J^κ_c J^λ_d`.
Equivalently `R'^a_{bcd} = (J⁻¹)^a_m R^m_{νκλ} J^ν_b J^κ_c J^λ_d`: the coordinate Riemann tensor is
a genuine `(1,3)`-tensor, so curvature statements do not depend on the chart. -/
theorem riemann_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) (m b c d : Fin n) :
    ∑ a, jac φ y m a * riemann (pullback g φ) a b c d y =
      ∑ ν, ∑ κ, ∑ l, riemann g m ν κ l (φ y) * jac φ y ν b * jac φ y κ c * jac φ y l d := by
  have hT : pd c (hess φ m d b) y = pd d (hess φ m c b) y :=
    pd_pd_comm (contDiffOn_pd (hφ.smooth m) hφ.isOpen b) hφ.isOpen hy c d
  have hH : hcol φ y c d = hcol φ y d c := funext fun μ => hφ.hess_symm hy μ c d
  have A1 := jac_pd_christoffel hg hφ hy m c d b
  have A2 := jac_pd_christoffel hg hφ hy m d c b
  have Q1 := jac_quad hg hφ hy m c d b
  have Q2 := jac_quad hg hφ hy m d c b
  rw [hH] at A1
  have hR := riemann_contract (g := g) (φ y) m (jcol φ y b) (jcol φ y c) (jcol φ y d)
  simp only [jcol] at hR
  rw [hR]
  simp only [riemann, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith

end RiemannLaw

/-! ## Ricci tensor, scalar curvature and the vacuum equations are chart-independent -/

/-- The Ricci tensor as a matrix. -/
def ricciMat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun σ ν => ricci g σ ν x

/-- **Ricci transforms as a (0,2)-tensor**: `Ric'_{bd} = J^ν_b J^λ_d Ric_{νλ}(φ y)`. -/
theorem ricci_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) (b d : Fin n) :
    ricci (pullback g φ) b d y =
      ∑ ν, ∑ l, ricci g ν l (φ y) * jac φ y ν b * jac φ y l d := by
  set J := jac φ y with hJdef
  have hJJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ (hφ.isUnit_det y hy)
  have hJJ' : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hφ.isUnit_det y hy)
  -- `A κ m = Σ_{νl} R^m_{νκl}(φ y) J^ν_b J^l_d`
  set A : Matrix (Fin n) (Fin n) ℝ :=
    fun κ m => ∑ ν, ∑ l, riemann g m ν κ l (φ y) * J ν b * J l d with hA
  -- invert the law: `R'^c_{bcd} = Σ_m J⁻¹_{cm} Σ_κ A_{κm} J_{κc}`
  have hinv : ∀ c, riemann (pullback g φ) c b c d y =
      ∑ m, J⁻¹ c m * ∑ κ, A κ m * J κ c := by
    intro c
    have h1 : riemann (pullback g φ) c b c d y =
        ∑ m, J⁻¹ c m * ∑ a, J m a * riemann (pullback g φ) a b c d y := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ a, ∑ m, J⁻¹ c m * (J m a * riemann (pullback g φ) a b c d y) =
          (J⁻¹ * J) c a * riemann (pullback g φ) a b c d y := fun a => by
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring
      simp only [this, hJJ, Matrix.one_apply]
      simp
    rw [h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [riemann_pullback hg hφ hy m b c d]
    congr 1
    simp only [hA, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun ν _ =>
      Finset.sum_congr rfl fun l _ => by ring
  -- trace trick: `Σ_c Σ_m J⁻¹_{cm} Σ_κ A_{κm} J_{κc} = tr(J⁻¹ Aᵀ J) = tr A`
  have htr : ∑ c, ∑ m, J⁻¹ c m * ∑ κ, A κ m * J κ c = Matrix.trace A := by
    have : ∑ c, ∑ m, J⁻¹ c m * ∑ κ, A κ m * J κ c = Matrix.trace (J⁻¹ * Aᵀ * J) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun m _ => by ring
    rw [this, Matrix.trace_mul_cycle, hJJ', Matrix.one_mul, Matrix.trace_transpose]
  simp only [ricci]
  rw [Finset.sum_congr rfl fun c _ => hinv c, htr]
  simp only [Matrix.trace, Matrix.diag, hA, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [Finset.sum_comm]

lemma ricciMat_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U) {y : Fin n → ℝ}
    (hy : y ∈ V) : ricciMat (pullback g φ) y = (jac φ y)ᵀ * ricciMat g (φ y) * jac φ y := by
  ext b d
  rw [ricciMat, ricci_pullback hg hφ hy]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ricciMat, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun l _ => by ring

lemma scalarCurvature_eq_trace (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    scalarCurvature g x = Matrix.trace ((g x)⁻¹ * (ricciMat g x)ᵀ) := by
  simp [scalarCurvature, Matrix.trace, Matrix.mul_apply, ricciMat]

/-- **Scalar curvature is chart-independent**: `R'(y) = R(φ y)`. -/
theorem scalarCurvature_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U)
    {y : Fin n → ℝ} (hy : y ∈ V) : scalarCurvature (pullback g φ) y = scalarCurvature g (φ y) := by
  have hJt : IsUnit (jac φ y)ᵀ.det := by rw [Matrix.det_transpose]; exact hφ.isUnit_det y hy
  rw [scalarCurvature_eq_trace, scalarCurvature_eq_trace, ricciMat_pullback hg hφ hy,
    pullback_eq_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  have : (jac φ y)⁻¹ * ((g (φ y))⁻¹ * (jac φ y)ᵀ⁻¹) *
      ((jac φ y)ᵀ * ((ricciMat g (φ y))ᵀ * jac φ y)) =
      (jac φ y)⁻¹ * ((g (φ y))⁻¹ * (ricciMat g (φ y))ᵀ) * jac φ y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (jac φ y)ᵀ⁻¹ (jac φ y)ᵀ, Matrix.nonsing_inv_mul _ hJt, Matrix.one_mul]
  rw [this, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ (hφ.isUnit_det y hy), Matrix.one_mul]

/-- The Einstein tensor transforms as a (0,2)-tensor. -/
theorem einsteinTensor_pullback (hg : IsCoordMetric g U) (hφ : IsChartChange φ V U)
    {y : Fin n → ℝ} (hy : y ∈ V) (b d : Fin n) :
    einsteinTensor (pullback g φ) b d y =
      ∑ ν, ∑ l, einsteinTensor g ν l (φ y) * jac φ y ν b * jac φ y l d := by
  simp only [einsteinTensor, ricci_pullback hg hφ hy, scalarCurvature_pullback hg hφ hy, pullback,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The vacuum Einstein equations are chart-independent**: if `g` solves them on `U`, the
same metric in the coordinates `φ` solves them on `V` (for any cosmological constant `Λ`). -/
theorem isVacuumSolution_pullback {Λ : ℝ} (hvac : IsVacuumSolution Λ g U)
    (hφ : IsChartChange φ V U) : IsVacuumSolution Λ (pullback g φ) V := by
  refine ⟨isCoordMetric_pullback hvac.1 hφ, fun y hy b d => ?_⟩
  rw [einsteinTensor_pullback hvac.1 hφ hy]
  simp only [pullback, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun ν _ => Finset.sum_eq_zero fun l _ => ?_
  have h := hvac.2 (φ y) (hφ.mapsTo hy) ν l
  have : einsteinTensor g ν l (φ y) * jac φ y ν b * jac φ y l d +
      Λ * (jac φ y ν b * g (φ y) ν l * jac φ y l d) =
      (einsteinTensor g ν l (φ y) + Λ * g (φ y) ν l) * jac φ y ν b * jac φ y l d := by ring
  rw [this, h]; ring

end Lightlike
