import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.ChartTensor
/-!
# The contracted Bianchi identity in coordinates (step 2 and 3 of the divergence-free Einstein tensor)

For a coordinate metric `g` on an open set `U ⊆ ℝⁿ` (`IsCoordMetric g U`), at a point `y ∈ U`:

* `covR g l μ ν y` is the matrix `(∇_l R)^ρ_{σμν}` (`ρ` row, `σ` column), the covariant derivative of the coordinate
  Riemann tensor; it is cyclic in `(l, μ, ν)` (`covR_cyc`, the second Bianchi identity, a computation in a
  non-commutative ring: `bianchiExpr_eq_zero`), antisymmetric in `(μ, ν)` (`covR_antisymm`) and antisymmetric for
  `g` (`covR_metric`);
* `contracted_bianchi_alg` contracts these three properties twice (pure algebra on a five-index array);
* `DRic`, `DG` are the covariant derivatives of the Ricci and Einstein tensors; `ricQ_eq` (the trace of `∇R` is
  `∇Ric`), `pd_scalarCurvature` (`∂_l S = g^{ab} ∇_l R_{ab}`, with the derivative of the inverse metric `dNmat_eq`)
  and `DG_eq` (`∇G = ∇Ric - ½ ∂S g`) give `einstein_div_coord`: `g^{στ} ∇_σ G_{τν} = 0`.

**Limits.** Coordinates on `ℝⁿ` only; no manifold, no connection. Nothing about Lorentzian signature is used: it holds for every
coordinate metric. The statement for a connection on a manifold (`T-GE1-P8`) is obtained in `DivergenceFree.lean`.
-/

open Matrix Filter
open scoped ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

section Alg
open Finset

/-- The Ricci-type contraction `Σ_ρ Q ρ a ρ b l` of a five-index array. -/
def ricQ (Q : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) (a b l : Fin n) : ℝ := ∑ ρ, Q ρ a ρ b l

/-- **The contracted second Bianchi identity, as algebra.** -/
theorem contracted_bianchi_alg (g N : Fin n → Fin n → ℝ)
    (hNg : ∀ a c, ∑ b, N a b * g b c = if a = c then 1 else 0)
    (hNs : ∀ a b, N a b = N b a)
    (Q : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ)
    (hb : ∀ ρ σ μ ν l, Q ρ σ μ ν l + Q ρ σ ν l μ + Q ρ σ l μ ν = 0)
    (ha1 : ∀ ρ σ μ ν l, Q ρ σ μ ν l = - Q ρ σ ν μ l)
    (ha2 : ∀ ρ σ μ ν l, ∑ α, (g ρ α * Q α σ μ ν l + g σ α * Q α ρ μ ν l) = 0) (ν : Fin n) :
    ∑ σ, ∑ τ, N σ τ * ricQ Q τ ν σ = (∑ σ, ∑ τ, N σ τ * ricQ Q σ τ ν) / 2 := by
  set T := ∑ σ, ∑ τ, N σ τ * ricQ Q τ ν σ with hT
  set Sc := ∑ σ, ∑ τ, N σ τ * ricQ Q σ τ ν with hSc
  -- the divergence of Q
  have hD : ∀ σ μ, ∑ ρ, Q ρ σ μ ν ρ = ricQ Q σ ν μ - ricQ Q σ μ ν := by
    intro σ μ
    have h := sum_eq_zero fun ρ (_ : ρ ∈ univ) => hb ρ σ μ ν ρ
    simp only [sum_add_distrib] at h
    have h2 : ∑ ρ, Q ρ σ ν ρ μ = - ricQ Q σ ν μ := by
      unfold ricQ; rw [← sum_neg_distrib]; exact sum_congr rfl fun ρ _ => ha1 ρ σ ν ρ μ
    have h3 : ∑ ρ, Q ρ σ ρ μ ν = ricQ Q σ μ ν := rfl
    linarith
  -- lowering
  have hlow : ∀ ρ σ μ l, Q ρ σ μ ν l = - ∑ β, N ρ β * ∑ α, g σ α * Q α β μ ν l := by
    intro ρ σ μ l
    have e : ∀ β, ∑ α, g σ α * Q α β μ ν l = - ∑ α, g β α * Q α σ μ ν l := fun β => by
      have := ha2 β σ μ ν l
      simp only [sum_add_distrib] at this
      -- ha2 with roles: g β α Q α σ + g σ α Q α β = 0
      linarith
    simp only [e, mul_neg, sum_neg_distrib, neg_neg]
    simp only [mul_sum]
    rw [sum_comm]
    simp only [← mul_assoc, ← sum_mul]
    simp [hNg]
  have hX : ∑ σ, ∑ μ, N σ μ * ∑ ρ, Q ρ σ μ ν ρ = - T := by
    have : ∀ σ μ ρ, Q ρ σ μ ν ρ = - ∑ β, N ρ β * ∑ α, g σ α * Q α β μ ν ρ := fun σ μ ρ => hlow ρ σ μ ρ
    have key : ∀ μ α, ∑ σ, N σ μ * g σ α = if μ = α then 1 else 0 := fun μ α => by
      simp only [hNs _ μ]; exact hNg μ α
    have step : ∀ σ μ, N σ μ * ∑ ρ, Q ρ σ μ ν ρ =
        ∑ ρ, ∑ β, ∑ α, (- (N ρ β * Q α β μ ν ρ)) * (N σ μ * g σ α) := by
      intro σ μ
      have e : ∑ ρ, Q ρ σ μ ν ρ = ∑ ρ, - ∑ β, N ρ β * ∑ α, g σ α * Q α β μ ν ρ :=
        sum_congr rfl fun ρ _ => this σ μ ρ
      rw [e]
      simp only [mul_sum, sum_mul, mul_neg, neg_mul, sum_neg_distrib]
      refine congrArg Neg.neg (sum_congr rfl fun ρ _ => sum_congr rfl fun β _ => sum_congr rfl fun α _ => ?_)
      ring
    have e2 : ∑ σ, ∑ μ, N σ μ * ∑ ρ, Q ρ σ μ ν ρ =
        ∑ σ, ∑ μ, ∑ ρ, ∑ β, ∑ α, (- (N ρ β * Q α β μ ν ρ)) * (N σ μ * g σ α) :=
      sum_congr rfl fun σ _ => sum_congr rfl fun μ _ => step σ μ
    rw [e2]
    have swap : ∀ (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ),
        ∑ σ, ∑ μ, ∑ ρ, ∑ β, ∑ α, f σ μ ρ β α = ∑ μ, ∑ ρ, ∑ β, ∑ α, ∑ σ, f σ μ ρ β α := by
      intro f
      rw [sum_comm]
      refine sum_congr rfl fun μ _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun ρ _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun β _ => ?_
      rw [sum_comm]
    rw [swap]
    have : ∀ μ ρ β α, ∑ σ, (- (N ρ β * Q α β μ ν ρ)) * (N σ μ * g σ α) =
        - (N ρ β * Q α β μ ν ρ) * (if μ = α then 1 else 0) := fun μ ρ β α => by
      rw [← mul_sum]; congr 1; simp only [hNs _ μ]; exact hNg μ α
    simp only [this]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
    simp only [hT, ricQ, mul_sum]
    simp only [sum_ite_eq, mem_univ, ite_true, sum_neg_distrib]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun ρ _ => ?_
    rw [sum_comm]
  have hY : ∑ σ, ∑ μ, N σ μ * (ricQ Q σ ν μ - ricQ Q σ μ ν) = T - Sc := by
    simp only [mul_sub, sum_sub_distrib]
    congr 1
    rw [hT, sum_comm]
    exact sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => by rw [hNs]
  have : -T = T - Sc := by rw [← hX, ← hY]; simp only [hD]
  linarith
end Alg

/-- The connection matrix `(A_l)^ρ_σ = Γ^ρ_{lσ}` at `y`. -/
def Amat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => christoffel g ρ l σ y

/-- `(∂_a A_b)^ρ_σ` at `y`. -/
def dAmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => pd a (christoffel g ρ b σ) y

/-- `(∂_a ∂_b A_c)^ρ_σ` at `y`. -/
def ddAmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (a b c : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => pd a (pd b (christoffel g ρ c σ)) y

/-- The curvature matrix `(R_{μν})^ρ_σ = R^ρ_{σμν}` at `y`. -/
def Rmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => riemann g ρ σ μ ν y

/-- `(∂_l R_{μν})^ρ_σ` at `y`. -/
def dRmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => pd l (riemann g ρ σ μ ν) y

/-- The curvature matrix is the curvature of the connection matrices. -/
theorem Rmat_eq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) (y : Fin n → ℝ) :
    Rmat g μ ν y = dAmat g μ ν y - dAmat g ν μ y + Amat g μ y * Amat g ν y - Amat g ν y * Amat g μ y := by
  ext ρ σ
  simp only [Rmat, dAmat, Amat, riemann, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_sub_distrib]
  ring

section
variable (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
include hg hy

/-- The Christoffel symbols of a coordinate metric are differentiable on its domain. -/
theorem differentiableAt_christoffel (i j k : Fin n) :
    DifferentiableAt ℝ (christoffel g i j k) y :=
  differentiableAt_of_contDiffOn (hg.contDiffOn_christoffel i j k) hg.isOpen hy

/-- The partial derivatives of the Christoffel symbols are differentiable on the domain. -/
theorem differentiableAt_pd_christoffel (a i j k : Fin n) :
    DifferentiableAt ℝ (pd a (christoffel g i j k)) y :=
  differentiableAt_of_contDiffOn (contDiffOn_pd (hg.contDiffOn_christoffel i j k) hg.isOpen a) hg.isOpen hy

/-- Second derivatives of the connection commute. -/
theorem ddAmat_comm (a b c : Fin n) : ddAmat g a b c y = ddAmat g b a c y := by
  ext ρ σ
  exact pd_pd_comm (hg.contDiffOn_christoffel ρ c σ) hg.isOpen hy a b

/-- The derivative of the curvature matrix by the Leibniz rule. -/
theorem dRmat_eq (l μ ν : Fin n) : dRmat g l μ ν y =
    ddAmat g l μ ν y - ddAmat g l ν μ y + dAmat g l μ y * Amat g ν y + Amat g μ y * dAmat g l ν y
      - dAmat g l ν y * Amat g μ y - Amat g ν y * dAmat g l μ y := by
  ext ρ σ
  have hd := differentiableAt_christoffel hg hy
  have hdd := differentiableAt_pd_christoffel hg hy
  have e : pd l (riemann g ρ σ μ ν) y = pd l (fun z => (pd μ (christoffel g ρ ν σ) z - pd ν (christoffel g ρ μ σ) z) +
      ∑ j, (christoffel g ρ μ j z * christoffel g j ν σ z - christoffel g ρ ν j z * christoffel g j μ σ z)) y := rfl
  simp only [dRmat, ddAmat, dAmat, Amat, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_apply, Finset.sum_sub_distrib]
  have hA : DifferentiableAt ℝ (fun z => pd μ (christoffel g ρ ν σ) z - pd ν (christoffel g ρ μ σ) z) y :=
    (hdd _ _ _ _).sub (hdd _ _ _ _)
  have hP : ∀ j, DifferentiableAt ℝ (fun z => christoffel g ρ μ j z * christoffel g j ν σ z
      - christoffel g ρ ν j z * christoffel g j μ σ z) y := fun j =>
    ((hd _ _ _).mul (hd _ _ _)).sub ((hd _ _ _).mul (hd _ _ _))
  have hB : DifferentiableAt ℝ (fun z => ∑ j, (christoffel g ρ μ j z * christoffel g j ν σ z
      - christoffel g ρ ν j z * christoffel g j μ σ z)) y := DifferentiableAt.fun_sum fun j _ => hP j
  rw [e, pd_add hA hB, pd_sub (hdd _ _ _ _) (hdd _ _ _ _), pd_sum _ (fun j _ => hP j)]
  have hq : ∀ j, pd l (fun z => christoffel g ρ μ j z * christoffel g j ν σ z
      - christoffel g ρ ν j z * christoffel g j μ σ z) y =
      pd l (christoffel g ρ μ j) y * christoffel g j ν σ y + christoffel g ρ μ j y * pd l (christoffel g j ν σ) y
      - (pd l (christoffel g ρ ν j) y * christoffel g j μ σ y + christoffel g ρ ν j y * pd l (christoffel g j μ σ) y) := by
    intro j
    have m1 : DifferentiableAt ℝ (fun z => christoffel g ρ μ j z * christoffel g j ν σ z) y := (hd _ _ _).mul (hd _ _ _)
    have m2 : DifferentiableAt ℝ (fun z => christoffel g ρ ν j z * christoffel g j μ σ z) y := (hd _ _ _).mul (hd _ _ _)
    rw [pd_sub (f₁ := fun z => christoffel g ρ μ j z * christoffel g j ν σ z)
      (f₂ := fun z => christoffel g ρ ν j z * christoffel g j μ σ z) m1 m2,
      pd_mul (f₁ := christoffel g ρ μ j) (f₂ := christoffel g j ν σ) (hd _ _ _) (hd _ _ _),
      pd_mul (f₁ := christoffel g ρ ν j) (f₂ := christoffel g j μ σ) (hd _ _ _) (hd _ _ _)]
  simp only [hq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring
end

/-- Algebraic second Bianchi expression: the cyclic sum of `∂_l F_{μν} + [A_l, F_{μν}]`. -/
def bianchiExpr {R : Type*} [Ring R] {ι : Type*} (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R)
    (l μ ν : ι) : R :=
  (ddA l μ ν - ddA l ν μ + dA l μ * A ν + A μ * dA l ν - dA l ν * A μ - A ν * dA l μ
        + A l * (dA μ ν - dA ν μ + A μ * A ν - A ν * A μ) - (dA μ ν - dA ν μ + A μ * A ν - A ν * A μ) * A l)
    + (ddA μ ν l - ddA μ l ν + dA μ ν * A l + A ν * dA μ l - dA μ l * A ν - A l * dA μ ν
        + A μ * (dA ν l - dA l ν + A ν * A l - A l * A ν) - (dA ν l - dA l ν + A ν * A l - A l * A ν) * A μ)
    + (ddA ν l μ - ddA ν μ l + dA ν l * A μ + A l * dA ν μ - dA ν μ * A l - A μ * dA ν l
        + A ν * (dA l μ - dA μ l + A l * A μ - A μ * A l) - (dA l μ - dA μ l + A l * A μ - A μ * A l) * A ν)

/-- **The second Bianchi identity for a matrix-valued 1-form** (non-commutative algebra), given that second
derivatives commute. -/
theorem bianchiExpr_eq_zero {R : Type*} [Ring R] {ι : Type*} (A : ι → R) (dA : ι → ι → R) (ddA : ι → ι → ι → R)
    (hdd : ∀ a b c, ddA a b c = ddA b a c) (l μ ν : ι) : bianchiExpr A dA ddA l μ ν = 0 := by
  have h1 := hdd l μ ν
  have h2 := hdd μ ν l
  have h3 := hdd ν l μ
  unfold bianchiExpr
  rw [h1, h2, h3]
  noncomm_ring

/-- The torsion-like correction of the covariant derivative of the curvature matrix. -/
def torsR (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k, christoffel g k l μ y • Rmat g k ν y + ∑ k, christoffel g k l ν y • Rmat g μ k y

/-- **The covariant derivative of the curvature in coordinates**:
`(∇_l R)^ρ_{σμν} = ∂_l R^ρ_{σμν} + Γ^ρ_{lk} R^k_{σμν} - Γ^k_{lσ} R^ρ_{kμν} - Γ^k_{lμ} R^ρ_{σkν} - Γ^k_{lν} R^ρ_{σμk}`,
as a matrix in `(ρ, σ)`. -/
def covR (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  dRmat g l μ ν y + Amat g l y * Rmat g μ ν y - Rmat g μ ν y * Amat g l y - torsR g l μ ν y

/-- `R_{μν}` is antisymmetric in `μ, ν`. -/
theorem Rmat_antisymm (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) (y : Fin n → ℝ) :
    Rmat g μ ν y = - Rmat g ν μ y := by
  ext ρ σ
  simp only [Rmat, Matrix.of_apply, Matrix.neg_apply]
  exact riemann_antisymm_last g ρ σ μ ν y

section
variable (hg : IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
include hg hy

/-- The Christoffel symbols are symmetric in the lower indices on the domain. -/
theorem christoffel_symm_at (k i j : Fin n) : christoffel g k i j y = christoffel g k j i y :=
  (hg.eventuallyEq_christoffel_symm hy k i j).self_of_nhds

/-- The torsion corrections cancel in the cyclic sum. -/
theorem torsR_cyc (l μ ν : Fin n) : torsR g l μ ν y + torsR g μ ν l y + torsR g ν l μ y = 0 := by
  have hs := christoffel_symm_at hg hy
  have ha := Rmat_antisymm g
  have e1 : ∑ k, christoffel g k l μ y • Rmat g k ν y + ∑ k, christoffel g k μ l y • Rmat g ν k y = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hs k μ l, ha ν k, smul_neg]; abel
  have e2 : ∑ k, christoffel g k l ν y • Rmat g μ k y + ∑ k, christoffel g k ν l y • Rmat g k μ y = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hs k ν l, ha k μ, smul_neg]; abel
  have e3 : ∑ k, christoffel g k μ ν y • Rmat g k l y + ∑ k, christoffel g k ν μ y • Rmat g l k y = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hs k ν μ, ha l k, smul_neg]; abel
  unfold torsR
  set a1 := ∑ k, christoffel g k l μ y • Rmat g k ν y
  set a2 := ∑ k, christoffel g k l ν y • Rmat g μ k y
  set a3 := ∑ k, christoffel g k μ ν y • Rmat g k l y
  set a4 := ∑ k, christoffel g k μ l y • Rmat g ν k y
  set a5 := ∑ k, christoffel g k ν l y • Rmat g k μ y
  set a6 := ∑ k, christoffel g k ν μ y • Rmat g l k y
  rw [show a1 + a2 + (a3 + a4) + (a5 + a6) = (a1 + a4) + (a2 + a5) + (a3 + a6) by abel, e1, e2, e3]
  simp

/-- **The second Bianchi identity in coordinates**: `∇_l R_{μν} + ∇_μ R_{νl} + ∇_ν R_{lμ} = 0`. -/
theorem covR_cyc (l μ ν : Fin n) : covR g l μ ν y + covR g μ ν l y + covR g ν l μ y = 0 := by
  have hB := bianchiExpr_eq_zero (fun a => Amat g a y) (fun a b => dAmat g a b y)
    (fun a b c => ddAmat g a b c y) (fun a b c => ddAmat_comm hg hy a b c) l μ ν
  have hT := torsR_cyc hg hy l μ ν
  have key : covR g l μ ν y + covR g μ ν l y + covR g ν l μ y =
      bianchiExpr (fun a => Amat g a y) (fun a b => dAmat g a b y) (fun a b c => ddAmat g a b c y) l μ ν
      - (torsR g l μ ν y + torsR g μ ν l y + torsR g ν l μ y) := by
    unfold covR bianchiExpr
    rw [dRmat_eq hg hy, dRmat_eq hg hy, dRmat_eq hg hy, Rmat_eq g μ ν y, Rmat_eq g ν l y, Rmat_eq g l μ y]
    abel
  rw [key, hB, hT]; simp

/-- `∇_l R_{μν}` is antisymmetric in `μ, ν`. -/
theorem covR_antisymm (l μ ν : Fin n) : covR g l μ ν y = - covR g l ν μ y := by
  have hs := christoffel_symm_at hg hy
  have ha := Rmat_antisymm g
  have e : torsR g l μ ν y = - torsR g l ν μ y := by
    unfold torsR
    have h1 : ∑ k, christoffel g k l μ y • Rmat g k ν y = - ∑ k, christoffel g k l μ y • Rmat g ν k y := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [ha k ν y, smul_neg]
    have h2 : ∑ k, christoffel g k l ν y • Rmat g μ k y = - ∑ k, christoffel g k l ν y • Rmat g k μ y := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [ha μ k y, smul_neg]
    rw [h1, h2]; abel
  have e2 : Rmat g μ ν y = - Rmat g ν μ y := ha μ ν y
  have e3 : dRmat g l μ ν y = - dRmat g l ν μ y := by
    rw [dRmat_eq hg hy, dRmat_eq hg hy]; abel
  unfold covR
  rw [e, e2, e3]
  noncomm_ring

/-- `g R_{μν} + R_{μν}ᵀ g = 0`: the curvature endomorphism is antisymmetric for `g`. -/
theorem metric_Rmat (μ ν : Fin n) {z : Fin n → ℝ} (hz : z ∈ U) :
    g z * Rmat g μ ν z + (Rmat g μ ν z)ᵀ * g z = 0 := by
  ext ρ σ
  have h := hg.riemannLower_antisymm_first hz ρ σ μ ν
  have hs := hg.symm z hz
  have e2 : ((Rmat g μ ν z)ᵀ * g z) ρ σ = (g z * Rmat g μ ν z) σ ρ := by
    conv_rhs => rw [← hs]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.transpose_apply, Matrix.of_apply, Rmat]
    rw [← hs]; simp [Matrix.transpose_apply]
    ring
  simp only [Matrix.add_apply, Matrix.zero_apply, e2]
  simp only [riemannLower, Matrix.mul_apply, Rmat, Matrix.of_apply] at h ⊢
  linarith

/-- `(∂_l g)` as a matrix at `y`. -/
def dGmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => pd l (fun z => g z a b) y

/-- **Metric compatibility in matrix form**: `∂_l g = A_lᵀ g + g A_l`. -/
theorem dGmat_eq (l : Fin n) : dGmat g l y = (Amat g l y)ᵀ * g y + g y * Amat g l y := by
  ext ρ α
  simp only [dGmat, Amat, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hg.pd_eq_christoffelFirst hy l ρ α, ← hg.lower_christoffel hy ρ l α, ← hg.lower_christoffel hy α l ρ]
  have : ∑ k, christoffel g k l ρ y * g y k α = ∑ k, g y α k * christoffel g k l ρ y := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    have := congrFun (congrFun (hg.symm y hy) α) k
    simp only [Matrix.transpose_apply] at this
    rw [this]
  rw [this]; ring

/-- The matrix `∂_l R_{μν}` and `∂_l g` satisfy the differentiated antisymmetry
`∂g R + g ∂R + Rᵀ ∂g + ∂Rᵀ g = 0`. -/
theorem dmetric_Rmat (l μ ν : Fin n) :
    dGmat g l y * Rmat g μ ν y + g y * dRmat g l μ ν y + (Rmat g μ ν y)ᵀ * dGmat g l y
      + (dRmat g l μ ν y)ᵀ * g y = 0 := by
  ext ρ σ
  have hg' : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hy
  have hR : ∀ a b c d, DifferentiableAt ℝ (riemann g a b c d) y := fun a b c d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_riemann a b c d) hg.isOpen hy
  have hid : (fun z => ∑ α, (g z ρ α * riemann g α σ μ ν z + riemann g α ρ μ ν z * g z α σ)) =ᶠ[nhds y]
      fun _ => (0 : ℝ) := by
    filter_upwards [hg.isOpen.mem_nhds hy] with z hz
    have := congrFun (congrFun (metric_Rmat hg hz μ ν hz) ρ) σ
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, Rmat,
      Matrix.of_apply] at this
    rw [Finset.sum_add_distrib]; exact this
  have h0 := pd_congr hid l
  have hd : ∀ α, DifferentiableAt ℝ (fun z => g z ρ α * riemann g α σ μ ν z + riemann g α ρ μ ν z * g z α σ) y :=
    fun α => ((hg' _ _).mul (hR _ _ _ _)).add ((hR _ _ _ _).mul (hg' _ _))
  rw [pd_sum _ (fun α _ => hd α)] at h0
  have hx : ∀ α, pd l (fun z => g z ρ α * riemann g α σ μ ν z + riemann g α ρ μ ν z * g z α σ) y =
      pd l (fun z => g z ρ α) y * riemann g α σ μ ν y + g y ρ α * pd l (riemann g α σ μ ν) y
      + (pd l (riemann g α ρ μ ν) y * g y α σ + riemann g α ρ μ ν y * pd l (fun z => g z α σ) y) := fun α => by
    rw [pd_add (f₁ := fun z => g z ρ α * riemann g α σ μ ν z) (f₂ := fun z => riemann g α ρ μ ν z * g z α σ)
      ((hg' _ _).mul (hR _ _ _ _)) ((hR _ _ _ _).mul (hg' _ _)),
      pd_mul (f₁ := fun z => g z ρ α) (f₂ := riemann g α σ μ ν) (hg' _ _) (hR _ _ _ _),
      pd_mul (f₁ := riemann g α ρ μ ν) (f₂ := fun z => g z α σ) (hR _ _ _ _) (hg' _ _)]
  simp only [hx] at h0
  have hz0 : pd l (fun _ : Fin n → ℝ => (0 : ℝ)) y = 0 := by simp [pd]
  rw [hz0] at h0
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, dGmat, dRmat, Rmat,
    Matrix.of_apply]
  rw [← h0]
  simp only [Finset.sum_add_distrib]
  ring

/-- The torsion corrections are antisymmetric for `g`. -/
theorem tors_metric (l μ ν : Fin n) :
    g y * torsR g l μ ν y + (torsR g l μ ν y)ᵀ * g y = 0 := by
  have h : ∀ μ ν, g y * Rmat g μ ν y + (Rmat g μ ν y)ᵀ * g y = 0 := fun μ ν => metric_Rmat hg hy μ ν hy
  unfold torsR
  simp only [Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e : ∀ (k : Fin n) (a b : Fin n) (c : ℝ), c • (g y * Rmat g a b y) + c • ((Rmat g a b y)ᵀ * g y) = 0 := by
    intro k a b c; rw [← smul_add, h]; simp
  have e1 : ∑ k, christoffel g k l μ y • (g y * Rmat g k ν y) + ∑ k, christoffel g k l μ y • ((Rmat g k ν y)ᵀ * g y) = 0 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun k _ => e k k ν _
  have e2 : ∑ k, christoffel g k l ν y • (g y * Rmat g μ k y) + ∑ k, christoffel g k l ν y • ((Rmat g μ k y)ᵀ * g y) = 0 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun k _ => e k μ k _
  calc _ = (∑ k, christoffel g k l μ y • (g y * Rmat g k ν y) + ∑ k, christoffel g k l μ y • ((Rmat g k ν y)ᵀ * g y))
        + (∑ k, christoffel g k l ν y • (g y * Rmat g μ k y) + ∑ k, christoffel g k l ν y • ((Rmat g μ k y)ᵀ * g y)) := by abel
    _ = 0 := by rw [e1, e2]; simp

/-- **`∇_l R_{μν}` is antisymmetric for `g`**: `g (∇R) + (∇R)ᵀ g = 0`. -/
theorem covR_metric (l μ ν : Fin n) :
    g y * covR g l μ ν y + (covR g l μ ν y)ᵀ * g y = 0 := by
  have hGs : (g y)ᵀ = g y := hg.symm y hy
  have h1 := metric_Rmat hg hy μ ν hy
  have h2 := dmetric_Rmat hg hy l μ ν
  rw [dGmat_eq hg hy] at h2
  have h3 := tors_metric hg hy l μ ν
  unfold covR
  set G := g y
  set A := Amat g l y
  set R := Rmat g μ ν y
  set dR := dRmat g l μ ν y
  set T := torsR g l μ ν y
  have hQT : (dR + A * R - R * A - T)ᵀ = dRᵀ + Rᵀ * Aᵀ - Aᵀ * Rᵀ - Tᵀ := by
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul]
  have key : G * (dR + A * R - R * A - T) + (dR + A * R - R * A - T)ᵀ * G =
      ((Aᵀ * G + G * A) * R + G * dR + Rᵀ * (Aᵀ * G + G * A) + dRᵀ * G)
        - (G * R + Rᵀ * G) * A - Aᵀ * (Rᵀ * G + G * R) - (G * T + Tᵀ * G) := by
    rw [hQT]; noncomm_ring
  have h1' : Rᵀ * G + G * R = 0 := by rw [add_comm]; exact h1
  rw [key, h1, h1', h3, h2]; simp

/-- The covariant derivative of the Ricci tensor in coordinates:
`(∇_l Ric)_{ab} = ∂_l R_{ab} - Γ^k_{la} R_{kb} - Γ^k_{lb} R_{ak}`. -/
def DRic (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l a b : Fin n) (y : Fin n → ℝ) : ℝ :=
  pd l (ricci g a b) y - ∑ k, christoffel g k l a y * ricci g k b y - ∑ k, christoffel g k l b y * ricci g a k y

/-- **The trace of `∇R` is `∇ Ric`.** -/
theorem ricQ_eq (l a b : Fin n) : ricQ (fun ρ σ μ ν l => covR g l μ ν y ρ σ) a b l = DRic g l a b y := by
  have hR : ∀ a b c d, DifferentiableAt ℝ (riemann g a b c d) y := fun a b c d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_riemann a b c d) hg.isOpen hy
  have hp : pd l (ricci g a b) y = ∑ ρ, pd l (riemann g ρ a ρ b) y := by
    have : ricci g a b = fun z => ∑ ρ, riemann g ρ a ρ b z := rfl
    rw [this, pd_sum _ (fun ρ _ => hR _ _ _ _)]
  unfold ricQ DRic
  rw [hp]
  simp only [covR, torsR, dRmat, Amat, Rmat, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ricci]
  have c : ∑ ρ, ∑ k, christoffel g ρ l k y * riemann g k b ρ a y =
      ∑ ρ, ∑ k, christoffel g k l ρ y * riemann g ρ b k a y := by
    rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul] 
  have e1 : ∑ x, ∑ j, christoffel g x l j y * riemann g j a x b y =
      ∑ x, ∑ c, christoffel g c l x y * riemann g x a c b y := Finset.sum_comm
  have e2 : ∑ x, ∑ j, riemann g x j x b y * christoffel g j l a y =
      ∑ x, ∑ i, christoffel g x l a y * riemann g i x i b y := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x, ∑ c, christoffel g c l b y * riemann g x a x c y =
      ∑ x, ∑ i, christoffel g x l b y * riemann g i a i x y := by
    rw [Finset.sum_comm]
  rw [e1, e2, e3]; ring

/-- **The contracted second Bianchi identity for the Ricci tensor in coordinates**:
`g^{στ} ∇_σ R_{τν} = ½ g^{στ} ∇_ν R_{στ}`. -/
theorem contracted_DRic (ν : Fin n) :
    ∑ σ, ∑ τ, (g y)⁻¹ σ τ * DRic g σ τ ν y = (∑ σ, ∑ τ, (g y)⁻¹ σ τ * DRic g ν σ τ y) / 2 := by
  have hdet := hg.isUnit_det y hy
  have := contracted_bianchi_alg (fun a b => g y a b) (fun a b => (g y)⁻¹ a b)
    (fun a c => by
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul (g y) hdet) a) c
      simpa [Matrix.mul_apply, Matrix.one_apply] using h)
    (fun a b => hg.inv_symm hy a b)
    (fun ρ σ μ ν l => covR g l μ ν y ρ σ)
    (fun ρ σ μ ν l => by
      have h := congrFun (congrFun (covR_cyc hg hy l μ ν) ρ) σ
      simpa [Matrix.add_apply] using h)
    (fun ρ σ μ ν l => by
      have h := congrFun (congrFun (covR_antisymm hg hy l μ ν) ρ) σ
      simpa using h)
    (fun ρ σ μ ν l => by
      have h := congrFun (congrFun (covR_metric hg hy l μ ν) ρ) σ
      have hs := hg.symm y hy
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h
      rw [Finset.sum_add_distrib]
      have e : ∑ α, g y σ α * covR g l μ ν y α ρ = ∑ j, covR g l μ ν y j ρ * g y j σ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have := congrFun (congrFun hs σ) j
        simp only [Matrix.transpose_apply] at this
        rw [this]; ring
      rw [e]; exact h) ν
  simpa [ricQ_eq hg hy] using this

/-- `(∂_l g⁻¹)` as a matrix at `y`. -/
def dNmat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => pd l (fun z => (g z)⁻¹ a b) y

/-- **The derivative of the inverse metric**: `∂_l g⁻¹ = - g⁻¹ A_lᵀ - A_l g⁻¹`. -/
theorem dNmat_eq (l : Fin n) : dNmat g l y = - ((g y)⁻¹ * (Amat g l y)ᵀ) - Amat g l y * (g y)⁻¹ := by
  have hdet := hg.isUnit_det y hy
  have hGN : g y * (g y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hNG : (g y)⁻¹ * g y = 1 := Matrix.nonsing_inv_mul _ hdet
  have hg' : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hy
  have hN' : ∀ a b, DifferentiableAt ℝ (fun z => (g z)⁻¹ a b) y := fun a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a b) hg.isOpen hy
  have h1 : dNmat g l y * g y + (g y)⁻¹ * dGmat g l y = 0 := by
    ext a b
    have hid : (fun z => ∑ c, (g z)⁻¹ a c * g z c b) =ᶠ[nhds y] fun _ => (if a = b then (1 : ℝ) else 0) := by
      filter_upwards [hg.isOpen.mem_nhds hy] with z hz
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul (g z) (hg.isUnit_det z hz)) a) b
      simpa [Matrix.mul_apply, Matrix.one_apply] using h
    have h0 := pd_congr hid l
    have hd : ∀ c, DifferentiableAt ℝ (fun z => (g z)⁻¹ a c * g z c b) y := fun c => (hN' _ _).mul (hg' _ _)
    rw [pd_sum _ (fun c _ => hd c)] at h0
    have hx : ∀ c, pd l (fun z => (g z)⁻¹ a c * g z c b) y =
        pd l (fun z => (g z)⁻¹ a c) y * g y c b + (g y)⁻¹ a c * pd l (fun z => g z c b) y := fun c =>
      pd_mul (f₁ := fun z => (g z)⁻¹ a c) (f₂ := fun z => g z c b) (hN' _ _) (hg' _ _) l
    simp only [hx] at h0
    have hz0 : pd l (fun _ : Fin n → ℝ => (if a = b then (1 : ℝ) else 0)) y = 0 := by simp [pd]
    rw [hz0] at h0
    simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, dNmat, dGmat, Matrix.of_apply]
    rw [← h0, Finset.sum_add_distrib]
  have h2 : dNmat g l y = - ((g y)⁻¹ * dGmat g l y * (g y)⁻¹) := by
    have : dNmat g l y = - ((g y)⁻¹ * dGmat g l y) * (g y)⁻¹ := by
      calc dNmat g l y = dNmat g l y * (g y * (g y)⁻¹) := by rw [hGN, Matrix.mul_one]
        _ = (dNmat g l y * g y) * (g y)⁻¹ := by rw [Matrix.mul_assoc]
        _ = - ((g y)⁻¹ * dGmat g l y) * (g y)⁻¹ := by rw [eq_neg_of_add_eq_zero_left h1]
    rw [this]; noncomm_ring
  rw [h2, dGmat_eq hg hy]
  set G := g y
  set N := (g y)⁻¹
  set A := Amat g l y
  calc -(N * (Aᵀ * G + G * A) * N) = -(N * Aᵀ * (G * N)) - ((N * G) * A * N) := by noncomm_ring
    _ = _ := by rw [hGN, hNG]; noncomm_ring

/-- **The derivative of the scalar curvature**: `∂_l S = g^{ab} ∇_l R_{ab}`. -/
theorem pd_scalarCurvature (l : Fin n) :
    pd l (scalarCurvature g) y = ∑ a, ∑ b, (g y)⁻¹ a b * DRic g l a b y := by
  have hN' : ∀ a b, DifferentiableAt ℝ (fun z => (g z)⁻¹ a b) y := fun a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a b) hg.isOpen hy
  have hRc : ∀ a b, DifferentiableAt ℝ (ricci g a b) y := fun a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_ricci a b) hg.isOpen hy
  have hm : ∀ a b, DifferentiableAt ℝ (fun z => (g z)⁻¹ a b * ricci g a b z) y := fun a b => (hN' _ _).mul (hRc _ _)
  have hs : ∀ a, DifferentiableAt ℝ (fun z => ∑ b, (g z)⁻¹ a b * ricci g a b z) y := fun a =>
    DifferentiableAt.fun_sum fun b _ => hm a b
  have e : scalarCurvature g = fun z => ∑ a, ∑ b, (g z)⁻¹ a b * ricci g a b z := rfl
  rw [e, pd_sum _ (fun a _ => hs a)]
  have e2 : ∀ a, pd l (fun z => ∑ b, (g z)⁻¹ a b * ricci g a b z) y =
      ∑ b, (pd l (fun z => (g z)⁻¹ a b) y * ricci g a b y + (g y)⁻¹ a b * pd l (ricci g a b) y) := fun a => by
    rw [pd_sum _ (fun b _ => hm a b)]
    exact Finset.sum_congr rfl fun b _ =>
      pd_mul (f₁ := fun z => (g z)⁻¹ a b) (f₂ := ricci g a b) (hN' _ _) (hRc _ _) l
  simp only [e2, DRic]
  have hdN : ∀ a b, pd l (fun z => (g z)⁻¹ a b) y =
      - ∑ c, (g y)⁻¹ a c * christoffel g b l c y - ∑ c, christoffel g a l c y * (g y)⁻¹ c b := by
    intro a b
    have := congrFun (congrFun (dNmat_eq hg hy l) a) b
    simpa [dNmat, Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply, Amat, Matrix.transpose_apply] using this
  simp only [hdN, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, neg_mul, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_neg_distrib, mul_add]
  have e1 : ∑ x, ∑ x_1, ∑ i, (g y)⁻¹ x i * christoffel g x_1 l i y * ricci g x x_1 y =
      ∑ x, ∑ x_1, ∑ i, (g y)⁻¹ x x_1 * (christoffel g i l x_1 y * ricci g x i y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x, ∑ x_1, ∑ i, christoffel g x l i y * (g y)⁻¹ i x_1 * ricci g x x_1 y =
      ∑ x, ∑ x_1, ∑ i, (g y)⁻¹ x x_1 * (christoffel g i l x y * ricci g i x_1 y) := by
    have s3 : ∀ F : Fin n → Fin n → Fin n → ℝ, ∑ x, ∑ x_1, ∑ i, F x x_1 i = ∑ i, ∑ x_1, ∑ x, F x x_1 i := by
      intro F
      rw [Finset.sum_comm]
      refine (Finset.sum_congr rfl fun x _ => ?_).trans (Finset.sum_comm)
      rw [Finset.sum_comm]
    rw [s3]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]; ring

/-- The covariant derivative of the Einstein tensor in coordinates. -/
def DG (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l a b : Fin n) (y : Fin n → ℝ) : ℝ :=
  pd l (einsteinTensor g a b) y - ∑ k, christoffel g k l a y * einsteinTensor g k b y
    - ∑ k, christoffel g k l b y * einsteinTensor g a k y

/-- `∇ G = ∇ Ric - ½ (∂S) g`, since `∇ g = 0`. -/
theorem DG_eq (l a b : Fin n) :
    DG g l a b y = DRic g l a b y - 1 / 2 * pd l (scalarCurvature g) y * g y a b := by
  have hg' : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hy
  have hRc : ∀ a b, DifferentiableAt ℝ (ricci g a b) y := fun a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_ricci a b) hg.isOpen hy
  have hS : DifferentiableAt ℝ (scalarCurvature g) y :=
    differentiableAt_of_contDiffOn hg.contDiffOn_scalarCurvature hg.isOpen hy
  have hm : DifferentiableAt ℝ (fun z => 1 / 2 * scalarCurvature g z * g z a b) y :=
    ((differentiableAt_const _).mul hS).mul (hg' _ _)
  have e : einsteinTensor g a b = fun z => ricci g a b z - 1 / 2 * scalarCurvature g z * g z a b := rfl
  have hpd : pd l (einsteinTensor g a b) y = pd l (ricci g a b) y -
      (1 / 2 * pd l (scalarCurvature g) y * g y a b + 1 / 2 * scalarCurvature g y * pd l (fun z => g z a b) y) := by
    rw [e, pd_sub (hRc _ _) hm]
    congr 1
    rw [pd_mul (f₁ := fun z => 1 / 2 * scalarCurvature g z) (f₂ := fun z => g z a b)
      ((differentiableAt_const _).mul hS) (hg' _ _),
      pd_const_mul (1 / 2 : ℝ) hS]
  have hdg := dGmat_eq hg hy l
  have hga : pd l (fun z => g z a b) y = ∑ k, christoffel g k l a y * g y k b + ∑ k, g y a k * christoffel g k l b y := by
    have := congrFun (congrFun hdg a) b
    simpa [dGmat, Amat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] using this
  unfold DG DRic
  rw [hpd, hga]
  simp only [einsteinTensor, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  have hs1 : ∑ x, christoffel g x l a y * (1 / 2 * scalarCurvature g y * g y x b) =
      1 / 2 * scalarCurvature g y * ∑ x, christoffel g x l a y * g y x b := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hs2 : ∑ x, christoffel g x l b y * (1 / 2 * scalarCurvature g y * g y a x) =
      1 / 2 * scalarCurvature g y * ∑ x, g y a x * christoffel g x l b y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs1, hs2]; ring


/-- **The contracted Bianchi identity in coordinates**: `g^{στ} ∇_σ G_{τν} = 0`. -/
theorem einstein_div_coord (ν : Fin n) :
    ∑ σ, ∑ τ, (g y)⁻¹ σ τ * DG g σ τ ν y = 0 := by
  have hdet := hg.isUnit_det y hy
  have hNG : (g y)⁻¹ * g y = 1 := Matrix.nonsing_inv_mul _ hdet
  have h1 := contracted_DRic hg hy ν
  have h2 := pd_scalarCurvature hg hy ν
  simp only [DG_eq hg hy, mul_sub, Finset.sum_sub_distrib]
  have h3 : ∑ σ, ∑ τ, (g y)⁻¹ σ τ * (1 / 2 * pd σ (scalarCurvature g) y * g y τ ν) =
      1 / 2 * pd ν (scalarCurvature g) y := by
    have : ∀ σ, ∑ τ, (g y)⁻¹ σ τ * (1 / 2 * pd σ (scalarCurvature g) y * g y τ ν) =
        1 / 2 * pd σ (scalarCurvature g) y * (if σ = ν then 1 else 0) := fun σ => by
      have h := congrFun (congrFun hNG σ) ν
      simp only [Matrix.mul_apply, Matrix.one_apply] at h
      rw [← h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h3, h1, ← h2]; ring
end
end Lightlike
