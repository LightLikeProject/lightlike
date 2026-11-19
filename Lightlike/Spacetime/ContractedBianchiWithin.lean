import Lightlike.Spacetime.ContractedBianchi
import Lightlike.Spacetime.RiemannSymmetryWithin
import Lightlike.Spacetime.ChartTensor
import Lightlike.Spacetime.Corners.ChartTensor
/-!
# The contracted Bianchi identity in coordinates within a set (GE11, corners)

The statements of `ContractedBianchi.lean` with derivatives within a set `S` and a coordinate metric `IsCoordMetricW S g U` on `U`
relatively open in `S` (`S = range I` for a manifold with corners): the connection and curvature matrices, the second Bianchi
identity for the matrix-valued form, the covariant derivative `covRW` of the Riemann tensor and its symmetries,
and `einstein_div_coordW`: `g^{στ} ∇_σ G_{τν} = 0` (`einstein_div_coordW`).

**Limits.** Coordinates on `ℝⁿ` only; the algebraic lemmas are those of `ContractedBianchi.lean`, which these reduce to for `S = univ`.
-/

open Matrix Filter Set
open scoped ContDiff Topology Matrix
noncomputable section
namespace Lightlike
variable {n : ℕ} {S : Set (Fin n → ℝ)} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The connection matrix `(A_l)^ρ_σ = Γ^ρ_{lσ}` at `y`. -/
def AmatW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => christoffelW S g ρ l σ y

/-- `(∂_a A_b)^ρ_σ` at `y`. -/
def dAmatW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (a b : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => pdW S a (christoffelW S g ρ b σ) y

/-- `(∂_a ∂_b A_c)^ρ_σ` at `y`. -/
def ddAmatW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (a b c : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => pdW S a (pdW S b (christoffelW S g ρ c σ)) y

/-- The curvature matrix `(R_{μν})^ρ_σ = R^ρ_{σμν}` at `y`. -/
def RmatW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => riemannW S g ρ σ μ ν y

/-- `(∂_l R_{μν})^ρ_σ` at `y`. -/
def dRmatW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => pdW S l (riemannW S g ρ σ μ ν) y

/-- The curvature matrix is the curvature of the connection matrices. -/
theorem Rmat_eqW (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) (y : Fin n → ℝ) :
    RmatW S g μ ν y = dAmatW S g μ ν y - dAmatW S g ν μ y + AmatW S g μ y * AmatW S g ν y - AmatW S g ν y * AmatW S g μ y := by
  ext ρ σ
  simp only [RmatW, dAmatW, AmatW, riemannW, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_sub_distrib]
  ring

section
variable (hg : IsCoordMetricW S g U) {y : Fin n → ℝ} (hy : y ∈ U)
include hg hy

/-- The Christoffel symbols of a coordinate metric are differentiable on its domain. -/
theorem differentiableAt_christoffelW (i j k : Fin n) :
    DifferentiableWithinAt ℝ (christoffelW S g i j k) S y :=
  differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_christoffel i j k) hy

/-- The partial derivatives of the Christoffel symbols are differentiable on the domain. -/
theorem differentiableAt_pd_christoffelW (a i j k : Fin n) :
    DifferentiableWithinAt ℝ (pdW S a (christoffelW S g i j k)) S y :=
  differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_pdW (hg.contDiffOn_christoffel i j k) a) hy

/-- Second derivatives of the connection commute. -/
theorem ddAmat_commW (a b c : Fin n) : ddAmatW S g a b c y = ddAmatW S g b a c y := by
  ext ρ σ
  exact hg.pdW_pdW_comm (hg.contDiffOn_christoffel ρ c σ) hy a b

/-- The derivative of the curvature matrix by the Leibniz rule. -/
theorem dRmat_eqW (l μ ν : Fin n) : dRmatW S g l μ ν y =
    ddAmatW S g l μ ν y - ddAmatW S g l ν μ y + dAmatW S g l μ y * AmatW S g ν y + AmatW S g μ y * dAmatW S g l ν y
      - dAmatW S g l ν y * AmatW S g μ y - AmatW S g ν y * dAmatW S g l μ y := by
  ext ρ σ
  have hd := differentiableAt_christoffelW hg hy
  have hdd := differentiableAt_pd_christoffelW hg hy
  have e : pdW S l (riemannW S g ρ σ μ ν) y = pdW S l (fun z => (pdW S μ (christoffelW S g ρ ν σ) z - pdW S ν (christoffelW S g ρ μ σ) z) +
      ∑ j, (christoffelW S g ρ μ j z * christoffelW S g j ν σ z - christoffelW S g ρ ν j z * christoffelW S g j μ σ z)) y := rfl
  simp only [dRmatW, ddAmatW, dAmatW, AmatW, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_apply, Finset.sum_sub_distrib]
  have hA : DifferentiableWithinAt ℝ (fun z => pdW S μ (christoffelW S g ρ ν σ) z - pdW S ν (christoffelW S g ρ μ σ) z) S y :=
    (hdd _ _ _ _).sub (hdd _ _ _ _)
  have hP : ∀ j, DifferentiableWithinAt ℝ (fun z => christoffelW S g ρ μ j z * christoffelW S g j ν σ z
      - christoffelW S g ρ ν j z * christoffelW S g j μ σ z) S y := fun j =>
    ((hd _ _ _).mul (hd _ _ _)).sub ((hd _ _ _).mul (hd _ _ _))
  have hB : DifferentiableWithinAt ℝ (fun z => ∑ j, (christoffelW S g ρ μ j z * christoffelW S g j ν σ z
      - christoffelW S g ρ ν j z * christoffelW S g j μ σ z)) S y := DifferentiableWithinAt.fun_sum fun j _ => hP j
  rw [e, pdW_add hg.uniqueDiff (hg.subset hy) hA hB, pdW_sub hg.uniqueDiff (hg.subset hy) (hdd _ _ _ _) (hdd _ _ _ _), pdW_sum hg.uniqueDiff (hg.subset hy) _ (fun j _ => hP j)]
  have hq : ∀ j, pdW S l (fun z => christoffelW S g ρ μ j z * christoffelW S g j ν σ z
      - christoffelW S g ρ ν j z * christoffelW S g j μ σ z) y =
      pdW S l (christoffelW S g ρ μ j) y * christoffelW S g j ν σ y + christoffelW S g ρ μ j y * pdW S l (christoffelW S g j ν σ) y
      - (pdW S l (christoffelW S g ρ ν j) y * christoffelW S g j μ σ y + christoffelW S g ρ ν j y * pdW S l (christoffelW S g j μ σ) y) := by
    intro j
    have m1 : DifferentiableWithinAt ℝ (fun z => christoffelW S g ρ μ j z * christoffelW S g j ν σ z) S y := (hd _ _ _).mul (hd _ _ _)
    have m2 : DifferentiableWithinAt ℝ (fun z => christoffelW S g ρ ν j z * christoffelW S g j μ σ z) S y := (hd _ _ _).mul (hd _ _ _)
    rw [pdW_sub hg.uniqueDiff (hg.subset hy) (f₁ := fun z => christoffelW S g ρ μ j z * christoffelW S g j ν σ z)
      (f₂ := fun z => christoffelW S g ρ ν j z * christoffelW S g j μ σ z) m1 m2,
      pdW_mul hg.uniqueDiff (hg.subset hy) (f₁ := christoffelW S g ρ μ j) (f₂ := christoffelW S g j ν σ) (hd _ _ _) (hd _ _ _),
      pdW_mul hg.uniqueDiff (hg.subset hy) (f₁ := christoffelW S g ρ ν j) (f₂ := christoffelW S g j μ σ) (hd _ _ _) (hd _ _ _)]
  simp only [hq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring
end

/-- The torsion-like correction of the covariant derivative of the curvature matrix. -/
def torsRW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k, christoffelW S g k l μ y • RmatW S g k ν y + ∑ k, christoffelW S g k l ν y • RmatW S g μ k y

/-- **The covariant derivative of the curvature in coordinates**:
`(∇_l R)^ρ_{σμν} = ∂_l R^ρ_{σμν} + Γ^ρ_{lk} R^k_{σμν} - Γ^k_{lσ} R^ρ_{kμν} - Γ^k_{lμ} R^ρ_{σkν} - Γ^k_{lν} R^ρ_{σμk}`,
as a matrix in `(ρ, σ)`. -/
def covRW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l μ ν : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  dRmatW S g l μ ν y + AmatW S g l y * RmatW S g μ ν y - RmatW S g μ ν y * AmatW S g l y - torsRW S g l μ ν y

/-- `R_{μν}` is antisymmetric in `μ, ν`. -/
theorem Rmat_antisymmW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (μ ν : Fin n) (y : Fin n → ℝ) :
    RmatW S g μ ν y = - RmatW S g ν μ y := by
  ext ρ σ
  simp only [RmatW, Matrix.of_apply, Matrix.neg_apply]
  exact riemannW_antisymm_last (S := S) g ρ σ μ ν y

section
variable (hg : IsCoordMetricW S g U) {y : Fin n → ℝ} (hy : y ∈ U)
include hg hy

/-- The Christoffel symbols are symmetric in the lower indices on the domain. -/
theorem christoffel_symm_atW (k i j : Fin n) : christoffelW S g k i j y = christoffelW S g k j i y :=
  (hg.eventuallyEq_christoffel_symm hy k i j).eq_of_nhdsWithin (hg.subset hy)

/-- The torsion corrections cancel in the cyclic sum. -/
theorem torsR_cycW (l μ ν : Fin n) : torsRW S g l μ ν y + torsRW S g μ ν l y + torsRW S g ν l μ y = 0 := by
  have hs := christoffel_symm_atW hg hy
  have ha := Rmat_antisymmW S g
  have e1 : ∑ k, christoffelW S g k l μ y • RmatW S g k ν y + ∑ k, christoffelW S g k μ l y • RmatW S g ν k y = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hs k μ l, ha ν k, smul_neg]; abel
  have e2 : ∑ k, christoffelW S g k l ν y • RmatW S g μ k y + ∑ k, christoffelW S g k ν l y • RmatW S g k μ y = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hs k ν l, ha k μ, smul_neg]; abel
  have e3 : ∑ k, christoffelW S g k μ ν y • RmatW S g k l y + ∑ k, christoffelW S g k ν μ y • RmatW S g l k y = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hs k ν μ, ha l k, smul_neg]; abel
  unfold torsRW
  set a1 := ∑ k, christoffelW S g k l μ y • RmatW S g k ν y
  set a2 := ∑ k, christoffelW S g k l ν y • RmatW S g μ k y
  set a3 := ∑ k, christoffelW S g k μ ν y • RmatW S g k l y
  set a4 := ∑ k, christoffelW S g k μ l y • RmatW S g ν k y
  set a5 := ∑ k, christoffelW S g k ν l y • RmatW S g k μ y
  set a6 := ∑ k, christoffelW S g k ν μ y • RmatW S g l k y
  rw [show a1 + a2 + (a3 + a4) + (a5 + a6) = (a1 + a4) + (a2 + a5) + (a3 + a6) by abel, e1, e2, e3]
  simp

/-- **The second Bianchi identity in coordinates**: `∇_l R_{μν} + ∇_μ R_{νl} + ∇_ν R_{lμ} = 0`. -/
theorem covR_cycW (l μ ν : Fin n) : covRW S g l μ ν y + covRW S g μ ν l y + covRW S g ν l μ y = 0 := by
  have hB := bianchiExpr_eq_zero (fun a => AmatW S g a y) (fun a b => dAmatW S g a b y)
    (fun a b c => ddAmatW S g a b c y) (fun a b c => ddAmat_commW hg hy a b c) l μ ν
  have hT := torsR_cycW hg hy l μ ν
  have key : covRW S g l μ ν y + covRW S g μ ν l y + covRW S g ν l μ y =
      bianchiExpr (fun a => AmatW S g a y) (fun a b => dAmatW S g a b y) (fun a b c => ddAmatW S g a b c y) l μ ν
      - (torsRW S g l μ ν y + torsRW S g μ ν l y + torsRW S g ν l μ y) := by
    unfold covRW bianchiExpr
    rw [dRmat_eqW hg hy, dRmat_eqW hg hy, dRmat_eqW hg hy, Rmat_eqW g μ ν y, Rmat_eqW g ν l y, Rmat_eqW g l μ y]
    abel
  rw [key, hB, hT]; simp

/-- `∇_l R_{μν}` is antisymmetric in `μ, ν`. -/
theorem covR_antisymmW (l μ ν : Fin n) : covRW S g l μ ν y = - covRW S g l ν μ y := by
  have hs := christoffel_symm_atW hg hy
  have ha := Rmat_antisymmW S g
  have e : torsRW S g l μ ν y = - torsRW S g l ν μ y := by
    unfold torsRW
    have h1 : ∑ k, christoffelW S g k l μ y • RmatW S g k ν y = - ∑ k, christoffelW S g k l μ y • RmatW S g ν k y := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [ha k ν y, smul_neg]
    have h2 : ∑ k, christoffelW S g k l ν y • RmatW S g μ k y = - ∑ k, christoffelW S g k l ν y • RmatW S g k μ y := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [ha μ k y, smul_neg]
    rw [h1, h2]; abel
  have e2 : RmatW S g μ ν y = - RmatW S g ν μ y := ha μ ν y
  have e3 : dRmatW S g l μ ν y = - dRmatW S g l ν μ y := by
    rw [dRmat_eqW hg hy, dRmat_eqW hg hy]; abel
  unfold covRW
  rw [e, e2, e3]
  noncomm_ring

/-- `g R_{μν} + R_{μν}ᵀ g = 0`: the curvature endomorphism is antisymmetric for `g`. -/
theorem metric_RmatW (μ ν : Fin n) {z : Fin n → ℝ} (hz : z ∈ U) :
    g z * RmatW S g μ ν z + (RmatW S g μ ν z)ᵀ * g z = 0 := by
  ext ρ σ
  have h := hg.riemannLower_antisymm_first hz ρ σ μ ν
  have hs := hg.symm z hz
  have e2 : ((RmatW S g μ ν z)ᵀ * g z) ρ σ = (g z * RmatW S g μ ν z) σ ρ := by
    conv_rhs => rw [← hs]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.transpose_apply, Matrix.of_apply, RmatW]
    rw [← hs]; simp [Matrix.transpose_apply]
    ring
  simp only [Matrix.add_apply, Matrix.zero_apply, e2]
  simp only [riemannLowerW, Matrix.mul_apply, RmatW, Matrix.of_apply] at h ⊢
  linarith

/-- `(∂_l g)` as a matrix at `y`. -/
def dGmatW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => pdW S l (fun z => g z a b) y

/-- **Metric compatibility in matrix form**: `∂_l g = A_lᵀ g + g A_l`. -/
theorem dGmat_eqW (l : Fin n) : dGmatW S g l y = (AmatW S g l y)ᵀ * g y + g y * AmatW S g l y := by
  ext ρ α
  simp only [dGmatW, AmatW, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [hg.pdW_eq_christoffelFirst hy l ρ α, ← hg.lower_christoffel hy ρ l α, ← hg.lower_christoffel hy α l ρ]
  have : ∑ k, christoffelW S g k l ρ y * g y k α = ∑ k, g y α k * christoffelW S g k l ρ y := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    have := congrFun (congrFun (hg.symm y hy) α) k
    simp only [Matrix.transpose_apply] at this
    rw [this]
  rw [this]; ring

/-- The matrix `∂_l R_{μν}` and `∂_l g` satisfy the differentiated antisymmetry
`∂g R + g ∂R + Rᵀ ∂g + ∂Rᵀ g = 0`. -/
theorem dmetric_RmatW (l μ ν : Fin n) :
    dGmatW S g l y * RmatW S g μ ν y + g y * dRmatW S g l μ ν y + (RmatW S g μ ν y)ᵀ * dGmatW S g l y
      + (dRmatW S g l μ ν y)ᵀ * g y = 0 := by
  ext ρ σ
  have hg' : ∀ a b, DifferentiableWithinAt ℝ (fun z => g z a b) S y := fun a b =>
    differentiableWithinAt_of_contDiffOn hg (hg.smooth a b) hy
  have hR : ∀ a b c d, DifferentiableWithinAt ℝ (riemannW S g a b c d) S y := fun a b c d =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_riemannW a b c d) hy
  have hid : (fun z => ∑ α, (g z ρ α * riemannW S g α σ μ ν z + riemannW S g α ρ μ ν z * g z α σ)) =ᶠ[𝓝[S] y]
      fun _ => (0 : ℝ) := by
    filter_upwards [hg.mem_nhdsWithin hy] with z hz
    have := congrFun (congrFun (metric_RmatW hg hz μ ν hz) ρ) σ
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, RmatW,
      Matrix.of_apply] at this
    rw [Finset.sum_add_distrib]; exact this
  have h0 := pdW_congr (hg.subset hy) hid l
  have hd : ∀ α, DifferentiableWithinAt ℝ (fun z => g z ρ α * riemannW S g α σ μ ν z + riemannW S g α ρ μ ν z * g z α σ) S y :=
    fun α => ((hg' _ _).mul (hR _ _ _ _)).add ((hR _ _ _ _).mul (hg' _ _))
  rw [pdW_sum hg.uniqueDiff (hg.subset hy) _ (fun α _ => hd α)] at h0
  have hx : ∀ α, pdW S l (fun z => g z ρ α * riemannW S g α σ μ ν z + riemannW S g α ρ μ ν z * g z α σ) y =
      pdW S l (fun z => g z ρ α) y * riemannW S g α σ μ ν y + g y ρ α * pdW S l (riemannW S g α σ μ ν) y
      + (pdW S l (riemannW S g α ρ μ ν) y * g y α σ + riemannW S g α ρ μ ν y * pdW S l (fun z => g z α σ) y) := fun α => by
    rw [pdW_add hg.uniqueDiff (hg.subset hy) (f₁ := fun z => g z ρ α * riemannW S g α σ μ ν z) (f₂ := fun z => riemannW S g α ρ μ ν z * g z α σ)
      ((hg' _ _).mul (hR _ _ _ _)) ((hR _ _ _ _).mul (hg' _ _)),
      pdW_mul hg.uniqueDiff (hg.subset hy) (f₁ := fun z => g z ρ α) (f₂ := riemannW S g α σ μ ν) (hg' _ _) (hR _ _ _ _),
      pdW_mul hg.uniqueDiff (hg.subset hy) (f₁ := riemannW S g α ρ μ ν) (f₂ := fun z => g z α σ) (hR _ _ _ _) (hg' _ _)]
  simp only [hx] at h0
  have hz0 : pdW S l (fun _ : Fin n → ℝ => (0 : ℝ)) y = 0 := by simp [pdW]
  rw [hz0] at h0
  simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, Matrix.transpose_apply, dGmatW, dRmatW, RmatW,
    Matrix.of_apply]
  rw [← h0]
  simp only [Finset.sum_add_distrib]
  ring

/-- The torsion corrections are antisymmetric for `g`. -/
theorem tors_metricW (l μ ν : Fin n) :
    g y * torsRW S g l μ ν y + (torsRW S g l μ ν y)ᵀ * g y = 0 := by
  have h : ∀ μ ν, g y * RmatW S g μ ν y + (RmatW S g μ ν y)ᵀ * g y = 0 := fun μ ν => metric_RmatW hg hy μ ν hy
  unfold torsRW
  simp only [Matrix.transpose_add, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e : ∀ (k : Fin n) (a b : Fin n) (c : ℝ), c • (g y * RmatW S g a b y) + c • ((RmatW S g a b y)ᵀ * g y) = 0 := by
    intro k a b c; rw [← smul_add, h]; simp
  have e1 : ∑ k, christoffelW S g k l μ y • (g y * RmatW S g k ν y) + ∑ k, christoffelW S g k l μ y • ((RmatW S g k ν y)ᵀ * g y) = 0 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun k _ => e k k ν _
  have e2 : ∑ k, christoffelW S g k l ν y • (g y * RmatW S g μ k y) + ∑ k, christoffelW S g k l ν y • ((RmatW S g μ k y)ᵀ * g y) = 0 := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun k _ => e k μ k _
  calc _ = (∑ k, christoffelW S g k l μ y • (g y * RmatW S g k ν y) + ∑ k, christoffelW S g k l μ y • ((RmatW S g k ν y)ᵀ * g y))
        + (∑ k, christoffelW S g k l ν y • (g y * RmatW S g μ k y) + ∑ k, christoffelW S g k l ν y • ((RmatW S g μ k y)ᵀ * g y)) := by abel
    _ = 0 := by rw [e1, e2]; simp

/-- **`∇_l R_{μν}` is antisymmetric for `g`**: `g (∇R) + (∇R)ᵀ g = 0`. -/
theorem covR_metricW (l μ ν : Fin n) :
    g y * covRW S g l μ ν y + (covRW S g l μ ν y)ᵀ * g y = 0 := by
  have hGs : (g y)ᵀ = g y := hg.symm y hy
  have h1 := metric_RmatW hg hy μ ν hy
  have h2 := dmetric_RmatW hg hy l μ ν
  rw [dGmat_eqW hg hy] at h2
  have h3 := tors_metricW hg hy l μ ν
  unfold covRW
  set G := g y
  set A := AmatW S g l y
  set R := RmatW S g μ ν y
  set dR := dRmatW S g l μ ν y
  set T := torsRW S g l μ ν y
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
def DRicW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l a b : Fin n) (y : Fin n → ℝ) : ℝ :=
  pdW S l (ricciW S g a b) y - ∑ k, christoffelW S g k l a y * ricciW S g k b y - ∑ k, christoffelW S g k l b y * ricciW S g a k y

/-- **The trace of `∇R` is `∇ Ric`.** -/
theorem ricQ_eqW (l a b : Fin n) : ricQ (fun ρ σ μ ν l => covRW S g l μ ν y ρ σ) a b l = DRicW S g l a b y := by
  have hR : ∀ a b c d, DifferentiableWithinAt ℝ (riemannW S g a b c d) S y := fun a b c d =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_riemannW a b c d) hy
  have hp : pdW S l (ricciW S g a b) y = ∑ ρ, pdW S l (riemannW S g ρ a ρ b) y := by
    have : ricciW S g a b = fun z => ∑ ρ, riemannW S g ρ a ρ b z := rfl
    rw [this, pdW_sum hg.uniqueDiff (hg.subset hy) _ (fun ρ _ => hR _ _ _ _)]
  unfold ricQ DRicW
  rw [hp]
  simp only [covRW, torsRW, dRmatW, AmatW, RmatW, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ricciW]
  have c : ∑ ρ, ∑ k, christoffelW S g ρ l k y * riemannW S g k b ρ a y =
      ∑ ρ, ∑ k, christoffelW S g k l ρ y * riemannW S g ρ b k a y := by
    rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul] 
  have e1 : ∑ x, ∑ j, christoffelW S g x l j y * riemannW S g j a x b y =
      ∑ x, ∑ c, christoffelW S g c l x y * riemannW S g x a c b y := Finset.sum_comm
  have e2 : ∑ x, ∑ j, riemannW S g x j x b y * christoffelW S g j l a y =
      ∑ x, ∑ i, christoffelW S g x l a y * riemannW S g i x i b y := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x, ∑ c, christoffelW S g c l b y * riemannW S g x a x c y =
      ∑ x, ∑ i, christoffelW S g x l b y * riemannW S g i a i x y := by
    rw [Finset.sum_comm]
  rw [e1, e2, e3]; ring

/-- **The contracted second Bianchi identity for the Ricci tensor in coordinates**:
`g^{στ} ∇_σ R_{τν} = ½ g^{στ} ∇_ν R_{στ}`. -/
theorem contracted_DRicW (ν : Fin n) :
    ∑ σ, ∑ τ, (g y)⁻¹ σ τ * DRicW S g σ τ ν y = (∑ σ, ∑ τ, (g y)⁻¹ σ τ * DRicW S g ν σ τ y) / 2 := by
  have hdet := hg.isUnit_det y hy
  have := contracted_bianchi_alg (fun a b => g y a b) (fun a b => (g y)⁻¹ a b)
    (fun a c => by
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul (g y) hdet) a) c
      simpa [Matrix.mul_apply, Matrix.one_apply] using h)
    (fun a b => hg.inv_symm hy a b)
    (fun ρ σ μ ν l => covRW S g l μ ν y ρ σ)
    (fun ρ σ μ ν l => by
      have h := congrFun (congrFun (covR_cycW hg hy l μ ν) ρ) σ
      simpa [Matrix.add_apply] using h)
    (fun ρ σ μ ν l => by
      have h := congrFun (congrFun (covR_antisymmW hg hy l μ ν) ρ) σ
      simpa using h)
    (fun ρ σ μ ν l => by
      have h := congrFun (congrFun (covR_metricW hg hy l μ ν) ρ) σ
      have hs := hg.symm y hy
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] at h
      rw [Finset.sum_add_distrib]
      have e : ∑ α, g y σ α * covRW S g l μ ν y α ρ = ∑ j, covRW S g l μ ν y j ρ * g y j σ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have := congrFun (congrFun hs σ) j
        simp only [Matrix.transpose_apply] at this
        rw [this]; ring
      rw [e]; exact h) ν
  simpa [ricQ_eqW hg hy] using this

/-- `(∂_l g⁻¹)` as a matrix at `y`. -/
def dNmatW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l : Fin n) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => pdW S l (fun z => (g z)⁻¹ a b) y

/-- **The derivative of the inverse metric**: `∂_l g⁻¹ = - g⁻¹ A_lᵀ - A_l g⁻¹`. -/
theorem dNmat_eqW (l : Fin n) : dNmatW S g l y = - ((g y)⁻¹ * (AmatW S g l y)ᵀ) - AmatW S g l y * (g y)⁻¹ := by
  have hdet := hg.isUnit_det y hy
  have hGN : g y * (g y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hNG : (g y)⁻¹ * g y = 1 := Matrix.nonsing_inv_mul _ hdet
  have hg' : ∀ a b, DifferentiableWithinAt ℝ (fun z => g z a b) S y := fun a b =>
    differentiableWithinAt_of_contDiffOn hg (hg.smooth a b) hy
  have hN' : ∀ a b, DifferentiableWithinAt ℝ (fun z => (g z)⁻¹ a b) S y := fun a b =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_inv a b) hy
  have h1 : dNmatW S g l y * g y + (g y)⁻¹ * dGmatW S g l y = 0 := by
    ext a b
    have hid : (fun z => ∑ c, (g z)⁻¹ a c * g z c b) =ᶠ[𝓝[S] y] fun _ => (if a = b then (1 : ℝ) else 0) := by
      filter_upwards [hg.mem_nhdsWithin hy] with z hz
      have h := congrFun (congrFun (Matrix.nonsing_inv_mul (g z) (hg.isUnit_det z hz)) a) b
      simpa [Matrix.mul_apply, Matrix.one_apply] using h
    have h0 := pdW_congr (hg.subset hy) hid l
    have hd : ∀ c, DifferentiableWithinAt ℝ (fun z => (g z)⁻¹ a c * g z c b) S y := fun c => (hN' _ _).mul (hg' _ _)
    rw [pdW_sum hg.uniqueDiff (hg.subset hy) _ (fun c _ => hd c)] at h0
    have hx : ∀ c, pdW S l (fun z => (g z)⁻¹ a c * g z c b) y =
        pdW S l (fun z => (g z)⁻¹ a c) y * g y c b + (g y)⁻¹ a c * pdW S l (fun z => g z c b) y := fun c =>
      pdW_mul hg.uniqueDiff (hg.subset hy) (f₁ := fun z => (g z)⁻¹ a c) (f₂ := fun z => g z c b) (hN' _ _) (hg' _ _) l
    simp only [hx] at h0
    have hz0 : pdW S l (fun _ : Fin n → ℝ => (if a = b then (1 : ℝ) else 0)) y = 0 := by simp [pdW]
    rw [hz0] at h0
    simp only [Matrix.add_apply, Matrix.zero_apply, Matrix.mul_apply, dNmatW, dGmatW, Matrix.of_apply]
    rw [← h0, Finset.sum_add_distrib]
  have h2 : dNmatW S g l y = - ((g y)⁻¹ * dGmatW S g l y * (g y)⁻¹) := by
    have : dNmatW S g l y = - ((g y)⁻¹ * dGmatW S g l y) * (g y)⁻¹ := by
      calc dNmatW S g l y = dNmatW S g l y * (g y * (g y)⁻¹) := by rw [hGN, Matrix.mul_one]
        _ = (dNmatW S g l y * g y) * (g y)⁻¹ := by rw [Matrix.mul_assoc]
        _ = - ((g y)⁻¹ * dGmatW S g l y) * (g y)⁻¹ := by rw [eq_neg_of_add_eq_zero_left h1]
    rw [this]; noncomm_ring
  rw [h2, dGmat_eqW hg hy]
  set G := g y
  set N := (g y)⁻¹
  set A := AmatW S g l y
  calc -(N * (Aᵀ * G + G * A) * N) = -(N * Aᵀ * (G * N)) - ((N * G) * A * N) := by noncomm_ring
    _ = _ := by rw [hGN, hNG]; noncomm_ring

/-- **The derivative of the scalar curvature**: `∂_l S = g^{ab} ∇_l R_{ab}`. -/
theorem pdW_scalarCurvatureW (l : Fin n) :
    pdW S l (scalarCurvatureW S g) y = ∑ a, ∑ b, (g y)⁻¹ a b * DRicW S g l a b y := by
  have hN' : ∀ a b, DifferentiableWithinAt ℝ (fun z => (g z)⁻¹ a b) S y := fun a b =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_inv a b) hy
  have hRc : ∀ a b, DifferentiableWithinAt ℝ (ricciW S g a b) S y := fun a b =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_ricciW a b) hy
  have hm : ∀ a b, DifferentiableWithinAt ℝ (fun z => (g z)⁻¹ a b * ricciW S g a b z) S y := fun a b => (hN' _ _).mul (hRc _ _)
  have hs : ∀ a, DifferentiableWithinAt ℝ (fun z => ∑ b, (g z)⁻¹ a b * ricciW S g a b z) S y := fun a =>
    DifferentiableWithinAt.fun_sum fun b _ => hm a b
  have e : scalarCurvatureW S g = fun z => ∑ a, ∑ b, (g z)⁻¹ a b * ricciW S g a b z := rfl
  rw [e, pdW_sum hg.uniqueDiff (hg.subset hy) _ (fun a _ => hs a)]
  have e2 : ∀ a, pdW S l (fun z => ∑ b, (g z)⁻¹ a b * ricciW S g a b z) y =
      ∑ b, (pdW S l (fun z => (g z)⁻¹ a b) y * ricciW S g a b y + (g y)⁻¹ a b * pdW S l (ricciW S g a b) y) := fun a => by
    rw [pdW_sum hg.uniqueDiff (hg.subset hy) _ (fun b _ => hm a b)]
    exact Finset.sum_congr rfl fun b _ =>
      pdW_mul hg.uniqueDiff (hg.subset hy) (f₁ := fun z => (g z)⁻¹ a b) (f₂ := ricciW S g a b) (hN' _ _) (hRc _ _) l
  simp only [e2, DRicW]
  have hdN : ∀ a b, pdW S l (fun z => (g z)⁻¹ a b) y =
      - ∑ c, (g y)⁻¹ a c * christoffelW S g b l c y - ∑ c, christoffelW S g a l c y * (g y)⁻¹ c b := by
    intro a b
    have := congrFun (congrFun (dNmat_eqW hg hy l) a) b
    simpa [dNmatW, Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply, AmatW, Matrix.transpose_apply] using this
  simp only [hdN, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, neg_mul, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_neg_distrib, mul_add]
  have e1 : ∑ x, ∑ x_1, ∑ i, (g y)⁻¹ x i * christoffelW S g x_1 l i y * ricciW S g x x_1 y =
      ∑ x, ∑ x_1, ∑ i, (g y)⁻¹ x x_1 * (christoffelW S g i l x_1 y * ricciW S g x i y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ x, ∑ x_1, ∑ i, christoffelW S g x l i y * (g y)⁻¹ i x_1 * ricciW S g x x_1 y =
      ∑ x, ∑ x_1, ∑ i, (g y)⁻¹ x x_1 * (christoffelW S g i l x y * ricciW S g i x_1 y) := by
    have s3 : ∀ F : Fin n → Fin n → Fin n → ℝ, ∑ x, ∑ x_1, ∑ i, F x x_1 i = ∑ i, ∑ x_1, ∑ x, F x x_1 i := by
      intro F
      rw [Finset.sum_comm]
      refine (Finset.sum_congr rfl fun x _ => ?_).trans (Finset.sum_comm)
      rw [Finset.sum_comm]
    rw [s3]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]; ring

/-- The covariant derivative of the Einstein tensor in coordinates. -/
def DGW (S : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (l a b : Fin n) (y : Fin n → ℝ) : ℝ :=
  pdW S l (einsteinTensorW S g a b) y - ∑ k, christoffelW S g k l a y * einsteinTensorW S g k b y
    - ∑ k, christoffelW S g k l b y * einsteinTensorW S g a k y

/-- `∇ G = ∇ Ric - ½ (∂S) g`, since `∇ g = 0`. -/
theorem DG_eqW (l a b : Fin n) :
    DGW S g l a b y = DRicW S g l a b y - 1 / 2 * pdW S l (scalarCurvatureW S g) y * g y a b := by
  have hg' : ∀ a b, DifferentiableWithinAt ℝ (fun z => g z a b) S y := fun a b =>
    differentiableWithinAt_of_contDiffOn hg (hg.smooth a b) hy
  have hRc : ∀ a b, DifferentiableWithinAt ℝ (ricciW S g a b) S y := fun a b =>
    differentiableWithinAt_of_contDiffOn hg (hg.contDiffOn_ricciW a b) hy
  have hS : DifferentiableWithinAt ℝ (scalarCurvatureW S g) S y :=
    differentiableWithinAt_of_contDiffOn hg hg.contDiffOn_scalarCurvatureW hy
  have hm : DifferentiableWithinAt ℝ (fun z => 1 / 2 * scalarCurvatureW S g z * g z a b) S y :=
    ((differentiableWithinAt_const _).mul hS).mul (hg' _ _)
  have e : einsteinTensorW S g a b = fun z => ricciW S g a b z - 1 / 2 * scalarCurvatureW S g z * g z a b := rfl
  have hpd : pdW S l (einsteinTensorW S g a b) y = pdW S l (ricciW S g a b) y -
      (1 / 2 * pdW S l (scalarCurvatureW S g) y * g y a b + 1 / 2 * scalarCurvatureW S g y * pdW S l (fun z => g z a b) y) := by
    rw [e, pdW_sub hg.uniqueDiff (hg.subset hy) (hRc _ _) hm]
    congr 1
    rw [pdW_mul hg.uniqueDiff (hg.subset hy) (f₁ := fun z => 1 / 2 * scalarCurvatureW S g z) (f₂ := fun z => g z a b)
      ((differentiableWithinAt_const _).mul hS) (hg' _ _),
      pdW_const_mul hg.uniqueDiff (1 / 2 : ℝ) (hg.subset hy) hS]
  have hdg := dGmat_eqW hg hy l
  have hga : pdW S l (fun z => g z a b) y = ∑ k, christoffelW S g k l a y * g y k b + ∑ k, g y a k * christoffelW S g k l b y := by
    have := congrFun (congrFun hdg a) b
    simpa [dGmatW, AmatW, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply] using this
  unfold DGW DRicW
  rw [hpd, hga]
  simp only [einsteinTensorW, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  have hs1 : ∑ x, christoffelW S g x l a y * (1 / 2 * scalarCurvatureW S g y * g y x b) =
      1 / 2 * scalarCurvatureW S g y * ∑ x, christoffelW S g x l a y * g y x b := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hs2 : ∑ x, christoffelW S g x l b y * (1 / 2 * scalarCurvatureW S g y * g y a x) =
      1 / 2 * scalarCurvatureW S g y * ∑ x, g y a x * christoffelW S g x l b y := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs1, hs2]; ring


/-- **The contracted Bianchi identity in coordinates**: `g^{στ} ∇_σ G_{τν} = 0`. -/
theorem einstein_div_coordW (ν : Fin n) :
    ∑ σ, ∑ τ, (g y)⁻¹ σ τ * DGW S g σ τ ν y = 0 := by
  have hdet := hg.isUnit_det y hy
  have hNG : (g y)⁻¹ * g y = 1 := Matrix.nonsing_inv_mul _ hdet
  have h1 := contracted_DRicW hg hy ν
  have h2 := pdW_scalarCurvatureW hg hy ν
  simp only [DG_eqW hg hy, mul_sub, Finset.sum_sub_distrib]
  have h3 : ∑ σ, ∑ τ, (g y)⁻¹ σ τ * (1 / 2 * pdW S σ (scalarCurvatureW S g) y * g y τ ν) =
      1 / 2 * pdW S ν (scalarCurvatureW S g) y := by
    have : ∀ σ, ∑ τ, (g y)⁻¹ σ τ * (1 / 2 * pdW S σ (scalarCurvatureW S g) y * g y τ ν) =
        1 / 2 * pdW S σ (scalarCurvatureW S g) y * (if σ = ν then 1 else 0) := fun σ => by
      have h := congrFun (congrFun hNG σ) ν
      simp only [Matrix.mul_apply, Matrix.one_apply] at h
      rw [← h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => by ring
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h3, h1, ← h2]; ring
end
end Lightlike
