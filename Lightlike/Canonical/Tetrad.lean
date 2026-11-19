import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.RicciContinuous

/-!
# The spin connection of a tetrad and its curvature

On a chart `ℝⁿ` (`n = 4` for spacetime), for a frame field (tetrad) `e` (entries `e^I_μ`, row `I` internal, column `μ`
spacetime) and a metric `g` with Christoffel symbols `Lightlike.christoffel g`:

* `chrMat g y μ`: the matrix `(Γ_μ)^ρ_σ = Γ^ρ_{μσ}`;
* `tetradConn e g y μ = e (∂_μ e⁻¹ + Γ_μ e⁻¹)`: the **spin connection of the tetrad**, `ω_μ^I_J = e^I_ν ∇_μ e^ν_J`
  (Holst, arXiv:gr-qc/9511026, eq. (3), p. 2, `A_α^{IJ} = e^{βI} ∇_α e_β^J`; Ashtekar–Lewandowski, arXiv:gr-qc/0404018,
  the compatibility condition (2.3)), the gauge transform of the Levi-Civita connection by the frame;
* `gaugeCurv ω y μ ν = ∂_μ ω_ν − ∂_ν ω_μ + ω_μ ω_ν − ω_ν ω_μ`: the **curvature of a matrix-valued connection**
  `F = dω + ω ∧ ω` in components (Holst's `F_αβ^{IJ}`, Ashtekar–Lewandowski's `Ω^{IJ}`).

`gaugeCurv_tetradConn`: **the curvature of the tetrad connection is the Riemann tensor in the frame**,
`F_μν = e R_μν e⁻¹` with `(R_μν)^ρ_σ = R^ρ_{σμν}` the `Lightlike.riemann` of `g` (`riemMat_eq_gaugeCurv`), for a smooth
invertible frame and a coordinate metric (gauge covariance of the curvature).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The entrywise partial derivative `∂_μ M` of a matrix-valued function. -/
def pdMat (μ : Fin n) (M : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Lightlike.pd μ (fun y => M y i j) x

/-- The Christoffel matrix `(Γ_μ)^ρ_σ = Γ^ρ_{μσ}` of a metric. -/
def chrMat (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (μ : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun ρ σ => Lightlike.christoffel g ρ μ σ y

/-- **The curvature of a matrix-valued connection** `F_μν = ∂_μ ω_ν − ∂_ν ω_μ + ω_μ ω_ν − ω_ν ω_μ`. -/
def gaugeCurv (om : (Fin n → ℝ) → Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (μ ν : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  pdMat μ (fun y => om y ν) x - pdMat ν (fun y => om y μ) x + om x μ * om x ν - om x ν * om x μ

/-- **The spin connection of a tetrad** `ω_μ = e (∂_μ e⁻¹ + Γ_μ e⁻¹)`, i.e. `ω_μ^I_J = e^I_ν ∇_μ e^ν_J`. -/
def tetradConn (e g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (μ : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  e y * (pdMat μ (fun z => (e z)⁻¹) y + chrMat g y μ * (e y)⁻¹)

/-- The Riemann tensor `R^ρ_{σμν}` of `g` is the curvature of its Christoffel matrices. -/
theorem riemMat_eq_gaugeCurv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (μ ν : Fin n) :
    (Matrix.of fun ρ σ => Lightlike.riemann g ρ σ μ ν x) = gaugeCurv (chrMat g) x μ ν := by
  ext ρ σ
  simp [Lightlike.riemann, gaugeCurv, chrMat, pdMat, Matrix.mul_apply, Finset.sum_sub_distrib]
  ring

/-- Product rule for `pdMat`. -/
lemma pdMat_mul {A B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x)
    (μ : Fin n) : pdMat μ (fun y => A y * B y) x = pdMat μ A x * B x + A x * pdMat μ B x := by
  ext i j
  simp only [pdMat, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [Lightlike.pd_sum (f := fun k y => A y i k * B y k j) _ (fun k _ => (hA i k).mul (hB k j))]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => Lightlike.pd_mul (hA i k) (hB k j) μ

/-- Sum rule for `pdMat`. -/
lemma pdMat_add {A B : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x) (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x)
    (μ : Fin n) : pdMat μ (fun y => A y + B y) x = pdMat μ A x + pdMat μ B x := by
  ext i j
  simp only [pdMat, Matrix.of_apply, Matrix.add_apply]
  exact Lightlike.pd_add (hA i j) (hB i j) μ

/-- `pdMat` of a function equal to a constant near `x` vanishes. -/
lemma pdMat_eventually_const {A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    {C : Matrix (Fin n) (Fin n) ℝ} (h : ∀ᶠ y in nhds x, A y = C) (μ : Fin n) : pdMat μ A x = 0 := by
  ext i j
  simp only [pdMat, Matrix.of_apply, Matrix.zero_apply]
  have : (fun y => A y i j) =ᶠ[nhds x] fun _ => C i j := h.mono fun y hy => by show A y i j = C i j; rw [hy]
  rw [Lightlike.pd_congr this, Lightlike.pd_const]

variable {e g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {x : Fin n → ℝ}

/-- **The curvature of the tetrad connection is the Riemann tensor in the frame**: `F_μν = e R_μν e⁻¹` (gauge
covariance), for a frame with smooth entries and nonzero determinant on the open set `U` and a coordinate metric `g`
on `U`. -/
theorem gaugeCurv_tetradConn (hU : IsOpen U) (hx : x ∈ U) (he : ∀ i j, ContDiffOn ℝ ∞ (fun y => e y i j) U)
    (hdet : ∀ y ∈ U, (e y).det ≠ 0) (hg : IsCoordMetric g U) (μ ν : Fin n) :
    gaugeCurv (tetradConn e g) x μ ν = e x * gaugeCurv (chrMat g) x μ ν * (e x)⁻¹ := by
  -- smoothness of the inverse frame, of its derivatives and of the Christoffel symbols
  have hf : ∀ i j, ContDiffOn ℝ ∞ (fun y => (e y)⁻¹ i j) U := Lightlike.contDiffOn_inv_entry he hdet
  have dAt : ∀ {F : (Fin n → ℝ) → ℝ}, ContDiffOn ℝ ∞ F U → ∀ y ∈ U, DifferentiableAt ℝ F y :=
    fun hF y hy => Lightlike.differentiableAt_of_contDiffOn hF hU hy
  have de : ∀ i j, DifferentiableAt ℝ (fun y => e y i j) x := fun i j => dAt (he i j) x hx
  have df : ∀ i j, DifferentiableAt ℝ (fun y => (e y)⁻¹ i j) x := fun i j => dAt (hf i j) x hx
  have dpf : ∀ (κ : Fin n) i j, DifferentiableAt ℝ (fun y => pdMat κ (fun z => (e z)⁻¹) y i j) x := fun κ i j =>
    dAt (Lightlike.contDiffOn_pd (hf i j) hU κ) x hx
  have dch : ∀ (κ : Fin n) i j, DifferentiableAt ℝ (fun y => chrMat g y κ i j) x := fun κ i j =>
    dAt (hg.contDiffOn_christoffel i κ j) x hx
  have dchf : ∀ (κ : Fin n) i j, DifferentiableAt ℝ (fun y => (chrMat g y κ * (e y)⁻¹) i j) x := fun κ i j => by
    simp only [Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun k _ => (dch κ i k).mul (df k j)
  have dsum : ∀ (κ : Fin n) i j,
      DifferentiableAt ℝ (fun y => (pdMat κ (fun z => (e z)⁻¹) y + chrMat g y κ * (e y)⁻¹) i j) x :=
    fun κ i j => (dpf κ i j).add (dchf κ i j)
  -- `e e⁻¹ = 1` near `x`, hence `∂e = -e (∂e⁻¹) e`
  have hu : ∀ y ∈ U, IsUnit (e y).det := fun y hy => isUnit_iff_ne_zero.2 (hdet y hy)
  have hef : e x * (e x)⁻¹ = 1 := mul_nonsing_inv _ (hu x hx)
  have hfe : (e x)⁻¹ * e x = 1 := nonsing_inv_mul _ (hu x hx)
  have hde : ∀ κ : Fin n, pdMat κ e x = -(e x * pdMat κ (fun z => (e z)⁻¹) x * e x) := fun κ => by
    have h0 : pdMat κ (fun y => e y * (e y)⁻¹) x = 0 :=
      pdMat_eventually_const (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => mul_nonsing_inv _ (hu y hy)) κ
    rw [pdMat_mul de df] at h0
    have h1 : pdMat κ e x * (e x)⁻¹ = -(e x * pdMat κ (fun z => (e z)⁻¹) x) := eq_neg_of_add_eq_zero_left h0
    calc pdMat κ e x = pdMat κ e x * ((e x)⁻¹ * e x) := by rw [hfe, Matrix.mul_one]
      _ = (pdMat κ e x * (e x)⁻¹) * e x := by rw [Matrix.mul_assoc]
      _ = -(e x * pdMat κ (fun z => (e z)⁻¹) x * e x) := by rw [h1, Matrix.neg_mul]
  -- the symmetric second derivatives of the inverse frame
  have hS : pdMat μ (fun y => pdMat ν (fun z => (e z)⁻¹) y) x = pdMat ν (fun y => pdMat μ (fun z => (e z)⁻¹) y) x := by
    ext i j
    simp only [pdMat, Matrix.of_apply]
    exact Lightlike.pd_pd_comm (hf i j) hU hx μ ν
  -- expand the derivatives of the connection
  have hdω : ∀ κ l : Fin n, pdMat κ (fun y => tetradConn e g y l) x =
      pdMat κ e x * (pdMat l (fun z => (e z)⁻¹) x + chrMat g x l * (e x)⁻¹) +
        e x * (pdMat κ (fun y => pdMat l (fun z => (e z)⁻¹) y) x +
          (pdMat κ (fun y => chrMat g y l) x * (e x)⁻¹ + chrMat g x l * pdMat κ (fun z => (e z)⁻¹) x)) := by
    intro κ l
    unfold tetradConn
    rw [pdMat_mul de (dsum l), pdMat_add (dpf l) (dchf l), pdMat_mul (dch l) df]
  unfold gaugeCurv
  rw [hdω μ ν, hdω ν μ, hde μ, hde ν, hS]
  unfold tetradConn
  have key : ∀ A : Matrix (Fin n) (Fin n) ℝ, A * (e x)⁻¹ * e x = A := fun A => by
    rw [Matrix.mul_assoc, hfe, Matrix.mul_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.neg_mul,
    ← Matrix.mul_assoc]
  simp only [key]
  noncomm_ring

end Lightlike.Canonical
