import Lightlike.Spacetime.ConformalCoord
import Lightlike.Spacetime.NullHypersurfaceCoord
import Lightlike.Spacetime.PalatiniCoord
import Lightlike.Spacetime.RicciContinuous
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The Ricci tensor and scalar curvature of a conformally related metric (G1-016)

For a coordinate metric `g` and a smooth function `ψ`, the metric `g̃ = e^{2ψ} g` (`conformalMetric`) has, in any dimension
`n` and signature,

* `ricci_conformal`: `R̃_{σν} = R_{σν} - (n - 2) ∇_σ ∇_ν ψ - g_{σν} □ψ + (n - 2) ∂_σ ψ ∂_ν ψ - (n - 2) g_{σν} |dψ|²`,
* `scalarCurvature_conformal`: `R̃ = e^{-2ψ} (R - 2 (n - 1) □ψ - (n - 1)(n - 2) |dψ|²)`,

with `∇_σ ∇_ν ψ` the covariant Hessian (`hessC`), `□ψ` its trace (`boxC`) and `|dψ|² = gᵃᵇ ∂_a ψ ∂_b ψ` (`gradSq`).

The steps: the Ricci tensors of two connections whose Christoffel symbols differ by a tensor `C` are related by
`R̃_{σν} = R_{σν} + ∇_ρ Cᵖ_{νσ} - ∇_ν Cᵖ_{ρσ} + Cᵖ_{νσ} Cˡ_{lρ} - Cᵖ_{νl} Cˡ_{ρσ}` (`ricci_of_christoffel_add_cov`, `covC`
the covariant derivative of `C`); for the conformal difference tensor, `∇_k Cᵃ_{bc} = δᵃ_c H_{kb} + δᵃ_b H_{kc} -
g_{bc} gᵃᵈ H_{kd}` (`covC_conformalC`), and the quadratic terms sum to `(n - 2)(∂_ν ψ ∂_σ ψ - g_{νσ} |dψ|²)`
(`sum_confCAt_quadratic`).

## References

* E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*, arXiv:gr-qc/0703035, section 6.3.1, eq. (6.44),
  p. 90: the general relation between the Ricci tensors of two connections, which "does not rely on the fact that the
  metrics ... are conformally related".
* A. Campos, E. Verdaguer, *Semiclassical equations for weakly inhomogeneous cosmologies*, arXiv:gr-qc/9307027v1,
  Appendix C, eqs. (C.1), (C.3), (C.4), p. 28: the Ricci tensor and scalar curvature of `g̃ = e^{2ω} g` in `n` dimensions.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The covariant derivative `∇_k Cᵃ_{bc}` of a three-index array for the Christoffel symbols of `g`. -/
def covC (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (C : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (k a b c : Fin n) (x : Fin n → ℝ) : ℝ :=
  pd k (C a b c) x + ∑ l, christoffel g a k l x * C l b c x - ∑ l, christoffel g l k b x * C a l c x -
    ∑ l, christoffel g l k c x * C a b l x

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}

/-- **The Ricci tensors of two connections differing by a tensor, in covariant form** (Gourgoulhon (6.44)). -/
theorem ricci_of_christoffel_add_cov {g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hgs : ∀ y a b, g y a b = g y b a) (C : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hC : ∀ᶠ y in nhds x, ∀ a b c, christoffel g' a b c y = christoffel g a b c y + C a b c y)
    (hΓd : ∀ a b c, DifferentiableAt ℝ (christoffel g a b c) x) (hCd : ∀ a b c, DifferentiableAt ℝ (C a b c) x)
    (σ ν : Fin n) :
    ricci g' σ ν x = ricci g σ ν x + ∑ ρ, covC g C ρ ρ ν σ x - ∑ ρ, covC g C ν ρ ρ σ x +
      ∑ ρ, ∑ l, (C ρ ν σ x * C l l ρ x - C ρ ν l x * C l ρ σ x) := by
  rw [ricci_of_christoffel_add C hC hΓd hCd σ ν]
  have hΓ : ∀ l a b, christoffel g l a b x = christoffel g l b a x := fun l a b => christoffel_symm g hgs l a b x
  have eCC : ∑ ρ, ∑ l, (C ρ ν σ x * C l l ρ x - C ρ ν l x * C l ρ σ x) =
      ∑ ρ, ∑ l, (C ρ ρ l x * C l ν σ x - C ρ ν l x * C l ρ σ x) := by
    simp only [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [eCC, add_assoc, add_sub_assoc, add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold covC
  have hsum : ∑ l, ((christoffel g ρ ρ l x + C ρ ρ l x) * C l ν σ x + C ρ ρ l x * christoffel g l ν σ x -
      ((christoffel g ρ ν l x + C ρ ν l x) * C l ρ σ x + C ρ ν l x * christoffel g l ρ σ x)) =
      (∑ l, christoffel g ρ ρ l x * C l ν σ x) - (∑ l, christoffel g l ρ ν x * C ρ l σ x) -
        (∑ l, christoffel g l ρ σ x * C ρ ν l x) -
        ((∑ l, christoffel g ρ ν l x * C l ρ σ x) - (∑ l, christoffel g l ν ρ x * C ρ l σ x) -
          (∑ l, christoffel g l ν σ x * C ρ ρ l x)) +
        ∑ l, (C ρ ρ l x * C l ν σ x - C ρ ν l x * C l ρ σ x) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hΓ l ρ ν]; ring
  rw [hsum]
  ring

end

/-- The conformal difference tensor `Cᵃ_{bc} = δᵃ_c P_b + δᵃ_b P_c - G_{bc} Vᵃ` at a point, for a matrix `G`, a covector
`P` and a vector `V`. -/
def confCAt (G : Matrix (Fin n) (Fin n) ℝ) (P V : Fin n → ℝ) (a b c : Fin n) : ℝ :=
  P b * (1 : Matrix (Fin n) (Fin n) ℝ) a c + P c * (1 : Matrix (Fin n) (Fin n) ℝ) a b - G b c * V a

section Algebra

variable (G : Matrix (Fin n) (Fin n) ℝ) (P V : Fin n → ℝ)

theorem sum_one_apply_mul (F : Fin n → ℝ) (j : Fin n) : ∑ l, (1 : Matrix (Fin n) (Fin n) ℝ) j l * F l = F j := by
  simp [Matrix.one_apply]

theorem sum_one_apply_mul' (F : Fin n → ℝ) (j : Fin n) : ∑ l, (1 : Matrix (Fin n) (Fin n) ℝ) l j * F l = F j := by
  simp [Matrix.one_apply]

theorem sum_mul_confCAt (F : Fin n → ℝ) (b c : Fin n) :
    ∑ l, F l * confCAt G P V l b c = F c * P b + F b * P c - G b c * ∑ l, F l * V l := by
  unfold confCAt
  have e : ∀ l, F l * (P b * (1 : Matrix (Fin n) (Fin n) ℝ) l c + P c * (1 : Matrix (Fin n) (Fin n) ℝ) l b -
      G b c * V l) = P b * ((1 : Matrix (Fin n) (Fin n) ℝ) l c * F l) +
        P c * ((1 : Matrix (Fin n) (Fin n) ℝ) l b * F l) - G b c * (F l * V l) := fun l => by ring
  rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_one_apply_mul', sum_one_apply_mul']
  ring

theorem sum_confCAt_mul (F : Fin n → ℝ) (a b : Fin n) :
    ∑ l, confCAt G P V a b l * F l =
      P b * F a + (1 : Matrix (Fin n) (Fin n) ℝ) a b * ∑ l, P l * F l - V a * ∑ l, G b l * F l := by
  unfold confCAt
  have e : ∀ l, (P b * (1 : Matrix (Fin n) (Fin n) ℝ) a l + P l * (1 : Matrix (Fin n) (Fin n) ℝ) a b -
      G b l * V a) * F l = P b * ((1 : Matrix (Fin n) (Fin n) ℝ) a l * F l) +
        (1 : Matrix (Fin n) (Fin n) ℝ) a b * (P l * F l) - V a * (G b l * F l) := fun l => by ring
  rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_one_apply_mul]

variable {G P V}

theorem sum_confCAt_trace (hG : ∀ a b, G a b = G b a) (hlow : ∀ b, ∑ l, G b l * V l = P b) (c : Fin n) :
    ∑ l, confCAt G P V l l c = n * P c := by
  unfold confCAt
  have hl : ∑ l, G l c * V l = P c := by rw [← hlow c]; exact Finset.sum_congr rfl fun l _ => by rw [hG]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hl]
  simp

/-- **The quadratic terms of the conformal Ricci tensor**:
`Σ (Cᵖ_{νσ} Cˡ_{lρ} - Cᵖ_{νl} Cˡ_{ρσ}) = (n - 2) (P_ν P_σ - G_{νσ} P_l Vˡ)`. -/
theorem sum_confCAt_quadratic (hG : ∀ a b, G a b = G b a) (hlow : ∀ b, ∑ l, G b l * V l = P b) (ν σ : Fin n) :
    ∑ ρ, ∑ l, (confCAt G P V ρ ν σ * confCAt G P V l l ρ - confCAt G P V ρ ν l * confCAt G P V l ρ σ) =
      (n - 2) * (P ν * P σ - G ν σ * ∑ l, P l * V l) := by
  have hl : ∀ c, ∑ l, G l c * V l = P c := fun c => by
    rw [← hlow c]; exact Finset.sum_congr rfl fun l _ => by rw [hG]
  have hS : ∑ l, V l * P l = ∑ l, P l * V l := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h1 : ∀ ρ, ∑ l, confCAt G P V ρ ν σ * confCAt G P V l l ρ = n * (P ρ * confCAt G P V ρ ν σ) := fun ρ => by
    rw [← Finset.mul_sum, sum_confCAt_trace hG hlow]; ring
  have h2 : ∀ ρ, ∑ l, confCAt G P V ρ ν l * confCAt G P V l ρ σ =
      P ν * confCAt G P V ρ ρ σ + (1 : Matrix (Fin n) (Fin n) ℝ) ρ ν * (P σ * P ρ + P ρ * P σ -
        G ρ σ * ∑ l, P l * V l) - V ρ * (G ν σ * P ρ + G ν ρ * P σ - G ρ σ * P ν) := fun ρ => by
    rw [sum_confCAt_mul, sum_mul_confCAt, sum_mul_confCAt, hlow ν]
  simp only [Finset.sum_sub_distrib, h1, h2, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, sum_mul_confCAt, ← Finset.mul_sum, sum_confCAt_trace hG hlow,
    sum_one_apply_mul' (fun ρ => P σ * P ρ + P ρ * P σ - G ρ σ * ∑ l, P l * V l)]
  have e3 : ∑ ρ, V ρ * (G ν σ * P ρ + G ν ρ * P σ - G ρ σ * P ν) =
      G ν σ * ∑ ρ, V ρ * P ρ + P σ * ∑ ρ, G ν ρ * V ρ - P ν * ∑ ρ, G ρ σ * V ρ := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e3, hS, hlow, hl]
  ring

end Algebra

/-- The covariant Hessian `H_{kb} = ∂_k ∂_b ψ - Γᵉ_{kb} ∂_e ψ` of a function. -/
def hessC (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ψ : (Fin n → ℝ) → ℝ) (k b : Fin n) (x : Fin n → ℝ) : ℝ :=
  pd k (fun y => pd b ψ y) x - ∑ e, christoffel g e k b x * pd e ψ x

/-- The wave operator (Laplacian) `□ψ = gᵏᵇ H_{kb}` of a function. -/
def boxC (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ψ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ k, ∑ b, (g x)⁻¹ k b * hessC g ψ k b x

/-- Raising an index and lowering it again: `g_{ρσ} gᵖᵈ F_d = F_σ`. -/
theorem sum_metric_mul_raise {G : Matrix (Fin n) (Fin n) ℝ} (hdet : G.det ≠ 0) (hG : ∀ a b, G a b = G b a)
    (F : Fin n → ℝ) (σ : Fin n) : ∑ ρ, G ρ σ * ∑ d, G⁻¹ ρ d * F d = F σ := by
  have h1 : ∀ d, ∑ ρ, G σ ρ * G⁻¹ ρ d = (1 : Matrix (Fin n) (Fin n) ℝ) σ d := fun d => by
    rw [← Matrix.mul_nonsing_inv _ (Ne.isUnit hdet), Matrix.mul_apply]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ d, ∑ ρ, G ρ σ * (G⁻¹ ρ d * F d) = (1 : Matrix (Fin n) (Fin n) ℝ) σ d * F d := fun d => by
    rw [← h1 d, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ρ _ => by rw [hG ρ σ]; ring
  simp only [e, sum_one_apply_mul]

section Conformal

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {ψ : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}

variable (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hψ : ContDiffOn ℝ ∞ ψ U) (hx : x ∈ U)
include hg hgs hψ hx

/-- **The covariant derivative of the conformal difference tensor**:
`∇_k Cᵃ_{bc} = δᵃ_c H_{kb} + δᵃ_b H_{kc} - g_{bc} gᵃᵈ H_{kd}`. -/
theorem covC_conformalC (k a b c : Fin n) :
    covC g (conformalC g ψ) k a b c x =
      (1 : Matrix (Fin n) (Fin n) ℝ) a c * hessC g ψ k b x + (1 : Matrix (Fin n) (Fin n) ℝ) a b * hessC g ψ k c x -
        g x b c * ∑ d, (g x)⁻¹ a d * hessC g ψ k d x := by
  have hdp : ∀ d, DifferentiableAt ℝ (fun y => pd d ψ y) x := fun d =>
    differentiableAt_of_contDiffOn (contDiffOn_pd hψ hg.isOpen d) hg.isOpen hx
  have hdi : ∀ a d, DifferentiableAt ℝ (fun y => (g y)⁻¹ a d) x := fun a d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a d) hg.isOpen hx
  have hdg : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hx
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have hl : (fun z => gradVec g ψ z a) = fun z => ∑ d, (g z)⁻¹ a d * pd d ψ z := by
    funext z; simp [gradVec, mulVec, dotProduct]
  have hlx : ∀ c, gradVec g ψ x c = ∑ d, (g x)⁻¹ c d * pd d ψ x := fun c => by
    simp [gradVec, mulVec, dotProduct]
  have hgv : DifferentiableAt ℝ (fun z => ∑ d, (g z)⁻¹ a d * pd d ψ z) x :=
    DifferentiableAt.fun_sum fun d _ => (hdi a d).mul (hdp d)
  have hcov := covD_gradVec hg hgs hψ hx a k
  unfold covD at hcov
  rw [hl] at hcov
  simp only [hlx] at hcov
  have hC : conformalC g ψ a b c = fun y => pd b ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a c +
      pd c ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a b - g y b c * ∑ d, (g y)⁻¹ a d * pd d ψ y := rfl
  unfold covC
  rw [hC, pd_sub (f₁ := fun y => pd b ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a c +
      pd c ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a b) (f₂ := fun y => g y b c * ∑ d, (g y)⁻¹ a d * pd d ψ y)
      (((hdp b).mul_const _).add ((hdp c).mul_const _)) ((hdg b c).mul hgv) k,
    pd_add (f₁ := fun y => pd b ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a c)
      (f₂ := fun y => pd c ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a b) ((hdp b).mul_const _) ((hdp c).mul_const _) k,
    pd_mul (f₂ := fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) a c) (hdp b) (differentiableAt_const _) k,
    pd_mul (f₂ := fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) a b) (hdp c) (differentiableAt_const _) k,
    pd_mul (f₁ := fun y => g y b c) (f₂ := fun z => ∑ d, (g z)⁻¹ a d * pd d ψ z) (hdg b c) hgv k, pd_const, pd_const, pd_metric_eq_christoffel hgs hdet k b c, eq_sub_of_add_eq hcov]
  simp only [hessC, conformalC, Matrix.one_apply, mul_add, add_mul, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have m1 : ∀ (F G : Fin n → ℝ) (r : ℝ), ∑ l, F l * (G l * r) = (∑ l, G l * F l) * r := fun F G r => by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
  have m2 : ∀ (F G : Fin n → ℝ) (r : ℝ), ∑ l, F l * (r * G l) = r * ∑ l, F l * G l := fun F G r => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  simp only [m1, m2, Finset.sum_ite_irrel, Finset.sum_const_zero]
  split_ifs <;> ring

/-- The covariant Hessian is symmetric. -/
theorem hessC_symm (k b : Fin n) : hessC g ψ k b x = hessC g ψ b k x := by
  unfold hessC
  rw [show (fun y => pd b ψ y) = pd b ψ from rfl, show (fun y => pd k ψ y) = pd k ψ from rfl,
    pd_pd_comm hψ hg.isOpen hx k b]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [christoffel_symm g hgs]

theorem sum_covC_conformalC_div (ν σ : Fin n) :
    ∑ ρ, covC g (conformalC g ψ) ρ ρ ν σ x = 2 * hessC g ψ σ ν x - g x ν σ * boxC g ψ x := by
  simp only [covC_conformalC hg hgs hψ hx, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_one_apply_mul']
  rw [← Finset.mul_sum, hessC_symm hg hgs hψ hx ν σ]
  unfold boxC
  ring

theorem sum_covC_conformalC_trace (ν σ : Fin n) :
    ∑ ρ, covC g (conformalC g ψ) ν ρ ρ σ x = n * hessC g ψ ν σ x := by
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  simp only [covC_conformalC hg hgs hψ hx, Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_one_apply_mul',
    sum_metric_mul_raise hdet (fun a b => hgs x a b) (fun d => hessC g ψ ν d x) σ]
  simp

/-- **The Ricci tensor of a conformally related metric** (Campos–Verdaguer (C.3)): for `g̃ = e^{2ψ} g`,
`R̃_{σν} = R_{σν} - (n - 2) ∇_σ ∇_ν ψ - g_{σν} □ψ + (n - 2) ∂_σ ψ ∂_ν ψ - (n - 2) g_{σν} |dψ|²`. -/
theorem ricci_conformal (σ ν : Fin n) :
    ricci (conformalMetric g ψ) σ ν x =
      ricci g σ ν x - (n - 2) * hessC g ψ σ ν x - g x σ ν * boxC g ψ x +
        (n - 2) * (pd σ ψ x * pd ν ψ x) - (n - 2) * g x σ ν * gradSq g ψ x := by
  have hdp : ∀ d, DifferentiableAt ℝ (fun y => pd d ψ y) x := fun d =>
    differentiableAt_of_contDiffOn (contDiffOn_pd hψ hg.isOpen d) hg.isOpen hx
  have hdi : ∀ a d, DifferentiableAt ℝ (fun y => (g y)⁻¹ a d) x := fun a d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a d) hg.isOpen hx
  have hdg : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hx
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have hΓd : ∀ a b c, DifferentiableAt ℝ (christoffel g a b c) x := fun a b c =>
    differentiableAt_of_contDiffOn (contDiffOn_christoffel hg a b c) hg.isOpen hx
  have hCd : ∀ a b c, DifferentiableAt ℝ (conformalC g ψ a b c) x := fun a b c =>
    (((hdp b).mul_const _).add ((hdp c).mul_const _)).sub
      ((hdg b c).mul (DifferentiableAt.fun_sum fun d _ => (hdi a d).mul (hdp d)))
  rw [ricci_of_christoffel_add_cov hgs (conformalC g ψ) (christoffel_conformal_eventually hg hψ hx) hΓd hCd σ ν,
    sum_covC_conformalC_div hg hgs hψ hx, sum_covC_conformalC_trace hg hgs hψ hx]
  have hcc : ∀ a b c, conformalC g ψ a b c x =
      confCAt (g x) (fun b => pd b ψ x) (fun a => ∑ d, (g x)⁻¹ a d * pd d ψ x) a b c := fun _ _ _ => rfl
  have hlow : ∀ b, ∑ l, g x b l * (∑ d, (g x)⁻¹ l d * pd d ψ x) = pd b ψ x := fun b => by
    rw [← sum_metric_mul_raise hdet (fun a b => hgs x a b) (fun d => pd d ψ x) b]
    exact Finset.sum_congr rfl fun l _ => by rw [hgs x b l]
  have hsq : gradSq g ψ x = ∑ l, pd l ψ x * ∑ d, (g x)⁻¹ l d * pd d ψ x := by
    simp [gradSq, gradVec, mulVec, dotProduct]
  simp only [hcc]
  rw [sum_confCAt_quadratic (fun a b => hgs x a b) hlow ν σ, hsq, hessC_symm hg hgs hψ hx ν σ, hgs x ν σ]
  ring

/-- **The scalar curvature of a conformally related metric** (Campos–Verdaguer (C.4)): for `g̃ = e^{2ψ} g`,
`R̃ = e^{-2ψ} (R - 2 (n - 1) □ψ - (n - 1)(n - 2) |dψ|²)`. -/
theorem scalarCurvature_conformal :
    scalarCurvature (conformalMetric g ψ) x =
      Real.exp (-(2 * ψ x)) * (scalarCurvature g x - 2 * (n - 1) * boxC g ψ x - (n - 1) * (n - 2) * gradSq g ψ x) := by
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have he : Real.exp (2 * ψ x) ≠ 0 := (Real.exp_pos _).ne'
  have hinv : (conformalMetric g ψ x)⁻¹ = (Real.exp (2 * ψ x))⁻¹ • (g x)⁻¹ := by
    have := Matrix.inv_smul' (Units.mk0 _ he) (A := g x) (Ne.isUnit hdet)
    simpa [conformalMetric, Units.smul_def] using this
  have htr : ∑ σ, ∑ ν, (g x)⁻¹ σ ν * g x σ ν = n := by
    have h1 : ∀ σ, ∑ ν, (g x)⁻¹ σ ν * g x σ ν = (1 : Matrix (Fin n) (Fin n) ℝ) σ σ := fun σ => by
      rw [← Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.mul_apply]
      exact Finset.sum_congr rfl fun ν _ => by rw [hgs x σ ν]
    simp [h1]
  have hsq : ∑ σ, ∑ ν, (g x)⁻¹ σ ν * (pd σ ψ x * pd ν ψ x) = gradSq g ψ x := by
    simp only [gradSq, gradVec, mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  unfold scalarCurvature
  rw [hinv]
  simp only [Matrix.smul_apply, smul_eq_mul, ricci_conformal hg hgs hψ hx]
  have e : ∀ σ ν, (Real.exp (2 * ψ x))⁻¹ * (g x)⁻¹ σ ν * (ricci g σ ν x - (n - 2) * hessC g ψ σ ν x -
      g x σ ν * boxC g ψ x + (n - 2) * (pd σ ψ x * pd ν ψ x) - (n - 2) * g x σ ν * gradSq g ψ x) =
      (Real.exp (2 * ψ x))⁻¹ * ((g x)⁻¹ σ ν * ricci g σ ν x) -
        (Real.exp (2 * ψ x))⁻¹ * (n - 2) * ((g x)⁻¹ σ ν * hessC g ψ σ ν x) -
        (Real.exp (2 * ψ x))⁻¹ * boxC g ψ x * ((g x)⁻¹ σ ν * g x σ ν) +
        (Real.exp (2 * ψ x))⁻¹ * (n - 2) * ((g x)⁻¹ σ ν * (pd σ ψ x * pd ν ψ x)) -
        (Real.exp (2 * ψ x))⁻¹ * (n - 2) * gradSq g ψ x * ((g x)⁻¹ σ ν * g x σ ν) := fun σ ν => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, htr, hsq]
  rw [Real.exp_neg]
  unfold boxC
  ring

end Conformal

end Lightlike
