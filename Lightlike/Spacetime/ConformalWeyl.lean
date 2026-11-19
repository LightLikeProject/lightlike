import Lightlike.Spacetime.ConformalRicci

/-!
# The Weyl tensor of a conformally related metric (G1-016)

For a coordinate metric `g` and a smooth function `ψ`, in any dimension and signature:

* `riemann_of_christoffel_add_cov`: the Riemann tensors of two connections whose Christoffel symbols differ by a tensor
  `C`, `R̃ᵖ_{σμν} = Rᵖ_{σμν} + ∇_μ Cᵖ_{νσ} - ∇_ν Cᵖ_{μσ} + Cᵖ_{μl} Cˡ_{νσ} - Cᵖ_{νl} Cˡ_{μσ}`;
* `riemann_conformal`, `riemannLow_conformal`: the Riemann tensor of `e^{2ψ} g`, with one index raised and with all
  indices down;
* `weyl`: the Weyl tensor `C_{ρσμν}`, and `weyl_conformal`: for `n ≥ 3`, `C̃_{ρσμν} = e^{2ψ} C_{ρσμν}`;
* `weylUp`, `weylUp_conformal`: for `n ≥ 3`, `C̃ᵖ_{σμν} = Cᵖ_{σμν}`, the conformal invariance of the Weyl tensor.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 3, eq. (3.97) and the paragraph after
  (3.99), p. 82: the Weyl tensor in `n` dimensions, "only defined in three or more dimensions", and "invariant under
  conformal transformations".
* A. Campos, E. Verdaguer, *Semiclassical equations for weakly inhomogeneous cosmologies*, arXiv:gr-qc/9307027v1,
  Appendix C, eqs. (C.1)–(C.2), p. 28: the Riemann tensor of `g̃ = e^{2ω} g` in `n` dimensions.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The Riemann tensor with all indices down, `R_{ρσμν} = g_{ρα} Rᵅ_{σμν}`. -/
def riemannLow (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ α, g x ρ α * riemann g α σ μ ν x

/-- **The Weyl tensor** (Carroll (3.97), the antisymmetrizations written out):
`C_{ρσμν} = R_{ρσμν} - (g_{ρμ} R_{νσ} - g_{ρν} R_{μσ} - g_{σμ} R_{νρ} + g_{σν} R_{μρ}) / (n - 2)
+ R (g_{ρμ} g_{νσ} - g_{ρν} g_{μσ}) / ((n - 1)(n - 2))`. -/
def weyl (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  riemannLow g ρ σ μ ν x -
    (g x ρ μ * ricci g ν σ x - g x ρ ν * ricci g μ σ x - g x σ μ * ricci g ν ρ x + g x σ ν * ricci g μ ρ x) /
      ((n : ℝ) - 2) +
    scalarCurvature g x * (g x ρ μ * g x ν σ - g x ρ ν * g x μ σ) / (((n : ℝ) - 1) * ((n : ℝ) - 2))

/-- The Weyl tensor with its first index raised, `Cᵖ_{σμν} = gᵖᵅ C_{ασμν}`. -/
def weylUp (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ σ μ ν : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∑ α, (g x)⁻¹ ρ α * weyl g α σ μ ν x

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}

/-- **The Riemann tensors of two connections differing by a tensor, in covariant form**:
`R̃ᵖ_{σμν} = Rᵖ_{σμν} + ∇_μ Cᵖ_{νσ} - ∇_ν Cᵖ_{μσ} + Cᵖ_{μl} Cˡ_{νσ} - Cᵖ_{νl} Cˡ_{μσ}`. -/
theorem riemann_of_christoffel_add_cov {g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hgs : ∀ y a b, g y a b = g y b a) (C : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hC : ∀ᶠ y in nhds x, ∀ a b c, christoffel g' a b c y = christoffel g a b c y + C a b c y)
    (hΓd : ∀ a b c, DifferentiableAt ℝ (christoffel g a b c) x) (hCd : ∀ a b c, DifferentiableAt ℝ (C a b c) x)
    (ρ σ μ ν : Fin n) :
    riemann g' ρ σ μ ν x = riemann g ρ σ μ ν x + covC g C μ ρ ν σ x - covC g C ν ρ μ σ x +
      ∑ l, (C ρ μ l x * C l ν σ x - C ρ ν l x * C l μ σ x) := by
  rw [riemann_of_christoffel_add C hC hΓd hCd ρ σ μ ν]
  have hΓ : ∀ l a b, christoffel g l a b x = christoffel g l b a x := fun l a b => christoffel_symm g hgs l a b x
  unfold covC
  have hsum : ∑ l, ((christoffel g ρ μ l x + C ρ μ l x) * C l ν σ x + C ρ μ l x * christoffel g l ν σ x -
      ((christoffel g ρ ν l x + C ρ ν l x) * C l μ σ x + C ρ ν l x * christoffel g l μ σ x)) =
      (∑ l, christoffel g ρ μ l x * C l ν σ x) - (∑ l, christoffel g l μ ν x * C ρ l σ x) -
        (∑ l, christoffel g l μ σ x * C ρ ν l x) -
        ((∑ l, christoffel g ρ ν l x * C l μ σ x) - (∑ l, christoffel g l ν μ x * C ρ l σ x) -
          (∑ l, christoffel g l ν σ x * C ρ μ l x)) +
        ∑ l, (C ρ μ l x * C l ν σ x - C ρ ν l x * C l μ σ x) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hΓ l μ ν]; ring
  rw [hsum]
  ring

end

section Conformal

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {ψ : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}

variable (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hψ : ContDiffOn ℝ ∞ ψ U) (hx : x ∈ U)
include hg hgs hψ hx

/-- **The Riemann tensor of a conformally related metric** (Campos–Verdaguer (C.2), one index raised): for
`g̃ = e^{2ψ} g` and `A_{μσ} = ∇_μ ∇_σ ψ - ∂_μ ψ ∂_σ ψ`,
`R̃ᵖ_{σμν} = Rᵖ_{σμν} + δᵖ_ν A_{μσ} - δᵖ_μ A_{νσ} - g_{νσ} Aᵖ_μ + g_{μσ} Aᵖ_ν - (δᵖ_μ g_{νσ} - δᵖ_ν g_{μσ}) |dψ|²`. -/
theorem riemann_conformal (ρ σ μ ν : Fin n) :
    riemann (conformalMetric g ψ) ρ σ μ ν x =
      riemann g ρ σ μ ν x +
        (1 : Matrix (Fin n) (Fin n) ℝ) ρ ν * (hessC g ψ μ σ x - pd μ ψ x * pd σ ψ x) -
        (1 : Matrix (Fin n) (Fin n) ℝ) ρ μ * (hessC g ψ ν σ x - pd ν ψ x * pd σ ψ x) -
        g x ν σ * (∑ d, (g x)⁻¹ ρ d * hessC g ψ μ d x - pd μ ψ x * ∑ d, (g x)⁻¹ ρ d * pd d ψ x) +
        g x μ σ * (∑ d, (g x)⁻¹ ρ d * hessC g ψ ν d x - pd ν ψ x * ∑ d, (g x)⁻¹ ρ d * pd d ψ x) -
        ((1 : Matrix (Fin n) (Fin n) ℝ) ρ μ * g x ν σ - (1 : Matrix (Fin n) (Fin n) ℝ) ρ ν * g x μ σ) *
          gradSq g ψ x := by
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
  rw [riemann_of_christoffel_add_cov hgs (conformalC g ψ) (christoffel_conformal_eventually hg hψ hx) hΓd hCd,
    covC_conformalC hg hgs hψ hx, covC_conformalC hg hgs hψ hx]
  have hcc : ∀ a b c, conformalC g ψ a b c x =
      confCAt (g x) (fun b => pd b ψ x) (fun a => ∑ d, (g x)⁻¹ a d * pd d ψ x) a b c := fun _ _ _ => rfl
  have hlow : ∀ b, ∑ l, g x b l * (∑ d, (g x)⁻¹ l d * pd d ψ x) = pd b ψ x := fun b => by
    rw [← sum_metric_mul_raise hdet (fun a b => hgs x a b) (fun d => pd d ψ x) b]
    exact Finset.sum_congr rfl fun l _ => by rw [hgs x b l]
  have hsq : gradSq g ψ x = ∑ l, pd l ψ x * ∑ d, (g x)⁻¹ l d * pd d ψ x := by
    simp [gradSq, gradVec, mulVec, dotProduct]
  simp only [hcc]
  rw [Finset.sum_sub_distrib, sum_confCAt_mul, sum_confCAt_mul, sum_mul_confCAt, sum_mul_confCAt,
    sum_mul_confCAt, sum_mul_confCAt, hlow, hlow, hsq, hessC_symm hg hgs hψ hx μ ν]
  unfold confCAt
  rw [hgs x ν μ]
  ring

/-- **The Riemann tensor of a conformally related metric, all indices down** (Campos–Verdaguer (C.2)):
`R̃_{ρσμν} = e^{2ψ} (R_{ρσμν} + g_{ρν} A_{μσ} - g_{ρμ} A_{νσ} - g_{νσ} A_{μρ} + g_{μσ} A_{νρ}
- (g_{ρμ} g_{νσ} - g_{ρν} g_{μσ}) |dψ|²)`, with `A_{μσ} = ∇_μ ∇_σ ψ - ∂_μ ψ ∂_σ ψ`. -/
theorem riemannLow_conformal (ρ σ μ ν : Fin n) :
    riemannLow (conformalMetric g ψ) ρ σ μ ν x =
      Real.exp (2 * ψ x) * (riemannLow g ρ σ μ ν x +
        g x ρ ν * (hessC g ψ μ σ x - pd μ ψ x * pd σ ψ x) - g x ρ μ * (hessC g ψ ν σ x - pd ν ψ x * pd σ ψ x) -
        g x ν σ * (hessC g ψ μ ρ x - pd μ ψ x * pd ρ ψ x) + g x μ σ * (hessC g ψ ν ρ x - pd ν ψ x * pd ρ ψ x) -
        (g x ρ μ * g x ν σ - g x ρ ν * g x μ σ) * gradSq g ψ x) := by
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have hraise : ∀ (F : Fin n → ℝ) (r : Fin n), ∑ α, g x r α * ∑ d, (g x)⁻¹ α d * F d = F r := fun F r => by
    rw [← sum_metric_mul_raise hdet (fun a b => hgs x a b) F r]
    exact Finset.sum_congr rfl fun l _ => by rw [hgs x r l]
  unfold riemannLow
  simp only [conformalMetric, Matrix.smul_apply, smul_eq_mul, riemann_conformal hg hgs hψ hx]
  have e : ∀ α, Real.exp (2 * ψ x) * g x ρ α * (riemann g α σ μ ν x +
      (1 : Matrix (Fin n) (Fin n) ℝ) α ν * (hessC g ψ μ σ x - pd μ ψ x * pd σ ψ x) -
      (1 : Matrix (Fin n) (Fin n) ℝ) α μ * (hessC g ψ ν σ x - pd ν ψ x * pd σ ψ x) -
      g x ν σ * (∑ d, (g x)⁻¹ α d * hessC g ψ μ d x - pd μ ψ x * ∑ d, (g x)⁻¹ α d * pd d ψ x) +
      g x μ σ * (∑ d, (g x)⁻¹ α d * hessC g ψ ν d x - pd ν ψ x * ∑ d, (g x)⁻¹ α d * pd d ψ x) -
      ((1 : Matrix (Fin n) (Fin n) ℝ) α μ * g x ν σ - (1 : Matrix (Fin n) (Fin n) ℝ) α ν * g x μ σ) *
        gradSq g ψ x) =
      Real.exp (2 * ψ x) * (g x ρ α * riemann g α σ μ ν x) +
        Real.exp (2 * ψ x) * (hessC g ψ μ σ x - pd μ ψ x * pd σ ψ x + g x μ σ * gradSq g ψ x) *
          ((1 : Matrix (Fin n) (Fin n) ℝ) α ν * g x ρ α) -
        Real.exp (2 * ψ x) * (hessC g ψ ν σ x - pd ν ψ x * pd σ ψ x + g x ν σ * gradSq g ψ x) *
          ((1 : Matrix (Fin n) (Fin n) ℝ) α μ * g x ρ α) -
        Real.exp (2 * ψ x) * g x ν σ * (g x ρ α * ∑ d, (g x)⁻¹ α d * hessC g ψ μ d x) +
        Real.exp (2 * ψ x) * g x ν σ * pd μ ψ x * (g x ρ α * ∑ d, (g x)⁻¹ α d * pd d ψ x) +
        Real.exp (2 * ψ x) * g x μ σ * (g x ρ α * ∑ d, (g x)⁻¹ α d * hessC g ψ ν d x) -
        Real.exp (2 * ψ x) * g x μ σ * pd ν ψ x * (g x ρ α * ∑ d, (g x)⁻¹ α d * pd d ψ x) := fun α => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_one_apply_mul',
    hraise (fun d => hessC g ψ μ d x), hraise (fun d => hessC g ψ ν d x), hraise (fun d => pd d ψ x)]
  ring

/-- **The Weyl tensor is conformally invariant** (Carroll, the statement after (3.99)), all indices down: for
`n ≥ 3`, the Weyl tensor of `e^{2ψ} g` is `e^{2ψ}` times that of `g`. -/
theorem weyl_conformal (hn : 3 ≤ n) (ρ σ μ ν : Fin n) :
    weyl (conformalMetric g ψ) ρ σ μ ν x = Real.exp (2 * ψ x) * weyl g ρ σ μ ν x := by
  have h2 : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : (n : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have he : Real.exp (2 * ψ x) ≠ 0 := (Real.exp_pos _).ne'
  unfold weyl
  rw [riemannLow_conformal hg hgs hψ hx, ricci_conformal hg hgs hψ hx, ricci_conformal hg hgs hψ hx,
    ricci_conformal hg hgs hψ hx, ricci_conformal hg hgs hψ hx, scalarCurvature_conformal hg hgs hψ hx]
  simp only [conformalMetric, Matrix.smul_apply, smul_eq_mul]
  rw [hgs x σ μ, hgs x σ ν, hgs x ν ρ, hgs x μ ρ, Real.exp_neg]
  field_simp
  ring

/-- **The Weyl tensor is conformally invariant** (Carroll, the statement after (3.99)): for `n ≥ 3`, `Cᵖ_{σμν}` of
`e^{2ψ} g` equals that of `g`. -/
theorem weylUp_conformal (hn : 3 ≤ n) (ρ σ μ ν : Fin n) :
    weylUp (conformalMetric g ψ) ρ σ μ ν x = weylUp g ρ σ μ ν x := by
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have he : Real.exp (2 * ψ x) ≠ 0 := (Real.exp_pos _).ne'
  have hinv : (conformalMetric g ψ x)⁻¹ = (Real.exp (2 * ψ x))⁻¹ • (g x)⁻¹ := by
    have := Matrix.inv_smul' (Units.mk0 _ he) (A := g x) (Ne.isUnit hdet)
    simpa [conformalMetric, Units.smul_def] using this
  unfold weylUp
  rw [hinv]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [weyl_conformal hg hgs hψ hx hn, Matrix.smul_apply, smul_eq_mul]
  field_simp

end Conformal

end Lightlike
