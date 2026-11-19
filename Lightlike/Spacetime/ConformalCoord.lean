import Lightlike.Spacetime.Curvature
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.EHManifold.Locality

/-!
# Conformal change of a coordinate metric (G1-016)

For a coordinate metric `g` and a function `ψ`, the conformally related metric `g̃ = e^{2ψ} g` has the Christoffel symbols
`Γ̃ᵃ_{bc} = Γᵃ_{bc} + δᵃ_c ∂_b ψ + δᵃ_b ∂_c ψ - g_{bc} gᵃᵈ ∂_d ψ` (`christoffel_conformal`).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The conformally related metric `e^{2ψ} g`. -/
def conformalMetric (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ψ : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Real.exp (2 * ψ y) • g y

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {ψ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}

/-- **The Christoffel symbols of a conformally related metric**:
`Γ̃ᵃ_{bc} = Γᵃ_{bc} + δᵃ_c ∂_b ψ + δᵃ_b ∂_c ψ - g_{bc} gᵃᵈ ∂_d ψ` for `g̃ = e^{2ψ} g`. -/
theorem christoffel_conformal (hgd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x) (hψd : DifferentiableAt ℝ ψ x)
    (hdet : (g x).det ≠ 0) (hsym : ∀ a b, g x a b = g x b a) (a b c : Fin n) :
    christoffel (conformalMetric g ψ) a b c x =
      christoffel g a b c x + (pd b ψ x * (1 : Matrix (Fin n) (Fin n) ℝ) a c +
        pd c ψ x * (1 : Matrix (Fin n) (Fin n) ℝ) a b - g x b c * ∑ d, (g x)⁻¹ a d * pd d ψ x) := by
  have he : Real.exp (2 * ψ x) ≠ 0 := (Real.exp_pos _).ne'
  have hed : DifferentiableAt ℝ (fun y => Real.exp (2 * ψ y)) x := ((hψd.const_mul 2).exp)
  have hpe : ∀ j, pd j (fun y => Real.exp (2 * ψ y)) x = Real.exp (2 * ψ x) * (2 * pd j ψ x) := fun j => by
    unfold pd
    rw [((hψd.hasFDerivAt.const_mul 2).exp).fderiv]
    simp [smul_eq_mul, mul_comm]
  have hentry : ∀ l k, (fun y => conformalMetric g ψ y l k) = fun y => Real.exp (2 * ψ y) * g y l k := fun l k => by
    funext y; simp [conformalMetric]
  have hpd : ∀ j l k, pd j (fun y => conformalMetric g ψ y l k) x =
      Real.exp (2 * ψ x) * (2 * pd j ψ x * g x l k + pd j (fun y => g y l k) x) := fun j l k => by
    rw [hentry, pd_mul hed (hgd l k), hpe]
    ring
  have hinv : (conformalMetric g ψ x)⁻¹ = (Real.exp (2 * ψ x))⁻¹ • (g x)⁻¹ := by
    have := Matrix.inv_smul' (Units.mk0 _ he) (A := g x) (Ne.isUnit hdet)
    simpa [conformalMetric, Units.smul_def] using this
  have hone : ∀ a c, ∑ l, (g x)⁻¹ a l * g x l c = (1 : Matrix (Fin n) (Fin n) ℝ) a c := fun a c => by
    rw [← Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.mul_apply]
  unfold christoffel
  simp only [hpd, hinv, Matrix.smul_apply, smul_eq_mul]
  have e1 : ∑ l, (g x)⁻¹ a l * g x l b = (1 : Matrix (Fin n) (Fin n) ℝ) a b := hone a b
  have e2 : ∑ l, (g x)⁻¹ a l * g x l c = (1 : Matrix (Fin n) (Fin n) ℝ) a c := hone a c
  rw [← e1, ← e2]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hsym l b]
  field_simp
  ring

/-- **The Riemann tensor of a connection shifted by a difference tensor**: if `Γ̃ = Γ + C` near `x`, then
`R̃ᵖ_{σμν} = Rᵖ_{σμν} + ∂_μ Cᵖ_{νσ} - ∂_ν Cᵖ_{μσ} + Σ_l ((Γ + C)ᵖ_{μl} Cˡ_{νσ} + Cᵖ_{μl} Γˡ_{νσ} - (μ ↔ ν))`. -/
theorem riemann_of_christoffel_add {g g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (C : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hC : ∀ᶠ y in nhds x, ∀ a b c, christoffel g' a b c y = christoffel g a b c y + C a b c y)
    (hΓd : ∀ a b c, DifferentiableAt ℝ (christoffel g a b c) x) (hCd : ∀ a b c, DifferentiableAt ℝ (C a b c) x)
    (ρ σ μ ν : Fin n) :
    riemann g' ρ σ μ ν x = riemann g ρ σ μ ν x + (pd μ (C ρ ν σ) x - pd ν (C ρ μ σ) x) +
      ∑ l, ((christoffel g ρ μ l x + C ρ μ l x) * C l ν σ x + C ρ μ l x * christoffel g l ν σ x -
        ((christoffel g ρ ν l x + C ρ ν l x) * C l μ σ x + C ρ ν l x * christoffel g l μ σ x)) := by
  have hev : ∀ a b c, christoffel g' a b c =ᶠ[nhds x] fun y => christoffel g a b c y + C a b c y :=
    fun a b c => hC.mono fun y hy => hy a b c
  have hval : ∀ a b c, christoffel g' a b c x = christoffel g a b c x + C a b c x := fun a b c =>
    (hev a b c).eq_of_nhds
  have hpd : ∀ k a b c, pd k (christoffel g' a b c) x = pd k (christoffel g a b c) x + pd k (C a b c) x :=
    fun k a b c => by
      rw [(pd_eventuallyEq (hev a b c) k).eq_of_nhds, pd_add (hΓd a b c) (hCd a b c) k]
  unfold riemann
  simp only [hval, hpd]
  have hs : ∑ l, ((christoffel g ρ μ l x + C ρ μ l x) * (christoffel g l ν σ x + C l ν σ x) -
      (christoffel g ρ ν l x + C ρ ν l x) * (christoffel g l μ σ x + C l μ σ x)) =
      (∑ l, (christoffel g ρ μ l x * christoffel g l ν σ x - christoffel g ρ ν l x * christoffel g l μ σ x)) +
        ∑ l, ((christoffel g ρ μ l x + C ρ μ l x) * C l ν σ x + C ρ μ l x * christoffel g l ν σ x -
          ((christoffel g ρ ν l x + C ρ ν l x) * C l μ σ x + C ρ ν l x * christoffel g l μ σ x)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hs]
  ring

/-- The difference tensor `Cᵃ_{bc} = δᵃ_c ∂_b ψ + δᵃ_b ∂_c ψ - g_{bc} gᵃᵈ ∂_d ψ` of a conformal change. -/
def conformalC (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ψ : (Fin n → ℝ) → ℝ) (a b c : Fin n) (y : Fin n → ℝ) : ℝ :=
  pd b ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a c + pd c ψ y * (1 : Matrix (Fin n) (Fin n) ℝ) a b -
    g y b c * ∑ d, (g y)⁻¹ a d * pd d ψ y

/-- On the domain of a coordinate metric, the Christoffel symbols of `e^{2ψ} g` are `Γ + C` near every point. -/
theorem christoffel_conformal_eventually {U : Set (Fin n → ℝ)} (hg : IsCoordMetric g U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hx : x ∈ U) :
    ∀ᶠ y in nhds x, ∀ a b c, christoffel (conformalMetric g ψ) a b c y =
      christoffel g a b c y + conformalC g ψ a b c y := by
  filter_upwards [hg.isOpen.mem_nhds hx] with y hy a b c
  have hsym : ∀ a b, g y a b = g y b a := fun a b => by
    have := congrFun (congrFun (hg.symm y hy) b) a
    simpa [Matrix.transpose_apply] using this
  exact christoffel_conformal (fun a b => differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hy)
    (differentiableAt_of_contDiffOn hψ hg.isOpen hy) (hg.isUnit_det y hy).ne_zero hsym a b c

/-- **The coordinate Christoffel symbols are metric compatible**: `∂_k g_{ab} = g_{lb} Γˡ_{ka} + g_{al} Γˡ_{kb}`. -/
theorem pd_metric_eq_christoffel (hgs : ∀ y a b, g y a b = g y b a) (hdet : (g x).det ≠ 0) (k a b : Fin n) :
    pd k (fun y => g y a b) x = ∑ l, (g x l b * christoffel g l k a x + g x a l * christoffel g l k b x) := by
  have hsymf : ∀ a b, (fun y => g y a b) = fun y => g y b a := fun a b => funext fun y => hgs y a b
  have hone : ∀ b m, ∑ l, g x b l * (g x)⁻¹ l m = (1 : Matrix (Fin n) (Fin n) ℝ) b m := fun b m => by
    rw [← Matrix.mul_nonsing_inv _ (Ne.isUnit hdet), Matrix.mul_apply]
  have hlow : ∀ b k a, ∑ l, g x l b * christoffel g l k a x =
      (1 / 2) * (pd k (fun y => g y b a) x + pd a (fun y => g y b k) x - pd b (fun y => g y k a) x) := fun b k a => by
    unfold christoffel
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ m, ∑ l, g x l b * ((1 / 2) * ((g x)⁻¹ l m *
        (pd k (fun y => g y m a) x + pd a (fun y => g y m k) x - pd m (fun y => g y k a) x))) =
        (1 / 2) * ((∑ l, g x b l * (g x)⁻¹ l m) *
          (pd k (fun y => g y m a) x + pd a (fun y => g y m k) x - pd m (fun y => g y k a) x)) := fun m => by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hgs x l b]; ring
    simp only [this, hone, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  rw [Finset.sum_add_distrib, hlow b k a]
  have h2 : ∑ l, g x a l * christoffel g l k b x = ∑ l, g x l a * christoffel g l k b x :=
    Finset.sum_congr rfl fun l _ => by rw [hgs x a l]
  rw [h2, hlow a k b, hsymf b a, hsymf b k, hsymf k a, hsymf a k]
  ring

/-- The trace of the conformal difference tensor: `Cᵖ_{pσ} = n ∂_σ ψ`. -/
theorem sum_conformalC_trace (hdet : (g x).det ≠ 0) (hsym : ∀ a b, g x a b = g x b a) (σ : Fin n) :
    ∑ ρ, conformalC g ψ ρ ρ σ x = n * pd σ ψ x := by
  have hone : ∑ ρ, g x ρ σ * ∑ d, (g x)⁻¹ ρ d * pd d ψ x = pd σ ψ x := by
    have : ∀ d, ∑ ρ, g x σ ρ * (g x)⁻¹ ρ d = (1 : Matrix (Fin n) (Fin n) ℝ) σ d := fun d => by
      rw [← Matrix.mul_nonsing_inv _ (Ne.isUnit hdet), Matrix.mul_apply]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e : ∀ d, ∑ ρ, g x ρ σ * ((g x)⁻¹ ρ d * pd d ψ x) = (1 : Matrix (Fin n) (Fin n) ℝ) σ d * pd d ψ x := fun d => by
      rw [← this d, Finset.sum_mul]
      exact Finset.sum_congr rfl fun ρ _ => by rw [hsym ρ σ]; ring
    simp only [e, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold conformalC
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hone]
  simp

/-- **The Ricci tensor of a connection shifted by a difference tensor** (the contraction of
`riemann_of_christoffel_add`): `R̃_{σν} = R_{σν} + ∂_ρ Cᵖ_{νσ} - ∂_ν Cᵖ_{ρσ} + (Γ + C)ᵖ_{ρl} Cˡ_{νσ} + Cᵖ_{ρl} Γˡ_{νσ}
- (Γ + C)ᵖ_{νl} Cˡ_{ρσ} - Cᵖ_{νl} Γˡ_{ρσ}`. -/
theorem ricci_of_christoffel_add {g g' : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (C : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℝ)
    (hC : ∀ᶠ y in nhds x, ∀ a b c, christoffel g' a b c y = christoffel g a b c y + C a b c y)
    (hΓd : ∀ a b c, DifferentiableAt ℝ (christoffel g a b c) x) (hCd : ∀ a b c, DifferentiableAt ℝ (C a b c) x)
    (σ ν : Fin n) :
    ricci g' σ ν x = ricci g σ ν x + ∑ ρ, (pd ρ (C ρ ν σ) x - pd ν (C ρ ρ σ) x) +
      ∑ ρ, ∑ l, ((christoffel g ρ ρ l x + C ρ ρ l x) * C l ν σ x + C ρ ρ l x * christoffel g l ν σ x -
        ((christoffel g ρ ν l x + C ρ ν l x) * C l ρ σ x + C ρ ν l x * christoffel g l ρ σ x)) := by
  unfold ricci
  simp only [riemann_of_christoffel_add C hC hΓd hCd, Finset.sum_add_distrib]

end

end Lightlike
