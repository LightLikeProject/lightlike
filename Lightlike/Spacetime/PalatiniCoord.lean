import Lightlike.Spacetime.VariationRiemann
import Lightlike.Spacetime.VariationInverse
import Lightlike.Spacetime.PalatiniAlgebra
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The Palatini identity in coordinates (GE15, stage S2)

For smooth symmetric `g, h` on `ℝⁿ` with `det g x ≠ 0`, `W^ρ = g^{σν} δΓ^ρ_{σν} - g^{ρσ} δΓ^κ_{κσ}`, `δΓ = dChristoffel`:
`√|g| g^{σν} δR_{σν} = ∂_ρ (√|g| W^ρ)` (`palatini_coord`), where `δR_{σν} = dRicci` is the first variation of the coordinate Ricci tensor of
`g + t h`. The proof uses the algebraic core `palatini_alg_nd`, `palatini_dd`, the derivative of the inverse metric (`pd_inv_eq`) and of the
volume density (`pd_sqrt_abs_det`).

**Limits.** Coordinate statement on `ℝⁿ`, `C^∞` metric and perturbation; the integral statement (divergence of a compactly supported field)
is the next stage.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

theorem dChristoffel_symm (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (hgs : ∀ y a b, g y a b = g y b a)
    (hhs : ∀ y a b, h y a b = h y b a) (i j k : Fin n) (y : Fin n → ℝ) : dChristoffel g h i j k y = dChristoffel g h i k j y := by
  unfold dChristoffel
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have e1 : (fun z => g z l k) = fun z => g z l k := rfl
  have e2 : (fun z => g z j k) = fun z => g z k j := by funext z; exact hgs z j k
  have e3 : (fun z => h z j k) = fun z => h z k j := by funext z; exact hhs z j k
  rw [e2, e3]
  ring

theorem christoffel_symm (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (hgs : ∀ y a b, g y a b = g y b a)
    (i j k : Fin n) (y : Fin n → ℝ) : christoffel g i j k y = christoffel g i k j y := by
  unfold christoffel
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have e2 : (fun z => g z j k) = fun z => g z k j := by funext z; exact hgs z j k
  rw [e2]
  ring

section
variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (x : Fin n → ℝ) (hx : (g x).det ≠ 0)

theorem contDiffAt_dChristoffel (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b))
    (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b)) (hx : (g x).det ≠ 0) (i j k : Fin n) :
    ContDiffAt ℝ ∞ (dChristoffel g h i j k) x := by
  have hinv : ∀ a b, ContDiffAt ℝ ∞ (fun y => (g y)⁻¹ a b) x := fun a b => contDiffAt_inv_entry hg hx a b
  have hp : ∀ (f : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ), (∀ a b, ContDiff ℝ ∞ (fun y => f y a b)) →
      ∀ a b c, ContDiffAt ℝ ∞ (fun y => pd c (fun z => f z a b) y) x :=
    fun f hf a b c => (contDiff_pd (hf a b) c).contDiffAt
  unfold dChristoffel
  refine contDiffAt_const.mul (ContDiffAt.sum fun l _ => ?_)
  refine ContDiffAt.add (ContDiffAt.mul ?_ ?_) (ContDiffAt.mul (hinv i l) ?_)
  · simp only [Matrix.mul_apply, Matrix.neg_apply]
    exact (ContDiffAt.sum fun a _ => (ContDiffAt.sum fun b _ => (hinv i b).mul ((hh b a).contDiffAt)).mul (hinv a l)).neg
  · exact ((hp g hg l k j).add (hp g hg l j k)).sub (hp g hg j k l)
  · exact ((hp h hh l k j).add (hp h hh l j k)).sub (hp h hh j k l)


/-- The vector `W^ρ = g^{σν} δΓ^ρ_{σν} - g^{ρσ} δΓ^κ_{κσ}` as a function of the point. -/
def Wvec (ρ : Fin n) (y : Fin n → ℝ) : ℝ :=
  (∑ σ, ∑ ν, (g y)⁻¹ σ ν * dChristoffel g h ρ σ ν y) - ∑ σ, (g y)⁻¹ ρ σ * ∑ κ, dChristoffel g h κ κ σ y

include hg hh hx

theorem pd_Wvec (ρ : Fin n) :
    pd ρ (Wvec g h ρ) x =
      (∑ σ, ∑ ν, (pd ρ (fun y => (g y)⁻¹ σ ν) x * dChristoffel g h ρ σ ν x +
          (g x)⁻¹ σ ν * pd ρ (dChristoffel g h ρ σ ν) x)) -
        ∑ σ, (pd ρ (fun y => (g y)⁻¹ ρ σ) x * ∑ κ, dChristoffel g h κ κ σ x +
          (g x)⁻¹ ρ σ * ∑ κ, pd ρ (dChristoffel g h κ κ σ) x) := by
  have hd : ∀ i j k, DifferentiableAt ℝ (dChristoffel g h i j k) x :=
    fun i j k => (contDiffAt_dChristoffel g h x hg hh hx i j k).differentiableAt (by simp)
  have hgd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b => ((hg a b).differentiable (by simp)) x
  have hinv : ∀ a b, DifferentiableAt ℝ (fun y => (g y)⁻¹ a b) x := fun a b => differentiableAt_inv_entry hgd hx a b
  unfold Wvec
  have e1 : DifferentiableAt ℝ (fun y => ∑ σ, ∑ ν, (g y)⁻¹ σ ν * dChristoffel g h ρ σ ν y) x :=
    DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.fun_sum fun ν _ => (hinv σ ν).mul (hd ρ σ ν)
  have e2 : DifferentiableAt ℝ (fun y => ∑ σ, (g y)⁻¹ ρ σ * ∑ κ, dChristoffel g h κ κ σ y) x :=
    DifferentiableAt.fun_sum fun σ _ => (hinv ρ σ).mul (DifferentiableAt.fun_sum fun κ _ => hd κ κ σ)
  rw [pd_sub e1 e2]
  congr 1
  · rw [pd_sum Finset.univ (f := fun σ y => ∑ ν, (g y)⁻¹ σ ν * dChristoffel g h ρ σ ν y)
      (fun σ _ => DifferentiableAt.fun_sum fun ν _ => (hinv σ ν).mul (hd ρ σ ν))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [pd_sum Finset.univ (f := fun ν y => (g y)⁻¹ σ ν * dChristoffel g h ρ σ ν y)
      (fun ν _ => (hinv σ ν).mul (hd ρ σ ν))]
    refine Finset.sum_congr rfl fun ν _ => ?_
    exact pd_mul (hinv σ ν) (hd ρ σ ν) ρ
  · rw [pd_sum Finset.univ (f := fun σ y => (g y)⁻¹ ρ σ * ∑ κ, dChristoffel g h κ κ σ y)
      (fun σ _ => (hinv ρ σ).mul (DifferentiableAt.fun_sum fun κ _ => hd κ κ σ))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [pd_mul (hinv ρ σ) (DifferentiableAt.fun_sum fun κ _ => hd κ κ σ),
      pd_sum Finset.univ (f := fun κ y => dChristoffel g h κ κ σ y) (fun κ _ => hd κ κ σ)]


include hgs hhs

/-- **The Palatini identity in coordinates**: `√|g| g^{σν} δR_{σν} = ∂_ρ (√|g| W^ρ)`. -/
theorem palatini_coord :
    √|(g x).det| * ∑ σ, ∑ ν, (g x)⁻¹ σ ν * dRicci g h x σ ν =
      ∑ ρ, pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x := by
  have hgd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b => ((hg a b).differentiable (by simp)) x
  have hd : ∀ i j k, DifferentiableAt ℝ (dChristoffel g h i j k) x :=
    fun i j k => (contDiffAt_dChristoffel g h x hg hh hx i j k).differentiableAt (by simp)
  have hinv : ∀ a b, DifferentiableAt ℝ (fun y => (g y)⁻¹ a b) x := fun a b => differentiableAt_inv_entry hgd hx a b
  have hdet : DifferentiableAt ℝ (fun y => (g y).det) x := differentiableAt_det_of hgd
  have hsq : DifferentiableAt ℝ (fun y => √|(g y).det|) x := (hdet.abs hx).sqrt (abs_ne_zero.2 hx)
  have hWd : ∀ ρ, DifferentiableAt ℝ (Wvec g h ρ) x := by
    intro ρ
    unfold Wvec
    exact (DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.fun_sum fun ν _ => (hinv σ ν).mul (hd ρ σ ν)).sub
      (DifferentiableAt.fun_sum fun σ _ => (hinv ρ σ).mul (DifferentiableAt.fun_sum fun κ _ => hd κ κ σ))
  -- the arrays
  set G : Fin n → Fin n → ℝ := fun a b => (g x)⁻¹ a b with hGdef
  set Γ : Fin n → Fin n → Fin n → ℝ := fun r a b => christoffel g r a b x with hΓdef
  set δ : Fin n → Fin n → Fin n → ℝ := fun r a b => dChristoffel g h r a b x with hδdef
  set dd : Fin n → Fin n → Fin n → Fin n → ℝ := fun m r a b => pd m (dChristoffel g h r a b) x with hdddef
  have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
    have : (g x)ᵀ = g x := by ext i j; exact hgs x j i
    rw [Matrix.transpose_nonsing_inv, this]
  have hG : ∀ a b, G a b = G b a := by
    intro a b
    simpa [hGdef, Matrix.transpose_apply] using (congrFun (congrFun hT a) b).symm
  have hΓ : ∀ r a b, Γ r a b = Γ r b a := fun r a b => christoffel_symm g hgs r a b x
  have hδ : ∀ r a b, δ r a b = δ r b a := fun r a b => dChristoffel_symm g h hgs hhs r a b x
  have hdd : ∀ m r a b, dd m r a b = dd m r b a := by
    intro m r a b
    simp only [hdddef]
    have : dChristoffel g h r a b = dChristoffel g h r b a := by
      funext y; exact dChristoffel_symm g h hgs hhs r a b y
    rw [this]
  have hDG : ∀ ρ σ ν, pd ρ (fun y => (g y)⁻¹ σ ν) x =
      -∑ α, (Γ σ ρ α * G α ν + Γ ν ρ α * G σ α) := fun ρ σ ν => pd_inv_eq g x hgs hgd hx ρ σ ν
  have hS : ∀ ρ, pd ρ (fun y => √|(g y).det|) x = √|(g x).det| * ∑ κ, Γ κ κ ρ :=
    fun ρ => pd_sqrt_abs_det g x hgs hgd hx ρ
  have pdd := palatini_dd G hG dd hdd
  have pnd := palatini_alg_nd G Γ δ hG hΓ hδ
  -- the right side
  have hR : ∑ ρ, pd ρ (fun y => √|(g y).det| * Wvec g h ρ y) x =
      √|(g x).det| * ∑ ρ, ((∑ κ, Γ κ κ ρ) * Wvec g h ρ x + pd ρ (Wvec g h ρ) x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [pd_mul hsq (hWd ρ), hS ρ]
    ring
  rw [hR]
  congr 1
  have hRic : ∀ σ ν, dRicci g h x σ ν = ((∑ ρ, dd ρ ρ ν σ) - ∑ ρ, dd ν ρ ρ σ) +
      ∑ ρ, ∑ κ, (δ ρ ρ κ * Γ κ ν σ + Γ ρ ρ κ * δ κ ν σ - δ ρ ν κ * Γ κ ρ σ - Γ ρ ν κ * δ κ ρ σ) := by
    intro σ ν
    unfold dRicci
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hdddef, hδdef, hΓdef]
  have hL : ∑ σ, ∑ ν, (g x)⁻¹ σ ν * dRicci g h x σ ν =
      (∑ σ, ∑ ν, G σ ν * ((∑ ρ, dd ρ ρ ν σ) - ∑ ρ, dd ν ρ ρ σ)) +
      ∑ σ, ∑ ν, G σ ν * ∑ ρ, ∑ κ, (δ ρ ρ κ * Γ κ ν σ + Γ ρ ρ κ * δ κ ν σ - δ ρ ν κ * Γ κ ρ σ - Γ ρ ν κ * δ κ ρ σ) := by
    simp only [hRic, mul_add, Finset.sum_add_distrib]
    rfl
  have hpd : ∀ ρ, pd ρ (Wvec g h ρ) x =
      (∑ σ, ∑ ν, ((-∑ α, (Γ σ ρ α * G α ν + Γ ν ρ α * G σ α)) * δ ρ σ ν + G σ ν * dd ρ ρ σ ν)) -
        ∑ σ, ((-∑ α, (Γ ρ ρ α * G α σ + Γ σ ρ α * G ρ α)) * ∑ κ, δ κ κ σ + G ρ σ * ∑ κ, dd ρ κ κ σ) := by
    intro ρ
    rw [pd_Wvec g h hg hh x hx ρ]
    simp only [hDG, hGdef, hδdef, hdddef]
  have hW : ∀ ρ, Wvec g h ρ x = (∑ σ, ∑ ν, G σ ν * δ ρ σ ν) - ∑ σ, G ρ σ * ∑ κ, δ κ κ σ := fun ρ => rfl
  rw [hL, pdd, pnd]
  simp only [hpd, hW, Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, mul_add]
  ring

end

end Lightlike
