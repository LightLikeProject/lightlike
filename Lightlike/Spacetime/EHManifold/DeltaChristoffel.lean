import Lightlike.Spacetime.PalatiniCoord

/-!
# The variation of the Christoffel symbols is a tensor (M16, step 1)

`dChristoffel_eq_cov`: `δΓⁱ_{jk} = ½ gⁱˡ (∇ⱼ h_{lk} + ∇ₖ h_{lj} - ∇ₗ h_{jk})`, with `∇ⱼ h_{lk} = ∂ⱼ h_{lk} - Γᵐ_{jl} h_{mk} - Γᵐ_{jk} h_{lm}`
the covariant derivative of `h` for the Levi-Civita connection of `g` (`covH`). So the variation of the connection, and
with it the boundary vector of the variation of the Einstein–Hilbert action, is built from `∇h`.
-/

open Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The coordinate covariant derivative `∇ⱼ h_{lk} = ∂ⱼ h_{lk} - Γᵐ_{jl} h_{mk} - Γᵐ_{jk} h_{lm}`. -/
def covH (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (j l k : Fin n) (y : Fin n → ℝ) : ℝ :=
  pd j (fun z => h z l k) y - ∑ m, christoffel g m j l y * h y m k - ∑ m, christoffel g m j k y * h y l m

/-- **The variation of the Christoffel symbols in covariant form**. -/
theorem dChristoffel_eq_cov (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (hgs : ∀ z a b, g z a b = g z b a) (hhs : ∀ a b, h y a b = h y b a) (i j k : Fin n) :
    dChristoffel g h i j k y =
      (1 / 2) * ∑ l, (g y)⁻¹ i l * (covH g h j l k y + covH g h k l j y - covH g h l j k y) := by
  have hΓ : ∀ m a b, christoffel g m a b y = christoffel g m b a y := fun m a b => by
    unfold christoffel
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have : (fun z => g z a b) = fun z => g z b a := funext fun z => hgs z a b
    rw [this]; ring
  -- `½ Σ_l g^{bl} (∂ⱼ g_{lk} + ∂ₖ g_{lj} - ∂ₗ g_{jk}) = Γᵇ_{jk}`
  have hΓdef : ∀ b, (1 / 2) * ∑ l, (g y)⁻¹ b l *
      (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y) = christoffel g b j k y :=
    fun b => rfl
  unfold dChristoffel covH
  -- the Christoffel terms of the covariant derivatives combine to `-2 Γᵐ_{jk} h_{lm}`
  have hcomb : ∀ l, (pd j (fun z => h z l k) y - ∑ m, christoffel g m j l y * h y m k -
        ∑ m, christoffel g m j k y * h y l m) +
      (pd k (fun z => h z l j) y - ∑ m, christoffel g m k l y * h y m j - ∑ m, christoffel g m k j y * h y l m) -
      (pd l (fun z => h z j k) y - ∑ m, christoffel g m l j y * h y m k - ∑ m, christoffel g m l k y * h y j m) =
      (pd j (fun z => h z l k) y + pd k (fun z => h z l j) y - pd l (fun z => h z j k) y) -
        2 * ∑ m, christoffel g m j k y * h y l m := by
    intro l
    have e1 : ∑ m, christoffel g m j l y * h y m k = ∑ m, christoffel g m l j y * h y m k :=
      Finset.sum_congr rfl fun m _ => by rw [hΓ m j l]
    have e2 : ∑ m, christoffel g m k l y * h y m j = ∑ m, christoffel g m l k y * h y j m :=
      Finset.sum_congr rfl fun m _ => by rw [hΓ m k l, hhs m j]
    have e3 : ∑ m, christoffel g m k j y * h y l m = ∑ m, christoffel g m j k y * h y l m :=
      Finset.sum_congr rfl fun m _ => by rw [hΓ m k j]
    rw [e1, e2, e3]; ring
  simp only [hcomb]
  have hinv : ∀ l, ((g y)⁻¹ * h y * (g y)⁻¹) i l = ∑ a, ∑ b, (g y)⁻¹ i a * h y a b * (g y)⁻¹ b l := by
    intro l
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have h2Γ : ∀ b, ∑ l, (g y)⁻¹ b l *
      (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y) = 2 * christoffel g b j k y :=
    fun b => by rw [← hΓdef b]; ring
  have hkey : ∑ l, ((g y)⁻¹ * h y * (g y)⁻¹) i l *
      (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y) =
      2 * ∑ l, (g y)⁻¹ i l * ∑ m, christoffel g m j k y * h y l m := by
    calc ∑ l, ((g y)⁻¹ * h y * (g y)⁻¹) i l *
          (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y)
        = ∑ a, ∑ b, (g y)⁻¹ i a * h y a b * ∑ l, (g y)⁻¹ b l *
            (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y) := by
          simp only [hinv, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 2 * ∑ l, (g y)⁻¹ i l * ∑ m, christoffel g m j k y * h y l m := by
          simp only [h2Γ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hL : ∑ l, (-((g y)⁻¹ * h y * (g y)⁻¹) i l *
        (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y) +
      (g y)⁻¹ i l * (pd j (fun z => h z l k) y + pd k (fun z => h z l j) y - pd l (fun z => h z j k) y)) =
      -(2 * ∑ l, (g y)⁻¹ i l * ∑ m, christoffel g m j k y * h y l m) +
        ∑ l, (g y)⁻¹ i l * (pd j (fun z => h z l k) y + pd k (fun z => h z l j) y - pd l (fun z => h z j k) y) := by
    rw [Finset.sum_add_distrib, ← hkey, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hL]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [← Finset.mul_sum]
  ring_nf
  rw [← Finset.sum_mul]
  ring

/-- **The boundary vector of the variation in covariant form**:
`W^ρ = g^{σν} δΓ^ρ_{σν} - g^{ρσ} δΓ^κ_{κσ} = g^{ρl} g^{σν} (∇_σ h_{lν} - ∇_l h_{σν})`, i.e. `div h♯ - grad (tr_g h)`. -/
theorem Wvec_eq_cov (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)
    (hgs : ∀ z a b, g z a b = g z b a) (hhs : ∀ z a b, h z a b = h z b a) (ρ : Fin n) :
    Wvec g h ρ y = ∑ l, (g y)⁻¹ ρ l * ∑ σ, ∑ ν, (g y)⁻¹ σ ν * (covH g h σ l ν y - covH g h l σ ν y) := by
  have hGi : ∀ a b, (g y)⁻¹ a b = (g y)⁻¹ b a := fun a b => by
    have : ((g y)⁻¹)ᵀ = (g y)⁻¹ := by
      rw [transpose_nonsing_inv]
      congr 1
      ext i j; exact hgs y j i
    conv_rhs => rw [← this]
    rfl
  have hcs : ∀ a b c, covH g h a b c y = covH g h a c b y := fun a b c => by
    unfold covH
    have : (fun z => h z b c) = fun z => h z c b := funext fun z => hhs z b c
    have e1 : ∑ m, christoffel g m a b y * h y m c = ∑ m, christoffel g m a b y * h y c m :=
      Finset.sum_congr rfl fun m _ => by rw [hhs y m c]
    have e2 : ∑ m, christoffel g m a c y * h y b m = ∑ m, christoffel g m a c y * h y m b :=
      Finset.sum_congr rfl fun m _ => by rw [hhs y b m]
    rw [this, e1, e2]; ring
  unfold Wvec
  simp only [dChristoffel_eq_cov g h y hgs (fun a b => hhs y a b)]
  -- the first part
  have hA : ∀ l, ∑ σ, ∑ ν, (g y)⁻¹ σ ν * covH g h ν l σ y = ∑ σ, ∑ ν, (g y)⁻¹ σ ν * covH g h σ l ν y := by
    intro l
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [hGi]
  have h1 : ∑ σ, ∑ ν, (g y)⁻¹ σ ν *
      (1 / 2 * ∑ l, (g y)⁻¹ ρ l * (covH g h σ l ν y + covH g h ν l σ y - covH g h l σ ν y)) =
      ∑ l, (g y)⁻¹ ρ l * (∑ σ, ∑ ν, (g y)⁻¹ σ ν * covH g h σ l ν y -
        1 / 2 * ∑ σ, ∑ ν, (g y)⁻¹ σ ν * covH g h l σ ν y) := by
    have e : ∀ l, ∑ σ, ∑ ν, (g y)⁻¹ σ ν * covH g h σ l ν y -
        1 / 2 * ∑ σ, ∑ ν, (g y)⁻¹ σ ν * covH g h l σ ν y =
        ∑ σ, ∑ ν, 1 / 2 * ((g y)⁻¹ σ ν * (covH g h σ l ν y + covH g h ν l σ y - covH g h l σ ν y)) := by
      intro l
      have := hA l
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at this ⊢
      rw [this]; ring
    calc ∑ σ, ∑ ν, (g y)⁻¹ σ ν *
          (1 / 2 * ∑ l, (g y)⁻¹ ρ l * (covH g h σ l ν y + covH g h ν l σ y - covH g h l σ ν y))
        = ∑ σ, ∑ ν, ∑ l, (g y)⁻¹ ρ l * (1 / 2 * ((g y)⁻¹ σ ν *
            (covH g h σ l ν y + covH g h ν l σ y - covH g h l σ ν y))) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
            ring
      _ = ∑ σ, ∑ l, ∑ ν, (g y)⁻¹ ρ l * (1 / 2 * ((g y)⁻¹ σ ν *
            (covH g h σ l ν y + covH g h ν l σ y - covH g h l σ ν y))) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ σ, ∑ ν, (g y)⁻¹ ρ l * (1 / 2 * ((g y)⁻¹ σ ν *
            (covH g h σ l ν y + covH g h ν l σ y - covH g h l σ ν y))) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [e l, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by rw [Finset.mul_sum]
  -- the second part
  have hB : ∀ σ, ∑ κ, 1 / 2 * ∑ l, (g y)⁻¹ κ l * (covH g h κ l σ y + covH g h σ l κ y - covH g h l κ σ y) =
      1 / 2 * ∑ κ, ∑ l, (g y)⁻¹ κ l * covH g h σ l κ y := by
    intro σ
    have e : ∑ κ, ∑ l, (g y)⁻¹ κ l * covH g h l κ σ y = ∑ κ, ∑ l, (g y)⁻¹ κ l * covH g h κ l σ y := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [hGi]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e]
    ring
  simp only [hB]
  rw [h1, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e2 : ∑ κ, ∑ l', (g y)⁻¹ κ l' * covH g h l l' κ y = ∑ σ, ∑ ν, (g y)⁻¹ σ ν * covH g h l σ ν y :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [hcs]
  rw [e2, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf
  simp only [← Finset.sum_mul]
  ring

end Lightlike
