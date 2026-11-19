import Lightlike.Spacetime.PalatiniCoord

/-!
# The Palatini vector as a first-order operator in the perturbation

`Wvec_split`: for symmetric `g⁻¹` and symmetric `h`,

`W^ρ = W₀^ρ + (g^{ρα} g^{μβ} - g^{ρμ} g^{αβ}) ∂_μ h_{αβ}`,

where `W₀^ρ` (`Wvec0`) is the part of `W^ρ` that contains only the values of `h` (through
`δΓ₀^ρ_{σν} = -½ (g⁻¹ h g⁻¹)^{ρλ} (∂_σ g_{λν} + ∂_ν g_{λσ} - ∂_λ g_{σν})`, `dChristoffel0`).

Supporting lemma for the second integration by parts in the `f(R)` variation; no catalogue entry.
-/

open Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The part of the variation of the Christoffel symbols that contains only the values of `h`. -/
def dChristoffel0 (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) (y : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ l, -((g y)⁻¹ * h y * (g y)⁻¹) i l *
    (pd j (fun z => g z l k) y + pd k (fun z => g z l j) y - pd l (fun z => g z j k) y)

/-- The part of the Palatini vector that contains only the values of `h`. -/
def Wvec0 (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (ρ : Fin n) (y : Fin n → ℝ) : ℝ :=
  (∑ σ, ∑ ν, (g y)⁻¹ σ ν * dChristoffel0 g h ρ σ ν y) -
    ∑ σ, (g y)⁻¹ ρ σ * ∑ κ, dChristoffel0 g h κ κ σ y

/-- The variation of the Christoffel symbols: values part plus derivative part. -/
lemma dChristoffel_eq_add (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n)
    (y : Fin n → ℝ) :
    dChristoffel g h i j k y = dChristoffel0 g h i j k y +
      (1 / 2) * ∑ l, (g y)⁻¹ i l *
        (pd j (fun z => h z l k) y + pd k (fun z => h z l j) y - pd l (fun z => h z j k) y) := by
  unfold dChristoffel dChristoffel0
  rw [← mul_add, ← Finset.sum_add_distrib]

/-- Reordering a triple sum: `(a, b, c) ↦ (b, c, a)`. -/
lemma sum3_rotate (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- Reordering a triple sum: swapping the last two indices. -/
lemma sum3_swap23 (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
  Finset.sum_congr rfl fun a _ => Finset.sum_comm

/-- Reordering a triple sum: swapping the first two indices. -/
lemma sum3_swap12 (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c :=
  Finset.sum_comm

/-- **The derivative part of the Palatini vector**, as an identity between sums: for symmetric `G` and `D`
symmetric in its last two indices. -/
lemma palatini_derivative_part (G : Fin n → Fin n → ℝ) (hG : ∀ a b, G a b = G b a)
    (D : Fin n → Fin n → Fin n → ℝ) (hD : ∀ μ a b, D μ a b = D μ b a) (ρ : Fin n) :
    (∑ σ, ∑ ν, G σ ν * ((1 / 2) * ∑ l, G ρ l * (D σ l ν + D ν l σ - D l σ ν))) -
        ∑ σ, G ρ σ * ∑ κ, (1 / 2) * ∑ l, G κ l * (D κ l σ + D σ l κ - D l κ σ) =
      ∑ μ, ∑ α, ∑ β, (G ρ α * G μ β - G ρ μ * G α β) * D μ α β := by
  -- the six sums in the index order `(μ, α, β)`
  have t1 : ∑ σ, ∑ ν, ∑ l, G σ ν * G ρ l * D σ l ν = ∑ μ, ∑ α, ∑ β, G ρ α * G μ β * D μ α β := by
    rw [sum3_swap23]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by ring
  have t2 : ∑ σ, ∑ ν, ∑ l, G σ ν * G ρ l * D ν l σ = ∑ μ, ∑ α, ∑ β, G ρ α * G μ β * D μ α β := by
    rw [sum3_rotate]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by rw [hG β μ]; ring
  have t3 : ∑ σ, ∑ ν, ∑ l, G σ ν * G ρ l * D l σ ν = ∑ μ, ∑ α, ∑ β, G ρ μ * G α β * D μ α β := by
    rw [sum3_rotate, sum3_rotate]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by ring
  have t4 : ∑ σ, ∑ κ, ∑ l, G ρ σ * G κ l * D κ l σ = ∑ μ, ∑ α, ∑ β, G ρ α * G μ β * D μ α β := by
    rw [sum3_swap12]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by rw [hD μ β α]
  have t5 : ∑ σ, ∑ κ, ∑ l, G ρ σ * G κ l * D σ l κ = ∑ μ, ∑ α, ∑ β, G ρ μ * G α β * D μ α β := by
    rw [sum3_swap23]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by rw [hG β α]
  have t6 : ∑ σ, ∑ κ, ∑ l, G ρ σ * G κ l * D l κ σ = ∑ μ, ∑ α, ∑ β, G ρ α * G μ β * D μ α β := by
    rw [sum3_rotate, sum3_rotate]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => by rw [hG β μ, hD μ β α]
  have hA : ∑ σ, ∑ ν, G σ ν * ((1 / 2) * ∑ l, G ρ l * (D σ l ν + D ν l σ - D l σ ν)) =
      (1 / 2) * ((∑ σ, ∑ ν, ∑ l, G σ ν * G ρ l * D σ l ν) +
        (∑ σ, ∑ ν, ∑ l, G σ ν * G ρ l * D ν l σ) - ∑ σ, ∑ ν, ∑ l, G σ ν * G ρ l * D l σ ν) := by
    have hterm : ∀ σ ν, G σ ν * ((1 / 2) * ∑ l, G ρ l * (D σ l ν + D ν l σ - D l σ ν)) =
        (1 / 2) * (∑ l, G σ ν * G ρ l * D σ l ν) + (1 / 2) * (∑ l, G σ ν * G ρ l * D ν l σ) -
          (1 / 2) * ∑ l, G σ ν * G ρ l * D l σ ν := by
      intro σ ν
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => hterm σ ν]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hB : ∑ σ, G ρ σ * ∑ κ, (1 / 2) * ∑ l, G κ l * (D κ l σ + D σ l κ - D l κ σ) =
      (1 / 2) * ((∑ σ, ∑ κ, ∑ l, G ρ σ * G κ l * D κ l σ) +
        (∑ σ, ∑ κ, ∑ l, G ρ σ * G κ l * D σ l κ) - ∑ σ, ∑ κ, ∑ l, G ρ σ * G κ l * D l κ σ) := by
    have hterm : ∀ σ, G ρ σ * ∑ κ, (1 / 2) * ∑ l, G κ l * (D κ l σ + D σ l κ - D l κ σ) =
        (1 / 2) * (∑ κ, ∑ l, G ρ σ * G κ l * D κ l σ) + (1 / 2) * (∑ κ, ∑ l, G ρ σ * G κ l * D σ l κ) -
          (1 / 2) * ∑ κ, ∑ l, G ρ σ * G κ l * D l κ σ := by
      intro σ
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.sum_congr rfl fun σ _ => hterm σ]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hR : ∑ μ, ∑ α, ∑ β, (G ρ α * G μ β - G ρ μ * G α β) * D μ α β =
      (∑ μ, ∑ α, ∑ β, G ρ α * G μ β * D μ α β) - ∑ μ, ∑ α, ∑ β, G ρ μ * G α β * D μ α β := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hA, hB, t1, t2, t3, t4, t5, t6, hR]
  ring

/-- **The Palatini vector as a first-order operator in the perturbation.** -/
theorem Wvec_split (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (hhs : ∀ y a b, h y a b = h y b a) (ρ : Fin n) :
    Wvec g h ρ x = Wvec0 g h ρ x +
      ∑ μ, ∑ α, ∑ β, ((g x)⁻¹ ρ α * (g x)⁻¹ μ β - (g x)⁻¹ ρ μ * (g x)⁻¹ α β) *
        pd μ (fun z => h z α β) x := by
  obtain ⟨G, hGdef⟩ : ∃ G : Fin n → Fin n → ℝ, ∀ a b, G a b = (g x)⁻¹ a b :=
    ⟨fun a b => (g x)⁻¹ a b, fun _ _ => rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : Fin n → Fin n → Fin n → ℝ,
      ∀ μ a b, D μ a b = pd μ (fun z => h z a b) x := ⟨fun μ a b => pd μ (fun z => h z a b) x,
    fun _ _ _ => rfl⟩
  have hGs : ∀ a b, G a b = G b a := fun a b => by rw [hGdef, hGdef, hinv a b]
  have hDs : ∀ μ a b, D μ a b = D μ b a := by
    intro μ a b
    have : (fun z => h z a b) = fun z => h z b a := funext fun z => hhs z a b
    rw [hDdef, hDdef, this]
  have key := palatini_derivative_part G hGs D hDs ρ
  unfold Wvec Wvec0
  simp only [dChristoffel_eq_add, mul_add, Finset.sum_add_distrib, ← hGdef, ← hDdef]
  linarith [key]

end Lightlike
