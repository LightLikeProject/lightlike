import Mathlib

/-!
# The covariant Jacobi identity at a point (G1-012, step D3b, algebra)

With Christoffel symbols `Γ a b c` (symmetric in `b c`), their derivatives `dΓ d a b c` (symmetric in
`b c`) and the Riemann tensor built from them as in `Lightlike.riemann`, the covariant second derivative
`D²J` of a vector `J` along a geodesic `v` (`v' = -Γ(v, v)`) is the coordinate linearised geodesic
operator minus the tidal term: `D²J = E₁ - R(v, J, v)`.
-/

open Finset

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ}

/-- The Riemann tensor from the symbols: `R^a_{σ μ ν} = ∂_μ Γ^a_{νσ} - ∂_ν Γ^a_{μσ} + Γ^a_{μ l} Γ^l_{νσ} - Γ^a_{ν l} Γ^l_{μσ}`. -/
def riemS (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (a σ μ ν : Fin n) : ℝ :=
  dG μ a ν σ - dG ν a μ σ + ∑ l, (G a μ l * G l ν σ - G a ν l * G l μ σ)

/-- The tidal term `R^a_{σ γ δ} vσ Jγ vδ`. -/
def tidal (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (v J : Fin n → ℝ) (a : Fin n) : ℝ :=
  ∑ σ, ∑ γ, ∑ δ, riemS G dG a σ γ δ * v σ * J γ * v δ

/-- `D J = J' + Γ(v, J)`. -/
def covD1 (G : Fin n → Fin n → Fin n → ℝ) (v J J1 : Fin n → ℝ) (a : Fin n) : ℝ :=
  J1 a + ∑ b, ∑ c, G a b c * v b * J c

/-- `D D J`, with `v' = -Γ(v,v)` and `J'' = J2`. -/
def covD2 (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (v J J1 J2 : Fin n → ℝ) (a : Fin n) : ℝ :=
  (J2 a + ∑ d, ∑ b, ∑ c, dG d a b c * v d * v b * J c +
      ∑ b, ∑ c, G a b c * (-(∑ d, ∑ e, G b d e * v d * v e)) * J c +
      ∑ b, ∑ c, G a b c * v b * J1 c) +
    ∑ b, ∑ c, G a b c * v b * covD1 G v J J1 c

/-- The linearised geodesic operator `J'' + 2Γ(v, J') + ∂_dΓ J^d v v`. -/
def linGeo (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (v J J1 J2 : Fin n → ℝ) (a : Fin n) : ℝ :=
  J2 a + 2 * ∑ b, ∑ c, G a b c * v b * J1 c + ∑ d, ∑ b, ∑ c, dG d a b c * J d * v b * v c

/-- Reordering of a triple sum `Σσ Σγ Σδ f σ γ δ = Σγ Σδ Σσ f σ γ δ`. -/
theorem sum3_rot (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ σ, ∑ γ, ∑ δ, f σ γ δ = ∑ γ, ∑ δ, ∑ σ, f σ γ δ := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]

theorem sum3_swap12 (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm

theorem sum3_swap23 (f : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
  Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem tidal_h2 (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hdG : ∀ d a b c, dG d a b c = dG d a c b) (v J : Fin n → ℝ) (a : Fin n) :
    ∑ σ, ∑ γ, ∑ δ, dG δ a γ σ * v σ * J γ * v δ =
      ∑ d, ∑ b, ∑ c, dG d a b c * v d * v b * J c := by
  rw [sum3_rot, sum3_rot]
  exact Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun γ _ => by rw [hdG δ a γ σ]; ring

theorem tidal_h3 (G : Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b c, G a b c = G a c b)
    (v J : Fin n → ℝ) (a : Fin n) :
    ∑ σ, ∑ γ, ∑ δ, (∑ l, G a γ l * G l δ σ) * v σ * J γ * v δ =
      ∑ b, ∑ c, G a b c * (∑ d, ∑ e, G b d e * v d * v e) * J c := by
  -- push the sum over `l` out
  have h : ∀ σ γ δ, (∑ l, G a γ l * G l δ σ) * v σ * J γ * v δ =
      ∑ l, G a γ l * G l δ σ * v σ * J γ * v δ := fun σ γ δ => by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  simp only [h]
  -- reorder to `Σ γ Σ l Σ δ Σ σ`
  calc ∑ σ, ∑ γ, ∑ δ, ∑ l, G a γ l * G l δ σ * v σ * J γ * v δ
      = ∑ γ, ∑ σ, ∑ δ, ∑ l, G a γ l * G l δ σ * v σ * J γ * v δ := Finset.sum_comm
    _ = ∑ γ, ∑ l, ∑ σ, ∑ δ, G a γ l * G l δ σ * v σ * J γ * v δ := by
        refine Finset.sum_congr rfl fun γ _ => ?_
        calc ∑ σ, ∑ δ, ∑ l, G a γ l * G l δ σ * v σ * J γ * v δ
            = ∑ σ, ∑ l, ∑ δ, G a γ l * G l δ σ * v σ * J γ * v δ :=
              Finset.sum_congr rfl fun σ _ => Finset.sum_comm
          _ = ∑ l, ∑ σ, ∑ δ, G a γ l * G l δ σ * v σ * J γ * v δ := Finset.sum_comm
    _ = ∑ l, ∑ γ, ∑ σ, ∑ δ, G a γ l * G l δ σ * v σ * J γ * v δ := Finset.sum_comm
    _ = ∑ b, ∑ c, G a b c * (∑ d, ∑ e, G b d e * v d * v e) * J c := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun γ _ => ?_
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        rw [hG a γ l]; ring

theorem tidal_h4 (G : Fin n → Fin n → Fin n → ℝ) (hG : ∀ a b c, G a b c = G a c b)
    (v J : Fin n → ℝ) (a : Fin n) :
    ∑ σ, ∑ γ, ∑ δ, (∑ l, G a δ l * G l γ σ) * v σ * J γ * v δ =
      ∑ b, ∑ c, G a b c * v b * (∑ d, ∑ e, G c d e * v d * J e) := by
  have h : ∀ σ γ δ, (∑ l, G a δ l * G l γ σ) * v σ * J γ * v δ =
      ∑ l, G a δ l * G l γ σ * v σ * J γ * v δ := fun σ γ δ => by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  simp only [h]
  rw [sum3_rot, sum3_rot]
  refine Finset.sum_congr rfl fun δ _ => ?_
  calc ∑ σ, ∑ γ, ∑ l, G a δ l * G l γ σ * v σ * J γ * v δ
      = ∑ σ, ∑ l, ∑ γ, G a δ l * G l γ σ * v σ * J γ * v δ :=
        Finset.sum_congr rfl fun σ _ => Finset.sum_comm
    _ = ∑ l, ∑ σ, ∑ γ, G a δ l * G l γ σ * v σ * J γ * v δ := Finset.sum_comm
    _ = ∑ c, G a δ c * v δ * (∑ d, ∑ e, G c d e * v d * J e) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun γ _ => ?_
        rw [hG l γ σ]; ring

theorem tidal_eq (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b c, G a b c = G a c b) (hdG : ∀ d a b c, dG d a b c = dG d a c b)
    (v J : Fin n → ℝ) (a : Fin n) :
    tidal G dG v J a =
      (∑ d, ∑ b, ∑ c, dG d a b c * J d * v b * v c) -
        (∑ d, ∑ b, ∑ c, dG d a b c * v d * v b * J c) +
      (∑ b, ∑ c, G a b c * (∑ d, ∑ e, G b d e * v d * v e) * J c) -
        (∑ b, ∑ c, G a b c * v b * (∑ d, ∑ e, G c d e * v d * J e)) := by
  have T1 : ∑ σ, ∑ γ, ∑ δ, dG γ a δ σ * v σ * J γ * v δ =
      ∑ d, ∑ b, ∑ c, dG d a b c * J d * v b * v c := by
    rw [sum3_rot]
    exact Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun δ _ =>
      Finset.sum_congr rfl fun σ _ => by ring
  have T2 := tidal_h2 dG hdG v J a
  have T3 := tidal_h3 G hG v J a
  have T4 := tidal_h4 G hG v J a
  unfold tidal riemS
  have hsplit : ∀ σ γ δ,
      (dG γ a δ σ - dG δ a γ σ + ∑ l, (G a γ l * G l δ σ - G a δ l * G l γ σ)) * v σ * J γ * v δ =
        dG γ a δ σ * v σ * J γ * v δ - dG δ a γ σ * v σ * J γ * v δ +
          ((∑ l, G a γ l * G l δ σ) * v σ * J γ * v δ -
            (∑ l, G a δ l * G l γ σ) * v σ * J γ * v δ) := fun σ γ δ => by
    rw [Finset.sum_sub_distrib]; ring
  have hall : ∑ σ, ∑ γ, ∑ δ,
      (dG γ a δ σ - dG δ a γ σ + ∑ l, (G a γ l * G l δ σ - G a δ l * G l γ σ)) * v σ * J γ * v δ =
      (∑ σ, ∑ γ, ∑ δ, dG γ a δ σ * v σ * J γ * v δ) -
        (∑ σ, ∑ γ, ∑ δ, dG δ a γ σ * v σ * J γ * v δ) +
      ((∑ σ, ∑ γ, ∑ δ, (∑ l, G a γ l * G l δ σ) * v σ * J γ * v δ) -
        (∑ σ, ∑ γ, ∑ δ, (∑ l, G a δ l * G l γ σ) * v σ * J γ * v δ)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun δ _ => hsplit σ γ δ
  rw [hall, T1, T2, T3, T4]
  ring

theorem covD2_eq (G : Fin n → Fin n → Fin n → ℝ) (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hG : ∀ a b c, G a b c = G a c b) (hdG : ∀ d a b c, dG d a b c = dG d a c b)
    (v J J1 J2 : Fin n → ℝ) (a : Fin n) :
    covD2 G dG v J J1 J2 a = linGeo G dG v J J1 J2 a - tidal G dG v J a := by
  rw [tidal_eq G dG hG hdG]
  unfold covD2 linGeo covD1
  have e1 : ∑ b, ∑ c, G a b c * (-(∑ d, ∑ e, G b d e * v d * v e)) * J c =
      -(∑ b, ∑ c, G a b c * (∑ d, ∑ e, G b d e * v d * v e) * J c) := by
    simp only [mul_neg, neg_mul, Finset.sum_neg_distrib]
  have e2 : ∑ b, ∑ c, G a b c * v b * (J1 c + ∑ d, ∑ e, G c d e * v d * J e) =
      (∑ b, ∑ c, G a b c * v b * J1 c) + ∑ b, ∑ c, G a b c * v b * (∑ d, ∑ e, G c d e * v d * J e) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [e1, e2]
  ring

end Lightlike.Penrose
